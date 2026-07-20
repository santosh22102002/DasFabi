"""
Mendikot (Hukum-style trump reveal) - single-file FastAPI app.

No login, no database, no persistence beyond process memory.
Rooms are ephemeral, held in RAM, and garbage-collected after inactivity.

Run:
    pip install fastapi "uvicorn[standard]" --break-system-packages
    python3 main.py
    (or: uvicorn main:app --host 0.0.0.0 --port 8000)

Then open http://localhost:8000 in up to 4 browser tabs/devices.
"""

import asyncio
import json
import random
import string
import time
import uuid
from dataclasses import dataclass, field
from enum import Enum
from typing import Optional

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse

"""
Mendikot game engine - pure logic, no I/O.
Rules implemented (as specified):
- 4 players, seats 0-3. Teams: {0,2} vs {1,3}.
- Deal 5 cards each first (20 dealt, 32 in boot).
- Play tricks. First player unable to follow suit MUST reveal a trump
  card from hand (their choice). Revealing is a single action that:
  locks the trump suit, immediately plays that same card into the
  current trick (possibly completing it), and only THEN deals all
  remaining boot cards (32, 8 per seat) to everyone. There is no
  separate follow-up tap to "play" the revealed card - the reveal IS
  the play.
- If all first 5 tricks complete with everyone following suit (nobody
  ever revealed), the hand has NO TRUMP for its entirety, and the
  remaining 32 cards are dealt only after that 5th trick finishes.
- Winner of trick leads next.
- Must follow suit if able. If void: may play trump (if revealed) or
  any card. If trump never revealed, may play any card when void.
- Mendi = the four 10s. Team with more Mendi wins (4-0 or 3-1).
  2-2 is a draw, broken by total cards won.
"""


SUITS = ["S", "H", "D", "C"]  # Spades, Hearts, Diamonds, Clubs
RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"]
RANK_VALUE = {r: i for i, r in enumerate(RANKS)}

SUIT_SYMBOL = {"S": "\u2660", "H": "\u2665", "D": "\u2666", "C": "\u2663"}


class Phase(str, Enum):
    LOBBY = "LOBBY"
    PHASE1_PLAY = "PHASE1_PLAY"          # first 5 tricks
    AWAITING_TRUMP_REVEAL = "AWAITING_TRUMP_REVEAL"  # blocked on one player's choice
    PHASE2_PLAY = "PHASE2_PLAY"          # remaining 8 tricks
    HAND_COMPLETE = "HAND_COMPLETE"


def make_deck():
    return [f"{r}{s}" for s in SUITS for r in RANKS]


def card_rank(card: str) -> str:
    return card[:-1]


def card_suit(card: str) -> str:
    return card[-1]


class Card:
    """Helper for parsing/formatting; cards are stored as plain strings e.g. '10H', 'AS'."""
    pass


class MendikotHand:
    """
    Represents a single hand (deal) of Mendikot for one room.
    Seats 0-3. Teams: team A = {0,2}, team B = {1,3}.
    """

    def __init__(self, dealer_seat: int = 0, rng: Optional[random.Random] = None):
        self.rng = rng or random.Random()
        self.dealer_seat = dealer_seat
        deck = make_deck()
        self.rng.shuffle(deck)

        # Deal 5 cards to each seat first, then keep remaining 32 as "boot"
        self.hands = {s: [] for s in range(4)}
        for i in range(5):
            for s in range(4):
                self.hands[s].append(deck.pop())
        self.boot = deck  # 32 cards remaining, to be dealt after phase 1

        self.phase = Phase.PHASE1_PLAY
        self.trump_suit: Optional[str] = None
        self.trump_revealed_card: Optional[str] = None
        self.trump_revealer_seat: Optional[int] = None

        self.current_trick: list[dict] = []  # [{seat, card}]
        self.led_suit: Optional[str] = None
        self.turn_seat = (dealer_seat + 1) % 4  # player left of dealer leads first
        self.leader_seat = self.turn_seat

        self.tricks_played = 0
        self.trick_history: list[dict] = []  # completed tricks: {cards, winner_seat, mendi_count}

        self.mendi_won = {0: 0, 1: 0, 2: 0, 3: 0}  # mendi count per seat (aggregate by team later)
        self.mendi_suits_won = {0: [], 1: [], 2: [], 3: []}  # which ten-suits each seat has won

        # Total cards won per seat (4 per trick)
        self.cards_won = {0: 0, 1: 0, 2: 0, 3: 0}

        # tracks whether we're still in the "watch for void" sub-phase
        self.awaiting_reveal_from: Optional[int] = None
        self.pending_void_card: Optional[str] = None  # the card that triggered the reveal requirement

        # If a mid-trick deal happens (trump revealed mid-trick), any seat that
        # was already known to be void in the led suit at that moment stays
        # exempt from follow-suit for the REST of that specific trick, even if
        # their newly dealt cards happen to include the led suit. Cleared
        # whenever a new trick starts.
        self.trick_void_exempt_seats: set[int] = set()

        # True from the moment trump is revealed until the boot cards have
        # actually been dealt. The reveal happens mid-trick, but the boot deal
        # itself is deferred until the CURRENT trick finishes (all 4 plays in),
        # so opponents can't infer anything about the newly dealt cards from
        # watching mid-trick.
        self.boot_deal_pending: bool = False

        self.winner_team: Optional[str] = None  # "A", "B", or "DRAW"
        self.final_mendi: Optional[dict] = None  # {"A": n, "B": n}
        self.final_cards: Optional[dict] = None  # {"A": n, "B": n}

    # ---------- helpers ----------

    def team_of(self, seat: int) -> str:
        return "A" if seat in (0, 2) else "B"

    def legal_moves(self, seat: int) -> list[str]:
        hand = self.hands[seat]
        if not self.current_trick:
            return list(hand)  # leading, any card legal
        if seat in self.trick_void_exempt_seats:
            return list(hand)  # locked-in void status for this trick, any card legal
        led = self.led_suit
        same_suit = [c for c in hand if card_suit(c) == led]
        if same_suit:
            return same_suit
        # void in led suit: any card is legal (including trump if revealed)
        return list(hand)

    def must_reveal_trump(self, seat: int, card_being_played_suit_check: bool) -> bool:
        """True if this seat, being void in led suit during phase 1 pre-reveal, must reveal."""
        return (
            self.phase == Phase.PHASE1_PLAY
            and self.trump_suit is None
            and self.current_trick
            and card_being_played_suit_check
        )

    # ---------- actions ----------

    def play_card(self, seat: int, card: str) -> dict:
        """
        Attempt to play `card` for `seat`. Returns an event dict describing what happened.
        Raises ValueError on illegal move.
        """
        if self.phase not in (Phase.PHASE1_PLAY, Phase.PHASE2_PLAY):
            raise ValueError("Not in a playable phase")
        if seat != self.turn_seat:
            raise ValueError("Not your turn")
        if card not in self.hands[seat]:
            raise ValueError("Card not in hand")

        hand = self.hands[seat]
        is_leading = not self.current_trick

        if not is_leading and seat not in self.trick_void_exempt_seats:
            led = self.led_suit
            has_led_suit = any(card_suit(c) == led for c in hand)
            if has_led_suit and card_suit(card) != led:
                raise ValueError(f"Must follow suit ({led})")

            # If void in led suit during phase 1 pre-reveal -> must reveal trump instead of playing
            if (
                not has_led_suit
                and self.phase == Phase.PHASE1_PLAY
                and self.trump_suit is None
            ):
                raise ValueError("VOID_MUST_REVEAL_TRUMP")

        # legal - commit the play
        hand.remove(card)
        self.current_trick.append({"seat": seat, "card": card})
        if is_leading:
            self.led_suit = card_suit(card)

        result = {"type": "card_played", "seat": seat, "card": card}

        if len(self.current_trick) == 4:
            trick_result = self._resolve_trick()
            result["trick_result"] = trick_result
        else:
            self.turn_seat = (self.turn_seat + 1) % 4

        return result

    def reveal_trump(self, seat: int, card: str) -> dict:
        """
        Player reveals a trump card from hand (their own choice) when void in
        led suit. This single action: (1) locks the trump suit, (2) immediately
        plays that same card into the current trick - possibly completing the
        trick. The boot cards are NOT dealt here - dealing is deferred until
        the current trick actually finishes (see _resolve_trick), so that
        opponents watching the rest of this trick play out can't use the
        timing of the deal to infer anything about what's in other hands.
        """
        if self.phase != Phase.PHASE1_PLAY or self.trump_suit is not None:
            raise ValueError("Trump reveal not applicable")
        if seat != self.turn_seat:
            raise ValueError("Not your turn")
        hand = self.hands[seat]
        if card not in hand:
            raise ValueError("Card not in hand")
        if not self.current_trick:
            # Reveal is only ever triggered by being void when following, never
            # while leading a trick.
            raise ValueError("Cannot reveal trump while leading a trick")

        led = self.led_suit
        has_led_suit = any(card_suit(c) == led for c in hand)
        if has_led_suit:
            raise ValueError("You can follow suit, cannot reveal trump")

        # Step 1: lock the trump suit. Phase flips to PHASE2_PLAY immediately
        # so normal follow-suit/trump-beats rules apply to the rest of this
        # trick - but the boot deal itself is deferred (see boot_deal_pending).
        self.trump_suit = card_suit(card)
        self.trump_revealed_card = card
        self.trump_revealer_seat = seat
        self.phase = Phase.PHASE2_PLAY
        self.boot_deal_pending = True

        # This seat's void-in-led-suit status is locked in for the rest of
        # THIS trick: even after receiving new boot cards that might include
        # the led suit, they remain exempt from follow-suit for this trick.
        self.trick_void_exempt_seats.add(seat)

        # Step 2: immediately play the revealed card into the current trick.
        hand.remove(card)
        self.current_trick.append({"seat": seat, "card": card})

        result = {
            "type": "trump_revealed",
            "seat": seat,
            "card": card,
            "trump_suit": self.trump_suit,
        }

        if len(self.current_trick) == 4:
            # This reveal happened to be the trick's 4th card - resolve now.
            # _resolve_trick() will see boot_deal_pending and deal there.
            trick_result = self._resolve_trick()
            result["trick_result"] = trick_result
        else:
            self.turn_seat = (self.turn_seat + 1) % 4

        return result

    def _resolve_trick(self) -> dict:
        winner_seat = self._trick_winner()
        cards_in_trick = [p["card"] for p in self.current_trick]
        mendi_cards = [c for c in cards_in_trick if card_rank(c) == "10"]
        if mendi_cards:
            self.mendi_won[winner_seat] += len(mendi_cards)
            for c in mendi_cards:
                self.mendi_suits_won[winner_seat].append(card_suit(c))

        # Track total cards won
        self.cards_won[winner_seat] += 4

        self.trick_history.append({
            "cards": list(self.current_trick),
            "winner_seat": winner_seat,
            "mendi_count": len(mendi_cards),
        })

        self.tricks_played += 1
        self.current_trick = []
        self.led_suit = None
        self.turn_seat = winner_seat
        self.leader_seat = winner_seat
        self.trick_void_exempt_seats = set()  # exemptions only apply within one trick

        trick_summary = {
            "winner_seat": winner_seat,
            "mendi_count": len(mendi_cards),
        }

        if self.boot_deal_pending:
            # Trump was revealed at some point during this trick; the deal was
            # deferred until now, so it happens only once the trick is fully
            # finished (all 4 plays visible) rather than mid-trick.
            self.boot_deal_pending = False
            self._deal_phase2()
            trick_summary["phase2_dealt"] = True
        elif self.phase == Phase.PHASE1_PLAY and self.tricks_played == 5:
            # Trump was NEVER revealed during the first 5 tricks -> no trump
            # for the rest of the hand, and boot is dealt now regardless.
            trick_summary["no_trump_locked"] = True
            self._deal_phase2()
            self.phase = Phase.PHASE2_PLAY
            trick_summary["phase2_dealt"] = True

        if self.tricks_played == 13:
            self._finalize_hand()
            trick_summary["hand_complete"] = True

        return trick_summary

    def _trick_winner(self) -> int:
        led = self.led_suit
        trump = self.trump_suit

        def strength(play):
            c = play["card"]
            suit = card_suit(c)
            rank = RANK_VALUE[card_rank(c)]
            if trump and suit == trump:
                return (2, rank)  # trump beats everything
            if suit == led:
                return (1, rank)
            return (0, rank)  # can't win

        best = max(self.current_trick, key=strength)
        return best["seat"]

    def _deal_phase2(self):
        # boot has 32 cards, deal 8 to each seat
        for s in range(4):
            self.hands[s].extend(self.boot[s * 8:(s + 1) * 8])
        self.boot = []

    def _finalize_hand(self):
        self.phase = Phase.HAND_COMPLETE
        team_mendi = {"A": 0, "B": 0}
        team_cards = {"A": 0, "B": 0}
        for seat, count in self.mendi_won.items():
            team_mendi[self.team_of(seat)] += count
        for seat, count in self.cards_won.items():
            team_cards[self.team_of(seat)] += count
        self.final_mendi = team_mendi
        self.final_cards = team_cards

        if team_mendi["A"] == team_mendi["B"]:
            # Tiebreaker: total cards won
            if team_cards["A"] == team_cards["B"]:
                self.winner_team = "DRAW"
            elif team_cards["A"] > team_cards["B"]:
                self.winner_team = "A"
            else:
                self.winner_team = "B"
        elif team_mendi["A"] > team_mendi["B"]:
            self.winner_team = "A"
        else:
            self.winner_team = "B"

    # ---------- serialization for clients ----------

    def public_state(self, viewer_seat: Optional[int] = None) -> dict:
        """State safe to send to a client: own hand only, everything else public."""
        state = {
            "phase": self.phase.value,
            "trump_suit": self.trump_suit,
            "trump_revealed_card": self.trump_revealed_card,
            "trump_revealer_seat": self.trump_revealer_seat,
            "current_trick": list(self.current_trick),
            "led_suit": self.led_suit,
            "turn_seat": self.turn_seat,
            "tricks_played": self.tricks_played,
            "mendi_won": dict(self.mendi_won),
            "mendi_suits_won": {s: list(v) for s, v in self.mendi_suits_won.items()},
            "cards_won": dict(self.cards_won),
            "hand_sizes": {s: len(h) for s, h in self.hands.items()},
            "trick_void_exempt_seats": sorted(self.trick_void_exempt_seats),
        }
        if viewer_seat is not None:
            state["your_hand"] = sorted(
                self.hands[viewer_seat],
                key=lambda c: (card_suit(c), RANK_VALUE[card_rank(c)]),
            )
            state["your_seat"] = viewer_seat
        if self.phase == Phase.HAND_COMPLETE:
            state["winner_team"] = self.winner_team
            state["final_mendi"] = self.final_mendi
            state["final_cards"] = self.final_cards
        return state


"""Room management: lobby state, team-based seating, connection tracking, GC of stale rooms."""



ROOM_CODE_CHARS = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"  # no 0/O/I/1 ambiguity
ROOM_TTL_SECONDS = 10 * 60  # GC empty/stale rooms after 10 min

TEAM_SEATS = {"A": (0, 2), "B": (1, 3)}


def gen_room_code(existing: set[str], length: int = 5) -> str:
    while True:
        code = "".join(random.choices(ROOM_CODE_CHARS, k=length))
        if code not in existing:
            return code


@dataclass
class Player:
    player_id: str
    name: str
    seat: int
    ws: Optional[WebSocket] = None
    connected: bool = True
    is_bot: bool = False


@dataclass
class Room:
    code: str
    players: dict[int, Player] = field(default_factory=dict)  # seat -> Player
    hand: Optional[MendikotHand] = None
    dealer_seat: int = 0
    created_at: float = field(default_factory=time.time)
    last_active: float = field(default_factory=time.time)
    locked_until: float = 0.0  # monotonic time; no new plays accepted before this
    cancelled: bool = False  # set once any player explicitly exits, or host leaves
    solo: bool = False

    def touch(self):
        self.last_active = time.time()

    def lock_for(self, seconds: float):
        self.locked_until = time.monotonic() + seconds

    def is_locked(self) -> bool:
        return time.monotonic() < self.locked_until

    def is_full(self) -> bool:
        return len(self.players) == 4

    def team_of(self, seat: int) -> str:
        return "A" if seat in TEAM_SEATS["A"] else "B"

    def open_seat_for_team(self, team: str) -> Optional[int]:
        for s in TEAM_SEATS.get(team, ()):
            if s not in self.players:
                return s
        return None

    def team_is_full(self, team: str) -> bool:
        return self.open_seat_for_team(team) is None

    def lobby_state(self) -> dict:
        return {
            "type": "room_update",
            "room_code": self.code,
            "seats": {
                str(s): {
                    "name": p.name,
                    "connected": p.connected,
                    "team": self.team_of(s),
                }
                for s, p in self.players.items()
            },
            "team_full": {
                "A": self.team_is_full("A"),
                "B": self.team_is_full("B"),
            },
            "is_full": self.is_full(),
            "host_seat": 0,
            "game_in_progress": self.hand is not None and self.hand.phase.value != "HAND_COMPLETE",
        }


class RoomManager:
    def __init__(self):
        self.rooms: dict[str, Room] = {}

    def create_room(self, host_name: str, host_player_id: str, team: str) -> tuple[Room, Player]:
        code = gen_room_code(set(self.rooms.keys()))
        room = Room(code=code)
        seat = TEAM_SEATS[team][0]  # host always takes the first seat of their chosen team
        player = Player(player_id=host_player_id, name=host_name, seat=seat)
        room.players[seat] = player
        self.rooms[code] = room
        return room, player

    def join_room(self, code: str, name: str, player_id: str, team: str) -> tuple[Optional[Room], Optional[Player], Optional[str]]:
        room = self.rooms.get(code)
        if room is None:
            return None, None, "ROOM_NOT_FOUND"

        # reconnect case: same player_id already seated (e.g. brief network drop, not an explicit exit)
        for p in room.players.values():
            if p.player_id == player_id:
                p.connected = True
                room.touch()
                return room, p, None

        if room.is_full():
            return None, None, "ROOM_FULL"

        seat = room.open_seat_for_team(team)
        if seat is None:
            return None, None, "TEAM_FULL"

        player = Player(player_id=player_id, name=name, seat=seat)
        room.players[seat] = player
        room.touch()
        return room, player, None

    def get_room(self, code: str) -> Optional[Room]:
        return self.rooms.get(code)

    def remove_stale_rooms(self):
        now = time.time()
        stale = [
            code for code, r in self.rooms.items()
            if now - r.last_active > ROOM_TTL_SECONDS
        ]
        for code in stale:
            del self.rooms[code]
        return stale

    def mark_disconnected(self, room: Room, seat: int):
        if seat in room.players:
            room.players[seat].connected = False
            room.players[seat].ws = None

    def cancel_room(self, code: str):
        if code in self.rooms:
            del self.rooms[code]


"""FastAPI WebSocket server for Mendikot. Orchestrates rooms + game engine."""



app = FastAPI()
manager = RoomManager()

TRICK_PAUSE_SECONDS = 2.5  # how long a completed trick stays visible before clearing


async def send_json(ws: WebSocket, payload: dict):
    try:
        await ws.send_text(json.dumps(payload))
    except Exception:
        pass


async def broadcast(room, payload: dict, exclude_seat: int | None = None):
    for seat, p in room.players.items():
        if seat == exclude_seat or not p.connected or p.ws is None:
            continue
        await send_json(p.ws, payload)


async def send_hand_state_to_all(room):
    """Send each connected player their personalized game state."""
    h = room.hand
    for seat, p in room.players.items():
        if not p.connected or p.ws is None:
            continue
        state = h.public_state(viewer_seat=seat)
        await send_json(p.ws, {"type": "game_state", "state": state})


async def start_new_hand(room):
    room.hand = MendikotHand(dealer_seat=room.dealer_seat)
    await send_hand_state_to_all(room)
    await broadcast(room, {"type": "hand_started", "dealer_seat": room.dealer_seat})
    if room.solo:
        asyncio.create_task(bot_play_turn(room))


def rotate_dealer(room):
    room.dealer_seat = (room.dealer_seat + 1) % 4


async def cancel_room_and_notify(room, leaving_seat: int, reason: str = "player_left"):
    """Cancel the room entirely for everyone."""
    room.cancelled = True
    await broadcast(room, {
        "type": "room_cancelled",
        "reason": reason,
        "leaving_seat": leaving_seat,
    })
    manager.cancel_room(room.code)


async def _process_play_event(room, ev, seat):
    """Shared play event broadcast + bot chaining."""
    room.touch()
    await broadcast(room, {
        "type": "card_played",
        "seat": ev["seat"],
        "card": ev["card"],
    })

    if "trick_result" in ev:
        tr = ev["trick_result"]
        await broadcast(room, {
            "type": "trick_won",
            "winner_seat": tr["winner_seat"],
            "mendi_count": tr["mendi_count"],
            "no_trump_locked": tr.get("no_trump_locked", False),
            "phase2_dealt": tr.get("phase2_dealt", False),
        })
        room.lock_for(TRICK_PAUSE_SECONDS)
        await asyncio.sleep(TRICK_PAUSE_SECONDS)
        await send_hand_state_to_all(room)

        if tr.get("hand_complete"):
            await broadcast(room, {
                "type": "hand_complete",
                "winner_team": room.hand.winner_team,
                "final_mendi": room.hand.final_mendi,
                "final_cards": room.hand.final_cards,
            })
    else:
        await send_hand_state_to_all(room)

    if room.solo:
        asyncio.create_task(bot_play_turn(room))


async def _process_reveal_event(room, ev, seat):
    """Shared reveal event broadcast + bot chaining."""
    room.touch()
    await broadcast(room, {
        "type": "trump_revealed",
        "seat": ev["seat"],
        "card": ev["card"],
        "trump_suit": ev["trump_suit"],
    })

    if "trick_result" in ev:
        tr = ev["trick_result"]
        await broadcast(room, {
            "type": "trick_won",
            "winner_seat": tr["winner_seat"],
            "mendi_count": tr["mendi_count"],
            "no_trump_locked": tr.get("no_trump_locked", False),
            "phase2_dealt": tr.get("phase2_dealt", False),
        })
        room.lock_for(TRICK_PAUSE_SECONDS)
        await asyncio.sleep(TRICK_PAUSE_SECONDS)
        await send_hand_state_to_all(room)

        if tr.get("hand_complete"):
            await broadcast(room, {
                "type": "hand_complete",
                "winner_team": room.hand.winner_team,
                "final_mendi": room.hand.final_mendi,
                "final_cards": room.hand.final_cards,
            })
    else:
        await send_hand_state_to_all(room)

    if room.solo:
        asyncio.create_task(bot_play_turn(room))


async def bot_play_turn(room: Room):
    """Bot AI: lowest legal card, auto-triggered. Reveals lowest card when void."""
    if not room.solo:
        return
    h = room.hand
    if h is None or h.phase == Phase.HAND_COMPLETE:
        return

    seat = h.turn_seat
    if seat not in room.players or not room.players[seat].is_bot:
        return

    bot_key = f"_bot_active_{seat}"
    if getattr(room, bot_key, False):
        return
    setattr(room, bot_key, True)

    try:
        while room.is_locked():
            await asyncio.sleep(0.2)
        await asyncio.sleep(0.7)

        if room.hand is None or room.hand.phase == Phase.HAND_COMPLETE:
            return
        if room.hand.turn_seat != seat:
            return

        hand = h.hands[seat]

        # Must reveal trump?
        if h.phase == Phase.PHASE1_PLAY and h.trump_suit is None and h.current_trick:
            led = h.led_suit
            has_led = any(card_suit(c) == led for c in hand)
            if not has_led:
                card = min(hand, key=lambda c: (RANK_VALUE[card_rank(c)], SUITS.index(card_suit(c))))
                try:
                    ev = h.reveal_trump(seat, card)
                    await _process_reveal_event(room, ev, seat)
                except ValueError:
                    pass
                return

        legal = h.legal_moves(seat)
        if not legal:
            return
        card = min(legal, key=lambda c: (RANK_VALUE[card_rank(c)], SUITS.index(card_suit(c))))
        try:
            ev = h.play_card(seat, card)
            await _process_play_event(room, ev, seat)
        except ValueError:
            pass
    finally:
        setattr(room, bot_key, False)


@app.websocket("/ws")
async def websocket_endpoint(ws: WebSocket):
    await ws.accept()
    room = None
    seat = None
    player_id = None

    try:
        while True:
            raw = await ws.receive_text()
            try:
                msg = json.loads(raw)
            except json.JSONDecodeError:
                await send_json(ws, {"type": "error", "message": "Invalid JSON"})
                continue

            mtype = msg.get("type")

            # ---------------- SOLO GAME ----------------
            if mtype == "solo_game":
                name = (msg.get("player_name") or "Player").strip()[:20] or "Player"
                player_id = str(uuid.uuid4())
                room, player = manager.create_room(name, player_id, "A")
                room.solo = True
                player.ws = ws
                seat = player.seat

                bot_names = ["Bot Alpha", "Bot Beta", "Bot Gamma"]
                for bot_name in bot_names:
                    for t in ("A", "B"):
                        s = room.open_seat_for_team(t)
                        if s is not None:
                            bot = Player(player_id=f"bot_{s}", name=bot_name, seat=s, is_bot=True, connected=True)
                            room.players[s] = bot
                            break

                await send_json(ws, {
                    "type": "joined",
                    "room_code": room.code,
                    "player_id": player_id,
                    "your_seat": seat,
                    "solo": True,
                })
                await broadcast(room, room.lobby_state())
                await start_new_hand(room)

            # ---------------- CREATE ROOM ----------------
            elif mtype == "create_room":
                name = (msg.get("player_name") or "Host").strip()[:20] or "Host"
                team = msg.get("team")
                if team not in ("A", "B"):
                    await send_json(ws, {"type": "error", "message": "Choose a team"})
                    continue
                player_id = str(uuid.uuid4())
                room, player = manager.create_room(name, player_id, team)
                player.ws = ws
                seat = player.seat
                await send_json(ws, {
                    "type": "joined",
                    "room_code": room.code,
                    "player_id": player_id,
                    "your_seat": seat,
                    "solo": False,
                })
                await broadcast(room, room.lobby_state())

            # ---------------- JOIN ROOM ----------------
            elif mtype == "join_room":
                code = (msg.get("room_code") or "").strip().upper()
                name = (msg.get("player_name") or "Player").strip()[:20] or "Player"
                pid = msg.get("player_id") or str(uuid.uuid4())
                team = msg.get("team")

                # team is required for NEW joins, but not for reconnects (server
                # already knows their seat/team from a prior join in this room)
                existing_room = manager.get_room(code)
                is_reconnect = existing_room is not None and any(
                    p.player_id == pid for p in existing_room.players.values()
                )
                if not is_reconnect and team not in ("A", "B"):
                    await send_json(ws, {"type": "error", "message": "Choose a team"})
                    continue

                r, player, err = manager.join_room(code, name, pid, team)
                if err:
                    await send_json(ws, {"type": "error", "message": err})
                    continue

                room = r
                player.ws = ws
                seat = player.seat
                player_id = player.player_id

                await send_json(ws, {
                    "type": "joined",
                    "room_code": room.code,
                    "player_id": player_id,
                    "your_seat": seat,
                    "solo": False,
                })
                await broadcast(room, room.lobby_state())

                # if game already in progress (reconnect case), resend state
                if room.hand is not None:
                    state = room.hand.public_state(viewer_seat=seat)
                    await send_json(ws, {"type": "game_state", "state": state})

            # ---------------- START GAME ----------------
            elif mtype == "start_game":
                if room is None:
                    await send_json(ws, {"type": "error", "message": "Not in a room"})
                    continue
                if seat != 0:
                    await send_json(ws, {"type": "error", "message": "Only host can start"})
                    continue
                if not room.is_full():
                    await send_json(ws, {"type": "error", "message": "Room not full"})
                    continue
                await start_new_hand(room)

            # ---------------- PLAY CARD ----------------
            elif mtype == "play_card":
                if room is None or room.hand is None:
                    await send_json(ws, {"type": "error", "message": "No active hand"})
                    continue
                if room.is_locked():
                    await send_json(ws, {"type": "error", "message": "Please wait, trick is still being shown"})
                    continue
                card = msg.get("card")
                h = room.hand
                try:
                    ev = h.play_card(seat, card)
                except ValueError as e:
                    if str(e) == "VOID_MUST_REVEAL_TRUMP":
                        await send_json(ws, {
                            "type": "must_reveal_trump",
                            "led_suit": h.led_suit,
                        })
                    else:
                        await send_json(ws, {"type": "error", "message": str(e)})
                    continue

                await _process_play_event(room, ev, seat)

            # ---------------- REVEAL TRUMP ----------------
            elif mtype == "reveal_trump":
                if room is None or room.hand is None:
                    await send_json(ws, {"type": "error", "message": "No active hand"})
                    continue
                if room.is_locked():
                    await send_json(ws, {"type": "error", "message": "Please wait, trick is still being shown"})
                    continue
                card = msg.get("card")
                h = room.hand
                try:
                    ev = h.reveal_trump(seat, card)
                except ValueError as e:
                    await send_json(ws, {"type": "error", "message": str(e)})
                    continue

                await _process_reveal_event(room, ev, seat)

            # ---------------- EXIT GAME (explicit) ----------------
            elif mtype == "exit_game":
                if room is None or seat is None:
                    await send_json(ws, {"type": "error", "message": "Not in a room"})
                    continue

                is_lobby = room.hand is None or room.hand.phase == Phase.HAND_COMPLETE

                # Cancel only if host leaves lobby, or any player exits during active game
                if seat == 0 and is_lobby:
                    await cancel_room_and_notify(room, seat, reason="host_left")
                elif not is_lobby:
                    await cancel_room_and_notify(room, seat, reason="player_left")
                else:
                    # Non-host leaves lobby - just remove them so others can join
                    if seat in room.players:
                        del room.players[seat]
                    await broadcast(room, room.lobby_state())

                room = None
                seat = None

            # ---------------- REMATCH ----------------
            elif mtype == "rematch":
                if room is None:
                    await send_json(ws, {"type": "error", "message": "Not in a room"})
                    continue
                if seat != 0:
                    await send_json(ws, {"type": "error", "message": "Only host can start rematch"})
                    continue
                if room.hand is None or room.hand.phase != Phase.HAND_COMPLETE:
                    await send_json(ws, {"type": "error", "message": "Hand not complete"})
                    continue
                rotate_dealer(room)
                await start_new_hand(room)

            else:
                await send_json(ws, {"type": "error", "message": f"Unknown message type: {mtype}"})

    except WebSocketDisconnect:
        pass
    finally:
        # A dropped connection (closed tab, lost network) is NOT the same as
        # an explicit Exit tap - we don't cancel the room here, just mark this
        # seat disconnected so others can see it.
        if room is not None and seat is not None:
            manager.mark_disconnected(room, seat)
            if not room.cancelled:
                await broadcast(room, room.lobby_state())


async def gc_loop():
    while True:
        await asyncio.sleep(60)
        manager.remove_stale_rooms()


@app.on_event("startup")
async def on_startup():
    asyncio.create_task(gc_loop())


# ---------------------------------------------------------------------------
# Frontend - served as a single embedded HTML/CSS/JS page, no build step.
# ---------------------------------------------------------------------------

INDEX_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1, user-scalable=no">
<title>Mendikot</title>
<link href="https://fonts.googleapis.com/css2?family=Open+Sans:wght@400;600;700&display=swap" rel="stylesheet">
<style>
  :root {
    --bg-deep: #35654d;
    --bg-panel: #2d553f;
    --bg-panel-2: #264a36;
    --felt: #35654d;
    --gold: #d4a24c;
    --gold-bright: #e8be6e;
    --cream: #f5ede0;
    --ink: #1c1410;
    --teal-bright: #5fcb9e;
    --red-suit: #c0453a;
    --line: rgba(212, 162, 76, 0.22);
  }

  * { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }

  html, body {
    margin: 0;
    padding: 0;
    height: 100%;
    width: 100%;
    overflow: hidden;
    background: #35654d;
    font-family: 'Open Sans', sans-serif;
    color: var(--cream);
  }

  /* No shadows anywhere */
  * { box-shadow: none !important; }

  #app {
    height: 100%;
    width: 100%;
    display: flex;
    flex-direction: column;
    position: relative;
  }

  /* ---------------- VIEWS ---------------- */
  .view {
    flex: 1;
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    padding: 24px 16px;
    gap: 20px;
    overflow-y: auto;
  }
  .view.hidden { display: none !important; }

  /* ---------------- HOME ---------------- */
  .home-title {
    font-size: 48px;
    letter-spacing: 1px;
    color: var(--gold-bright);
    margin: 0;
    text-align: center;
    font-weight: 700;
  }
  .home-title .stamp-suits {
    display: block;
    font-size: 20px;
    letter-spacing: 8px;
    color: var(--cream);
    opacity: 0.65;
    margin-top: 6px;
  }

  .menu-buttons {
    display: flex;
    flex-direction: column;
    gap: 12px;
    width: 100%;
    max-width: 320px;
  }

  /* ---------------- SHARED UI ---------------- */
  .screen-title {
    font-size: 24px;
    color: var(--gold-bright);
    margin: 0 0 4px;
    text-align: center;
    font-weight: 700;
  }

  .back-link {
    background: none;
    border: none;
    color: rgba(245,237,224,0.55);
    font-family: 'Open Sans', sans-serif;
    font-size: 14px;
    align-self: flex-start;
    padding: 4px 0;
    margin-bottom: 4px;
    cursor: pointer;
  }
  .back-link:hover { color: var(--cream); }

  .home-card {
    background: var(--bg-panel);
    border: 1px solid var(--line);
    border-radius: 6px 10px 5px 8px;
    padding: 24px;
    width: 100%;
    max-width: 360px;
  }

  .field-label {
    font-size: 11px;
    text-transform: uppercase;
    letter-spacing: 1.5px;
    color: var(--gold);
    display: block;
    margin-bottom: 8px;
    font-weight: 600;
  }

  input[type=text] {
    width: 100%;
    padding: 12px 14px;
    border-radius: 5px 8px 4px 7px;
    border: 1px solid var(--line);
    background: var(--bg-panel-2);
    color: var(--cream);
    font-size: 16px;
    font-family: 'Open Sans', sans-serif;
    outline: none;
    margin-bottom: 14px;
  }
  input[type=text]:focus { border-color: var(--gold); }
  input[type=text]::placeholder { color: rgba(245,237,224,0.35); }
  input#join-code { text-transform: uppercase; letter-spacing: 3px; text-align: center; font-size: 20px; }

  button {
    font-family: 'Open Sans', sans-serif;
    cursor: pointer;
    border: none;
    border-radius: 6px 10px 5px 8px;
    font-weight: 600;
    letter-spacing: 0.3px;
    transition: transform 0.08s ease, filter 0.15s ease;
  }
  button:active { transform: scale(0.97); }
  button:disabled { opacity: 0.4; cursor: not-allowed; }

  .btn-primary {
    width: 100%;
    padding: 14px;
    background: linear-gradient(180deg, var(--gold-bright), var(--gold));
    color: var(--ink);
    font-size: 16px;
  }
  .btn-primary:hover:not(:disabled) { filter: brightness(1.08); }

  .btn-secondary {
    width: 100%;
    padding: 14px;
    background: transparent;
    border: 1.5px solid var(--teal-bright);
    color: var(--teal-bright);
    font-size: 16px;
  }
  .btn-secondary:hover:not(:disabled) { background: rgba(63,139,126,0.12); }

  .team-picker {
    display: flex;
    gap: 10px;
    margin-bottom: 16px;
  }
  .team-btn {
    flex: 1;
    padding: 14px 8px;
    background: rgba(245,237,224,0.04);
    border: 1.5px solid rgba(245,237,224,0.18);
    border-radius: 5px 8px 4px 7px;
    color: rgba(245,237,224,0.7);
    font-size: 14px;
    font-weight: 600;
    transition: all 0.15s ease;
    cursor: pointer;
  }
  .team-btn.team-a.selected {
    border-color: var(--gold);
    background: rgba(212,162,76,0.16);
    color: var(--gold-bright);
  }
  .team-btn.team-b.selected {
    border-color: var(--teal-bright);
    background: rgba(95,203,158,0.14);
    color: var(--teal-bright);
  }
  .team-btn.full { opacity: 0.35; cursor: not-allowed; }

  .error-banner {
    background: rgba(166,54,44,0.25);
    border: 1px solid var(--red-suit);
    color: #FFD9D4;
    padding: 10px 14px;
    border-radius: 4px 7px 3px 6px;
    font-size: 13px;
    margin-bottom: 12px;
    display: none;
  }
  .error-banner.show { display: block; }

  .exit-link {
    background: none;
    border: none;
    color: rgba(245,237,224,0.4);
    font-size: 13px;
    margin-top: 14px;
    padding: 6px;
    cursor: pointer;
  }
  .exit-link:hover { color: var(--red-suit); }

  /* ---------------- ROOM ---------------- */
  .room-code-display { text-align: center; }
  .room-code-display .label {
    font-size: 11px;
    text-transform: uppercase;
    letter-spacing: 2px;
    color: rgba(245,237,224,0.55);
    margin-bottom: 8px;
    font-weight: 600;
  }
  .room-code-display .code {
    font-size: 42px;
    letter-spacing: 8px;
    color: var(--gold-bright);
    background: var(--bg-panel);
    border: 1px solid var(--line);
    padding: 12px 18px 12px 26px;
    border-radius: 6px 10px 5px 8px;
    display: inline-block;
    font-weight: 700;
  }
  .copy-hint {
    font-size: 12px;
    color: rgba(245,237,224,0.5);
    margin-top: 8px;
    cursor: pointer;
  }
  .copy-hint:hover { color: var(--gold); }

  .seats-grid {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 10px;
    width: 100%;
    max-width: 400px;
  }
  .seat-slot {
    background: var(--bg-panel);
    border: 1px solid var(--line);
    border-radius: 5px 8px 4px 7px;
    padding: 14px;
    text-align: center;
    position: relative;
  }
  .seat-slot.team-a { border-left: 3px solid var(--gold); }
  .seat-slot.team-b { border-left: 3px solid var(--teal-bright); }
  .seat-slot.empty { opacity: 0.4; border-style: dashed; }
  .seat-slot .seat-name { font-size: 15px; font-weight: 700; }
  .seat-slot .seat-team {
    font-size: 10px;
    text-transform: uppercase;
    letter-spacing: 1px;
    opacity: 0.6;
    margin-top: 3px;
    font-weight: 600;
  }
  .seat-slot .disconnected-badge {
    position: absolute;
    top: 8px; right: 8px;
    width: 8px; height: 8px;
    border-radius: 50%;
    background: #A6362C;
  }
  .seat-slot .you-badge {
    font-size: 9px;
    color: var(--gold);
    letter-spacing: 1px;
    margin-top: 2px;
    font-weight: 600;
  }

  .waiting-note {
    font-size: 13px;
    color: rgba(245,237,224,0.6);
    text-align: center;
  }

  /* ---------------- GAME VIEW ---------------- */
  #view-game {
    flex: 1;
    display: flex;
    flex-direction: column;
    width: 100%;
    max-width: 900px;
    margin: 0 auto;
    padding: 6px 8px 8px;
    min-height: 0;
    overflow: hidden;
    position: relative;
  }

  /* Top bar: scores + 10s + trump */
  .top-bar {
    flex-shrink: 0;
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 8px;
    padding: 2px 0 6px;
  }

  .score-block {
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 2px;
    min-width: 56px;
  }
  .score-block-label {
    font-size: 9px;
    text-transform: uppercase;
    letter-spacing: 0.5px;
    opacity: 0.7;
    font-weight: 700;
  }
  .score-block-num {
    font-size: 24px;
    font-weight: 700;
    color: var(--gold-bright);
    line-height: 1;
  }

  .center-info {
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 4px;
    flex: 1;
  }

  .ten-slots {
    display: flex;
    gap: 3px;
  }
  .ten-slot {
    width: clamp(16px, 4vw, 22px);
    height: clamp(22px, 5.5vw, 30px);
    border-radius: 3px 5px 2px 4px;
    display: flex;
    align-items: center;
    justify-content: center;
    font-weight: 700;
    font-size: 7px;
    line-height: 1;
    background: rgba(0,0,0,0.14);
    color: rgba(245,237,224,0.18);
    transition: transform 0.25s cubic-bezier(.2,1.4,.4,1), background 0.25s ease;
  }
  .ten-slot .ts-suit { font-size: clamp(9px, 2.4vw, 12px); line-height: 1; }
  .ten-slot.won {
    background: var(--cream);
    transform: translateY(-2px) scale(1.05);
    animation: mendiWon 0.5s cubic-bezier(.2,1.4,.4,1);
  }
  @keyframes mendiWon {
    0% { transform: translateY(6px) scale(0.6) rotate(-10deg); opacity: 0; }
    60% { transform: translateY(-4px) scale(1.12) rotate(4deg); opacity: 1; }
    100% { transform: translateY(-2px) scale(1.05) rotate(0deg); }
  }
  .ten-slot.won.red { color: var(--red-suit); }
  .ten-slot.won.black { color: var(--ink); }
  .ten-slot.won.mine { border: 1.5px solid var(--gold); }
  .ten-slot.won.theirs { border: 1.5px solid var(--teal-bright); }

  .trump-box {
    width: clamp(28px, 7vw, 36px);
    height: clamp(38px, 9.5vw, 50px);
    border-radius: 4px 6px 3px 5px;
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: clamp(14px, 3.5vw, 20px);
    background: rgba(0,0,0,0.16);
    color: rgba(245,237,224,0.3);
    font-weight: 700;
    flex-shrink: 0;
    transition: transform 0.3s cubic-bezier(.2,1.4,.4,1), background 0.3s ease;
  }
  .trump-box.revealed {
    background: var(--cream);
    animation: trumpLockIn 0.5s cubic-bezier(.2,1.4,.4,1);
  }
  @keyframes trumpLockIn {
    0% { transform: scale(1.6) rotate(-6deg); opacity: 0.3; }
    60% { transform: scale(0.92) rotate(3deg); }
    100% { transform: scale(1) rotate(0deg); }
  }
  .trump-box.revealed.red { color: var(--red-suit); }
  .trump-box.revealed.black { color: var(--ink); }

  /* Table felt */
  .table-felt {
    flex: 1;
    min-height: 0;
    display: grid;
    grid-template-areas:
      ".    top    ."
      "left center right"
      ".    bottom .";
    grid-template-columns: clamp(44px, 13vw, 64px) 1fr clamp(44px, 13vw, 64px);
    grid-template-rows: clamp(32px, 9vh, 52px) 1fr clamp(32px, 9vh, 52px);
    padding: 2px;
    gap: 2px;
    position: relative;
  }

  .seat-marker {
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    gap: 2px;
  }
  .seat-marker .seat-mini-name {
    font-size: 11px;
    font-weight: 600;
    color: rgba(245,237,224,0.75);
    white-space: nowrap;
    max-width: 80px;
    overflow: hidden;
    text-overflow: ellipsis;
    transition: color 0.25s ease;
  }
  .seat-marker .turn-dot {
    width: 5px;
    height: 5px;
    border-radius: 50%;
    background: var(--gold-bright);
    opacity: 0;
    transform: scale(0.5);
    transition: opacity 0.25s ease, transform 0.25s ease;
  }
  .seat-marker.active .seat-mini-name { color: var(--gold-bright); }
  .seat-marker.active .turn-dot {
    opacity: 1;
    transform: scale(1);
    animation: turnPulse 1.4s ease-in-out infinite;
  }
  @keyframes turnPulse {
    0%, 100% { transform: scale(1); opacity: 1; }
    50% { transform: scale(1.4); opacity: 0.6; }
  }
  .seat-marker.disconnected .seat-mini-name { opacity: 0.35; text-decoration: line-through; }
  .seat-marker.top { grid-area: top; }
  .seat-marker.left { grid-area: left; }
  .seat-marker.right { grid-area: right; }
  .seat-marker.bottom-marker { grid-area: bottom; }

  .trick-center {
    position: relative;
    grid-area: center;
    width: 100%;
    height: 100%;
    display: flex;
    align-items: center;
    justify-content: center;
  }
  .trick-slot {
    position: absolute;
    width: clamp(32px, 7.5vw, 42px);
    height: clamp(45px, 10.5vw, 58px);
  }
  .trick-slot.pos-top { top: 2px; left: 50%; transform: translateX(-50%); }
  .trick-slot.pos-left { left: 2px; top: 50%; transform: translateY(-50%); }
  .trick-slot.pos-right { right: 2px; top: 50%; transform: translateY(-50%); }
  .trick-slot.pos-bottom { bottom: 2px; left: 50%; transform: translateX(-50%); }

  /* Directional entry animations */
  .trick-slot.enter-bottom { animation: enterBottom 0.35s ease; }
  .trick-slot.enter-top { animation: enterTop 0.35s ease; }
  .trick-slot.enter-left { animation: enterLeft 0.35s ease; }
  .trick-slot.enter-right { animation: enterRight 0.35s ease; }

  @keyframes enterBottom {
    from { opacity: 0; transform: translateX(-50%) translateY(30px); }
    to { opacity: 1; transform: translateX(-50%) translateY(0); }
  }
  @keyframes enterTop {
    from { opacity: 0; transform: translateX(-50%) translateY(-30px); }
    to { opacity: 1; transform: translateX(-50%) translateY(0); }
  }
  @keyframes enterLeft {
    from { opacity: 0; transform: translateY(-50%) translateX(-30px); }
    to { opacity: 1; transform: translateY(-50%) translateX(0); }
  }
  @keyframes enterRight {
    from { opacity: 0; transform: translateY(-50%) translateX(30px); }
    to { opacity: 1; transform: translateY(-50%) translateX(0); }
  }

  /* Trick collection */
  .trick-center.collect-mine .trick-slot { animation: collectLeft 0.5s ease forwards; }
  .trick-center.collect-theirs .trick-slot { animation: collectRight 0.5s ease forwards; }
  @keyframes collectLeft { to { opacity: 0; left: -30%; } }
  @keyframes collectRight { to { opacity: 0; left: 130%; } }

  /* Playing card on table */
  .pcard {
    width: clamp(32px, 7.5vw, 42px);
    height: clamp(45px, 10.5vw, 58px);
    background: var(--cream);
    border-radius: 4px 6px 3px 5px;
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    padding: 3px 4px;
    font-weight: 700;
    position: relative;
  }
  .pcard.red { color: var(--red-suit); }
  .pcard.black { color: var(--ink); }
  .pcard .pcard-rank { font-size: 11px; line-height: 1; }
  .pcard .pcard-suit-big {
    position: absolute;
    top: 50%; left: 50%;
    transform: translate(-50%, -50%);
    font-size: 16px;
    opacity: 0.85;
  }
  .pcard .pcard-rank.bottom { align-self: flex-end; transform: rotate(180deg); }
  .pcard.trump-marked::after {
    content: "";
    position: absolute;
    top: 2px; right: 2px;
    width: 6px; height: 6px;
    border-radius: 50%;
    background: var(--gold);
  }

  /* Bottom hand area */
  .hand-area {
    flex-shrink: 0;
    display: flex;
    flex-direction: column;
    gap: 4px;
    padding: 4px 2px 6px;
    min-height: 0;
  }

  .action-bar {
    text-align: center;
    min-height: 36px;
    display: flex;
    align-items: center;
    justify-content: center;
  }
  .reveal-btn {
    padding: 8px 18px;
    background: linear-gradient(180deg, var(--gold-bright), var(--gold));
    color: var(--ink);
    border-radius: 16px 20px 14px 18px;
    font-size: 13px;
    font-weight: 700;
    cursor: pointer;
  }

  .hand-strip {
    display: flex;
    justify-content: center;
    align-items: flex-end;
    gap: 4px;
    padding: 2px 4px;
    min-height: 0;
    --hand-scale: 1;
    touch-action: manipulation;
  }

  .hand-card {
    width: calc(48px * var(--hand-scale));
    height: calc(67px * var(--hand-scale));
    background: var(--cream);
    border-radius: 4px 7px 3px 6px;
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    padding: 4px 5px;
    font-weight: 700;
    cursor: pointer;
    position: relative;
    flex-shrink: 0;
    user-select: none;
    -webkit-user-select: none;
    touch-action: manipulation;
    transition: transform 0.12s ease, opacity 0.2s ease, outline 0.12s ease;
    outline: none;
  }
  .hand-card.red { color: var(--red-suit); }
  .hand-card.black { color: var(--ink); }
  .hand-card .hc-rank { font-size: 13px; line-height: 1; }
  .hand-card .hc-suit-big {
    position: absolute;
    top: 50%; left: 50%;
    transform: translate(-50%,-50%);
    font-size: 20px;
    opacity: 0.85;
    pointer-events: none;
  }
  .hand-card .hc-rank.bottom { align-self: flex-end; transform: rotate(180deg); pointer-events: none; }

  .hand-card.playable:hover { transform: translateY(-8px); outline: 2px solid var(--gold-bright); }
  .hand-card.playable:active { transform: translateY(-4px) scale(0.97); }
  .hand-card.disabled { opacity: 0.35; cursor: not-allowed; }
  .hand-card.disabled:hover { transform: none; outline: none; }
  .hand-card.trump-marked { outline: 1.5px solid var(--gold); outline-offset: -1.5px; }
  .hand-card.selected-for-reveal { outline: 3px solid var(--gold-bright); outline-offset: -3px; transform: translateY(-6px); }

  /* Overlays */
  .trump-flash {
    position: fixed;
    inset: 0;
    background: rgba(43,14,23,0.75);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 50;
  }
  .trump-flash.show { display: flex; animation: fadeIn 0.2s ease; }
  .trump-flash .stamp {
    width: 110px;
    height: 154px;
    border-radius: 10px 14px 8px 12px;
    background: var(--cream);
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 72px;
    animation: stampIn 0.4s cubic-bezier(.2,1.4,.4,1);
  }
  .trump-flash .stamp.red { color: var(--red-suit); }
  .trump-flash .stamp.black { color: var(--ink); }
  @keyframes stampIn {
    0% { transform: scale(2.2) rotate(-8deg); opacity: 0; }
    60% { transform: scale(0.95) rotate(2deg); opacity: 1; }
    100% { transform: scale(1) rotate(0deg); opacity: 1; }
  }
  @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }

  .result-overlay {
    position: fixed;
    inset: 0;
    background: rgba(20,7,11,0.88);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 60;
    padding: 20px;
  }
  .result-overlay.show { display: flex; animation: fadeIn 0.25s ease; }
  .result-card {
    background: var(--bg-panel);
    border: 1px solid var(--line);
    border-radius: 8px 12px 6px 10px;
    padding: 28px 24px;
    text-align: center;
    max-width: 340px;
    width: 100%;
  }
  .result-headline {
    font-size: 26px;
    color: var(--gold-bright);
    margin: 0 0 6px;
    font-weight: 700;
  }
  .result-headline.draw { color: rgba(245,237,224,0.75); }
  .result-sub {
    font-size: 14px;
    color: rgba(245,237,224,0.6);
    margin-bottom: 20px;
  }
  .result-mendi-row {
    display: flex;
    justify-content: center;
    gap: 20px;
    margin-bottom: 20px;
  }
  .result-mendi-row .mendi-counter {
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 6px;
  }
  .result-mendi-row .mendi-label {
    font-size: 10px;
    text-transform: uppercase;
    letter-spacing: 1px;
    opacity: 0.6;
    font-weight: 600;
  }
  .result-mendi-row .ten-slots { gap: 4px; }
  .result-mendi-row .ten-slot {
    width: 22px;
    height: 32px;
    font-size: 8px;
  }
  .result-mendi-row .ten-slot .ts-suit { font-size: 13px; }

  .result-card-counts {
    display: flex;
    justify-content: center;
    gap: 36px;
    margin-bottom: 20px;
  }
  .result-cc { text-align: center; }
  .result-cc-num { font-size: 22px; font-weight: 700; color: var(--gold-bright); }
  .result-cc-label { font-size: 10px; text-transform: uppercase; opacity: 0.6; font-weight: 600; }

  .confirm-overlay {
    position: fixed;
    inset: 0;
    background: rgba(4,14,9,0.82);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 90;
    padding: 20px;
  }
  .confirm-overlay.show { display: flex; animation: fadeIn 0.2s ease; }
  .confirm-card {
    background: var(--bg-panel);
    border-radius: 8px 12px 6px 10px;
    padding: 24px 20px;
    max-width: 320px;
    width: 100%;
    text-align: center;
  }
  .confirm-text {
    font-size: 15px;
    color: var(--cream);
    margin-bottom: 18px;
    line-height: 1.4;
  }
  .confirm-buttons { display: flex; gap: 10px; }
  .confirm-buttons button { flex: 1; padding: 12px; font-size: 14px; }
  .btn-danger {
    background: var(--red-suit);
    color: var(--cream);
    border-radius: 6px 10px 5px 8px;
  }

  .toast {
    position: fixed;
    bottom: 20px;
    left: 50%;
    transform: translateX(-50%);
    background: var(--bg-panel);
    border: 1px solid var(--red-suit);
    color: var(--cream);
    padding: 12px 20px;
    border-radius: 20px;
    font-size: 13px;
    z-index: 100;
    opacity: 0;
    pointer-events: none;
    transition: opacity 0.2s ease;
  }
  .toast.show { opacity: 1; }

  .exit-icon-btn {
    position: absolute;
    top: 6px;
    right: 6px;
    z-index: 20;
    width: 30px;
    height: 30px;
    border-radius: 50%;
    background: rgba(0,0,0,0.28);
    border: none;
    color: rgba(245,237,224,0.6);
    font-size: 20px;
    line-height: 1;
    display: flex;
    align-items: center;
    justify-content: center;
    padding: 0;
    cursor: pointer;
  }
  .exit-icon-btn:hover { background: rgba(166,54,44,0.5); color: var(--cream); }

  @media (max-width: 380px) {
    .home-title { font-size: 40px; }
    .room-code-display .code { font-size: 34px; letter-spacing: 6px; }
  }
  @media (max-height: 420px) {
    .table-felt {
      grid-template-columns: clamp(36px, 10vw, 52px) 1fr clamp(36px, 10vw, 52px);
      grid-template-rows: clamp(26px, 12vh, 44px) 1fr clamp(26px, 12vh, 44px);
    }
    .ten-slot { width: 14px; height: 20px; }
    .trump-box { width: 24px; height: 34px; font-size: 13px; }
    .score-block-num { font-size: 20px; }
  }
</style>
</head>
<body>
<div id="app">

  <!-- ============ LANDING MENU ============ -->
  <div id="view-menu" class="view">
    <h1 class="home-title">Mendikot<span class="stamp-suits">\u2660 \u2665 \u2666 \u2663</span></h1>
    <div class="menu-buttons">
      <button class="btn-primary" id="btn-solo">Solo</button>
      <button class="btn-secondary" id="btn-goto-hub">Play with Friends</button>
    </div>
  </div>

  <!-- ============ HUB SCREEN ============ -->
  <div id="view-hub" class="view hidden">
    <button class="back-link" id="btn-hub-back">&larr; Back</button>
    <h2 class="screen-title">Play with Friends</h2>
    <div class="menu-buttons">
      <button class="btn-primary" id="btn-goto-create">Create Room</button>
      <button class="btn-secondary" id="btn-goto-join">Join Room</button>
    </div>
  </div>

  <!-- ============ CREATE ROOM SCREEN ============ -->
  <div id="view-create" class="view hidden">
    <button class="back-link" id="btn-create-back">&larr; Back</button>
    <h2 class="screen-title">Create Room</h2>
    <div class="home-card">
      <div class="error-banner" id="create-error"></div>
      <label class="field-label">Your name</label>
      <input type="text" id="create-player-name" placeholder="Enter your name" maxlength="20">
      <label class="field-label">Choose your team</label>
      <div class="team-picker" id="create-team-picker">
        <button class="team-btn team-a" data-team="A">Team A</button>
        <button class="team-btn team-b" data-team="B">Team B</button>
      </div>
      <button class="btn-primary" id="btn-create-confirm">Create Room</button>
    </div>
  </div>

  <!-- ============ JOIN ROOM SCREEN ============ -->
  <div id="view-join" class="view hidden">
    <button class="back-link" id="btn-join-back">&larr; Back</button>
    <h2 class="screen-title">Join Room</h2>
    <div class="home-card">
      <div class="error-banner" id="join-error"></div>
      <label class="field-label">Your name</label>
      <input type="text" id="join-player-name" placeholder="Enter your name" maxlength="20">
      <label class="field-label">Room code</label>
      <input type="text" id="join-code" placeholder="ABCDE" maxlength="5">
      <label class="field-label">Choose your team</label>
      <div class="team-picker" id="join-team-picker">
        <button class="team-btn team-a" data-team="A">Team A</button>
        <button class="team-btn team-b" data-team="B">Team B</button>
      </div>
      <button class="btn-secondary" id="btn-join-confirm">Join Room</button>
    </div>
  </div>

  <!-- ============ ROOM / LOBBY VIEW ============ -->
  <div id="view-room" class="view hidden">
    <div class="room-code-display">
      <div class="label">Room Code</div>
      <div class="code" id="room-code-text">-----</div>
      <div class="copy-hint" id="copy-hint">Tap to copy</div>
    </div>

    <div class="seats-grid" id="seats-grid"></div>

    <div class="waiting-note" id="waiting-note">Waiting for players to join\u2026</div>

    <button class="btn-primary hidden" id="btn-start" style="max-width:280px;">Start Game</button>
    <button class="exit-link" id="btn-exit-room">Exit Room</button>
  </div>

  <!-- ============ GAME TABLE VIEW ============ -->
  <div id="view-game" class="hidden">
    <button class="exit-icon-btn" id="btn-exit-game" title="Exit game">&times;</button>

    <!-- Top bar: Your Cards | Your 10s | Trump | Opp 10s | Opp Cards -->
    <div class="top-bar">
      <div class="score-block">
        <div class="score-block-label">Your Cards</div>
        <div class="score-block-num" id="my-card-count">0</div>
      </div>

      <div class="center-info">
        <div class="score-block-label" style="margin-bottom:2px;">Your 10s</div>
        <div class="ten-slots" id="my-ten-slots"></div>
      </div>

      <div class="trump-box" id="trump-symbol">?</div>

      <div class="center-info">
        <div class="score-block-label" style="margin-bottom:2px;">Opp 10s</div>
        <div class="ten-slots" id="opp-ten-slots"></div>
      </div>

      <div class="score-block">
        <div class="score-block-label">Opp Cards</div>
        <div class="score-block-num" id="opp-card-count">0</div>
      </div>
    </div>

    <!-- Table felt -->
    <div class="table-felt">
      <div class="seat-marker top" id="marker-top"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>
      <div class="seat-marker left" id="marker-left"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>
      <div class="seat-marker right" id="marker-right"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>
      <div class="seat-marker bottom-marker" id="marker-bottom"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>

      <div class="trick-center" id="trick-center"></div>
    </div>

    <!-- Bottom hand area -->
    <div class="hand-area">
      <div class="action-bar" id="action-bar"></div>
      <div class="hand-strip" id="hand-strip"></div>
    </div>
  </div>

</div>

<div class="trump-flash" id="trump-flash">
  <div class="stamp" id="trump-flash-symbol">?</div>
</div>

<div class="result-overlay" id="result-overlay">
  <div class="result-card">
    <h2 class="result-headline" id="result-headline">You Win!</h2>
    <div class="result-sub" id="result-sub">4 \u2013 0 Mendi</div>
    <div class="result-mendi-row" id="result-mendi-row"></div>
    <div class="result-card-counts" id="result-card-counts"></div>
    <button class="btn-primary" id="btn-rematch">Rematch</button>
    <div style="height:10px"></div>
    <button class="btn-secondary" id="btn-leave">Leave Room</button>
  </div>
</div>

<div class="confirm-overlay" id="confirm-overlay">
  <div class="confirm-card">
    <div class="confirm-text">Leave game? This will end it for everyone.</div>
    <div class="confirm-buttons">
      <button class="btn-secondary" id="btn-confirm-exit-cancel">Cancel</button>
      <button class="btn-danger" id="btn-confirm-exit-yes">Leave</button>
    </div>
  </div>
</div>

<div class="toast" id="toast"></div>

<script>
(function() {
  "use strict";

  // ---------------- state ----------------
  const S = {
    ws: null,
    playerId: null,
    roomCode: null,
    mySeat: null,
    seats: {},
    teamFull: { A: false, B: false },
    hostSeat: 0,
    gameState: null,
    pendingReveal: false,
    selectedRevealCard: null,
    view: 'menu',
    createTeam: null,
    joinTeam: null,
    displayedTrick: [],
    lastHand: [],
    isSolo: false,
  };

  const SUIT_SYMBOL = { S: '\\u2660', H: '\\u2665', D: '\\u2666', C: '\\u2663' };
  const RED_SUITS = new Set(['H', 'D']);
  const SUITS_ORDER = ['S', 'H', 'D', 'C'];

  // ---------------- persistence ----------------
  function saveSession(playerId, roomCode) {
    try {
      sessionStorage.setItem('mendikot_player_id', playerId);
      sessionStorage.setItem('mendikot_room_code', roomCode);
    } catch (e) {}
  }
  function loadSession() {
    try {
      return {
        playerId: sessionStorage.getItem('mendikot_player_id'),
        roomCode: sessionStorage.getItem('mendikot_room_code'),
      };
    } catch (e) { return {playerId: null, roomCode: null}; }
  }
  function clearSession() {
    try {
      sessionStorage.removeItem('mendikot_player_id');
      sessionStorage.removeItem('mendikot_room_code');
    } catch (e) {}
  }
  function uuid() {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function(c) {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }

  // ---------------- view switching ----------------
  const ALL_VIEWS = ['menu', 'hub', 'create', 'join', 'room', 'game'];
  function showView(name) {
    S.view = name;
    ALL_VIEWS.forEach(v => {
      const el = document.getElementById('view-' + v);
      if (el) {
        el.classList.toggle('hidden', v !== name);
        if (v === 'game') {
          el.style.display = v === name ? 'flex' : 'none';
          el.style.flexDirection = 'column';
        }
      }
    });
  }

  function showToast(msg) {
    const t = document.getElementById('toast');
    t.textContent = msg;
    t.classList.add('show');
    clearTimeout(t._hideTimer);
    t._hideTimer = setTimeout(() => t.classList.remove('show'), 2600);
  }

  function showError(bannerId, msg) {
    const el = document.getElementById(bannerId);
    if (!el) return;
    el.textContent = msg;
    el.classList.add('show');
  }
  function clearError(bannerId) {
    const el = document.getElementById(bannerId);
    if (el) el.classList.remove('show');
  }

  // ---------------- websocket ----------------
  function connect() {
    const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
    S.ws = new WebSocket(proto + '//' + location.host + '/ws');
    S.ws.onopen = () => { tryAutoRejoin(); };
    S.ws.onmessage = (ev) => handleMessage(JSON.parse(ev.data));
    S.ws.onclose = () => {
      showToast('Connection lost. Reconnecting\u2026');
      setTimeout(connect, 1500);
    };
    S.ws.onerror = () => {};
  }

  function send(payload) {
    if (S.ws && S.ws.readyState === WebSocket.OPEN) {
      S.ws.send(JSON.stringify(payload));
    }
  }

  function tryAutoRejoin() {
    const sess = loadSession();
    if (sess.playerId && sess.roomCode) {
      send({ type: 'join_room', room_code: sess.roomCode, player_name: localStorage.getItem('mendikot_name') || 'Player', player_id: sess.playerId });
    }
  }

  function handleMessage(msg) {
    switch (msg.type) {
      case 'joined':
        S.playerId = msg.player_id;
        S.roomCode = msg.room_code;
        S.mySeat = msg.your_seat;
        S.isSolo = msg.solo || false;
        saveSession(S.playerId, S.roomCode);
        document.getElementById('room-code-text').textContent = S.roomCode;
        if (!S.isSolo) showView('room');
        break;

      case 'room_update':
        S.seats = msg.seats;
        S.teamFull = msg.team_full || { A: false, B: false };
        S.hostSeat = msg.host_seat;
        renderLobby(msg);
        if (msg.game_in_progress && S.view !== 'game') {
          showView('game');
        }
        break;

      case 'game_state':
        S.gameState = msg.state;
        S.displayedTrick = (msg.state.current_trick || []).slice();
        if (S.view !== 'game') showView('game');
        renderGame();
        break;

      case 'hand_started':
        S.pendingReveal = false;
        S.selectedRevealCard = null;
        S.displayedTrick = [];
        S.lastHand = [];
        hideResultOverlay();
        break;

      case 'card_played':
        if (!S.displayedTrick.some(p => p.seat === msg.seat)) {
          S.displayedTrick.push({ seat: msg.seat, card: msg.card });
        }
        renderGame();
        break;

      case 'must_reveal_trump':
        S.pendingReveal = true;
        renderGame();
        break;

      case 'trump_revealed':
        S.pendingReveal = false;
        if (!S.displayedTrick.some(p => p.seat === msg.seat)) {
          S.displayedTrick.push({ seat: msg.seat, card: msg.card });
        }
        flashTrumpReveal(msg.trump_suit);
        renderGame();
        break;

      case 'trick_won':
        const winnerTeam = (msg.winner_seat % 2 === S.mySeat % 2) ? 'mine' : 'theirs';
        animateTrickCollection(winnerTeam);
        setTimeout(() => {
          S.displayedTrick = [];
          renderGame();
        }, 500);
        break;

      case 'hand_complete':
        showResultOverlay(msg.winner_team, msg.final_mendi, msg.final_cards);
        break;

      case 'room_cancelled':
        handleRoomCancelled(msg);
        break;

      case 'error':
        const friendly = friendlyErrorMessage(msg.message);
        showToast(friendly);
        if (S.view === 'create') showError('create-error', friendly);
        else if (S.view === 'join') showError('join-error', friendly);
        break;
    }
  }

  function friendlyErrorMessage(code) {
    const map = {
      'ROOM_NOT_FOUND': 'Room not found. Check the code and try again.',
      'ROOM_FULL': 'That room is already full.',
      'TEAM_FULL': 'That team is already full \\u2014 try the other team.',
    };
    return map[code] || code;
  }

  function handleRoomCancelled(msg) {
    clearSession();
    showToast('A player left the game, so the room was closed.');
    setTimeout(() => { location.reload(); }, 1800);
  }

  // ---------------- menu / navigation actions ----------------
  document.getElementById('btn-solo').addEventListener('click', () => {
    const name = (localStorage.getItem('mendikot_name') || 'Player').trim() || 'Player';
    send({ type: 'solo_game', player_name: name });
  });
  document.getElementById('btn-goto-hub').addEventListener('click', () => showView('hub'));
  document.getElementById('btn-hub-back').addEventListener('click', () => showView('menu'));
  document.getElementById('btn-goto-create').addEventListener('click', () => showView('create'));
  document.getElementById('btn-goto-join').addEventListener('click', () => showView('join'));
  document.getElementById('btn-create-back').addEventListener('click', () => showView('hub'));
  document.getElementById('btn-join-back').addEventListener('click', () => showView('hub'));

  // ---------------- team picker ----------------
  function setupTeamPicker(pickerId, stateKey) {
    const picker = document.getElementById(pickerId);
    picker.querySelectorAll('.team-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        if (btn.classList.contains('full')) return;
        S[stateKey] = btn.dataset.team;
        picker.querySelectorAll('.team-btn').forEach(b => b.classList.toggle('selected', b === btn));
      });
    });
  }
  setupTeamPicker('create-team-picker', 'createTeam');
  setupTeamPicker('join-team-picker', 'joinTeam');

  // ---------------- create room ----------------
  document.getElementById('btn-create-confirm').addEventListener('click', () => {
    clearError('create-error');
    const name = document.getElementById('create-player-name').value.trim() || 'Host';
    if (!S.createTeam) { showError('create-error', 'Choose a team'); return; }
    localStorage.setItem('mendikot_name', name);
    send({ type: 'create_room', player_name: name, team: S.createTeam });
  });

  // ---------------- join room ----------------
  document.getElementById('btn-join-confirm').addEventListener('click', () => {
    clearError('join-error');
    const name = document.getElementById('join-player-name').value.trim() || 'Player';
    const code = document.getElementById('join-code').value.trim().toUpperCase();
    if (!code) { showError('join-error', 'Enter a room code'); return; }
    if (!S.joinTeam) { showError('join-error', 'Choose a team'); return; }
    localStorage.setItem('mendikot_name', name);
    send({ type: 'join_room', room_code: code, player_name: name, player_id: uuid(), team: S.joinTeam });
  });

  document.getElementById('join-code').addEventListener('input', (e) => {
    e.target.value = e.target.value.toUpperCase();
  });

  document.getElementById('copy-hint').addEventListener('click', () => {
    if (navigator.clipboard) {
      navigator.clipboard.writeText(S.roomCode).then(() => showToast('Room code copied'));
    }
  });

  document.getElementById('btn-start').addEventListener('click', () => {
    send({ type: 'start_game' });
  });

  document.getElementById('btn-rematch').addEventListener('click', () => {
    send({ type: 'rematch' });
  });

  document.getElementById('btn-leave').addEventListener('click', () => {
    clearSession();
    location.reload();
  });

  // ---------------- exit game/room ----------------
  function showConfirmExit() {
    document.getElementById('confirm-overlay').classList.add('show');
  }
  function hideConfirmExit() {
    document.getElementById('confirm-overlay').classList.remove('show');
  }
  document.getElementById('btn-exit-room').addEventListener('click', showConfirmExit);
  document.getElementById('btn-exit-game').addEventListener('click', showConfirmExit);
  document.getElementById('btn-confirm-exit-cancel').addEventListener('click', hideConfirmExit);
  document.getElementById('btn-confirm-exit-yes').addEventListener('click', () => {
    send({ type: 'exit_game' });
    hideConfirmExit();
    clearSession();
    location.reload();
  });

  // ---------------- lobby render ----------------
  function renderLobby(msg) {
    const grid = document.getElementById('seats-grid');
    grid.innerHTML = '';
    for (let s = 0; s < 4; s++) {
      const seatData = msg.seats[String(s)];
      const div = document.createElement('div');
      const team = s % 2 === 0 ? 'team-a' : 'team-b';
      div.className = 'seat-slot ' + team + (seatData ? '' : ' empty');
      if (seatData) {
        div.innerHTML =
          '<div class="seat-name">' + escapeHtml(seatData.name) + '</div>' +
          '<div class="seat-team">Team ' + (s % 2 === 0 ? 'A' : 'B') + '</div>' +
          (s === S.mySeat ? '<div class="you-badge">YOU</div>' : '') +
          (!seatData.connected ? '<div class="disconnected-badge"></div>' : '');
      } else {
        div.innerHTML = '<div class="seat-name">Open Seat</div><div class="seat-team">Team ' + (s % 2 === 0 ? 'A' : 'B') + '</div>';
      }
      grid.appendChild(div);
    }

    const startBtn = document.getElementById('btn-start');
    const note = document.getElementById('waiting-note');
    if (S.mySeat === 0) {
      startBtn.classList.toggle('hidden', !msg.is_full);
      note.classList.toggle('hidden', msg.is_full);
    } else {
      startBtn.classList.add('hidden');
      note.textContent = msg.is_full ? 'Waiting for host to start\u2026' : 'Waiting for players to join\u2026';
    }
  }

  function escapeHtml(s) {
    const d = document.createElement('div');
    d.textContent = s;
    return d.innerHTML;
  }

  // ---------------- card rendering helpers ----------------
  function cardColor(card) {
    const suit = card.slice(-1);
    return RED_SUITS.has(suit) ? 'red' : 'black';
  }
  function cardRank(card) { return card.slice(0, -1); }
  function cardSuit(card) { return card.slice(-1); }

  function makeCardEl(card, cls, trumpSuit) {
    const el = document.createElement('div');
    const color = cardColor(card);
    el.className = cls + ' ' + color;
    if (trumpSuit && cardSuit(card) === trumpSuit) el.classList.add('trump-marked');
    const rank = cardRank(card);
    const suitSym = SUIT_SYMBOL[cardSuit(card)];
    const rCls = cls === 'pcard' ? 'pcard-rank' : 'hc-rank';
    const sCls = cls === 'pcard' ? 'pcard-suit-big' : 'hc-suit-big';
    el.innerHTML =
      '<div class="' + rCls + '">' + rank + suitSym + '</div>' +
      '<div class="' + sCls + '">' + suitSym + '</div>' +
      '<div class="' + rCls + ' bottom">' + rank + suitSym + '</div>';
    return el;
  }

  // ---------------- game render ----------------
  function renderGame() {
    const st = S.gameState;
    if (!st) return;

    const mySeat = st.your_seat;
    const myTeam = mySeat % 2 === 0 ? 'A' : 'B';

    // aggregate team data
    let mineMendiSuits = [];
    let theirsMendiSuits = [];
    let myCards = 0;
    let oppCards = 0;
    for (const seatStr in st.mendi_suits_won) {
      const seat = parseInt(seatStr, 10);
      const team = seat % 2 === 0 ? 'A' : 'B';
      const suits = st.mendi_suits_won[seatStr] || [];
      if (team === myTeam) mineMendiSuits.push(...suits);
      else theirsMendiSuits.push(...suits);
    }
    for (const seatStr in st.cards_won) {
      const seat = parseInt(seatStr, 10);
      const team = seat % 2 === 0 ? 'A' : 'B';
      const count = st.cards_won[seatStr] || 0;
      if (team === myTeam) myCards += count;
      else oppCards += count;
    }

    document.getElementById('my-card-count').textContent = myCards;
    document.getElementById('opp-card-count').textContent = oppCards;

    renderTenSlots('my-ten-slots', mineMendiSuits, 'mine');
    renderTenSlots('opp-ten-slots', theirsMendiSuits, 'theirs');

    // trump
    const trumpBox = document.getElementById('trump-symbol');
    if (st.trump_suit) {
      trumpBox.className = 'trump-box revealed ' + (RED_SUITS.has(st.trump_suit) ? 'red' : 'black');
      trumpBox.textContent = SUIT_SYMBOL[st.trump_suit];
    } else {
      trumpBox.className = 'trump-box';
      trumpBox.textContent = '?';
    }

    // seat markers
    const order = [mySeat, (mySeat + 1) % 4, (mySeat + 2) % 4, (mySeat + 3) % 4];
    const posMap = { bottom: order[0], left: order[1], top: order[2], right: order[3] };
    for (const pos in posMap) {
      const seat = posMap[pos];
      const seatInfo = S.seats[String(seat)] || { name: 'P' + seat, connected: true };
      const el = document.getElementById('marker-' + pos);
      el.classList.toggle('active', st.turn_seat === seat && st.phase !== 'HAND_COMPLETE');
      el.classList.toggle('disconnected', seatInfo.connected === false);
      const nameEl = el.querySelector('.seat-mini-name');
      nameEl.textContent = (seat === mySeat ? 'You' : seatInfo.name);
    }

    // trick center
    renderTrick(st, order);

    // action bar
    const actionBar = document.getElementById('action-bar');
    actionBar.innerHTML = '';
    if (S.pendingReveal && st.turn_seat === mySeat) {
      if (S.selectedRevealCard) {
        const btn = document.createElement('button');
        btn.className = 'reveal-btn';
        btn.textContent = 'Reveal ' + cardRank(S.selectedRevealCard) + SUIT_SYMBOL[cardSuit(S.selectedRevealCard)];
        btn.onclick = () => {
          send({ type: 'reveal_trump', card: S.selectedRevealCard });
          S.selectedRevealCard = null;
        };
        actionBar.appendChild(btn);
      }
    }

    // hand strip
    renderHand(st);
  }

  function renderTenSlots(containerId, suits, kind) {
    const el = document.getElementById(containerId);
    el.innerHTML = '';
    const wonSet = new Set(suits);
    SUITS_ORDER.forEach(suit => {
      const slot = document.createElement('div');
      const isWon = wonSet.has(suit);
      const color = RED_SUITS.has(suit) ? 'red' : 'black';
      slot.className = 'ten-slot' + (isWon ? ' won ' + color + ' ' + kind : '');
      slot.innerHTML = '<div class="ts-suit">' + SUIT_SYMBOL[suit] + '</div>';
      el.appendChild(slot);
    });
  }

  function renderTrick(st, order) {
    const center = document.getElementById('trick-center');
    const posOf = {};
    posOf[order[0]] = 'pos-bottom';
    posOf[order[1]] = 'pos-left';
    posOf[order[2]] = 'pos-top';
    posOf[order[3]] = 'pos-right';

    const dirOf = {};
    dirOf[order[0]] = 'enter-bottom';
    dirOf[order[1]] = 'enter-left';
    dirOf[order[2]] = 'enter-top';
    dirOf[order[3]] = 'enter-right';

    // Build a key map of existing
    const existing = new Map();
    center.querySelectorAll('.trick-slot').forEach(el => {
      existing.set(el.dataset.seat + '-' + el.dataset.card, el);
    });

    // Remove old
    existing.forEach((el, key) => {
      const [s, c] = key.split('-');
      const has = S.displayedTrick.some(p => String(p.seat) === s && p.card === c);
      if (!has) el.remove();
    });

    // Add new
    S.displayedTrick.forEach(play => {
      const key = play.seat + '-' + play.card;
      if (!existing.has(key)) {
        const slot = document.createElement('div');
        slot.className = 'trick-slot ' + posOf[play.seat] + ' ' + dirOf[play.seat];
        slot.dataset.seat = play.seat;
        slot.dataset.card = play.card;
        const cardEl = makeCardEl(play.card, 'pcard', st.trump_suit);
        slot.appendChild(cardEl);
        center.appendChild(slot);
      }
    });
  }

  function animateTrickCollection(winnerTeam) {
    const center = document.getElementById('trick-center');
    center.classList.add('collect-' + winnerTeam);
    setTimeout(() => center.classList.remove('collect-mine', 'collect-theirs'), 600);
  }

  function renderHand(st) {
    const hand = st.your_hand || [];
    const strip = document.getElementById('hand-strip');

    // Calculate scale to fit all cards without scrolling
    const containerWidth = strip.parentElement.clientWidth - 8;
    const baseCardWidth = 48;
    const gap = 4;
    const totalWidth = hand.length * baseCardWidth + (hand.length - 1) * gap;
    const scale = totalWidth > containerWidth ? containerWidth / totalWidth : 1;
    strip.style.setProperty('--hand-scale', scale.toFixed(3));

    const existing = new Map();
    strip.querySelectorAll('.hand-card').forEach(el => {
      existing.set(el.dataset.card, el);
    });

    // Fade out played cards
    existing.forEach((el, card) => {
      if (!hand.includes(card)) {
        el.style.opacity = '0';
        el.style.transform = 'translateY(12px)';
        setTimeout(() => { if (el.parentNode) el.remove(); }, 180);
      }
    });

    const myTurn = st.turn_seat === st.your_seat && st.phase !== 'HAND_COMPLETE';
    const legalSet = computeLegalMoves(st, hand);

    hand.forEach((card, index) => {
      let el = existing.get(card);
      if (!el) {
        el = makeCardEl(card, 'hand-card', st.trump_suit);
        el.dataset.card = card;
        el.style.opacity = '0';
        el.style.transform = 'translateY(12px)';
        strip.appendChild(el);
        requestAnimationFrame(() => {
          setTimeout(() => {
            el.style.transition = 'opacity 0.2s ease, transform 0.2s ease';
            el.style.opacity = '1';
            el.style.transform = 'translateY(0)';
          }, index * 25);
        });
      }

      // Update classes without destroying element
      el.classList.remove('playable', 'disabled', 'selected-for-reveal');
      el.classList.toggle('trump-marked', st.trump_suit && cardSuit(card) === st.trump_suit);

      if (S.pendingReveal && myTurn) {
        el.classList.add('playable');
        if (card === S.selectedRevealCard) el.classList.add('selected-for-reveal');
      } else if (myTurn) {
        if (legalSet.has(card)) el.classList.add('playable');
        else el.classList.add('disabled');
      } else {
        el.classList.add('disabled');
      }
    });

    S.lastHand = hand.slice();
  }

  // Click handler for hand cards
  document.getElementById('hand-strip').addEventListener('click', (e) => {
    const cardEl = e.target.closest('.hand-card');
    if (!cardEl) return;
    const card = cardEl.dataset.card;
    if (!card || !S.gameState) return;

    if (S.pendingReveal && S.gameState.turn_seat === S.mySeat) {
      S.selectedRevealCard = card;
      renderGame();
    } else if (S.gameState.turn_seat === S.mySeat) {
      const legal = computeLegalMoves(S.gameState, S.gameState.your_hand || []);
      if (legal.has(card)) {
        send({ type: 'play_card', card: card });
      }
    }
  });

  // Touch handler for mobile responsiveness
  document.getElementById('hand-strip').addEventListener('touchend', (e) => {
    e.preventDefault();
    const cardEl = e.target.closest('.hand-card');
    if (!cardEl) return;
    const card = cardEl.dataset.card;
    if (!card || !S.gameState) return;

    if (S.pendingReveal && S.gameState.turn_seat === S.mySeat) {
      S.selectedRevealCard = card;
      renderGame();
    } else if (S.gameState.turn_seat === S.mySeat) {
      const legal = computeLegalMoves(S.gameState, S.gameState.your_hand || []);
      if (legal.has(card)) {
        send({ type: 'play_card', card: card });
      }
    }
  }, { passive: false });

  function computeLegalMoves(st, hand) {
    if (!st.current_trick || st.current_trick.length === 0) {
      return new Set(hand);
    }
    if (st.trick_void_exempt_seats && st.trick_void_exempt_seats.includes(st.your_seat)) {
      return new Set(hand);
    }
    const led = st.led_suit;
    const sameSuit = hand.filter(c => cardSuit(c) === led);
    if (sameSuit.length > 0) return new Set(sameSuit);
    return new Set(hand);
  }

  // ---------------- trump flash ----------------
  function flashTrumpReveal(trumpSuit) {
    const overlay = document.getElementById('trump-flash');
    const symbolEl = document.getElementById('trump-flash-symbol');
    symbolEl.textContent = SUIT_SYMBOL[trumpSuit];
    symbolEl.className = 'stamp ' + (RED_SUITS.has(trumpSuit) ? 'red' : 'black');
    overlay.classList.add('show');
    setTimeout(() => overlay.classList.remove('show'), 1200);
  }

  // ---------------- result overlay ----------------
  function showResultOverlay(winnerTeam, finalMendi, finalCards) {
    const overlay = document.getElementById('result-overlay');
    const headline = document.getElementById('result-headline');
    const sub = document.getElementById('result-sub');
    const row = document.getElementById('result-mendi-row');
    const ccRow = document.getElementById('result-card-counts');

    const myTeam = S.mySeat % 2 === 0 ? 'A' : 'B';
    let mineM = finalMendi[myTeam];
    let theirsM = finalMendi[myTeam === 'A' ? 'B' : 'A'];
    let mineC = finalCards[myTeam];
    let theirsC = finalCards[myTeam === 'A' ? 'B' : 'A'];

    if (winnerTeam === 'DRAW') {
      headline.textContent = 'Draw';
      headline.className = 'result-headline draw';
      sub.textContent = '2 \\u2013 2 split';
    } else if (winnerTeam === myTeam) {
      headline.textContent = 'You Win!';
      headline.className = 'result-headline';
      sub.textContent = mineM + ' \\u2013 ' + theirsM + ' Mendi';
    } else {
      headline.textContent = 'You Lose';
      headline.className = 'result-headline draw';
      sub.textContent = theirsM + ' \\u2013 ' + mineM + ' Mendi';
    }

    const mineSuits = [];
    const theirsSuits = [];
    const suitsWon = (S.gameState && S.gameState.mendi_suits_won) || {};
    for (const seatStr in suitsWon) {
      const seat = parseInt(seatStr, 10);
      const team = seat % 2 === 0 ? 'A' : 'B';
      const suits = suitsWon[seatStr] || [];
      if (team === myTeam) mineSuits.push(...suits);
      else theirsSuits.push(...suits);
    }

    row.innerHTML =
      '<div class="mendi-counter mine"><div class="mendi-label">Your Team</div><div class="ten-slots" id="result-my-slots"></div></div>' +
      '<div class="mendi-counter theirs"><div class="mendi-label">Opponents</div><div class="ten-slots" id="result-opp-slots"></div></div>';
    renderTenSlots('result-my-slots', mineSuits, 'mine');
    renderTenSlots('result-opp-slots', theirsSuits, 'theirs');

    ccRow.innerHTML =
      '<div class="result-cc"><div class="result-cc-num">' + mineC + '</div><div class="result-cc-label">Your Cards</div></div>' +
      '<div class="result-cc"><div class="result-cc-num">' + theirsC + '</div><div class="result-cc-label">Opp Cards</div></div>';

    document.getElementById('btn-rematch').classList.toggle('hidden', S.mySeat !== 0);

    overlay.classList.add('show');
  }
  function hideResultOverlay() {
    document.getElementById('result-overlay').classList.remove('show');
  }

  // ---------------- boot ----------------
  connect();
})();
</script>
</body>
</html>
"""


@app.get("/", response_class=HTMLResponse)
async def index():
    return INDEX_HTML


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
