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
  2-2 is a draw.
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
        for seat, count in self.mendi_won.items():
            team_mendi[self.team_of(seat)] += count
        self.final_mendi = team_mendi
        if team_mendi["A"] == team_mendi["B"]:
            self.winner_team = "DRAW"
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

TRICK_PAUSE_SECONDS = 3.0  # how long a completed trick stays visible before clearing


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


def rotate_dealer(room):
    room.dealer_seat = (room.dealer_seat + 1) % 4


async def cancel_room_and_notify(room, leaving_seat: int, reason: str = "player_left"):
    """Any player exiting (host or not) cancels the room entirely for everyone."""
    room.cancelled = True
    await broadcast(room, {
        "type": "room_cancelled",
        "reason": reason,
        "leaving_seat": leaving_seat,
    })
    manager.cancel_room(room.code)


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

            # ---------------- CREATE ROOM ----------------
            if mtype == "create_room":
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
                            "winner_team": h.winner_team,
                            "final_mendi": h.final_mendi,
                        })
                else:
                    await send_hand_state_to_all(room)

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
                            "winner_team": h.winner_team,
                            "final_mendi": h.final_mendi,
                        })
                else:
                    # Reveal didn't complete the trick - remaining players still
                    # need to play into it normally, no pause needed here.
                    await send_hand_state_to_all(room)

            # ---------------- EXIT GAME (explicit, cancels room for everyone) ----------------
            elif mtype == "exit_game":
                if room is None or seat is None:
                    await send_json(ws, {"type": "error", "message": "Not in a room"})
                    continue
                await cancel_room_and_notify(room, seat, reason="player_left")
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
        # seat disconnected so others can see it. Explicit exits are handled
        # entirely by the exit_game branch above, which already nulls out
        # `room`/`seat` before we get here, so this block is a no-op for that
        # case (avoids double-cancelling or cancelling an already-gone room).
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
<link href="https://fonts.googleapis.com/css2?family=Open+Sans:wght@400;600;700&display=swap" rel="stylesheet">
<title>Mendikot</title>
<style>
  :root {
    --bg-deep: #1e3a5f;
    --bg-panel: #2a4d7a;
    --bg-panel-2: #3b5f94;
    --felt: #254670;
    --felt-light: #355a85;
    --table-bg: #1e3a5f;
    --gold: #e2e8f0;
    --gold-bright: #ffffff;
    --cream: #e2e8f0;
    --ink: #1a202c;
    --teal-bright: #90cdf4;
    --red-suit: #fc8181;
    --line: rgba(255, 255, 255, 0.25);
  }

  * { box-sizing: border-box; -webkit-tap-highlight-color: transparent; }

  body {
    margin: 0;
    height: 100vh;
    height: 100dvh;
    background-color: #1e3a5f;
    background-image:
      linear-gradient(rgba(255,255,255,0.07) 1px, transparent 1px),
      linear-gradient(90deg, rgba(255,255,255,0.07) 1px, transparent 1px),
      linear-gradient(rgba(255,255,255,0.04) 1px, transparent 1px),
      linear-gradient(90deg, rgba(255,255,255,0.04) 1px, transparent 1px);
    background-size: 20px 20px, 20px 20px, 100px 100px, 100px 100px;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    color: var(--cream);
    overflow: hidden;
    transition: background 0.2s ease;
  }

  body.in-game {
    background: var(--table-bg);
  }

  .display {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-weight: 700;
  }
  .ui {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  }

  /* doodle texture overlay */
  body::before {
    content: "";
    position: fixed;
    inset: 0;
    pointer-events: none;
    background-image:
      repeating-linear-gradient(45deg, rgba(255,255,255,0.02) 0px, rgba(255,255,255,0.02) 1px, transparent 1px, transparent 14px);
    z-index: 0;
  }

  #app {
    position: relative;
    z-index: 1;
    height: 100vh;
    height: 100dvh;
    display: flex;
    flex-direction: column;
    overflow: hidden;
  }

  #view-menu, #view-create, #view-join, #view-room {
    overflow-y: auto;
    min-height: 0;
  }

  /* ---------------- LOBBY / HOME ---------------- */

  .home-wrap {
    flex: 1;
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    padding: 32px 20px;
    gap: 28px;
  }

  .home-title {
    font-size: 52px;
    letter-spacing: 1px;
    color: var(--gold-bright);
    margin: 0;
    text-align: center;
    animation: doodleBounce 0.8s cubic-bezier(.2,1.4,.4,1);
  }
  .home-title .stamp-suits {
    display: block;
    font-size: 22px;
    letter-spacing: 8px;
    color: var(--cream);
    opacity: 0.65;
    margin-top: 6px;
  }

  .home-card {
    background: var(--bg-panel);
    border: 2px solid var(--line);
    border-radius: 4px 12px 6px 10px;
    padding: 28px;
    width: 100%;
    max-width: 380px;
    animation: sketchyAppear 0.5s ease;
  }

  .home-card + .home-card { margin-top: 4px; }

  .field-label {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 11px;
    text-transform: uppercase;
    letter-spacing: 1.5px;
    color: var(--gold);
    display: block;
    margin-bottom: 8px;
  }

  input[type=text] {
    width: 100%;
    padding: 13px 14px;
    border-radius: 4px 8px 6px 3px;
    border: 2px solid var(--line);
    background: var(--bg-panel-2);
    color: var(--cream);
    font-size: 17px;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    outline: none;
    margin-bottom: 16px;
    transition: border-color 0.2s ease, transform 0.15s ease;
  }
  input[type=text]:focus { 
    border-color: var(--gold); 
    transform: scale(1.01) rotate(-0.5deg);
  }
  input[type=text]::placeholder { color: rgba(245,237,224,0.35); }
  input#join-code { text-transform: uppercase; letter-spacing: 3px; text-align: center; font-size: 22px; font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; }

  button {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    cursor: pointer;
    border: 2px solid rgba(255,255,255,0.3);
    border-radius: 5px 9px 4px 8px;
    font-weight: 600;
    letter-spacing: 0.3px;
    transition: transform 0.12s ease, filter 0.15s ease, background 0.2s ease;
  }
  button:active { transform: scale(0.97) rotate(-1deg); }
  button:disabled { opacity: 0.4; cursor: not-allowed; }

  .btn-primary {
    width: 100%;
    padding: 14px;
    background: linear-gradient(180deg, var(--gold-bright), var(--gold));
    color: var(--ink);
    font-size: 16px;
    border: 2px solid rgba(255,255,255,0.5);
  }
  .btn-primary:hover:not(:disabled) { filter: brightness(1.08); transform: translateY(-2px) rotate(0.5deg); }

  .btn-secondary {
    width: 100%;
    padding: 14px;
    background: transparent;
    border: 2px solid var(--teal-bright);
    color: var(--teal-bright);
    font-size: 16px;
  }
  .btn-secondary:hover:not(:disabled) { background: rgba(144,205,244,0.12); transform: translateY(-2px) rotate(-0.5deg); }

  .menu-buttons {
    display: flex;
    flex-direction: column;
    gap: 14px;
    width: 100%;
    max-width: 340px;
  }

  .screen-title {
    font-size: 26px;
    color: var(--gold-bright);
    margin: 0 0 4px;
    text-align: center;
    animation: doodleBounce 0.6s ease;
  }

  .back-link {
    background: none;
    border: none;
    color: rgba(245,237,224,0.55);
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 14px;
    align-self: flex-start;
    padding: 4px 0;
    margin-bottom: 4px;
    transition: color 0.2s ease, transform 0.15s ease;
  }
  .back-link:hover { color: var(--cream); transform: translateX(-3px); }

  .team-picker {
    display: flex;
    gap: 10px;
    margin-bottom: 18px;
  }
  .team-btn {
    flex: 1;
    padding: 14px 8px;
    background: rgba(245,237,224,0.04);
    border: 2px solid rgba(245,237,224,0.25);
    border-radius: 5px 10px 4px 8px;
    color: rgba(245,237,224,0.7);
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 14px;
    font-weight: 600;
    transition: all 0.2s ease;
  }
  .team-btn.team-a.selected {
    border-color: var(--gold);
    background: rgba(226,232,240,0.16);
    color: var(--gold-bright);
    transform: rotate(-1deg) scale(1.02);
  }
  .team-btn.team-b.selected {
    border-color: var(--teal-bright);
    background: rgba(144,205,244,0.14);
    color: var(--teal-bright);
    transform: rotate(1deg) scale(1.02);
  }
  .team-btn.full {
    opacity: 0.35;
    cursor: not-allowed;
  }
  .team-btn:disabled { cursor: not-allowed; }

  .exit-link {
    background: none;
    border: none;
    color: rgba(245,237,224,0.4);
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 13px;
    margin-top: 18px;
    padding: 6px;
    transition: color 0.2s ease, transform 0.15s ease;
  }
  .exit-link:hover { color: var(--red-suit); transform: scale(1.05); }

  .exit-icon-btn {
    position: absolute;
    top: 6px;
    right: 6px;
    z-index: 20;
    width: 32px;
    height: 32px;
    border-radius: 50%;
    background: rgba(255,255,255,0.1);
    border: 2px solid rgba(255,255,255,0.2);
    color: rgba(245,237,224,0.6);
    font-size: 20px;
    line-height: 1;
    display: flex;
    align-items: center;
    justify-content: center;
    padding: 0;
    transition: transform 0.15s ease, background 0.2s ease;
  }
  .exit-icon-btn:hover { background: rgba(252,129,129,0.3); color: var(--cream); transform: rotate(90deg); }

  .confirm-overlay {
    position: fixed;
    inset: 0;
    background: rgba(10,20,35,0.85);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 90;
    padding: 20px;
  }
  .confirm-overlay.show { display: flex; animation: fadeIn 0.2s ease; }
  .confirm-card {
    background: var(--bg-panel);
    border: 2px solid var(--line);
    border-radius: 6px 14px 8px 10px;
    padding: 28px 24px;
    max-width: 320px;
    width: 100%;
    text-align: center;
    animation: sketchyAppear 0.4s ease;
  }
  .confirm-text {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 15px;
    color: var(--cream);
    margin-bottom: 20px;
    line-height: 1.4;
  }
  .confirm-buttons {
    display: flex;
    gap: 10px;
  }
  .confirm-buttons button { flex: 1; padding: 12px; font-size: 14px; }
  .btn-danger {
    background: var(--red-suit);
    color: var(--cream);
    border: 2px solid rgba(255,255,255,0.3);
  }

  .rotate-prompt {
    display: none;
    position: fixed;
    inset: 0;
    z-index: 200;
    background: var(--table-bg);
    flex-direction: column;
    align-items: center;
    justify-content: center;
    gap: 18px;
    text-align: center;
    padding: 30px;
  }
  .rotate-icon {
    font-size: 56px;
    color: var(--gold-bright);
    animation: rotateHint 1.8s ease-in-out infinite;
  }
  @keyframes rotateHint {
    0%, 100% { transform: rotate(0deg); }
    50% { transform: rotate(-90deg); }
  }
  .rotate-text {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 16px;
    color: var(--cream);
    max-width: 260px;
  }
  /* Game is now vertical-first; no portrait lock needed */

  .error-banner {
    background: rgba(252,129,129,0.2);
    border: 2px solid var(--red-suit);
    color: #FFD9D4;
    padding: 10px 14px;
    border-radius: 4px 8px 5px 6px;
    font-size: 14px;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    margin-bottom: 14px;
    display: none;
    animation: sketchyAppear 0.3s ease;
  }
  .error-banner.show { display: block; }

  /* ---------------- ROOM / WAITING ---------------- */

  .room-wrap {
    flex: 1;
    display: flex;
    flex-direction: column;
    align-items: center;
    padding: 40px 20px;
    gap: 24px;
  }

  .room-code-display {
    text-align: center;
    animation: doodleBounce 0.5s ease;
  }
  .room-code-display .label {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 12px;
    text-transform: uppercase;
    letter-spacing: 2px;
    color: rgba(245,237,224,0.55);
    margin-bottom: 10px;
  }
  .room-code-display .code {
    font-size: 48px;
    letter-spacing: 10px;
    color: var(--gold-bright);
    background: var(--bg-panel);
    border: 2px solid var(--line);
    border-radius: 5px 10px 6px 8px;
    padding: 14px 20px 14px 30px;
    display: inline-block;
    animation: pencilDraw 0.6s ease;
  }
  .copy-hint {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 13px;
    color: rgba(245,237,224,0.5);
    margin-top: 10px;
    cursor: pointer;
    transition: color 0.2s ease, transform 0.15s ease;
  }
  .copy-hint:hover { color: var(--gold); transform: scale(1.05); }

  .seats-grid {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 12px;
    width: 100%;
    max-width: 420px;
  }
  .seat-slot {
    background: var(--bg-panel);
    border: 2px solid var(--line);
    border-radius: 5px 10px 4px 8px;
    padding: 16px;
    text-align: center;
    position: relative;
    animation: sketchyAppear 0.4s ease backwards;
  }
  .seat-slot:nth-child(1) { animation-delay: 0.05s; }
  .seat-slot:nth-child(2) { animation-delay: 0.10s; }
  .seat-slot:nth-child(3) { animation-delay: 0.15s; }
  .seat-slot:nth-child(4) { animation-delay: 0.20s; }
  .seat-slot.team-a { border-left: 3px solid var(--gold); }
  .seat-slot.team-b { border-left: 3px solid var(--teal-bright); }
  .seat-slot.empty { opacity: 0.4; border-style: dashed; }
  .seat-slot .seat-name {
    font-size: 16px;
    font-weight: 700;
  }
  .seat-slot .seat-team {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 10px;
    text-transform: uppercase;
    letter-spacing: 1px;
    opacity: 0.6;
    margin-top: 4px;
  }
  .seat-slot .disconnected-badge {
    position: absolute;
    top: 8px; right: 8px;
    width: 8px; height: 8px;
    border-radius: 50%;
    background: #fc8181;
    animation: pulseBadge 1.5s ease-in-out infinite;
  }
  @keyframes pulseBadge {
    0%, 100% { transform: scale(1); opacity: 1; }
    50% { transform: scale(1.3); opacity: 0.7; }
  }
  .seat-slot .you-badge {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 9px;
    color: var(--gold);
    letter-spacing: 1px;
    margin-top: 2px;
  }

  .waiting-note {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 14px;
    color: rgba(245,237,224,0.6);
    text-align: center;
    animation: fadeIn 0.5s ease;
  }

  /* ---------------- GAME TABLE ---------------- */

  .table-wrap {
    flex: 1;
    display: flex;
    flex-direction: column;
    max-width: 900px;
    width: 100%;
    margin: 0 auto;
    padding: clamp(6px, 2vh, 10px);
    min-height: 0;
    overflow: hidden;
    position: relative;
  }

  .game-vertical-layout {
    flex: 1;
    display: flex;
    flex-direction: column;
    gap: clamp(6px, 1.5vw, 14px);
    min-height: 0;
  }

  .game-vertical-layout .table-felt {
    flex: 2;
    min-width: 0;
    min-height: 0;
  }

  .game-vertical-layout .hand-strip-wrap {
    flex: 1;
    min-width: 0;
    min-height: 0;
    display: flex;
    flex-direction: column;
    margin-top: 0;
    padding: 4px;
  }
  .game-vertical-layout .hand-strip {
    flex: 1;
    min-height: 0;
    align-content: flex-start;
  }

  .score-cluster-top {
    display: flex;
    align-items: flex-start;
    justify-content: center;
    gap: clamp(8px, 2.5vw, 18px);
    flex-shrink: 0;
    padding: 4px 0 6px;
    animation: fadeIn 0.3s ease;
  }

  .center-stack {
    grid-area: center;
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    gap: clamp(4px, 1.2vh, 10px);
    height: 100%;
    width: 100%;
  }



  .score-side {
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 3px;
  }
  .score-side-label {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 9px;
    text-transform: uppercase;
    letter-spacing: 1px;
    color: rgba(245,237,224,0.5);
  }
  .score-side.mine .score-side-label { color: rgba(255,255,255,0.75); }
  .score-side.theirs .score-side-label { color: rgba(144,205,244,0.7); }

  .ten-slots {
    display: flex;
    gap: clamp(2px, 0.8vw, 4px);
  }
  .ten-slot {
    width: clamp(17px, 4.2vw, 22px);
    height: clamp(24px, 6vw, 31px);
    border-radius: 3px;
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-weight: 700;
    font-size: 8px;
    line-height: 1;
    background: rgba(0,0,0,0.14);
    color: rgba(245,237,224,0.18);
    border: 1px solid rgba(255,255,255,0.1);
    transition: transform 0.25s cubic-bezier(.2,1.4,.4,1), background 0.25s ease;
  }
  .ten-slot .ts-suit { font-size: clamp(10px, 2.6vw, 13px); line-height: 1; }
  .ten-slot.won {
    background: var(--cream);
    transform: translateY(-2px) scale(1.05);
    animation: mendiWon 0.5s cubic-bezier(.2,1.4,.4,1);
    border: 2px solid var(--gold-bright);
  }
  @keyframes mendiWon {
    0% { transform: translateY(6px) scale(0.6) rotate(-10deg); opacity: 0; }
    60% { transform: translateY(-4px) scale(1.12) rotate(4deg); opacity: 1; }
    100% { transform: translateY(-2px) scale(1.05) rotate(0deg); }
  }
  .ten-slot.won.red { color: var(--red-suit); }
  .ten-slot.won.black { color: var(--ink); }
  .ten-slot.won.mine { border-color: var(--gold); }
  .ten-slot.won.theirs { border-color: var(--teal-bright); }

  .trump-card-box {
    width: clamp(30px, 7.5vw, 40px);
    height: clamp(42px, 10.5vw, 56px);
    border-radius: 5px 8px 4px 7px;
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: clamp(16px, 4vw, 22px);
    background: rgba(0,0,0,0.16);
    color: rgba(245,237,224,0.3);
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-weight: 700;
    flex-shrink: 0;
    border: 2px solid rgba(255,255,255,0.15);
    transition: transform 0.3s cubic-bezier(.2,1.4,.4,1), background 0.3s ease;
  }
  .trump-card-box.revealed {
    background: var(--cream);
    animation: trumpLockIn 0.5s cubic-bezier(.2,1.4,.4,1);
    border: 2px solid var(--gold);
  }
  @keyframes trumpLockIn {
    0% { transform: scale(1.6) rotate(-6deg); opacity: 0.3; }
    60% { transform: scale(0.92) rotate(3deg); }
    100% { transform: scale(1) rotate(0deg); }
  }
  .trump-card-box.revealed.red { color: var(--red-suit); }
  .trump-card-box.revealed.black { color: var(--ink); }

  .table-felt {
    flex: 1;
    background: transparent;
    border-radius: 0;
    border: none;
    position: relative;
    min-height: 0;
    display: grid;
    grid-template-areas:
      ".    top    ."
      "left center right"
      ".    bottom .";
    grid-template-columns: clamp(48px, 15vw, 70px) 1fr clamp(48px, 15vw, 70px);
    grid-template-rows: clamp(48px, 12vh, 70px) 1fr clamp(48px, 12vh, 70px);
    padding: clamp(6px, 1.5vw, 10px);
    gap: 4px;
  }

  .seat-marker {
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    gap: 3px;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  }
  .seat-marker .seat-mini-name {
    font-size: 12px;
    font-weight: 600;
    color: rgba(245,237,224,0.75);
    white-space: nowrap;
    max-width: 92px;
    overflow: hidden;
    text-overflow: ellipsis;
    transition: color 0.25s ease, transform 0.2s ease;
  }
  .seat-marker .turn-dot {
    width: 6px;
    height: 6px;
    border-radius: 50%;
    background: var(--gold-bright);
    opacity: 0;
    transform: scale(0.5);
    transition: opacity 0.25s ease, transform 0.25s ease;
    border: 1px solid rgba(255,255,255,0.5);
  }
  .seat-marker.active .seat-mini-name {
    color: var(--gold-bright);
    transform: scale(1.05);
  }
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
    flex: 1;
    width: 100%;
    display: flex;
    align-items: center;
    justify-content: center;
    min-height: 0;
  }
  .trick-slot {
    position: absolute;
    width: clamp(38px, 9vw, 46px);
    height: clamp(53px, 12.5vw, 64px);
    animation: cardPopIn 0.35s cubic-bezier(.2,1.4,.4,1);
  }
  .trick-slot.pos-top { top: 0; left: 50%; transform: translateX(-50%); }
  .trick-slot.pos-left { left: 0; top: 50%; transform: translateY(-50%); }
  .trick-slot.pos-right { right: 0; top: 50%; transform: translateY(-50%); }
  .trick-slot.pos-bottom { bottom: 0; left: 50%; transform: translateX(-50%); }

  /* playing card */
  .pcard {
    width: clamp(38px, 9vw, 46px);
    height: clamp(53px, 12.5vw, 64px);
    background: var(--cream);
    border-radius: 4px 6px 5px 7px;
    border: 2px solid var(--ink);
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    padding: 3px 4px;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-weight: 700;
    position: relative;
    flex-shrink: 0;
    animation: cardFlipIn 0.3s ease;
  }
  .pcard.red { color: var(--red-suit); }
  .pcard.black { color: var(--ink); }
  .pcard .pcard-rank { font-size: 13px; line-height: 1; }
  .pcard .pcard-suit-big {
    position: absolute;
    top: 50%; left: 50%;
    transform: translate(-50%, -50%);
    font-size: 20px;
    opacity: 0.85;
  }
  .pcard .pcard-rank.bottom { align-self: flex-end; transform: rotate(180deg); }

  .pcard.trump-marked::after {
    content: "";
    position: absolute;
    top: 2px; right: 2px;
    width: 7px; height: 7px;
    border-radius: 50%;
    background: var(--gold);
    border: 1px solid var(--ink);
  }

  .pcard.face-down {
    background: repeating-linear-gradient(135deg, var(--bg-panel-2) 0 4px, var(--bg-panel) 4px 8px);
    border: 2px solid var(--gold);
  }

  /* hand strip */
  .hand-strip-wrap {
    margin-top: clamp(4px, 1.5vh, 14px);
    padding: clamp(6px, 1.5vh, 12px) 4px 4px;
    flex-shrink: 0;
  }

  .hand-strip {
    display: flex;
    justify-content: center;
    flex-wrap: wrap;
    align-content: flex-start;
    gap: clamp(4px, 1vw, 8px);
    padding: 12px 8px 8px;
    overflow-y: auto;
    overflow-x: visible;
    -webkit-overflow-scrolling: touch;
    scrollbar-width: thin;
  }
  .hand-card {
    width: clamp(44px, 8vw, 64px);
    height: clamp(62px, 11.3vw, 90px);
    background: var(--cream);
    border-radius: 5px 8px 4px 9px;
    border: 2px solid var(--ink);
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    padding: 5px 6px;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-weight: 700;
    cursor: pointer;
    transition: transform 0.18s ease, border-color 0.15s ease;
    position: relative;
    flex-shrink: 0;
    animation: cardDealIn 0.4s cubic-bezier(.2,1.4,.4,1) backwards;
  }
  .hand-card:nth-child(1) { animation-delay: 0.03s; }
  .hand-card:nth-child(2) { animation-delay: 0.06s; }
  .hand-card:nth-child(3) { animation-delay: 0.09s; }
  .hand-card:nth-child(4) { animation-delay: 0.12s; }
  .hand-card:nth-child(5) { animation-delay: 0.15s; }
  .hand-card:nth-child(6) { animation-delay: 0.18s; }
  .hand-card:nth-child(7) { animation-delay: 0.21s; }
  .hand-card:nth-child(8) { animation-delay: 0.24s; }
  .hand-card:nth-child(9) { animation-delay: 0.27s; }
  .hand-card:nth-child(10) { animation-delay: 0.30s; }
  .hand-card:nth-child(11) { animation-delay: 0.33s; }
  .hand-card:nth-child(12) { animation-delay: 0.36s; }
  .hand-card:nth-child(13) { animation-delay: 0.39s; }
  .hand-card.red { color: var(--red-suit); }
  .hand-card.black { color: var(--ink); }
  .hand-card .hc-rank { font-size: 16px; line-height: 1; }
  .hand-card .hc-suit-big {
    position: absolute;
    top: 50%; left: 50%;
    transform: translate(-50%,-50%);
    font-size: 26px;
    opacity: 0.85;
  }
  .hand-card .hc-rank.bottom { align-self: flex-end; transform: rotate(180deg); }
  .hand-card:hover { transform: translateY(-6px) rotate(-1deg); z-index: 5; }
  .hand-card.playable:hover { transform: translateY(-8px) rotate(1deg); border-color: var(--gold); }
  .hand-card.disabled { opacity: 0.35; cursor: not-allowed; }
  .hand-card.disabled:hover { transform: none; }
  .hand-card.trump-marked { outline: 2px solid var(--gold); outline-offset: -2px; }
  .hand-card.selected-for-reveal { outline: 3px solid var(--gold-bright); outline-offset: -3px; transform: translateY(-6px) rotate(-2deg); }

  .action-bar {
    text-align: center;
    padding: 6px 0 2px;
    min-height: 40px;
  }
  .reveal-btn {
    padding: 10px 22px;
    background: linear-gradient(180deg, var(--gold-bright), var(--gold));
    color: var(--ink);
    border-radius: 20px;
    font-size: 14px;
    border: 2px solid rgba(255,255,255,0.4);
    animation: sketchyAppear 0.3s ease;
    transition: transform 0.15s ease;
  }
  .reveal-btn:hover { transform: scale(1.05) rotate(-1deg); }
  .reveal-btn:active { transform: scale(0.97); }
  .reveal-prompt {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 13px;
    color: var(--gold-bright);
    margin-bottom: 8px;
    animation: fadeIn 0.3s ease;
  }

  /* trump reveal flash overlay */
  .trump-flash {
    position: fixed;
    inset: 0;
    background: rgba(30,20,40,0.75);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 50;
  }
  .trump-flash.show { display: flex; animation: fadeIn 0.2s ease; }
  .trump-flash .stamp {
    width: 130px;
    height: 182px;
    border-radius: 8px 14px 10px 12px;
    background: var(--cream);
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 88px;
    animation: stampIn 0.4s cubic-bezier(.2,1.4,.4,1);
    border: 3px solid var(--ink);
  }
  .trump-flash .stamp.red { color: var(--red-suit); }
  .trump-flash .stamp.black { color: var(--ink); }
  @keyframes stampIn {
    0% { transform: scale(2.2) rotate(-8deg); opacity: 0; }
    60% { transform: scale(0.95) rotate(2deg); opacity: 1; }
    100% { transform: scale(1) rotate(0deg); opacity: 1; }
  }
  @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }

  /* hand complete overlay */
  .result-overlay {
    position: fixed;
    inset: 0;
    background: rgba(15,25,45,0.9);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 60;
    padding: 20px;
  }
  .result-overlay.show { display: flex; animation: fadeIn 0.25s ease; }
  .result-card {
    background: var(--bg-panel);
    border: 2px solid var(--line);
    border-radius: 6px 14px 8px 10px;
    padding: 36px 30px;
    text-align: center;
    max-width: 340px;
    width: 100%;
    animation: sketchyAppear 0.5s ease;
  }
  .result-headline {
    font-size: 30px;
    color: var(--gold-bright);
    margin: 0 0 6px;
    animation: doodleBounce 0.5s ease;
  }
  .result-headline.draw { color: rgba(245,237,224,0.75); }
  .result-sub {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 14px;
    color: rgba(245,237,224,0.6);
    margin-bottom: 22px;
  }
  .result-mendi-row {
    display: flex;
    justify-content: center;
    gap: 24px;
    margin-bottom: 26px;
  }
  .result-mendi-row .mendi-counter {
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 8px;
  }
  .result-mendi-row .mendi-label {
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 10px;
    text-transform: uppercase;
    letter-spacing: 1px;
    opacity: 0.6;
  }
  .result-mendi-row .ten-slots { gap: 5px; }
  .result-mendi-row .ten-slot {
    width: 26px;
    height: 36px;
    font-size: 10px;
  }
  .result-mendi-row .ten-slot .ts-suit { font-size: 15px; }

  .toast {
    position: fixed;
    bottom: 20px;
    left: 50%;
    transform: translateX(-50%);
    background: var(--bg-panel);
    border: 2px solid var(--red-suit);
    color: var(--cream);
    padding: 12px 20px;
    border-radius: 20px;
    font-family: 'Open Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    font-size: 13px;
    z-index: 100;
    opacity: 0;
    pointer-events: none;
    transition: opacity 0.2s ease, transform 0.3s ease;
  }
  .toast.show { opacity: 1; transform: translateX(-50%) translateY(0); animation: toastSlide 0.3s ease; }
  @keyframes toastSlide {
    from { transform: translateX(-50%) translateY(20px); opacity: 0; }
    to { transform: translateX(-50%) translateY(0); opacity: 1; }
  }

  .hidden { display: none !important; }

  /* ---- Animation keyframes ---- */
  @keyframes cardDealIn {
    0% { transform: translateY(-40px) rotate(-8deg) scale(0.7); opacity: 0; }
    60% { transform: translateY(4px) rotate(2deg) scale(1.04); opacity: 1; }
    100% { transform: translateY(0) rotate(0deg) scale(1); }
  }
  @keyframes cardPopIn {
    0% { transform: scale(0.3) rotate(-15deg); opacity: 0; }
    70% { transform: scale(1.08) rotate(3deg); opacity: 1; }
    100% { transform: scale(1) rotate(0deg); opacity: 1; }
  }
  @keyframes cardFlipIn {
    0% { transform: rotateY(90deg) scale(0.6); opacity: 0; }
    100% { transform: rotateY(0deg) scale(1); opacity: 1; }
  }
  @keyframes sketchyAppear {
    0% { transform: scale(0.9) rotate(-2deg); opacity: 0; }
    50% { transform: scale(1.01) rotate(0.5deg); }
    100% { transform: scale(1) rotate(0deg); opacity: 1; }
  }
  @keyframes doodleBounce {
    0% { transform: translateY(-20px) scale(0.9); opacity: 0; }
    50% { transform: translateY(4px) scale(1.02); }
    70% { transform: translateY(-2px) scale(0.99); }
    100% { transform: translateY(0) scale(1); opacity: 1; }
  }
  @keyframes pencilDraw {
    0% { clip-path: inset(0 100% 0 0); opacity: 0; }
    100% { clip-path: inset(0 0 0 0); opacity: 1; }
  }

  @media (max-width: 380px) {
    .home-title { font-size: 42px; }
    .room-code-display .code { font-size: 38px; letter-spacing: 7px; }
  }

  @media (max-height: 420px) {
    .table-felt {
      grid-template-columns: clamp(34px, 10vw, 52px) 1fr clamp(34px, 10vw, 52px);
      grid-template-rows: clamp(34px, 14vh, 50px) 1fr clamp(34px, 14vh, 50px);
    }
    .ten-slot { width: 15px; height: 21px; }
    .trump-card-box { width: 26px; height: 36px; font-size: 14px; }
    .score-side-label { font-size: 8px; }
    .action-bar { min-height: 26px; padding: 2px 0; }
  }

  @media (max-height: 340px) {
    .ten-slot { width: 13px; height: 18px; }
    .trump-card-box { width: 22px; height: 30px; font-size: 12px; }
    .score-cluster { gap: 6px; }
  }

  @media (min-width: 900px) {
    .table-wrap { max-width: 1100px; }
    .hand-card { width: clamp(50px, 6vw, 70px); height: clamp(70px, 8.4vw, 98px); }
  }
</style>
</head>
<body>
<div id="app">

  <!-- ============ LANDING MENU ============ -->
  <div id="view-menu" class="home-wrap">
    <h1 class="home-title">Mendikot<span class="stamp-suits">♠ ♥ ♦ ♣</span></h1>
    <div class="menu-buttons">
      <button class="btn-primary" id="btn-goto-create">Create Room</button>
      <button class="btn-secondary" id="btn-goto-join">Join Room</button>
    </div>
  </div>

  <!-- ============ CREATE ROOM SCREEN ============ -->
  <div id="view-create" class="home-wrap hidden">
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
  <div id="view-join" class="home-wrap hidden">
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
  <div id="view-room" class="room-wrap hidden">
    <div class="room-code-display">
      <div class="label">Room Code</div>
      <div class="code" id="room-code-text">-----</div>
      <div class="copy-hint" id="copy-hint">Tap to copy</div>
    </div>

    <div class="seats-grid" id="seats-grid"></div>

    <div class="waiting-note" id="waiting-note">Waiting for players to join…</div>

    <button class="btn-primary hidden" id="btn-start" style="max-width:280px;">Start Game</button>
    <button class="exit-link" id="btn-exit-room">Exit Room</button>
  </div>

  <!-- ============ GAME TABLE VIEW ============ -->

  <div id="view-game" class="table-wrap hidden">
    <button class="exit-icon-btn" id="btn-exit-game" title="Exit game">&times;</button>

    <!-- Score cluster at very top -->
    <div class="score-cluster-top">
      <div class="score-side mine">
        <div class="score-side-label">Your</div>
        <div class="ten-slots" id="my-ten-slots"></div>
      </div>
      <div class="trump-card-box" id="trump-symbol">?</div>
      <div class="score-side theirs">
        <div class="score-side-label">Opponent</div>
        <div class="ten-slots" id="opp-ten-slots"></div>
      </div>
    </div>

    <div class="game-vertical-layout">
      <div class="table-felt">
        <div class="seat-marker top" id="marker-top"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>
        <div class="seat-marker left" id="marker-left"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>
        <div class="seat-marker right" id="marker-right"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>
        <div class="seat-marker bottom-marker" id="marker-bottom"><div class="turn-dot"></div><div class="seat-mini-name">-</div></div>

        <div class="center-stack">
          <div class="trick-center" id="trick-center"></div>
        </div>
      </div>

      <div class="hand-strip-wrap">
        <div class="action-bar" id="action-bar"></div>
        <div class="hand-strip" id="hand-strip"></div>
      </div>
    </div>
  </div>

</div>

<div class="rotate-prompt" id="rotate-prompt">
  <div class="rotate-icon">&#8635;</div>
  <div class="rotate-text">Rotate your device to play</div>
</div>

<div class="trump-flash" id="trump-flash">
  <div class="stamp" id="trump-flash-symbol">?</div>
</div>

<div class="result-overlay" id="result-overlay">
  <div class="result-card">
    <h2 class="result-headline" id="result-headline">You Win!</h2>
    <div class="result-sub" id="result-sub">4 – 0 Mendi</div>
    <div class="result-mendi-row" id="result-mendi-row"></div>
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
    seats: {},          // seat -> {name, connected, team}
    teamFull: { A: false, B: false },
    hostSeat: 0,
    gameState: null,    // latest game_state.state
    pendingReveal: false,
    selectedRevealCard: null,
    view: 'menu',
    createTeam: null,
    joinTeam: null,
    // Cards currently shown on the table, built up live from card_played
    // events. This is NOT the same as gameState.current_trick: the server
    // resolves a trick (clearing current_trick) the instant the 4th card is
    // played, then pauses ~3s before sending the next game_state. If we only
    // rendered from gameState.current_trick, the 4th card would never
    // visibly appear - it'd already be gone by the time state arrives. So
    // displayedTrick is pushed to directly on every card_played, and only
    // cleared once the next game_state confirms a fresh trick has begun.
    displayedTrick: [],
    lastTrickKey: '',   // to avoid re-animating trick cards on state refresh
  };

  const SUIT_SYMBOL = { S: '\\u2660', H: '\\u2665', D: '\\u2666', C: '\\u2663' };
  const RED_SUITS = new Set(['H', 'D']);
  const SUITS_ORDER = ['S', 'H', 'D', 'C'];
  const SEAT_POS_FROM_ME = { 0: 'bottom', 1: 'left', 2: 'top', 3: 'right' }; // relative offsets computed dynamically

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
  const ALL_VIEWS = ['menu', 'create', 'join', 'room', 'game'];
  function showView(name) {
    S.view = name;
    ALL_VIEWS.forEach(v => {
      document.getElementById('view-' + v).classList.toggle('hidden', v !== name);
    });
    document.body.classList.toggle('in-game', name === 'game');
    if (name === 'game') updateOrientationState();
  }

  // ---------------- orientation / rotate-prompt ----------------
  function updateOrientationState() {
    const isPortrait = window.innerHeight > window.innerWidth;
    document.body.classList.toggle('is-portrait', isPortrait);
  }
  window.addEventListener('resize', () => {
    if (S.view === 'game') updateOrientationState();
  });
  window.addEventListener('orientationchange', () => {
    if (S.view === 'game') setTimeout(updateOrientationState, 50);
  });

  function showToast(msg) {
    const t = document.getElementById('toast');
    t.textContent = msg;
    t.classList.add('show');
    clearTimeout(t._hideTimer);
    t._hideTimer = setTimeout(() => t.classList.remove('show'), 2600);
  }

  function showError(bannerId, msg) {
    const el = document.getElementById(bannerId);
    el.textContent = msg;
    el.classList.add('show');
  }
  function clearError(bannerId) {
    document.getElementById(bannerId).classList.remove('show');
  }

  // ---------------- websocket ----------------
  function connect() {
    const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
    S.ws = new WebSocket(proto + '//' + location.host + '/ws');
    S.ws.onopen = () => { tryAutoRejoin(); };
    S.ws.onmessage = (ev) => handleMessage(JSON.parse(ev.data));
    S.ws.onclose = () => {
      showToast('Connection lost. Reconnecting…');
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
        saveSession(S.playerId, S.roomCode);
        document.getElementById('room-code-text').textContent = S.roomCode;
        if (S.view === 'create' || S.view === 'join' || S.view === 'menu') showView('room');
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
        // Sync the displayed trick from server state. During normal mid-trick
        // updates (1-3 cards in) this just mirrors current_trick. When this
        // arrives AFTER the 3s pause (current_trick now empty because the
        // server already resolved it), this is what actually clears the
        // table for the next trick.
        S.displayedTrick = (msg.state.current_trick || []).slice();
        if (S.view !== 'game') showView('game');
        renderGame();
        break;

      case 'hand_started':
        S.pendingReveal = false;
        S.selectedRevealCard = null;
        S.displayedTrick = [];
        S.lastTrickKey = '';
        hideResultOverlay();
        break;

      case 'card_played':
        // Push immediately so the card appears on the table in real time,
        // even for the trick-completing 4th card (whose play already
        // resolved the trick server-side, clearing current_trick before the
        // next game_state - which won't arrive until after the 3s pause).
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
        // The reveal itself plays a card into the trick too (see main.py's
        // reveal_trump) - show it immediately just like card_played does.
        if (!S.displayedTrick.some(p => p.seat === msg.seat)) {
          S.displayedTrick.push({ seat: msg.seat, card: msg.card });
        }
        flashTrumpReveal(msg.trump_suit, msg.seat, msg.phase2_dealt);
        renderGame();
        break;

      case 'trick_won':
        break;

      case 'hand_complete':
        showResultOverlay(msg.winner_team, msg.final_mendi);
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
    const reasonText = 'A player left the game, so the room was closed.';
    showToast(reasonText);
    // Give the toast a beat to be visible before reloading back to the menu.
    setTimeout(() => { location.reload(); }, 1800);
  }

  // ---------------- menu / navigation actions ----------------
  document.getElementById('btn-goto-create').addEventListener('click', () => {
    showView('create');
  });
  document.getElementById('btn-goto-join').addEventListener('click', () => {
    showView('join');
  });
  document.getElementById('btn-create-back').addEventListener('click', () => {
    showView('menu');
  });
  document.getElementById('btn-join-back').addEventListener('click', () => {
    showView('menu');
  });

  // ---------------- team picker (shared logic for create + join screens) ----------------
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

  // ---------------- exit game/room (cancels for everyone) ----------------
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
      note.textContent = msg.is_full ? 'Waiting for host to start…' : 'Waiting for players to join…';
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
    el.innerHTML =
      '<div class="' + (cls === 'pcard' ? 'pcard-rank' : 'hc-rank') + '">' + rank + suitSym + '</div>' +
      '<div class="' + (cls === 'pcard' ? 'pcard-suit-big' : 'hc-suit-big') + '">' + suitSym + '</div>' +
      '<div class="' + (cls === 'pcard' ? 'pcard-rank bottom' : 'hc-rank bottom') + '">' + rank + suitSym + '</div>';
    return el;
  }

  // ---------------- game render ----------------
  function renderGame() {
    const st = S.gameState;
    if (!st) return;

    const mySeat = st.your_seat;
    const myTeam = mySeat % 2 === 0 ? 'A' : 'B';
    const oppTeam = myTeam === 'A' ? 'B' : 'A';

    // aggregate which ten-suits each team has won
    const mineSuits = [];
    const theirsSuits = [];
    for (const seatStr in st.mendi_suits_won) {
      const seat = parseInt(seatStr, 10);
      const team = seat % 2 === 0 ? 'A' : 'B';
      const suits = st.mendi_suits_won[seatStr] || [];
      if (team === myTeam) mineSuits.push(...suits);
      else theirsSuits.push(...suits);
    }
    renderTenSlots('my-ten-slots', mineSuits, 'mine');
    renderTenSlots('opp-ten-slots', theirsSuits, 'theirs');

    // trump card: "?" before reveal, suit symbol only after reveal
    const trumpBox = document.getElementById('trump-symbol');
    if (st.trump_suit) {
      trumpBox.className = 'trump-card-box revealed ' + (RED_SUITS.has(st.trump_suit) ? 'red' : 'black');
      trumpBox.textContent = SUIT_SYMBOL[st.trump_suit];
    } else {
      trumpBox.className = 'trump-card-box';
      trumpBox.textContent = '?';
    }

    // seat markers (relative to me: bottom = me, then left/top/right going clockwise from my left)
    const order = [mySeat, (mySeat + 1) % 4, (mySeat + 2) % 4, (mySeat + 3) % 4];
    const posMap = { bottom: order[0], left: order[1], top: order[2], right: order[3] };
    for (const pos in posMap) {
      const seat = posMap[pos];
      const seatInfo = S.seats[String(seat)] || { name: 'P' + seat, connected: true };
      const el = document.getElementById('marker-' + pos);
      el.classList.toggle('active', st.turn_seat === seat && st.phase !== 'HAND_COMPLETE');
      el.classList.toggle('disconnected', seatInfo.connected === false);
      const nameEl = el.querySelector('.seat-mini-name');
      nameEl.textContent = (seat === mySeat ? 'You' : seatInfo.name) + (seat % 2 === (mySeat % 2) ? '' : '');
    }

    // trick center - render from S.displayedTrick (client-side accumulated,
    // kept accurate live via card_played events) rather than st.current_trick
    // directly, since the server clears current_trick the instant a trick's
    // 4th card lands, before the 3s pause even starts.
    const center = document.getElementById('trick-center');
    // Detect if this is a genuinely new trick state (new cards added) vs a
    // re-render of the same trick (e.g. game_state arriving after card_played).
    // Only animate when cards are actually new.
    const currentTrickKey = S.displayedTrick.map(p => p.seat + '-' + p.card).sort().join('|');
    const trickIsNew = S.lastTrickKey !== currentTrickKey;
    S.lastTrickKey = currentTrickKey;
    center.innerHTML = '';
    if (S.displayedTrick && S.displayedTrick.length > 0) {
      const posOf = { };
      posOf[order[0]] = 'pos-bottom';
      posOf[order[1]] = 'pos-left';
      posOf[order[2]] = 'pos-top';
      posOf[order[3]] = 'pos-right';
      S.displayedTrick.forEach(play => {
        const slot = document.createElement('div');
        slot.className = 'trick-slot ' + posOf[play.seat];
        if (!trickIsNew) {
          slot.style.animation = 'none';
        }
        const cardEl = makeCardEl(play.card, 'pcard', st.trump_suit);
        slot.appendChild(cardEl);
        center.appendChild(slot);
      });
    }

    // whose turn it is: communicated via the seat-marker glow/pulse-dot only
    // (see seat marker rendering below) - no separate text row.

    // action bar (reveal button / prompt)
    const actionBar = document.getElementById('action-bar');
    actionBar.innerHTML = '';
    if (S.pendingReveal && st.turn_seat === mySeat) {
      const prompt = document.createElement('div');
      prompt.className = 'reveal-prompt';
      prompt.textContent = 'Tap a trump card in your hand, then confirm:';
      actionBar.appendChild(prompt);
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
    const handStrip = document.getElementById('hand-strip');
    handStrip.innerHTML = '';
    const hand = st.your_hand || [];
    const myTurn = st.turn_seat === mySeat && st.phase !== 'HAND_COMPLETE';
    const legalSet = computeLegalMoves(st, hand);

    hand.forEach(card => {
      const el = makeCardEl(card, 'hand-card', st.trump_suit);
      let isPlayable = false;

      if (S.pendingReveal && myTurn) {
        // during reveal, only trump-suit-eligible... actually any card that IS trump can be chosen
        // (player picks which trump card to reveal - so only cards matching what WOULD become trump)
        // Since trump suit isn't locked yet, any card can theoretically be revealed as the trump card;
        // the suit of the revealed card becomes trump. All cards are technically selectable here,
        // but only cards NOT matching led suit make sense (server enforces this).
        isPlayable = true;
        if (card === S.selectedRevealCard) el.classList.add('selected-for-reveal');
        el.addEventListener('click', () => {
          S.selectedRevealCard = card;
          renderGame();
        });
      } else if (myTurn) {
        isPlayable = legalSet.has(card);
        if (isPlayable) {
          el.classList.add('playable');
          el.addEventListener('click', () => {
            send({ type: 'play_card', card: card });
          });
        } else {
          el.classList.add('disabled');
        }
      } else {
        el.classList.add('disabled');
      }
      handStrip.appendChild(el);
    });
  }

  function renderTenSlots(containerId, wonSuits, kind) {
    const el = document.getElementById(containerId);
    el.innerHTML = '';
    const wonSet = new Set(wonSuits);
    SUITS_ORDER.forEach(suit => {
      const slot = document.createElement('div');
      const isWon = wonSet.has(suit);
      const color = RED_SUITS.has(suit) ? 'red' : 'black';
      slot.className = 'ten-slot' + (isWon ? ' won ' + color + ' ' + kind : '');
      slot.innerHTML = '<div class="ts-suit">' + SUIT_SYMBOL[suit] + '</div>';
      el.appendChild(slot);
    });
  }

  function computeLegalMoves(st, hand) {
    if (!st.current_trick || st.current_trick.length === 0) {
      return new Set(hand);
    }
    if (st.trick_void_exempt_seats && st.trick_void_exempt_seats.includes(st.your_seat)) {
      return new Set(hand);  // locked-in void status for this trick, any card legal
    }
    const led = st.led_suit;
    const sameSuit = hand.filter(c => cardSuit(c) === led);
    if (sameSuit.length > 0) return new Set(sameSuit);
    return new Set(hand);
  }

  // ---------------- trump flash ----------------
  function flashTrumpReveal(trumpSuit, seat, phase2Dealt) {
    const overlay = document.getElementById('trump-flash');
    const symbolEl = document.getElementById('trump-flash-symbol');
    symbolEl.textContent = SUIT_SYMBOL[trumpSuit];
    symbolEl.className = 'stamp ' + (RED_SUITS.has(trumpSuit) ? 'red' : 'black');
    overlay.classList.add('show');
    setTimeout(() => overlay.classList.remove('show'), 1400);

    const seatInfo = S.seats[String(seat)] || { name: 'Seat ' + seat };
    const who = seat === S.mySeat ? 'You' : seatInfo.name;
    let msg = who + ' revealed trump: ' + fullSuitName(trumpSuit);
    if (phase2Dealt) msg += ' \\u2014 remaining cards dealt';
    showToast(msg);
  }
  function fullSuitName(s) {
    return { S: 'Spades', H: 'Hearts', D: 'Diamonds', C: 'Clubs' }[s];
  }

  // ---------------- result overlay ----------------
  function showResultOverlay(winnerTeam, finalMendi) {
    const overlay = document.getElementById('result-overlay');
    const headline = document.getElementById('result-headline');
    const sub = document.getElementById('result-sub');
    const row = document.getElementById('result-mendi-row');

    const myTeam = S.mySeat % 2 === 0 ? 'A' : 'B';
    let mine = finalMendi[myTeam];
    let theirs = finalMendi[myTeam === 'A' ? 'B' : 'A'];

    if (winnerTeam === 'DRAW') {
      headline.textContent = 'Draw';
      headline.className = 'result-headline draw';
      sub.textContent = '2 \\u2013 2 split';
    } else if (winnerTeam === myTeam) {
      headline.textContent = 'You Win!';
      headline.className = 'result-headline';
      sub.textContent = mine + ' \\u2013 ' + theirs;
    } else {
      headline.textContent = 'You Lose';
      headline.className = 'result-headline draw';
      sub.textContent = theirs + ' \\u2013 ' + mine;
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
