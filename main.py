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
  2-2 is a draw. If tied on mendi, total cards won breaks the tie.
"""


SUITS = ["S", "H", "D", "C"]
RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"]
RANK_VALUE = {r: i for i, r in enumerate(RANKS)}

SUIT_SYMBOL = {"S": "\u2660", "H": "\u2665", "D": "\u2666", "C": "\u2663"}


class Phase(str, Enum):
    LOBBY = "LOBBY"
    PHASE1_PLAY = "PHASE1_PLAY"
    AWAITING_TRUMP_REVEAL = "AWAITING_TRUMP_REVEAL"
    PHASE2_PLAY = "PHASE2_PLAY"
    HAND_COMPLETE = "HAND_COMPLETE"


def make_deck():
    return [f"{r}{s}" for s in SUITS for r in RANKS]


def card_rank(card: str) -> str:
    return card[:-1]


def card_suit(card: str) -> str:
    return card[-1]


class MendikotHand:
    def __init__(self, dealer_seat: int = 0, rng: Optional[random.Random] = None):
        self.rng = rng or random.Random()
        self.dealer_seat = dealer_seat
        deck = make_deck()
        self.rng.shuffle(deck)

        self.hands = {s: [] for s in range(4)}
        for i in range(5):
            for s in range(4):
                self.hands[s].append(deck.pop())
        self.boot = deck

        self.phase = Phase.PHASE1_PLAY
        self.trump_suit: Optional[str] = None
        self.trump_revealed_card: Optional[str] = None
        self.trump_revealer_seat: Optional[int] = None

        self.current_trick: list[dict] = []
        self.led_suit: Optional[str] = None
        self.turn_seat = (dealer_seat + 1) % 4
        self.leader_seat = self.turn_seat

        self.tricks_played = 0
        self.trick_history: list[dict] = []

        self.mendi_won = {0: 0, 1: 0, 2: 0, 3: 0}
        self.mendi_suits_won = {0: [], 1: [], 2: [], 3: []}
        self.cards_won = {"A": 0, "B": 0}

        self.awaiting_reveal_from: Optional[int] = None
        self.pending_void_card: Optional[str] = None
        self.trick_void_exempt_seats: set[int] = set()
        self.boot_deal_pending: bool = False

        self.winner_team: Optional[str] = None
        self.final_mendi: Optional[dict] = None
        self.final_cards: Optional[dict] = None

    def team_of(self, seat: int) -> str:
        return "A" if seat in (0, 2) else "B"

    def legal_moves(self, seat: int) -> list[str]:
        hand = self.hands[seat]
        if not self.current_trick:
            return list(hand)
        if seat in self.trick_void_exempt_seats:
            return list(hand)
        led = self.led_suit
        same_suit = [c for c in hand if card_suit(c) == led]
        if same_suit:
            return same_suit
        return list(hand)

    def must_reveal_trump(self, seat: int, card_being_played_suit_check: bool) -> bool:
        return (
            self.phase == Phase.PHASE1_PLAY
            and self.trump_suit is None
            and self.current_trick
            and card_being_played_suit_check
        )

    def play_card(self, seat: int, card: str) -> dict:
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
            if not has_led_suit and self.phase == Phase.PHASE1_PLAY and self.trump_suit is None:
                raise ValueError("VOID_MUST_REVEAL_TRUMP")

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
        if self.phase != Phase.PHASE1_PLAY or self.trump_suit is not None:
            raise ValueError("Trump reveal not applicable")
        if seat != self.turn_seat:
            raise ValueError("Not your turn")
        hand = self.hands[seat]
        if card not in hand:
            raise ValueError("Card not in hand")
        if not self.current_trick:
            raise ValueError("Cannot reveal trump while leading a trick")

        led = self.led_suit
        has_led_suit = any(card_suit(c) == led for c in hand)
        if has_led_suit:
            raise ValueError("You can follow suit, cannot reveal trump")

        self.trump_suit = card_suit(card)
        self.trump_revealed_card = card
        self.trump_revealer_seat = seat
        self.phase = Phase.PHASE2_PLAY
        self.boot_deal_pending = True
        self.trick_void_exempt_seats.add(seat)

        hand.remove(card)
        self.current_trick.append({"seat": seat, "card": card})

        result = {
            "type": "trump_revealed",
            "seat": seat,
            "card": card,
            "trump_suit": self.trump_suit,
        }

        if len(self.current_trick) == 4:
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

        winning_team = self.team_of(winner_seat)
        self.cards_won[winning_team] += 4

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
        self.trick_void_exempt_seats = set()

        trick_summary = {
            "winner_seat": winner_seat,
            "mendi_count": len(mendi_cards),
            "winner_team": winning_team,
        }

        if self.boot_deal_pending:
            self.boot_deal_pending = False
            self._deal_phase2()
            trick_summary["phase2_dealt"] = True
        elif self.phase == Phase.PHASE1_PLAY and self.tricks_played == 5:
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
                return (2, rank)
            if suit == led:
                return (1, rank)
            return (0, rank)

        best = max(self.current_trick, key=strength)
        return best["seat"]

    def _deal_phase2(self):
        for s in range(4):
            self.hands[s].extend(self.boot[s * 8:(s + 1) * 8])
        self.boot = []

    def _finalize_hand(self):
        self.phase = Phase.HAND_COMPLETE
        team_mendi = {"A": 0, "B": 0}
        for seat, count in self.mendi_won.items():
            team_mendi[self.team_of(seat)] += count
        self.final_mendi = team_mendi
        self.final_cards = dict(self.cards_won)

        if team_mendi["A"] > team_mendi["B"]:
            self.winner_team = "A"
        elif team_mendi["B"] > team_mendi["A"]:
            self.winner_team = "B"
        else:
            if self.cards_won["A"] > self.cards_won["B"]:
                self.winner_team = "A"
            elif self.cards_won["B"] > self.cards_won["A"]:
                self.winner_team = "B"
            else:
                self.winner_team = "DRAW"

    def public_state(self, viewer_seat: Optional[int] = None) -> dict:
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


ROOM_CODE_CHARS = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"
ROOM_TTL_SECONDS = 10 * 60

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
    players: dict[int, Player] = field(default_factory=dict)
    hand: Optional[MendikotHand] = None
    dealer_seat: int = 0
    created_at: float = field(default_factory=time.time)
    last_active: float = field(default_factory=time.time)
    locked_until: float = 0.0
    cancelled: bool = False
    game_active: bool = False

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
        seat = TEAM_SEATS[team][0]
        player = Player(player_id=host_player_id, name=host_name, seat=seat)
        room.players[seat] = player
        self.rooms[code] = room
        return room, player

    def join_room(self, code: str, name: str, player_id: str, team: str) -> tuple[Optional[Room], Optional[Player], Optional[str]]:
        room = self.rooms.get(code)
        if room is None:
            return None, None, "ROOM_NOT_FOUND"

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


app = FastAPI()
manager = RoomManager()

TRICK_PAUSE_SECONDS = 3.0

BOT_NAMES = ["Raj", "Vikram", "Priya", "Arjun", "Neha", "Karan", "Anita", "Dev"]


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
    room.cancelled = True
    await broadcast(room, {
        "type": "room_cancelled",
        "reason": reason,
        "leaving_seat": leaving_seat,
    })
    manager.cancel_room(room.code)


async def handle_bot_turns(room):
    while room.hand and room.hand.phase not in (Phase.HAND_COMPLETE, Phase.LOBBY):
        turn_seat = room.hand.turn_seat
        if turn_seat not in room.players or not room.players[turn_seat].is_bot:
            break

        bot = room.players[turn_seat]
        h = room.hand

        await asyncio.sleep(0.8 + random.random() * 0.7)

        if room.cancelled or room.hand is None or room.hand.phase == Phase.HAND_COMPLETE:
            break

        legal = h.legal_moves(turn_seat)
        if not legal:
            break

        def card_sort_key(c):
            return (RANK_VALUE.get(card_rank(c), 99), SUITS.index(card_suit(c)))

        chosen = min(legal, key=card_sort_key)

        try:
            if not h.current_trick:
                ev = h.play_card(turn_seat, chosen)
            else:
                led = h.led_suit
                has_led = any(card_suit(c) == led for c in h.hands[turn_seat])
                if not has_led and h.phase == Phase.PHASE1_PLAY and h.trump_suit is None:
                    ev = h.reveal_trump(turn_seat, chosen)
                else:
                    ev = h.play_card(turn_seat, chosen)

            room.touch()

            if ev["type"] == "trump_revealed":
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
                        "winner_team": tr.get("winner_team"),
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
                            "final_cards": h.final_cards,
                        })
                else:
                    await send_hand_state_to_all(room)
            else:
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
                        "winner_team": tr.get("winner_team"),
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
                            "final_cards": h.final_cards,
                        })
                else:
                    await send_hand_state_to_all(room)

        except ValueError:
            break


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

            elif mtype == "join_room":
                code = (msg.get("room_code") or "").strip().upper()
                name = (msg.get("player_name") or "Player").strip()[:20] or "Player"
                pid = msg.get("player_id") or str(uuid.uuid4())
                team = msg.get("team")

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

                if room.hand is not None:
                    state = room.hand.public_state(viewer_seat=seat)
                    await send_json(ws, {"type": "game_state", "state": state})

            elif mtype == "start_solo":
                name = (msg.get("player_name") or "Player").strip()[:20] or "Player"
                player_id = str(uuid.uuid4())
                room, player = manager.create_room(name, player_id, "A")
                player.ws = ws
                seat = player.seat

                bot_names = random.sample(BOT_NAMES, 3)
                bot_seats = [1, 2, 3]
                for i, bs in enumerate(bot_seats):
                    bot = Player(
                        player_id=str(uuid.uuid4()),
                        name=bot_names[i],
                        seat=bs,
                        is_bot=True,
                    )
                    room.players[bs] = bot

                room.game_active = True

                await send_json(ws, {
                    "type": "joined",
                    "room_code": room.code,
                    "player_id": player_id,
                    "your_seat": seat,
                })
                await broadcast(room, room.lobby_state())
                await start_new_hand(room)

                asyncio.create_task(handle_bot_turns(room))

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
                room.game_active = True
                await start_new_hand(room)

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
                        "winner_team": tr.get("winner_team"),
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
                            "final_cards": h.final_cards,
                        })
                else:
                    await send_hand_state_to_all(room)

                asyncio.create_task(handle_bot_turns(room))

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
                        "winner_team": tr.get("winner_team"),
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
                            "final_cards": h.final_cards,
                        })
                else:
                    await send_hand_state_to_all(room)

                asyncio.create_task(handle_bot_turns(room))

            elif mtype == "exit_game":
                if room is None or seat is None:
                    await send_json(ws, {"type": "error", "message": "Not in a room"})
                    continue
                is_host = seat == 0
                in_lobby = room.hand is None or room.hand.phase == Phase.LOBBY
                if is_host or room.game_active:
                    await cancel_room_and_notify(room, seat, reason="player_left")
                else:
                    if seat in room.players:
                        del room.players[seat]
                    room.touch()
                    await broadcast(room, room.lobby_state())
                room = None
                seat = None

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
                asyncio.create_task(handle_bot_turns(room))

            else:
                await send_json(ws, {"type": "error", "message": f"Unknown message type: {mtype}"})

    except WebSocketDisconnect:
        pass
    finally:
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
