#!/usr/bin/env python3
"""
Mendikot — Single-file FastAPI server with embedded React frontend.
Run: python main.py
"""

import asyncio
import json
import os
import random
import string
import time
import uuid
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse

# ===================== CONSTANTS =====================
SUITS = ["♠", "♥", "♦", "♣"]
RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"]
RANK_VALUES = {r: i + 2 for i, r in enumerate(RANKS)}
SUIT_COLORS = {"♠": "black", "♣": "black", "♥": "red", "♦": "red"}
TEAM_A_SEATS = {0, 2}
TEAM_B_SEATS = {1, 3}
ROOM_TTL_SECONDS = 600
BOT_NAMES = ["Raju", "Vijay", "Amit"]
TRICK_PAUSE_SECONDS = 3.0
BOT_DELAY_MIN = 0.8
BOT_DELAY_MAX = 1.5


def _make_id() -> str:
    return uuid.uuid4().hex[:12]


def _room_code() -> str:
    return "".join(random.choices(string.ascii_uppercase, k=4))


# ===================== GAME ENGINE =====================

@dataclass
class Card:
    suit: str
    rank: str
    id: str = field(default_factory=_make_id)

    def to_dict(self):
        return {"suit": self.suit, "rank": self.rank, "id": self.id, "value": RANK_VALUES[self.rank]}

    @property
    def value(self) -> int:
        return RANK_VALUES[self.rank]

    def is_mendi(self) -> bool:
        return self.rank == "10"


def create_deck() -> List[Card]:
    deck = [Card(s, r) for s in SUITS for r in RANKS]
    random.shuffle(deck)
    return deck


@dataclass
class Player:
    seat: int
    name: str
    team: str
    is_bot: bool
    hand: List[Card] = field(default_factory=list)
    void_exempt: bool = False
    ws: Optional[WebSocket] = None
    disconnected: bool = False

    def to_dict(self, hide_hand: bool = True):
        return {
            "seat": self.seat,
            "name": self.name,
            "team": self.team,
            "is_bot": self.is_bot,
            "hand_size": len(self.hand),
            "hand": [c.to_dict() for c in self.hand] if not hide_hand else None,
            "disconnected": self.disconnected,
        }


@dataclass
class Room:
    code: str
    host_id: str
    players: Dict[str, Player] = field(default_factory=dict)
    seats: List[Optional[str]] = field(default_factory=lambda: [None, None, None, None])
    game: Optional["MendikotGame"] = None
    created_at: float = field(default_factory=time.time)
    last_activity: float = field(default_factory=time.time)
    solo: bool = False
    cancelled: bool = False
    _bot_tasks: List[asyncio.Task] = field(default_factory=list)

    def touch(self):
        self.last_activity = time.time()

    def is_full(self) -> bool:
        return all(s is not None for s in self.seats)

    def broadcast(self, msg: dict):
        for p in self.players.values():
            if p.ws and not p.disconnected:
                asyncio.create_task(_safe_send(p.ws, msg))

    def get_seat_team(self, seat: int) -> str:
        return "A" if seat in TEAM_A_SEATS else "B"

    def cancel(self, reason: str):
        self.cancelled = True
        self.broadcast({"type": "room_cancelled", "reason": reason})
        for t in self._bot_tasks:
            t.cancel()
        self._bot_tasks.clear()


async def _safe_send(ws: WebSocket, msg: dict):
    try:
        await ws.send_json(msg)
    except Exception:
        pass


class MendikotGame:
    def __init__(self, room: Room):
        self.room = room
        deck = create_deck()
        self.boot: List[Card] = deck[20:]
        self.dealer = 0
        self.leader = (self.dealer + 1) % 4
        self.turn = self.leader
        self.trick: List[dict] = []
        self.trump_suit: Optional[str] = None
        self.trump_revealed = False
        self.phase = "phase1"
        self.trick_number = 1
        self.mendi: Dict[str, List[Card]] = {"A": [], "B": []}
        self.total_cards: Dict[str, List[Card]] = {"A": [], "B": []}
        self.paused = False
        self.hand_complete = False
        self.result: Optional[str] = None

        for seat in range(4):
            pid = room.seats[seat]
            player = room.players[pid]
            player.hand = sorted(deck[seat * 5 : seat * 5 + 5], key=lambda c: (SUITS.index(c.suit), c.value))
            player.void_exempt = False

    def to_state(self, for_seat: int) -> dict:
        pid = self.room.seats[for_seat]
        p = self.room.players[pid]
        return {
            "dealer": self.dealer,
            "leader": self.leader,
            "turn": self.turn,
            "trick": [{"seat": t["seat"], "card": t["card"].to_dict(), "is_reveal": t.get("is_reveal", False)} for t in self.trick],
            "trump_suit": self.trump_suit,
            "trump_revealed": self.trump_revealed,
            "phase": self.phase,
            "trick_number": self.trick_number,
            "mendi": {k: [c.to_dict() for c in v] for k, v in self.mendi.items()},
            "scores": {k: len(v) for k, v in self.mendi.items()},
            "total_cards": {k: len(v) for k, v in self.total_cards.items()},
            "paused": self.paused,
            "hand_complete": self.hand_complete,
            "result": self.result,
            "your_seat": for_seat,
            "your_hand": [c.to_dict() for c in p.hand],
            "players": [self.room.players[self.room.seats[s]].to_dict(hide_hand=(s != for_seat)) for s in range(4)],
        }

    def get_legal_mask(self, seat: int) -> List[bool]:
        pid = self.room.seats[seat]
        p = self.room.players[pid]
        if self.trick:
            led = self.trick[0]["card"].suit
            has_led = any(c.suit == led for c in p.hand)
            if has_led:
                return [c.suit == led for c in p.hand]
        return [True] * len(p.hand)

    def must_reveal_trump(self, seat: int) -> bool:
        if self.trump_suit or self.phase != "phase1":
            return False
        if not self.trick:
            return False
        pid = self.room.seats[seat]
        p = self.room.players[pid]
        led = self.trick[0]["card"].suit
        return not any(c.suit == led for c in p.hand)

    def play_card(self, seat: int, card_idx: int) -> Optional[dict]:
        if self.paused or self.hand_complete or self.turn != seat:
            return None
        pid = self.room.seats[seat]
        p = self.room.players[pid]
        if card_idx < 0 or card_idx >= len(p.hand):
            return None
        legal = self.get_legal_mask(seat)
        if not legal[card_idx]:
            return None

        is_reveal = self.must_reveal_trump(seat)
        card = p.hand.pop(card_idx)

        if is_reveal:
            self.trump_suit = card.suit
            self.trump_revealed = True
            for s in range(4):
                if s == seat:
                    continue
                other_pid = self.room.seats[s]
                other = self.room.players[other_pid]
                led = self.trick[0]["card"].suit
                if not any(c.suit == led for c in other.hand):
                    other.void_exempt = True

        self.trick.append({"seat": seat, "card": card, "is_reveal": is_reveal})
        self.turn = (seat + 1) % 4
        return {"seat": seat, "card": card.to_dict(), "is_reveal": is_reveal}

    def resolve_trick(self) -> int:
        led = self.trick[0]["card"].suit
        winner_idx = 0
        best_val = -1
        for i, t in enumerate(self.trick):
            c = t["card"]
            val = c.value
            if self.trump_suit and c.suit == self.trump_suit:
                val += 100
            elif c.suit != led:
                val = -1
            if val > best_val:
                best_val = val
                winner_idx = i
        winner_seat = self.trick[winner_idx]["seat"]
        team = "A" if winner_seat in TEAM_A_SEATS else "B"
        for t in self.trick:
            self.total_cards[team].append(t["card"])
            if t["card"].is_mendi():
                self.mendi[team].append(t["card"])
        return winner_seat

    def deal_boot(self):
        for seat in range(4):
            pid = self.room.seats[seat]
            p = self.room.players[pid]
            new_cards = self.boot[:8]
            self.boot = self.boot[8:]
            p.hand.extend(new_cards)
            p.hand.sort(key=lambda c: (SUITS.index(c.suit), c.value))
        self.phase = "phase2"

    def check_hand_end(self):
        if self.trick_number > 13:
            self.hand_complete = True
            ma = len(self.mendi["A"])
            mb = len(self.mendi["B"])
            if ma > mb:
                self.result = "A"
            elif mb > ma:
                self.result = "B"
            else:
                self.result = "draw"

    def next_hand(self):
        self.dealer = (self.dealer + 1) % 4
        # Save old total for reference? No, just reset
        self.__init__(self.room)


# ===================== ROOM MANAGER =====================

class RoomManager:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}

    def create(self, host_id: str, solo: bool = False) -> Room:
        while True:
            code = _room_code()
            if code not in self.rooms:
                break
        room = Room(code=code, host_id=host_id, solo=solo)
        self.rooms[code] = room
        return room

    def get(self, code: str) -> Optional[Room]:
        return self.rooms.get(code)

    def remove(self, code: str):
        self.rooms.pop(code, None)

    def gc(self):
        now = time.time()
        expired = [code for code, r in self.rooms.items() if now - r.last_activity > ROOM_TTL_SECONDS]
        for code in expired:
            room = self.rooms[code]
            room.cancel("Room expired due to inactivity")
            self.remove(code)


manager = RoomManager()


# ===================== BOT AI =====================

def bot_choose_card(game: "MendikotGame", seat: int) -> Optional[int]:
    pid = game.room.seats[seat]
    p = game.room.players[pid]
    legal = game.get_legal_mask(seat)
    options = [i for i, ok in enumerate(legal) if ok]
    if not options:
        return None
    options.sort(key=lambda i: p.hand[i].value)
    return options[0]


def bot_reveal_card(game: "MendikotGame", seat: int) -> int:
    pid = game.room.seats[seat]
    p = game.room.players[pid]
    return min(range(len(p.hand)), key=lambda i: p.hand[i].value)


async def bot_loop(room: Room):
    try:
        while True:
            await asyncio.sleep(0.3)
            game = room.game
            if not game or game.hand_complete or game.paused:
                continue
            seat = game.turn
            pid = room.seats[seat]
            if not pid:
                continue
            p = room.players[pid]
            if not p.is_bot:
                continue
            delay = random.uniform(BOT_DELAY_MIN, BOT_DELAY_MAX)
            await asyncio.sleep(delay)
            if not room.game or room.game.hand_complete or room.game.paused or room.game.turn != seat:
                continue
            if game.must_reveal_trump(seat):
                idx = bot_reveal_card(game, seat)
            else:
                idx = bot_choose_card(game, seat)
            if idx is None:
                continue
            result = game.play_card(seat, idx)
            if result:
                room.touch()
                await _handle_play_result(room, result)
    except asyncio.CancelledError:
        pass


async def _handle_play_result(room: Room, result: dict):
    game = room.game
    room.broadcast({"type": "card_played", **result})

    if result.get("is_reveal"):
        room.broadcast({"type": "trump_revealed", "suit": game.trump_suit, "by_seat": result["seat"]})

    if len(game.trick) == 4:
        game.paused = True
        winner_seat = game.resolve_trick()
        game.leader = winner_seat
        room.broadcast({
            "type": "trick_won",
            "winner_seat": winner_seat,
            "team": "A" if winner_seat in TEAM_A_SEATS else "B",
            "trick": [{"seat": t["seat"], "card": t["card"].to_dict()} for t in game.trick],
            "mendi": {k: [c.to_dict() for c in v] for k, v in game.mendi.items()},
            "scores": {k: len(v) for k, v in game.mendi.items()},
            "total_cards": {k: len(v) for k, v in game.total_cards.items()},
        })

        await asyncio.sleep(TRICK_PAUSE_SECONDS)

        if room.cancelled:
            return

        boot_dealt = False
        if game.phase == "phase1":
            if game.trump_revealed or game.trick_number >= 5:
                game.deal_boot()
                boot_dealt = True

        game.trick = []
        game.turn = game.leader
        game.trick_number += 1
        game.paused = False
        for p in room.players.values():
            p.void_exempt = False

        game.check_hand_end()

        if boot_dealt:
            room.broadcast({"type": "boot_dealt", "state": game.to_state(0)})

        if game.hand_complete:
            room.broadcast({
                "type": "hand_complete",
                "result": game.result,
                "mendi": {k: [c.to_dict() for c in v] for k, v in game.mendi.items()},
                "scores": {k: len(v) for k, v in game.mendi.items()},
                "total_cards": {k: len(v) for k, v in game.total_cards.items()},
            })
        else:
            room.broadcast({"type": "turn_change", "turn": game.turn, "state": game.to_state(0)})
    else:
        room.broadcast({"type": "turn_change", "turn": game.turn})


# ===================== WEBSOCKET HANDLER =====================

async def handle_ws(websocket: WebSocket):
    await websocket.accept()
    player_id: Optional[str] = None
    room_code: Optional[str] = None

    try:
        while True:
            raw = await websocket.receive_text()
            msg = json.loads(raw)
            mtype = msg.get("type")

            if mtype == "create_room":
                name = msg.get("name", "Player").strip() or "Player"
                team = msg.get("team", "A")
                solo = msg.get("solo", False)
                player_id = _make_id()
                room = manager.create(player_id, solo=solo)
                room_code = room.code
                room.seats[0] = player_id
                room.players[player_id] = Player(seat=0, name=name, team=team, is_bot=False, ws=websocket)
                room.touch()
                await websocket.send_json({
                    "type": "room_created",
                    "room_code": room.code,
                    "player_id": player_id,
                    "seat": 0,
                    "players": [room.players[room.seats[s]].to_dict() if room.seats[s] else None for s in range(4)],
                })
                if solo:
                    for seat in range(1, 4):
                        bot_id = f"bot_{seat}"
                        bot_team = "A" if seat in TEAM_A_SEATS else "B"
                        room.seats[seat] = bot_id
                        room.players[bot_id] = Player(seat=seat, name=BOT_NAMES[seat - 1], team=bot_team, is_bot=True)
                    room.game = MendikotGame(room)
                    room.broadcast({"type": "game_started", "state": room.game.to_state(0)})
                    task = asyncio.create_task(bot_loop(room))
                    room._bot_tasks.append(task)

            elif mtype == "join_room":
                code = msg.get("room_code", "").upper().strip()
                name = msg.get("name", "Player").strip() or "Player"
                team = msg.get("team", "A")
                room = manager.get(code)
                if not room:
                    await websocket.send_json({"type": "error", "message": "Room not found"})
                    continue
                if room.cancelled:
                    await websocket.send_json({"type": "error", "message": "Room has been cancelled"})
                    continue
                if room.solo:
                    await websocket.send_json({"type": "error", "message": "Cannot join solo room"})
                    continue
                target_seats = [s for s in range(4) if room.get_seat_team(s) == team and room.seats[s] is None]
                if not target_seats:
                    await websocket.send_json({"type": "error", "message": "Team full"})
                    continue
                seat = target_seats[0]
                player_id = _make_id()
                room_code = room.code
                room.seats[seat] = player_id
                room.players[player_id] = Player(seat=seat, name=name, team=team, is_bot=False, ws=websocket)
                room.touch()
                await websocket.send_json({
                    "type": "room_joined",
                    "room_code": room.code,
                    "player_id": player_id,
                    "seat": seat,
                    "players": [room.players[room.seats[s]].to_dict() if room.seats[s] else None for s in range(4)],
                })
                room.broadcast({
                    "type": "player_joined",
                    "seat": seat,
                    "players": [room.players[room.seats[s]].to_dict() if room.seats[s] else None for s in range(4)],
                })

            elif mtype == "start_game":
                if not room_code:
                    continue
                room = manager.get(room_code)
                if not room or room.players.get(player_id) is None:
                    continue
                if room.players[player_id].seat != 0:
                    await websocket.send_json({"type": "error", "message": "Only host can start"})
                    continue
                if not room.is_full():
                    await websocket.send_json({"type": "error", "message": "Room not full"})
                    continue
                room.game = MendikotGame(room)
                room.touch()
                room.broadcast({"type": "game_started", "state": room.game.to_state(0)})
                task = asyncio.create_task(bot_loop(room))
                room._bot_tasks.append(task)

            elif mtype == "play_card":
                if not room_code:
                    continue
                room = manager.get(room_code)
                if not room or not room.game:
                    continue
                p = room.players.get(player_id)
                if not p:
                    continue
                card_id = msg.get("card_id")
                seat = p.seat
                idx = next((i for i, c in enumerate(p.hand) if c.id == card_id), None)
                if idx is None:
                    continue
                result = room.game.play_card(seat, idx)
                if result:
                    room.touch()
                    await _handle_play_result(room, result)

            elif mtype == "reveal_trump":
                if not room_code:
                    continue
                room = manager.get(room_code)
                if not room or not room.game:
                    continue
                p = room.players.get(player_id)
                if not p:
                    continue
                seat = p.seat
                if not room.game.must_reveal_trump(seat):
                    continue
                idx = bot_reveal_card(room.game, seat)
                result = room.game.play_card(seat, idx)
                if result:
                    room.touch()
                    await _handle_play_result(room, result)

            elif mtype == "rematch":
                if not room_code:
                    continue
                room = manager.get(room_code)
                if not room or not room.game:
                    continue
                if room.players.get(player_id) is None:
                    continue
                room.game.next_hand()
                room.touch()
                room.broadcast({"type": "game_started", "state": room.game.to_state(0)})

            elif mtype == "ping":
                await websocket.send_json({"type": "pong"})

    except WebSocketDisconnect:
        pass
    except Exception:
        pass
    finally:
        if room_code and player_id:
            room = manager.get(room_code)
            if room and player_id in room.players:
                p = room.players[player_id]
                p.disconnected = True
                p.ws = None
                room.touch()
                if room.solo:
                    pass
                elif room.game and not room.game.hand_complete:
                    room.cancel("A player left during the game")
                    manager.remove(room_code)
                elif not room.game:
                    if p.seat == 0:
                        room.cancel("Host left")
                        manager.remove(room_code)
                    else:
                        room.seats[p.seat] = None
                        room.broadcast({
                            "type": "player_left",
                            "seat": p.seat,
                            "players": [room.players[room.seats[s]].to_dict() if room.seats[s] else None for s in range(4)],
                        })


# ===================== FASTAPI APP =====================

app = FastAPI(title="Mendikot")


@app.get("/")
async def root():
    return HTMLResponse(content=FRONTEND_HTML, status_code=200)


@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await handle_ws(websocket)


@app.on_event("startup")
async def startup():
    asyncio.create_task(_gc_loop())


async def _gc_loop():
    while True:
        await asyncio.sleep(60)
        manager.gc()


# ===================== FRONTEND =====================

FRONTEND_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
<title>Mendikot</title>
<script crossorigin src="https://unpkg.com/react@18/umd/react.production.min.js"></script>
<script crossorigin src="https://unpkg.com/react-dom@18/umd/react-dom.production.min.js"></script>
<script src="https://unpkg.com/@babel/standalone/babel.min.js"></script>
<style>
  :root {
    --felt-green: #0d5c36;
    --felt-green-light: #147a48;
    --felt-green-dark: #084022;
    --accent-gold: #d4af37;
    --card-width: clamp(34px, 9.5vw, 64px);
    --card-height: calc(var(--card-width) * 1.4);
    --seat-size: clamp(38px, 10vw, 56px);
    --font-base: clamp(12px, 3.2vw, 15px);
    --radius-sm: 8px;
    --radius-md: 14px;
    --radius-lg: 22px;
    --shadow-card: 0 3px 10px rgba(0,0,0,0.35);
  }
  * { box-sizing: border-box; margin: 0; padding: 0; -webkit-tap-highlight-color: transparent; }
  html, body, #root { height: 100%; overflow: hidden; }
  body {
    font-family: 'Segoe UI', system-ui, -apple-system, sans-serif;
    font-size: var(--font-base);
    background: var(--felt-green-dark);
    color: #fff;
    touch-action: manipulation;
  }
  @keyframes cardPopIn {
    0% { transform: scale(0) rotateY(90deg); opacity: 0; }
    60% { transform: scale(1.1) rotateY(0deg); opacity: 1; }
    100% { transform: scale(1) rotateY(0deg); opacity: 1; }
  }
  @keyframes cardFlyIn {
    0% { transform: translate(var(--fly-x), var(--fly-y)) scale(0.5) rotateZ(var(--fly-r)); opacity: 0; }
    100% { transform: translate(0,0) scale(1) rotateZ(0deg); opacity: 1; }
  }
  @keyframes trumpFlash {
    0% { opacity: 0; transform: scale(0.8); }
    30% { opacity: 1; transform: scale(1.05); }
    70% { opacity: 1; transform: scale(1); }
    100% { opacity: 0; transform: scale(1.2); }
  }
  @keyframes suitPulse {
    0%, 100% { transform: scale(1); opacity: 0.9; }
    50% { transform: scale(1.15); opacity: 1; }
  }
  @keyframes mendiSpring {
    0% { transform: scale(0) rotate(-20deg); }
    50% { transform: scale(1.3) rotate(5deg); }
    70% { transform: scale(0.9) rotate(-3deg); }
    100% { transform: scale(1) rotate(0deg); }
  }
  @keyframes glowPulse {
    0%, 100% { box-shadow: 0 0 5px var(--accent-gold); }
    50% { box-shadow: 0 0 20px var(--accent-gold), 0 0 40px rgba(212,175,55,0.3); }
  }
  @keyframes thinking {
    0%, 100% { opacity: 0.3; }
    50% { opacity: 1; }
  }
  @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
  @keyframes slideUp { from { transform: translateY(100%); } to { transform: translateY(0); } }
  @keyframes slideDown { from { transform: translateY(-20px); opacity: 0; } to { transform: translateY(0); opacity: 1; } }
  @keyframes dealIn {
    0% { transform: translateY(20px) scale(0.85); opacity: 0; }
    100% { transform: translateY(0) scale(1); opacity: 1; }
  }
  .app { 
    height: 100vh; 
    height: 100dvh;
    display: flex; 
    flex-direction: column; 
    background: radial-gradient(ellipse at center, var(--felt-green) 0%, var(--felt-green-dark) 100%); 
  }
  .view { flex: 1; display: flex; flex-direction: column; align-items: center; justify-content: center; padding: 16px; animation: fadeIn 0.4s ease; }
  .menu-title { font-size: clamp(2rem, 8vw, 3.5rem); font-weight: 800; color: var(--accent-gold); text-shadow: 0 2px 10px rgba(0,0,0,0.5); margin-bottom: 8px; letter-spacing: 2px; }
  .menu-sub { color: rgba(255,255,255,0.6); margin-bottom: 40px; font-size: 0.95rem; }
  .menu-btn {
    width: min(280px, 80vw);
    padding: 16px 24px;
    margin: 10px 0;
    border: none;
    border-radius: var(--radius-lg);
    font-size: 1.1rem;
    font-weight: 700;
    cursor: pointer;
    transition: all 0.2s;
    text-transform: uppercase;
    letter-spacing: 1px;
  }
  .menu-btn.primary { background: linear-gradient(135deg, var(--accent-gold), #b8941f); color: #1a1a1a; box-shadow: 0 4px 15px rgba(212,175,55,0.3); }
  .menu-btn.primary:active { transform: scale(0.96); }
  .menu-btn.secondary { background: rgba(255,255,255,0.08); color: #fff; border: 1px solid rgba(255,255,255,0.15); }
  .menu-btn.secondary:active { background: rgba(255,255,255,0.15); }
  .form-card {
    background: rgba(0,0,0,0.25);
    backdrop-filter: blur(10px);
    border: 1px solid rgba(255,255,255,0.08);
    border-radius: var(--radius-lg);
    padding: 28px;
    width: min(340px, 90vw);
  }
  .form-title { font-size: 1.4rem; font-weight: 700; margin-bottom: 20px; text-align: center; color: var(--accent-gold); }
  .input-group { margin-bottom: 16px; }
  .input-group label { display: block; margin-bottom: 6px; font-size: 0.85rem; color: rgba(255,255,255,0.7); font-weight: 500; }
  .input-group input, .input-group select {
    width: 100%;
    padding: 12px 14px;
    border-radius: var(--radius-sm);
    border: 1px solid rgba(255,255,255,0.12);
    background: rgba(0,0,0,0.3);
    color: #fff;
    font-size: 1rem;
    outline: none;
    transition: border-color 0.2s;
  }
  .input-group input:focus, .input-group select:focus { border-color: var(--accent-gold); }
  .team-select { display: flex; gap: 10px; margin-bottom: 16px; }
  .team-option {
    flex: 1;
    padding: 12px;
    border-radius: var(--radius-sm);
    border: 2px solid rgba(255,255,255,0.1);
    background: rgba(0,0,0,0.2);
    text-align: center;
    cursor: pointer;
    transition: all 0.2s;
    font-weight: 600;
  }
  .team-option.active { border-color: var(--accent-gold); background: rgba(212,175,55,0.15); }
  .team-a { color: #6bb5ff; }
  .team-b { color: #ff8a8a; }
  .form-actions { display: flex; gap: 10px; margin-top: 8px; }
  .form-actions button { flex: 1; padding: 12px; border-radius: var(--radius-sm); border: none; font-weight: 700; cursor: pointer; font-size: 0.95rem; }
  .btn-back { background: rgba(255,255,255,0.08); color: #fff; }
  .btn-submit { background: var(--accent-gold); color: #1a1a1a; }
  .room-code { font-size: 2rem; font-weight: 800; letter-spacing: 4px; color: var(--accent-gold); text-align: center; margin: 10px 0; }
  .seats-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 12px; width: min(320px, 85vw); margin: 20px 0; }
  .seat {
    background: rgba(0,0,0,0.25);
    border: 2px solid rgba(255,255,255,0.1);
    border-radius: var(--radius-md);
    padding: 16px 10px;
    text-align: center;
    transition: all 0.3s;
  }
  .seat.filled { border-color: var(--accent-gold); background: rgba(212,175,55,0.08); }
  .seat-name { font-weight: 600; font-size: 0.95rem; }
  .seat-team { font-size: 0.75rem; opacity: 0.6; margin-top: 4px; }
  .seat-status { font-size: 0.75rem; margin-top: 6px; padding: 3px 8px; border-radius: 10px; display: inline-block; }
  .status-host { background: rgba(212,175,55,0.2); color: var(--accent-gold); }
  .status-waiting { background: rgba(255,255,255,0.08); color: rgba(255,255,255,0.5); }
  .start-btn {
    width: min(280px, 80vw);
    padding: 14px;
    background: linear-gradient(135deg, var(--accent-gold), #b8941f);
    border: none;
    border-radius: var(--radius-lg);
    color: #1a1a1a;
    font-weight: 800;
    font-size: 1.1rem;
    cursor: pointer;
    text-transform: uppercase;
    letter-spacing: 1px;
    margin-top: 10px;
  }
  .start-btn:disabled { opacity: 0.4; cursor: not-allowed; }
  .game-view { flex: 1; display: flex; flex-direction: column; position: relative; overflow: hidden; }
  .score-cluster {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: 6px 10px;
    background: rgba(0,0,0,0.2);
    backdrop-filter: blur(6px);
    border-bottom: 1px solid rgba(255,255,255,0.05);
    min-height: 56px;
    flex-shrink: 0;
    z-index: 10;
  }
  .score-side { display: flex; flex-direction: column; align-items: center; min-width: 60px; }
  .score-label { font-size: 0.65rem; text-transform: uppercase; letter-spacing: 1px; opacity: 0.7; margin-bottom: 2px; }
  .score-number { font-size: 1.3rem; font-weight: 800; }
  .score-you { color: #6bb5ff; }
  .score-opp { color: #ff8a8a; }
  .mendi-strip { display: flex; gap: 2px; margin-top: 3px; height: 18px; flex-wrap: wrap; justify-content: center; }
  .mendi-mini {
    width: 12px; height: 17px;
    border-radius: 3px;
    background: #fff;
    display: flex; align-items: center; justify-content: center;
    font-size: 8px; font-weight: 800;
    box-shadow: 0 1px 3px rgba(0,0,0,0.3);
    animation: mendiSpring 0.5s ease both;
  }
  .trump-slot {
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
  }
  .trump-icon {
    width: 36px; height: 36px;
    border-radius: 50%;
    background: rgba(255,255,255,0.12);
    display: flex; align-items: center; justify-content: center;
    font-size: 1.4rem;
    box-shadow: 0 2px 8px rgba(0,0,0,0.2);
  }
  .trump-icon.unknown {
    color: rgba(255,255,255,0.35);
    font-size: 1.1rem;
    background: rgba(255,255,255,0.06);
  }
  .table-felt {
    flex: 1;
    position: relative;
    display: flex;
    align-items: center;
    justify-content: center;
    min-height: 0;
    padding-bottom: calc(var(--seat-size) + 16px);
  }
  .felt-ellipse {
    position: absolute;
    width: 90%; height: 82%;
    background: radial-gradient(ellipse at center, rgba(20,122,72,0.6) 0%, rgba(13,92,54,0.3) 60%, transparent 100%);
    border-radius: 50%;
    pointer-events: none;
  }
  .seat-marker {
    position: absolute;
    display: flex;
    flex-direction: column;
    align-items: center;
    transition: all 0.3s ease;
    z-index: 5;
  }
  .seat-marker.active .seat-avatar { animation: glowPulse 1.5s infinite; border-color: var(--accent-gold); }
  .seat-avatar {
    width: var(--seat-size);
    height: var(--seat-size);
    border-radius: 50%;
    background: rgba(0,0,0,0.4);
    border: 2px solid rgba(255,255,255,0.15);
    display: flex; align-items: center; justify-content: center;
    font-size: 1.2rem;
    box-shadow: 0 2px 8px rgba(0,0,0,0.3);
    transition: all 0.3s;
  }
  .seat-name-tag {
    margin-top: 4px;
    font-size: 0.7rem;
    font-weight: 600;
    background: rgba(0,0,0,0.4);
    padding: 2px 8px;
    border-radius: 10px;
    white-space: nowrap;
    max-width: 80px;
    overflow: hidden;
    text-overflow: ellipsis;
  }
  .seat-marker.top { top: 3%; left: 50%; transform: translateX(-50%); }
  .seat-marker.left { left: 2%; top: 50%; transform: translateY(-50%); }
  .seat-marker.right { right: 2%; top: 50%; transform: translateY(-50%); }
  .seat-marker.bottom { bottom: 8px; left: 50%; transform: translateX(-50%); }
  .bot-badge { font-size: 0.55rem; background: rgba(255,255,255,0.1); padding: 1px 5px; border-radius: 6px; margin-top: 2px; }
  .thinking-dots {
    display: flex;
    gap: 3px;
    margin-top: 3px;
  }
  .thinking-dots span {
    width: 4px; height: 4px;
    background: var(--accent-gold);
    border-radius: 50%;
    animation: thinking 0.8s ease infinite;
  }
  .thinking-dots span:nth-child(2) { animation-delay: 0.15s; }
  .thinking-dots span:nth-child(3) { animation-delay: 0.3s; }
  .hand-count {
    position: absolute;
    bottom: -4px;
    right: -4px;
    background: var(--accent-gold);
    color: #1a1a1a;
    font-size: 0.55rem;
    font-weight: 800;
    width: 15px; height: 15px;
    border-radius: 50%;
    display: flex; align-items: center; justify-content: center;
    box-shadow: 0 1px 4px rgba(0,0,0,0.4);
  }
  .trick-center {
    position: relative;
    width: min(190px, 48vw);
    height: min(190px, 48vw);
    display: flex; align-items: center;
    justify-content: center;
  }
  .trick-card-wrapper {
    position: absolute;
    transition: all 0.4s cubic-bezier(0.34, 1.56, 0.64, 1);
  }
  .trick-card-wrapper.pos-0 { bottom: 0; left: 50%; transform: translateX(-50%) translateY(20%); }
  .trick-card-wrapper.pos-1 { left: 0; top: 50%; transform: translateY(-50%) translateX(-20%); }
  .trick-card-wrapper.pos-2 { top: 0; left: 50%; transform: translateX(-50%) translateY(-20%); }
  .trick-card-wrapper.pos-3 { right: 0; top: 50%; transform: translateY(-50%) translateX(20%); }
  .trick-card-wrapper.animating {
    animation: cardFlyIn 0.5s cubic-bezier(0.34, 1.56, 0.64, 1) both;
  }
  .card {
    width: var(--card-width);
    height: var(--card-height);
    background: #fff;
    border-radius: clamp(5px, 1.5vw, 9px);
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    box-shadow: var(--shadow-card);
    position: relative;
    user-select: none;
    cursor: pointer;
    transition: transform 0.2s, box-shadow 0.2s;
    animation: cardPopIn 0.4s cubic-bezier(0.34, 1.56, 0.64, 1) both;
    flex-shrink: 0;
  }
  .card:hover:not(.disabled):not(.back) { transform: translateY(-6px); box-shadow: 0 6px 20px rgba(0,0,0,0.4); }
  .card.disabled { opacity: 0.45; cursor: not-allowed; filter: grayscale(0.3); }
  .card.back {
    background: linear-gradient(135deg, #1e3a5f 0%, #2a5298 50%, #1e3a5f 100%);
    background-size: 8px 8px;
    border: 1px solid rgba(255,255,255,0.15);
    cursor: default;
  }
  .card.back::after {
    content: "";
    width: 60%; height: 60%;
    border: 2px solid rgba(255,255,255,0.15);
    border-radius: 6px;
    position: absolute;
  }
  .card-rank { font-size: clamp(0.75rem, 2.5vw, 1.1rem); font-weight: 800; line-height: 1; }
  .card-suit { font-size: clamp(0.75rem, 2.5vw, 1.1rem); line-height: 1; margin-top: 1px; }
  .card.red { color: #c41e3a; }
  .card.black { color: #1a1a1a; }
  .card-corner {
    position: absolute;
    font-size: clamp(0.45rem, 1.3vw, 0.65rem);
    font-weight: 700;
    line-height: 1;
  }
  .card-corner.top-left { top: 4px; left: 5px; }
  .card-corner.bottom-right { bottom: 4px; right: 5px; transform: rotate(180deg); }
  .hand-strip {
    display: flex;
    justify-content: center;
    align-items: flex-end;
    align-content: flex-end;
    flex-wrap: wrap;
    padding: 6px 4px 10px;
    gap: 3px;
    min-height: calc(var(--card-height) + 14px);
    flex-shrink: 0;
    background: rgba(0,0,0,0.15);
    border-top: 1px solid rgba(255,255,255,0.05);
  }
  .hand-card-wrapper {
    flex-shrink: 0;
    animation: dealIn 0.3s ease both;
  }
  .trump-flash-overlay {
    position: fixed;
    inset: 0;
    display: flex;
    align-items: center;
    justify-content: center;
    z-index: 100;
    pointer-events: none;
    animation: trumpFlash 1.8s ease both;
  }
  .trump-flash-content {
    text-align: center;
    padding: 40px;
    border-radius: var(--radius-lg);
    background: rgba(0,0,0,0.6);
    backdrop-filter: blur(10px);
    border: 2px solid var(--accent-gold);
  }
  .trump-flash-suit { font-size: clamp(4rem, 15vw, 7rem); animation: suitPulse 0.6s ease infinite; }
  .trump-flash-text { font-size: clamp(1.2rem, 4vw, 1.8rem); font-weight: 800; color: var(--accent-gold); margin-top: 10px; }
  .trump-flash-sub { font-size: 0.9rem; opacity: 0.8; margin-top: 6px; }
  .reveal-btn {
    position: absolute;
    bottom: calc(var(--card-height) + 24px);
    left: 50%;
    transform: translateX(-50%);
    padding: 10px 24px;
    background: linear-gradient(135deg, #c41e3a, #8b0000);
    border: none;
    border-radius: var(--radius-lg);
    color: #fff;
    font-weight: 700;
    font-size: 0.95rem;
    cursor: pointer;
    box-shadow: 0 4px 15px rgba(196,30,58,0.4);
    animation: slideUp 0.3s ease;
    z-index: 20;
  }
  .reveal-btn:active { transform: translateX(-50%) scale(0.95); }
  .result-overlay {
    position: fixed;
    inset: 0;
    background: rgba(0,0,0,0.7);
    backdrop-filter: blur(8px);
    display: flex;
    align-items: center;
    justify-content: center;
    z-index: 90;
    animation: fadeIn 0.3s ease;
  }
  .result-card {
    background: rgba(13,92,54,0.95);
    border: 2px solid var(--accent-gold);
    border-radius: var(--radius-lg);
    padding: 32px;
    text-align: center;
    width: min(320px, 85vw);
    animation: cardPopIn 0.5s ease both;
  }
  .result-title { font-size: 1.6rem; font-weight: 800; color: var(--accent-gold); margin-bottom: 16px; }
  .result-scores { display: flex; justify-content: center; gap: 30px; margin: 16px 0; }
  .result-team { text-align: center; }
  .result-team-name { font-size: 0.8rem; text-transform: uppercase; opacity: 0.7; }
  .result-team-score { font-size: 2rem; font-weight: 800; margin-top: 4px; }
  .result-mendi { display: flex; gap: 4px; justify-content: center; margin-top: 8px; flex-wrap: wrap; }
  .result-btn {
    margin-top: 20px;
    padding: 12px 32px;
    background: var(--accent-gold);
    border: none;
    border-radius: var(--radius-lg);
    color: #1a1a1a;
    font-weight: 800;
    font-size: 1rem;
    cursor: pointer;
  }
  .toast-container {
    position: fixed;
    top: 70px;
    left: 50%;
    transform: translateX(-50%);
    z-index: 80;
    display: flex;
    flex-direction: column;
    gap: 8px;
    pointer-events: none;
  }
  .toast {
    background: rgba(0,0,0,0.75);
    backdrop-filter: blur(6px);
    color: #fff;
    padding: 10px 20px;
    border-radius: var(--radius-sm);
    font-size: 0.9rem;
    font-weight: 500;
    border-left: 3px solid var(--accent-gold);
    animation: slideDown 0.3s ease, fadeIn 0.3s ease;
    white-space: nowrap;
  }
  .pause-indicator {
    position: absolute;
    top: 50%; left: 50%;
    transform: translate(-50%, -50%);
    background: rgba(0,0,0,0.5);
    padding: 8px 20px;
    border-radius: 20px;
    font-size: 0.8rem;
    opacity: 0.8;
    z-index: 15;
    pointer-events: none;
  }
  .exit-btn {
    position: absolute;
    top: 8px; left: 8px;
    z-index: 30;
    background: rgba(0,0,0,0.3);
    border: 1px solid rgba(255,255,255,0.1);
    color: #fff;
    width: 32px; height: 32px;
    border-radius: 50%;
    display: flex; align-items: center; justify-content: center;
    cursor: pointer;
    font-size: 1.1rem;
  }
  .dealer-chip {
    position: absolute;
    width: 16px; height: 16px;
    background: var(--accent-gold);
    border-radius: 50%;
    font-size: 0.55rem;
    font-weight: 800;
    color: #1a1a1a;
    display: flex; align-items: center; justify-content: center;
    box-shadow: 0 1px 4px rgba(0,0,0,0.4);
    z-index: 5;
  }
  .trick-counter {
    position: absolute;
    top: 8px; right: 8px;
    background: rgba(0,0,0,0.3);
    padding: 4px 10px;
    border-radius: 10px;
    font-size: 0.75rem;
    font-weight: 600;
    z-index: 10;
  }
  .confirm-overlay {
    position: fixed;
    inset: 0;
    background: rgba(0,0,0,0.6);
    backdrop-filter: blur(4px);
    display: flex;
    align-items: center;
    justify-content: center;
    z-index: 95;
  }
  .confirm-box {
    background: var(--felt-green);
    border: 1px solid rgba(255,255,255,0.15);
    border-radius: var(--radius-lg);
    padding: 24px;
    width: min(300px, 80vw);
    text-align: center;
  }
  .confirm-text { margin-bottom: 20px; font-size: 1rem; }
  .confirm-buttons { display: flex; gap: 10px; }
  .confirm-buttons button { flex: 1; padding: 10px; border-radius: var(--radius-sm); border: none; font-weight: 600; cursor: pointer; }
  .btn-cancel { background: rgba(255,255,255,0.1); color: #fff; }
  .btn-confirm { background: #c41e3a; color: #fff; }
  @media (min-width: 600px) {
    :root { --card-width: 60px; }
    .seat-marker.left { left: 6%; }
    .seat-marker.right { right: 6%; }
  }
  @media (max-height: 600px) {
    .score-cluster { min-height: 48px; padding: 4px 8px; }
    .hand-strip { padding-bottom: 6px; }
  }
</style>
</head>
<body>
<div id="root"></div>
<script type="text/babel">
const { useState, useEffect, useRef, useCallback } = React;

const SUITS = ['♠','♥','♦','♣'];
const SUIT_COLORS = { '♠':'black','♣':'black','♥':'red','♦':'red' };

function Card({ card, faceDown, disabled, onClick, style, className }) {
  if (faceDown || !card) {
    return <div className="card back" style={style} />;
  }
  const color = SUIT_COLORS[card.suit];
  return (
    <div className={`card ${color} ${disabled ? 'disabled' : ''} ${className || ''}`} style={style} onClick={disabled ? undefined : onClick}>
      <span className="card-corner top-left">{card.rank}<br/>{card.suit}</span>
      <span className="card-rank">{card.rank}</span>
      <span className="card-suit">{card.suit}</span>
      <span className="card-corner bottom-right">{card.rank}<br/>{card.suit}</span>
    </div>
  );
}

function TrumpFlash({ suit, onDone }) {
  useEffect(() => { const t = setTimeout(onDone, 1800); return () => clearTimeout(t); }, [onDone]);
  const color = SUIT_COLORS[suit] === 'red' ? '#c41e3a' : '#1a1a1a';
  return (
    <div className="trump-flash-overlay">
      <div className="trump-flash-content">
        <div className="trump-flash-suit" style={{ color }}>{suit}</div>
        <div className="trump-flash-text">TRUMP REVEALED!</div>
        <div className="trump-flash-sub">{suit} is now trump</div>
      </div>
    </div>
  );
}

function ResultOverlay({ result, scores, totalCards, mendi, onRematch, onExit, myTeam }) {
  const myLabel = 'You';
  const oppLabel = 'Opponents';
  const myScore = myTeam === 'A' ? totalCards.A : totalCards.B;
  const oppScore = myTeam === 'A' ? totalCards.B : totalCards.A;
  const myMendi = myTeam === 'A' ? mendi.A : mendi.B;
  const oppMendi = myTeam === 'A' ? mendi.B : mendi.A;
  const title = result === 'draw' ? 'Hand Drawn!' : (result === myTeam ? 'You Win!' : 'Opponents Win!');
  return (
    <div className="result-overlay">
      <div className="result-card">
        <div className="result-title">{title}</div>
        <div className="result-scores">
          <div className="result-team">
            <div className="result-team-name">{myLabel}</div>
            <div className="result-team-score score-you">{myScore}</div>
            <div className="result-mendi">
              {myMendi.map((c,i) => <div key={i} className="mendi-mini" style={{color: SUIT_COLORS[c.suit]==='red'?'#c41e3a':'#1a1a1a'}}>{c.suit}</div>)}
            </div>
          </div>
          <div className="result-team">
            <div className="result-team-name">{oppLabel}</div>
            <div className="result-team-score score-opp">{oppScore}</div>
            <div className="result-mendi">
              {oppMendi.map((c,i) => <div key={i} className="mendi-mini" style={{color: SUIT_COLORS[c.suit]==='red'?'#c41e3a':'#1a1a1a'}}>{c.suit}</div>)}
            </div>
          </div>
        </div>
        <button className="result-btn" onClick={onRematch}>Rematch</button>
        <button className="menu-btn secondary" style={{marginTop:10,width:'100%'}} onClick={onExit}>Exit to Menu</button>
      </div>
    </div>
  );
}

function ToastContainer({ toasts }) {
  return (
    <div className="toast-container">
      {toasts.map(t => <div key={t.id} className="toast">{t.msg}</div>)}
    </div>
  );
}

function ConfirmExit({ onConfirm, onCancel }) {
  return (
    <div className="confirm-overlay">
      <div className="confirm-box">
        <div className="confirm-text">Leave the game?</div>
        <div className="confirm-buttons">
          <button className="btn-cancel" onClick={onCancel}>Stay</button>
          <button className="btn-confirm" onClick={onConfirm}>Leave</button>
        </div>
      </div>
    </div>
  );
}

function MenuView({ onSolo, onHub }) {
  return (
    <div className="view">
      <div className="menu-title">MENDIKOT</div>
      <div className="menu-sub">The Classic Indian Card Game</div>
      <button className="menu-btn primary" onClick={onSolo}>Solo vs Bots</button>
      <button className="menu-btn secondary" onClick={onHub}>Play with Friends</button>
    </div>
  );
}

function HubView({ playerName, onBack, onCreate, onJoin, errorMsg }) {
  const [name, setName] = useState(playerName);
  const [code, setCode] = useState('');
  const [team, setTeam] = useState('A');
  const [mode, setMode] = useState('create');
  return (
    <div className="view">
      <div className="form-card">
        <div className="form-title">Play with Friends</div>
        <div style={{display:'flex',gap:8,marginBottom:16}}>
          <button className="menu-btn secondary" style={{flex:1,margin:0,fontSize:'0.9rem',opacity:mode==='create'?1:0.5}} onClick={()=>setMode('create')}>Create</button>
          <button className="menu-btn secondary" style={{flex:1,margin:0,fontSize:'0.9rem',opacity:mode==='join'?1:0.5}} onClick={()=>setMode('join')}>Join</button>
        </div>
        <div className="input-group">
          <label>Your Name</label>
          <input value={name} onChange={e => setName(e.target.value)} placeholder="Enter name" maxLength={12} />
        </div>
        {mode === 'join' && (
          <div className="input-group">
            <label>Room Code</label>
            <input value={code} onChange={e => setCode(e.target.value.toUpperCase())} placeholder="ABCD" maxLength={4} />
          </div>
        )}
        <label style={{fontSize:'0.85rem',color:'rgba(255,255,255,0.7)',marginBottom:'8px',display:'block'}}>Choose Team</label>
        <div className="team-select">
          <div className={`team-option team-a ${team==='A'?'active':''}`} onClick={() => setTeam('A')}>Team A</div>
          <div className={`team-option team-b ${team==='B'?'active':''}`} onClick={() => setTeam('B')}>Team B</div>
        </div>
        {errorMsg && <div style={{color:'#ff8a8a',fontSize:'0.85rem',marginBottom:10,textAlign:'center'}}>{errorMsg}</div>}
        <div className="form-actions">
          <button className="btn-back" onClick={onBack}>Back</button>
          <button className="btn-submit" onClick={() => {
            if(!name.trim()) return;
            if(mode==='create') onCreate(name.trim(), team);
            else if(code.trim().length===4) onJoin(name.trim(), code.trim(), team);
          }}>{mode==='create'?'Create Room':'Join Room'}</button>
        </div>
      </div>
    </div>
  );
}

function LobbyView({ roomCode, seat, players, onStart, onLeave, isHost, isFull }) {
  return (
    <div className="view">
      <div className="form-title">Lobby</div>
      <div className="room-code">{roomCode}</div>
      <div style={{textAlign:'center',opacity:0.6,fontSize:'0.85rem',marginBottom:10}}>Share this code with friends</div>
      <div className="seats-grid">
        {players.map((p,i) => (
          <div key={i} className={`seat ${p?'filled':''}`}>
            <div className="seat-name">{p ? p.name : 'Open'}</div>
            <div className="seat-team">Team {p ? p.team : (i%2===0?'A':'B')}</div>
            {p && <div className={`seat-status ${i===0?'status-host':'status-waiting'}`}>{i===0?'Host':'Waiting'}</div>}
          </div>
        ))}
      </div>
      {isHost ? (
        <button className="start-btn" disabled={!isFull} onClick={onStart}>Start Game</button>
      ) : (
        <div style={{opacity:0.6,fontSize:'0.9rem'}}>Waiting for host to start...</div>
      )}
      <button className="menu-btn secondary" style={{marginTop:16}} onClick={onLeave}>Leave Room</button>
    </div>
  );
}

function GameView({ gameState, trick, seat, onPlayCard, onRevealTrump, onRematch, onExit, showTrumpFlash, flashSuit, onTrumpDone, paused, handComplete, result, toasts, confirmExit, onConfirmExit, onCancelExit, myTeam }) {
  const myHand = gameState?.your_hand || [];
  const allPlayers = gameState?.players || [];
  const seatPositions = ['bottom','left','top','right'];
  const flyDirs = [
    {x: '0px', y: '80px', r: '0deg'},      // bottom (me)
    {x: '-80px', y: '0px', r: '-10deg'},   // left
    {x: '0px', y: '-80px', r: '0deg'},     // top
    {x: '80px', y: '0px', r: '10deg'},     // right
  ];

  const ledSuit = trick.length > 0 ? trick[0].card.suit : null;
  const hasLedSuit = ledSuit ? myHand.some(c => c.suit === ledSuit) : true;
  const isMyTurn = gameState?.turn === seat && !paused && !handComplete;
  const mustReveal = isMyTurn && gameState?.phase === 'phase1' && !gameState?.trump_suit
    && trick.length > 0 && !hasLedSuit;

  // Score labels based on my team
  const myScoreLabel = 'You';
  const oppScoreLabel = 'Opponents';
  const myScore = myTeam === 'A' ? (gameState?.total_cards?.A || 0) : (gameState?.total_cards?.B || 0);
  const oppScore = myTeam === 'A' ? (gameState?.total_cards?.B || 0) : (gameState?.total_cards?.A || 0);
  const myMendi = myTeam === 'A' ? (gameState?.mendi?.A || []) : (gameState?.mendi?.B || []);
  const oppMendi = myTeam === 'A' ? (gameState?.mendi?.B || []) : (gameState?.mendi?.A || []);

  return (
    <div className="game-view">
      <button className="exit-btn" onClick={onConfirmExit}>×</button>
      <div className="trick-counter">Trick {Math.min(gameState?.trick_number || 1, 13)} / 13</div>

      <div className="score-cluster">
        <div className="score-side">
          <span className="score-label">{myScoreLabel}</span>
          <span className="score-number score-you">{myScore}</span>
          <div className="mendi-strip">
            {myMendi.map((c,i) => (
              <div key={i} className="mendi-mini" style={{color: SUIT_COLORS[c.suit]==='red'?'#c41e3a':'#1a1a1a'}}>{c.suit}</div>
            ))}
          </div>
        </div>
        <div className="trump-slot">
          {gameState?.trump_suit ? (
            <div className="trump-icon" style={{color: SUIT_COLORS[gameState.trump_suit]==='red'?'#c41e3a':'#fff'}}>{gameState.trump_suit}</div>
          ) : (
            <div className="trump-icon unknown">?</div>
          )}
        </div>
        <div className="score-side">
          <span className="score-label">{oppScoreLabel}</span>
          <span className="score-number score-opp">{oppScore}</span>
          <div className="mendi-strip">
            {oppMendi.map((c,i) => (
              <div key={i} className="mendi-mini" style={{color: SUIT_COLORS[c.suit]==='red'?'#c41e3a':'#1a1a1a'}}>{c.suit}</div>
            ))}
          </div>
        </div>
      </div>

      <div className="table-felt">
        <div className="felt-ellipse" />
        {[2,1,3,0].map(s => {
          const pos = seatPositions[s];
          const isActive = gameState?.turn === s && !paused && !handComplete;
          const isDealer = gameState?.dealer === s;
          const pl = allPlayers[s];
          const handSize = pl?.hand_size ?? (s === seat ? myHand.length : 0);
          const isBotTurn = isActive && s !== seat && pl?.is_bot;
          return (
            <div key={s} className={`seat-marker ${pos} ${isActive ? 'active' : ''}`}>
              <div style={{position:'relative'}}>
                <div className="seat-avatar">{s === seat ? '👤' : '🤖'}</div>
                {handSize > 0 && <div className="hand-count">{handSize}</div>}
                {isDealer && <div className="dealer-chip" style={{top:-4,right:-4}}>D</div>}
              </div>
              <div className="seat-name-tag" style={{color: pl?.team==='A'?'#6bb5ff':'#ff8a8a'}}>
                {pl ? pl.name : 'Open'}
              </div>
              {isBotTurn && (
                <div className="thinking-dots">
                  <span></span><span></span><span></span>
                </div>
              )}
              {s !== seat && pl?.is_bot && !isBotTurn && <div className="bot-badge">BOT</div>}
            </div>
          );
        })}

        <div className="trick-center">
          {trick.map((t, i) => {
            const pos = (t.seat + 4 - seat) % 4;
            const dir = flyDirs[pos];
            const isNew = i === trick.length - 1;
            return (
              <div 
                key={`${t.card.id}-${i}`} 
                className={`trick-card-wrapper pos-${pos} ${isNew ? 'animating' : ''}`}
                style={isNew ? {
                  '--fly-x': dir.x,
                  '--fly-y': dir.y,
                  '--fly-r': dir.r,
                  animationDelay: '0.1s'
                } : {}}
              >
                <Card card={t.card} />
                {t.is_reveal && <div style={{position:'absolute',top:-20,left:'50%',transform:'translateX(-50%)',background:'var(--accent-gold)',color:'#1a1a1a',padding:'2px 8px',borderRadius:'10px',fontSize:'0.65rem',fontWeight:'800',whiteSpace:'nowrap'}}>TRUMP!</div>}
              </div>
            );
          })}
        </div>

        {paused && <div className="pause-indicator">Collecting trick...</div>}
      </div>

      {mustReveal && (
        <button className="reveal-btn" onClick={onRevealTrump}>
          Reveal Trump
        </button>
      )}

      <div className="hand-strip">
        {myHand.map((card) => (
          <div key={card.id} className="hand-card-wrapper">
            <Card
              card={card}
              disabled={!isMyTurn}
              onClick={() => onPlayCard(card.id)}
            />
          </div>
        ))}
      </div>

      {showTrumpFlash && <TrumpFlash suit={flashSuit} onDone={onTrumpDone} />}
      {handComplete && (
        <ResultOverlay
          result={result}
          scores={gameState?.scores || {A:0,B:0}}
          totalCards={gameState?.total_cards || {A:0,B:0}}
          mendi={gameState?.mendi || {A:[],B:[]}}
          onRematch={onRematch}
          onExit={onExit}
          myTeam={myTeam}
        />
      )}
      {confirmExit && <ConfirmExit onConfirm={onExit} onCancel={onCancelExit} />}
      <ToastContainer toasts={toasts} />
    </div>
  );
}

function App() {
  const [view, setView] = useState('menu');
  const [playerName, setPlayerName] = useState(localStorage.getItem('mendikot_name') || '');
  const [roomCode, setRoomCode] = useState('');
  const [seat, setSeat] = useState(null);
  const [myTeam, setMyTeam] = useState('A');
  const [players, setPlayers] = useState([null,null,null,null]);
  const [gameState, setGameState] = useState(null);
  const [trick, setTrick] = useState([]);
  const [showTrumpFlash, setShowTrumpFlash] = useState(false);
  const [flashSuit, setFlashSuit] = useState(null);
  const [toasts, setToasts] = useState([]);
  const [confirmExit, setConfirmExit] = useState(false);
  const [paused, setPaused] = useState(false);
  const [handComplete, setHandComplete] = useState(false);
  const [result, setResult] = useState(null);
  const [errorMsg, setErrorMsg] = useState('');
  const wsRef = useRef(null);
  const handlerRef = useRef(null);

  const addToast = useCallback((msg) => {
    const id = Date.now() + Math.random();
    setToasts(prev => [...prev, {id, msg}]);
    setTimeout(() => setToasts(prev => prev.filter(t => t.id !== id)), 2500);
  }, []);

  const handleMessage = useCallback((msg) => {
    const type = msg.type;
    if (type === 'room_created') {
      setRoomCode(msg.room_code);
      setSeat(msg.seat);
      setMyTeam(msg.players[msg.seat]?.team || 'A');
      setPlayers(msg.players);
      setView(msg.solo ? 'game' : 'lobby');
      if (msg.solo && msg.state) {
        setGameState(msg.state);
        setTrick(msg.state.trick || []);
        setPaused(msg.state.paused);
        setHandComplete(msg.state.hand_complete);
        setResult(msg.state.result);
      }
    } else if (type === 'room_joined') {
      setRoomCode(msg.room_code);
      setSeat(msg.seat);
      setMyTeam(msg.players[msg.seat]?.team || 'A');
      setPlayers(msg.players);
      setView('lobby');
    } else if (type === 'player_joined' || type === 'player_left') {
      setPlayers(msg.players);
    } else if (type === 'game_started') {
      setView('game');
      setGameState(msg.state);
      setTrick(msg.state.trick || []);
      setPaused(msg.state.paused);
      setHandComplete(msg.state.hand_complete);
      setResult(msg.state.result);
    } else if (type === 'card_played') {
      setTrick(prev => [...prev, {seat: msg.seat, card: msg.card, is_reveal: msg.is_reveal}]);
    } else if (type === 'trump_revealed') {
      setFlashSuit(msg.suit);
      setShowTrumpFlash(true);
      setGameState(prev => prev ? {...prev, trump_suit: msg.suit, trump_revealed: true} : prev);
    } else if (type === 'trick_won') {
      setPaused(true);
      setTrick(msg.trick.map(t => ({seat: t.seat, card: t.card, is_reveal: false})));
      setGameState(prev => prev ? {...prev, mendi: msg.mendi, scores: msg.scores, total_cards: msg.total_cards} : prev);
    } else if (type === 'turn_change') {
      if (msg.state) {
        setGameState(msg.state);
        setTrick(msg.state.trick || []);
        setPaused(msg.state.paused);
        setHandComplete(msg.state.hand_complete);
        setResult(msg.state.result);
      } else {
        setGameState(prev => prev ? {...prev, turn: msg.turn} : prev);
      }
    } else if (type === 'boot_dealt') {
      if (msg.state) {
        setGameState(msg.state);
        setTrick(msg.state.trick || []);
      }
      addToast('Boot dealt! +8 cards each');
    } else if (type === 'hand_complete') {
      setHandComplete(true);
      setResult(msg.result);
      setGameState(prev => prev ? {...prev, mendi: msg.mendi, scores: msg.scores, total_cards: msg.total_cards, hand_complete: true, result: msg.result} : prev);
    } else if (type === 'room_cancelled') {
      addToast(msg.reason || 'Room cancelled');
      setView('menu');
      setRoomCode('');
      setGameState(null);
    } else if (type === 'error') {
      setErrorMsg(msg.message);
      setTimeout(() => setErrorMsg(''), 3000);
    }
  }, [addToast]);

  useEffect(() => {
    handlerRef.current = handleMessage;
  }, [handleMessage]);

  const connect = useCallback(() => {
    const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const socket = new WebSocket(`${protocol}//${window.location.host}/ws`);
    wsRef.current = socket;
    socket.onopen = () => {};
    socket.onmessage = (ev) => {
      if (handlerRef.current) {
        handlerRef.current(JSON.parse(ev.data));
      }
    };
    socket.onclose = () => {};
    socket.onerror = () => {};
  }, []);

  const send = useCallback((msg) => {
    if (wsRef.current && wsRef.current.readyState === 1) {
      wsRef.current.send(JSON.stringify(msg));
    }
  }, []);

  useEffect(() => {
    connect();
    return () => {
      if (wsRef.current) wsRef.current.close();
    };
  }, [connect]);

  useEffect(() => {
    const interval = setInterval(() => {
      send({type: 'ping'});
    }, 30000);
    return () => clearInterval(interval);
  }, [send]);

  // Solo: auto-start with default name and team
  const startSolo = () => {
    const name = 'You';
    const team = 'A';
    localStorage.setItem('mendikot_name', name);
    send({type: 'create_room', name, team, solo: true});
  };

  const createRoom = (name, team) => {
    localStorage.setItem('mendikot_name', name);
    send({type: 'create_room', name, team, solo: false});
  };

  const joinRoom = (name, code, team) => {
    localStorage.setItem('mendikot_name', name);
    send({type: 'join_room', name, room_code: code, team});
  };

  const startGame = () => {
    send({type: 'start_game'});
  };

  const playCard = (cardId) => {
    send({type: 'play_card', card_id: cardId});
  };

  const revealTrump = () => {
    send({type: 'reveal_trump'});
  };

  const rematch = () => {
    send({type: 'rematch'});
    setHandComplete(false);
    setResult(null);
  };

  const exitGame = () => {
    if (wsRef.current) wsRef.current.close();
    setView('menu');
    setRoomCode('');
    setGameState(null);
    setTrick([]);
    setPaused(false);
    setHandComplete(false);
    setResult(null);
    setConfirmExit(false);
    setTimeout(() => connect(), 300);
  };

  if (view === 'menu') {
    return (
      <div className="app">
        <MenuView onSolo={startSolo} onHub={() => setView('hub')} />
      </div>
    );
  }

  if (view === 'hub') {
    return (
      <div className="app">
        <HubView playerName={playerName} onBack={() => setView('menu')} onCreate={createRoom} onJoin={joinRoom} errorMsg={errorMsg} />
      </div>
    );
  }

  if (view === 'lobby') {
    return (
      <div className="app">
        <LobbyView roomCode={roomCode} seat={seat} players={players} onStart={startGame} onLeave={exitGame} isHost={seat === 0} isFull={players.every(p => p !== null)} />
      </div>
    );
  }

  if (view === 'game') {
    return (
      <div className="app">
        <GameView
          gameState={gameState}
          trick={trick}
          seat={seat}
          myTeam={myTeam}
          onPlayCard={playCard}
          onRevealTrump={revealTrump}
          onRematch={rematch}
          onExit={exitGame}
          showTrumpFlash={showTrumpFlash}
          flashSuit={flashSuit}
          onTrumpDone={() => setShowTrumpFlash(false)}
          paused={paused}
          handComplete={handComplete}
          result={result}
          toasts={toasts}
          confirmExit={confirmExit}
          onConfirmExit={() => setConfirmExit(true)}
          onCancelExit={() => setConfirmExit(false)}
        />
      </div>
    );
  }

  return (
    <div className="app">
      <div className="view">
        <div className="menu-sub">Connecting...</div>
      </div>
    </div>
  );
}

const root = ReactDOM.createRoot(document.getElementById('root'));
root.render(<App />);
</script>
</body>
</html>"""

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=int(os.environ.get("PORT", "8000")))
