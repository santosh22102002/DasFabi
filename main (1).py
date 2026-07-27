#!/usr/bin/env python3
"""
Mendikot - Single-file web game
Backend: FastAPI + WebSocket
Frontend: React 18 (CDN) + Babel Standalone
Run: python main.py
"""

import asyncio
import json
import random
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
import uvicorn

SUITS = ["spades", "hearts", "diamonds", "clubs"]
SUIT_SYMBOLS = {"spades": "\u2660", "hearts": "\u2665", "diamonds": "\u2666", "clubs": "\u2663"}
RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"]
RANK_VALUE = {r: i + 2 for i, r in enumerate(RANKS)}
SUIT_COLOR = {"spades": "black", "clubs": "black", "hearts": "red", "diamonds": "red"}
TEAM_A_SEATS = {0, 2}
TEAM_B_SEATS = {1, 3}
BOT_NAMES = ["Raju", "Vijay", "Amit"]
ROOM_TTL = 600
BOT_DELAY_MIN = 0.8
BOT_DELAY_MAX = 1.6
TRICK_PAUSE = 2.5

@dataclass
class Card:
    suit: str
    rank: str
    @property
    def value(self): return RANK_VALUE[self.rank]
    @property
    def id(self): return f"{self.rank}_{self.suit}"
    def to_dict(self): return {"suit": self.suit, "rank": self.rank, "value": self.value, "id": self.id, "symbol": SUIT_SYMBOLS[self.suit]}

@dataclass
class Player:
    seat: int
    name: str
    team: str
    is_bot: bool = False
    hand: List[Card] = field(default_factory=list)
    void_exempt: bool = False
    ws: Optional[WebSocket] = None
    disconnected: bool = False

@dataclass
class TrickEntry:
    seat: int
    card: Card
    is_reveal: bool = False
    def to_dict(self): return {"seat": self.seat, "card": self.card.to_dict(), "is_reveal": self.is_reveal}

@dataclass
class MendikotGame:
    players: List[Player]
    boot: List[Card] = field(default_factory=list)
    dealer: int = 0
    leader: int = 1
    turn: int = 1
    trick: List[TrickEntry] = field(default_factory=list)
    trump_suit: Optional[str] = None
    trump_revealed: bool = False
    phase: str = "phase1"
    trick_number: int = 1
    mendi: Dict[str, List[Card]] = field(default_factory=lambda: {"A": [], "B": []})
    paused: bool = False
    trick_winner: Optional[int] = None
    hand_complete: bool = False
    result: Optional[str] = None
    solo: bool = False
    room_id: str = ""

    def to_state(self, for_seat=0):
        return {
            "dealer": self.dealer, "leader": self.leader, "turn": self.turn,
            "trick": [t.to_dict() for t in self.trick],
            "trump_suit": self.trump_suit, "trump_revealed": self.trump_revealed,
            "phase": self.phase, "trick_number": self.trick_number,
            "mendi": {k: [c.to_dict() for c in v] for k, v in self.mendi.items()},
            "scores": {"A": len(self.mendi["A"]), "B": len(self.mendi["B"])},
            "paused": self.paused, "trick_winner": self.trick_winner,
            "hand_complete": self.hand_complete, "result": self.result,
            "players": [
                {"seat": p.seat, "name": p.name, "team": p.team, "is_bot": p.is_bot,
                 "disconnected": p.disconnected, "hand_count": len(p.hand),
                 "hand": [c.to_dict() for c in p.hand] if p.seat == for_seat else None}
                for p in self.players
            ],
        }

def create_deck():
    return [Card(s, r) for s in SUITS for r in RANKS]

def shuffle_deck(deck):
    d = deck[:]
    random.shuffle(d)
    return d

def get_team(seat): return "A" if seat in TEAM_A_SEATS else "B"
def is_mendi(card): return card.rank == "10"

def deal_new_hand(solo, room_id, prev_dealer=3):
    deck = shuffle_deck(create_deck())
    dealer = (prev_dealer + 1) % 4
    players = [Player(seat=i, name="", team=get_team(i), is_bot=True) for i in range(4)]
    for i in range(4):
        players[i].hand = sorted(deck[i*5:(i+1)*5], key=lambda c: (SUITS.index(c.suit), c.value))
    boot = deck[20:]
    leader = (dealer + 1) % 4
    return MendikotGame(players=players, boot=boot, dealer=dealer, leader=leader, turn=leader, solo=solo, room_id=room_id)

def get_legal_cards(game, seat):
    p = game.players[seat]
    if game.trick:
        led = game.trick[0].card.suit
        has_led = any(c.suit == led for c in p.hand)
        if has_led:
            return [c.suit == led for c in p.hand]
    return [True] * len(p.hand)

def must_reveal_trump(game, seat):
    if game.trump_suit or game.phase != "phase1" or not game.trick:
        return False
    p = game.players[seat]
    led = game.trick[0].card.suit
    return not any(c.suit == led for c in p.hand)

def resolve_trick(game):
    led = game.trick[0].card.suit
    winner_idx = 0
    best_val = -1
    for i, entry in enumerate(game.trick):
        c = entry.card
        is_trump = game.trump_suit and c.suit == game.trump_suit
        eff = c.value
        if is_trump: eff += 100
        elif c.suit != led: eff = -1
        if eff > best_val:
            best_val = eff
            winner_idx = i
    winner_seat = game.trick[winner_idx].seat
    team = get_team(winner_seat)
    for entry in game.trick:
        if is_mendi(entry.card):
            game.mendi[team].append(entry.card)
    game.trick_winner = winner_seat
    return winner_seat

def deal_boot(game):
    for i in range(4):
        new_cards = game.boot[:8]
        game.boot = game.boot[8:]
        game.players[i].hand.extend(new_cards)
        game.players[i].hand.sort(key=lambda c: (SUITS.index(c.suit), c.value))
    game.phase = "phase2"

def bot_choose_card(game, seat):
    p = game.players[seat]
    legal = get_legal_cards(game, seat)
    opts = [c for c, ok in zip(p.hand, legal) if ok]
    if not opts: return None
    return min(opts, key=lambda c: c.value)

def bot_reveal_card(game, seat):
    return min(game.players[seat].hand, key=lambda c: c.value)

class Room:
    def __init__(self, room_id, host_ws, host_name, host_team):
        self.room_id = room_id
        self.host_id = id(host_ws)
        self.created_at = time.time()
        self.game_started = False
        self.game = None
        self.players = {}
        self.seats = [None, None, None, None]
        host = Player(seat=0, name=host_name, team=host_team, is_bot=False, ws=host_ws)
        self.players[id(host_ws)] = host
        self.seats[0] = id(host_ws)

    def is_full(self): return all(s is not None for s in self.seats)

    def add_player(self, ws, name, team):
        preferred = [i for i in range(4) if self.seats[i] is None and get_team(i) == team]
        if not preferred:
            preferred = [i for i in range(4) if self.seats[i] is None]
        if not preferred: return None
        seat = preferred[0]
        p = Player(seat=seat, name=name, team=get_team(seat), is_bot=False, ws=ws)
        self.players[id(ws)] = p
        self.seats[seat] = id(ws)
        return seat

    def remove_player(self, ws_id):
        if ws_id not in self.players: return
        p = self.players[ws_id]
        if p.seat is not None and self.seats[p.seat] == ws_id:
            self.seats[p.seat] = None
        del self.players[ws_id]

    def to_lobby_state(self):
        return {
            "room_id": self.room_id,
            "seats": [
                {"filled": s is not None,
                 "name": self.players[s].name if s and s in self.players else None,
                 "team": get_team(i), "is_host": s == self.host_id if s else False}
                for i, s in enumerate(self.seats)
            ],
            "game_started": self.game_started,
        }

    def fill_bots(self):
        for i in range(4):
            if self.seats[i] is None:
                bot = Player(seat=i, name=BOT_NAMES[i-1] if i > 0 else "Bot", team=get_team(i), is_bot=True)
                self.players[f"bot_{i}"] = bot
                self.seats[i] = f"bot_{i}"

    def start_game(self):
        self.fill_bots()
        self.game = deal_new_hand(solo=False, room_id=self.room_id)
        for ws_id, p in self.players.items():
            self.game.players[p.seat].name = p.name
            self.game.players[p.seat].is_bot = p.is_bot
            if not p.is_bot:
                self.game.players[p.seat].ws = p.ws
        self.game_started = True

class RoomManager:
    def __init__(self):
        self.rooms = {}
        self.ws_to_room = {}

    def create_room(self, host_ws, host_name, host_team):
        code = "".join(random.choices("ABCDEFGHJKLMNPQRSTUVWXYZ23456789", k=6))
        while code in self.rooms:
            code = "".join(random.choices("ABCDEFGHJKLMNPQRSTUVWXYZ23456789", k=6))
        room = Room(code, host_ws, host_name, host_team)
        self.rooms[code] = room
        self.ws_to_room[id(host_ws)] = code
        return code

    def get_room(self, code): return self.rooms.get(code.upper())

    def join_room(self, code, ws, name, team):
        room = self.get_room(code)
        if not room or room.game_started: return None
        seat = room.add_player(ws, name, team)
        if seat is None: return None
        self.ws_to_room[id(ws)] = code.upper()
        return room

    def disconnect(self, ws_id):
        code = self.ws_to_room.pop(ws_id, None)
        if not code: return
        room = self.rooms.get(code)
        if not room: return
        is_host = ws_id == room.host_id
        in_game = room.game_started
        room.remove_player(ws_id)
        if is_host or in_game:
            self._cancel_room(room, "Host left" if is_host else "Player left during game")
        elif not room.players:
            del self.rooms[code]
        else:
            asyncio.create_task(self._broadcast_lobby(room))

    async def _broadcast_lobby(self, room):
        msg = json.dumps({"type": "lobby_update", "data": room.to_lobby_state()})
        for p in room.players.values():
            if p.ws and not p.is_bot:
                try: await p.ws.send_text(msg)
                except: pass

    def _cancel_room(self, room, reason):
        msg = json.dumps({"type": "room_cancelled", "reason": reason})
        for p in room.players.values():
            if p.ws and not p.is_bot:
                try: asyncio.create_task(p.ws.send_text(msg))
                except: pass
        if room.room_id in self.rooms: del self.rooms[room.room_id]

    async def broadcast_game_state(self, room):
        if not room.game: return
        for p in room.players.values():
            if p.ws and not p.is_bot:
                try:
                    state = room.game.to_state(for_seat=p.seat)
                    await p.ws.send_text(json.dumps({"type": "game_state", "data": state}))
                except: pass

    async def send_to(self, ws, msg_type, data):
        try: await ws.send_text(json.dumps({"type": msg_type, "data": data}))
        except: pass

manager = RoomManager()

async def bot_loop(room):
    while room.game_started and room.game and not room.game.hand_complete:
        await asyncio.sleep(0.2)
        if not room.game or room.game.paused or room.game.hand_complete: continue
        turn = room.game.turn
        p = room.game.players[turn]
        if not p.is_bot: continue
        await asyncio.sleep(random.uniform(BOT_DELAY_MIN, BOT_DELAY_MAX))
        if not room.game or room.game.paused or room.game.hand_complete or room.game.turn != turn: continue
        g = room.game
        if must_reveal_trump(g, turn): card = bot_reveal_card(g, turn)
        else: card = bot_choose_card(g, turn)
        if card: await handle_play_card(room, turn, card.id)

async def handle_play_card(room, seat, card_id):
    g = room.game
    if not g or g.paused or g.hand_complete or g.turn != seat: return
    p = g.players[seat]
    card = next((c for c in p.hand if c.id == card_id), None)
    if not card: return
    legal = get_legal_cards(g, seat)
    idx = next((i for i, c in enumerate(p.hand) if c.id == card_id), -1)
    if idx == -1 or not legal[idx]: return

    is_reveal = must_reveal_trump(g, seat)
    p.hand.pop(idx)

    if is_reveal:
        g.trump_suit = card.suit
        g.trump_revealed = True
        for i in range(4):
            if i != seat:
                other = g.players[i]
                led = g.trick[0].card.suit
                if not any(c.suit == led for c in other.hand):
                    other.void_exempt = True
        for pl in room.players.values():
            if pl.ws and not pl.is_bot:
                await manager.send_to(pl.ws, "trump_revealed", {"seat": seat, "suit": card.suit, "card": card.to_dict()})

    g.trick.append(TrickEntry(seat=seat, card=card, is_reveal=is_reveal))
    g.turn = (seat + 1) % 4
    await manager.broadcast_game_state(room)

    if len(g.trick) == 4:
        g.paused = True
        winner = resolve_trick(g)
        g.leader = winner
        await manager.broadcast_game_state(room)
        await asyncio.sleep(TRICK_PAUSE)
        if not room.game: return
        g.trick = []
        g.turn = g.leader
        g.trick_winner = None
        g.paused = False
        for pl in g.players: pl.void_exempt = False
        g.trick_number += 1
        if g.phase == "phase1":
            if g.trump_revealed or g.trick_number > 5: deal_boot(g)
        if g.trick_number > 13:
            g.hand_complete = True
            ma, mb = len(g.mendi["A"]), len(g.mendi["B"])
            g.result = "A" if ma > mb else "B" if mb > ma else "draw"
        await manager.broadcast_game_state(room)

async def handle_rematch(room):
    if not room.game: return
    prev_dealer = room.game.dealer
    room.game = deal_new_hand(solo=room.game.solo, room_id=room.room_id, prev_dealer=prev_dealer)
    for ws_id, p in room.players.items():
        room.game.players[p.seat].name = p.name
        room.game.players[p.seat].is_bot = p.is_bot
        if not p.is_bot: room.game.players[p.seat].ws = p.ws
    await manager.broadcast_game_state(room)
    if not room.game.solo: asyncio.create_task(bot_loop(room))

solo_games = {}

async def start_solo(ws, name, team):
    g = deal_new_hand(solo=True, room_id="solo")
    g.players[0].name = name
    g.players[0].team = team
    g.players[0].ws = ws
    g.players[0].is_bot = False
    for i in range(1, 4): g.players[i].name = BOT_NAMES[i-1]
    solo_games[id(ws)] = g
    await manager.send_to(ws, "game_state", g.to_state(for_seat=0))
    asyncio.create_task(solo_bot_loop(ws, g))

async def solo_bot_loop(ws, g):
    while not g.hand_complete:
        await asyncio.sleep(0.2)
        if g.paused or g.hand_complete: continue
        turn = g.turn
        p = g.players[turn]
        if not p.is_bot: continue
        await asyncio.sleep(random.uniform(BOT_DELAY_MIN, BOT_DELAY_MAX))
        if g.paused or g.hand_complete or g.turn != turn: continue
        if must_reveal_trump(g, turn): card = bot_reveal_card(g, turn)
        else: card = bot_choose_card(g, turn)
        if card: await handle_solo_play(ws, g, turn, card.id)

async def handle_solo_play(ws, g, seat, card_id):
    if g.paused or g.hand_complete or g.turn != seat: return
    p = g.players[seat]
    card = next((c for c in p.hand if c.id == card_id), None)
    if not card: return
    legal = get_legal_cards(g, seat)
    idx = next((i for i, c in enumerate(p.hand) if c.id == card_id), -1)
    if idx == -1 or not legal[idx]: return

    is_reveal = must_reveal_trump(g, seat)
    p.hand.pop(idx)

    if is_reveal:
        g.trump_suit = card.suit
        g.trump_revealed = True
        for i in range(4):
            if i != seat:
                other = g.players[i]
                led = g.trick[0].card.suit
                if not any(c.suit == led for c in other.hand): other.void_exempt = True
        await manager.send_to(ws, "trump_revealed", {"seat": seat, "suit": card.suit, "card": card.to_dict()})

    g.trick.append(TrickEntry(seat=seat, card=card, is_reveal=is_reveal))
    g.turn = (seat + 1) % 4
    await manager.send_to(ws, "game_state", g.to_state(for_seat=0))

    if len(g.trick) == 4:
        g.paused = True
        winner = resolve_trick(g)
        g.leader = winner
        await manager.send_to(ws, "game_state", g.to_state(for_seat=0))
        await asyncio.sleep(TRICK_PAUSE)
        if g.hand_complete: return
        g.trick = []
        g.turn = g.leader
        g.trick_winner = None
        g.paused = False
        for pl in g.players: pl.void_exempt = False
        g.trick_number += 1
        if g.phase == "phase1":
            if g.trump_revealed or g.trick_number > 5: deal_boot(g)
        if g.trick_number > 13:
            g.hand_complete = True
            ma, mb = len(g.mendi["A"]), len(g.mendi["B"])
            g.result = "A" if ma > mb else "B" if mb > ma else "draw"
        await manager.send_to(ws, "game_state", g.to_state(for_seat=0))

async def gc_loop():
    while True:
        await asyncio.sleep(60)
        now = time.time()
        to_remove = [code for code, room in manager.rooms.items() if now - room.created_at > ROOM_TTL and not room.game_started]
        for code in to_remove: manager._cancel_room(manager.rooms[code], "Room expired")

app = FastAPI()

@app.on_event("startup")
async def startup(): asyncio.create_task(gc_loop())

@app.get("/")
async def root(): return HTMLResponse(content=HTML_PAGE)

@app.websocket("/ws")
async def websocket_endpoint(ws: WebSocket):
    await ws.accept()
    try:
        while True:
            raw = await ws.receive_text()
            msg = json.loads(raw)
            action = msg.get("type")

            if action == "start_solo":
                await start_solo(ws, msg.get("name", "Player"), msg.get("team", "A"))
            elif action == "create_room":
                code = manager.create_room(ws, msg.get("name", "Host"), msg.get("team", "A"))
                room = manager.get_room(code)
                await manager.send_to(ws, "room_created", room.to_lobby_state())
            elif action == "join_room":
                room = manager.join_room(msg.get("room_id", ""), ws, msg.get("name", "Player"), msg.get("team", "A"))
                if room:
                    await manager.send_to(ws, "lobby_update", room.to_lobby_state())
                    await manager._broadcast_lobby(room)
                else:
                    await manager.send_to(ws, "error", {"message": "Room full or not found"})
            elif action == "start_game":
                code = manager.ws_to_room.get(id(ws))
                room = manager.get_room(code) if code else None
                if room and id(ws) == room.host_id and room.is_full():
                    room.start_game()
                    await manager.broadcast_game_state(room)
                    asyncio.create_task(bot_loop(room))
            elif action == "play_card":
                code = manager.ws_to_room.get(id(ws))
                if code and code != "solo":
                    room = manager.get_room(code)
                    if room and room.game:
                        p = room.players.get(id(ws))
                        if p: await handle_play_card(room, p.seat, msg.get("card_id", ""))
                elif id(ws) in solo_games:
                    g = solo_games[id(ws)]
                    await handle_solo_play(ws, g, 0, msg.get("card_id", ""))
            elif action == "rematch":
                code = manager.ws_to_room.get(id(ws))
                if code and code != "solo":
                    room = manager.get_room(code)
                    if room and id(ws) == room.host_id: await handle_rematch(room)
                elif id(ws) in solo_games:
                    g = solo_games[id(ws)]
                    g2 = deal_new_hand(solo=True, room_id="solo", prev_dealer=g.dealer)
                    g2.players[0].name = g.players[0].name
                    g2.players[0].team = g.players[0].team
                    g2.players[0].ws = ws
                    g2.players[0].is_bot = False
                    for i in range(1, 4): g2.players[i].name = BOT_NAMES[i-1]
                    solo_games[id(ws)] = g2
                    await manager.send_to(ws, "game_state", g2.to_state(for_seat=0))
                    asyncio.create_task(solo_bot_loop(ws, g2))
            elif action == "exit":
                code = manager.ws_to_room.get(id(ws))
                if code: manager.disconnect(id(ws))
                if id(ws) in solo_games: del solo_games[id(ws)]
            elif action == "reconnect":
                await manager.send_to(ws, "error", {"message": "Reconnect not implemented"})
    except WebSocketDisconnect:
        manager.disconnect(id(ws))
        if id(ws) in solo_games: del solo_games[id(ws)]
    except Exception:
        manager.disconnect(id(ws))
        if id(ws) in solo_games: del solo_games[id(ws)]

# ============================================================
# FRONTEND HTML
# ============================================================

HTML_PAGE = """
<!DOCTYPE html>
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
  --felt-green: #0d5c36; --felt-green-light: #147a48; --felt-green-dark: #084022;
  --accent-gold: #d4af37; --accent-gold-light: #f0d878;
  --card-width: clamp(42px, 11vw, 72px); --card-height: calc(var(--card-width) * 1.4);
  --seat-size: clamp(44px, 12vw, 64px); --font-base: clamp(13px, 3.5vw, 16px);
  --radius-sm: 8px; --radius-md: 14px; --radius-lg: 22px;
  --shadow-card: 0 3px 10px rgba(0,0,0,0.35); --shadow-gold: 0 0 15px rgba(212,175,55,0.4);
}
* { box-sizing: border-box; margin: 0; padding: 0; -webkit-tap-highlight-color: transparent; }
html, body, #root { height: 100%; overflow: hidden; }
body { font-family: "Segoe UI", system-ui, -apple-system, sans-serif; font-size: var(--font-base); background: var(--felt-green-dark); color: #fff; touch-action: manipulation; }
@keyframes cardPopIn { 0% { transform: scale(0) rotateY(90deg); opacity: 0; } 60% { transform: scale(1.1) rotateY(0deg); opacity: 1; } 100% { transform: scale(1) rotateY(0deg); opacity: 1; } }
@keyframes trumpFlash { 0% { opacity: 0; transform: scale(0.8); } 30% { opacity: 1; transform: scale(1.05); } 70% { opacity: 1; transform: scale(1); } 100% { opacity: 0; transform: scale(1.2); } }
@keyframes suitPulse { 0%,100% { transform: scale(1); opacity: 0.9; } 50% { transform: scale(1.15); opacity: 1; } }
@keyframes mendiSpring { 0% { transform: scale(0) rotate(-20deg); } 50% { transform: scale(1.3) rotate(5deg); } 70% { transform: scale(0.9) rotate(-3deg); } 100% { transform: scale(1) rotate(0deg); } }
@keyframes glowPulse { 0%,100% { box-shadow: 0 0 5px var(--accent-gold); } 50% { box-shadow: 0 0 20px var(--accent-gold), 0 0 40px rgba(212,175,55,0.3); } }
@keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
@keyframes slideUp { from { transform: translateY(100%); } to { transform: translateY(0); } }
.app { height: 100vh; display: flex; flex-direction: column; background: radial-gradient(ellipse at center, var(--felt-green) 0%, var(--felt-green-dark) 100%); }
.view { flex: 1; display: flex; flex-direction: column; align-items: center; justify-content: center; padding: 16px; animation: fadeIn 0.4s ease; }
.menu-title { font-size: clamp(2rem, 8vw, 3.5rem); font-weight: 800; color: var(--accent-gold); text-shadow: 0 2px 10px rgba(0,0,0,0.5); margin-bottom: 8px; letter-spacing: 2px; }
.menu-sub { color: rgba(255,255,255,0.6); margin-bottom: 40px; font-size: 0.95rem; }
.menu-btn { width: min(280px, 80vw); padding: 16px 24px; margin: 10px 0; border: none; border-radius: var(--radius-lg); font-size: 1.1rem; font-weight: 700; cursor: pointer; transition: all 0.2s; text-transform: uppercase; letter-spacing: 1px; }
.menu-btn.primary { background: linear-gradient(135deg, var(--accent-gold), #b8941f); color: #1a1a1a; box-shadow: 0 4px 15px rgba(212,175,55,0.3); }
.menu-btn.primary:active { transform: scale(0.96); }
.menu-btn.secondary { background: rgba(255,255,255,0.08); color: #fff; border: 1px solid rgba(255,255,255,0.15); }
.menu-btn.secondary:active { background: rgba(255,255,255,0.15); }
.form-card { background: rgba(0,0,0,0.25); backdrop-filter: blur(10px); border: 1px solid rgba(255,255,255,0.08); border-radius: var(--radius-lg); padding: 28px; width: min(340px, 90vw); }
.form-title { font-size: 1.4rem; font-weight: 700; margin-bottom: 20px; text-align: center; color: var(--accent-gold); }
.input-group { margin-bottom: 16px; }
.input-group label { display: block; margin-bottom: 6px; font-size: 0.85rem; color: rgba(255,255,255,0.7); font-weight: 500; }
.input-group input { width: 100%; padding: 12px 14px; border-radius: var(--radius-sm); border: 1px solid rgba(255,255,255,0.12); background: rgba(0,0,0,0.3); color: #fff; font-size: 1rem; outline: none; transition: border-color 0.2s; }
.input-group input:focus { border-color: var(--accent-gold); }
.team-select { display: flex; gap: 10px; margin-bottom: 16px; }
.team-option { flex: 1; padding: 12px; border-radius: var(--radius-sm); border: 2px solid rgba(255,255,255,0.1); background: rgba(0,0,0,0.2); text-align: center; cursor: pointer; transition: all 0.2s; font-weight: 600; }
.team-option.active { border-color: var(--accent-gold); background: rgba(212,175,55,0.15); }
.team-a { color: #6bb5ff; } .team-b { color: #ff8a8a; }
.form-actions { display: flex; gap: 10px; margin-top: 8px; }
.form-actions button { flex: 1; padding: 12px; border-radius: var(--radius-sm); border: none; font-weight: 700; cursor: pointer; font-size: 0.95rem; }
.btn-back { background: rgba(255,255,255,0.08); color: #fff; }
.btn-submit { background: var(--accent-gold); color: #1a1a1a; }
.room-code { font-size: 2rem; font-weight: 800; letter-spacing: 4px; color: var(--accent-gold); text-align: center; margin: 10px 0; }
.seats-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 12px; width: min(320px, 85vw); margin: 20px 0; }
.seat { background: rgba(0,0,0,0.25); border: 2px solid rgba(255,255,255,0.1); border-radius: var(--radius-md); padding: 16px 10px; text-align: center; transition: all 0.3s; }
.seat.filled { border-color: var(--accent-gold); background: rgba(212,175,55,0.08); }
.seat-name { font-weight: 600; font-size: 0.95rem; }
.seat-team { font-size: 0.75rem; opacity: 0.6; margin-top: 4px; }
.seat-status { font-size: 0.75rem; margin-top: 6px; padding: 3px 8px; border-radius: 10px; display: inline-block; }
.status-host { background: rgba(212,175,55,0.2); color: var(--accent-gold); }
.status-waiting { background: rgba(255,255,255,0.08); color: rgba(255,255,255,0.5); }
.start-btn { width: min(280px, 80vw); padding: 14px; background: linear-gradient(135deg, var(--accent-gold), #b8941f); border: none; border-radius: var(--radius-lg); color: #1a1a1a; font-weight: 800; font-size: 1.1rem; cursor: pointer; text-transform: uppercase; letter-spacing: 1px; margin-top: 10px; }
.start-btn:disabled { opacity: 0.4; cursor: not-allowed; }
.game-view { flex: 1; display: flex; flex-direction: column; position: relative; overflow: hidden; }
.score-cluster { display: flex; align-items: center; justify-content: space-between; padding: 8px 12px; background: rgba(0,0,0,0.2); backdrop-filter: blur(6px); border-bottom: 1px solid rgba(255,255,255,0.05); min-height: 64px; flex-shrink: 0; z-index: 10; }
.score-side { display: flex; flex-direction: column; align-items: center; min-width: 70px; }
.score-label { font-size: 0.7rem; text-transform: uppercase; letter-spacing: 1px; opacity: 0.7; margin-bottom: 2px; }
.score-number { font-size: 1.4rem; font-weight: 800; }
.score-team-a { color: #6bb5ff; } .score-team-b { color: #ff8a8a; }
.mendi-strip { display: flex; gap: 3px; margin-top: 4px; height: 22px; }
.mendi-mini { width: 14px; height: 20px; border-radius: 3px; background: #fff; display: flex; align-items: center; justify-content: center; font-size: 9px; font-weight: 800; box-shadow: 0 1px 3px rgba(0,0,0,0.3); animation: mendiSpring 0.5s ease both; }
.trump-slot { display: flex; flex-direction: column; align-items: center; background: rgba(0,0,0,0.3); border-radius: var(--radius-sm); padding: 6px 14px; border: 1px solid rgba(255,255,255,0.1); }
.trump-label { font-size: 0.65rem; text-transform: uppercase; letter-spacing: 1px; opacity: 0.6; }
.trump-card-mini { width: 28px; height: 40px; background: #fff; border-radius: 4px; display: flex; align-items: center; justify-content: center; font-size: 1.1rem; margin-top: 4px; box-shadow: 0 2px 6px rgba(0,0,0,0.3); }
.trump-unknown { width: 28px; height: 40px; background: rgba(255,255,255,0.1); border-radius: 4px; display: flex; align-items: center; justify-content: center; font-size: 1rem; margin-top: 4px; color: rgba(255,255,255,0.4); border: 1px dashed rgba(255,255,255,0.2); }
.table-felt { flex: 1; position: relative; display: flex; align-items: center; justify-content: center; min-height: 0; }
.felt-ellipse { position: absolute; width: 92%; height: 85%; background: radial-gradient(ellipse at center, rgba(20,122,72,0.6) 0%, rgba(13,92,54,0.3) 60%, transparent 100%); border-radius: 50%; pointer-events: none; }
.seat-marker { position: absolute; display: flex; flex-direction: column; align-items: center; transition: all 0.3s ease; }
.seat-marker.active .seat-avatar { animation: glowPulse 1.5s infinite; border-color: var(--accent-gold); }
.seat-avatar { width: var(--seat-size); height: var(--seat-size); border-radius: 50%; background: rgba(0,0,0,0.4); border: 2px solid rgba(255,255,255,0.15); display: flex; align-items: center; justify-content: center; font-size: 1.3rem; box-shadow: 0 2px 8px rgba(0,0,0,0.3); }
.seat-name-tag { margin-top: 5px; font-size: 0.75rem; font-weight: 600; background: rgba(0,0,0,0.4); padding: 2px 10px; border-radius: 10px; white-space: nowrap; max-width: 90px; overflow: hidden; text-overflow: ellipsis; }
.seat-marker.top { top: 2%; left: 50%; transform: translateX(-50%); }
.seat-marker.left { left: 2%; top: 50%; transform: translateY(-50%); }
.seat-marker.right { right: 2%; top: 50%; transform: translateY(-50%); }
.seat-marker.bottom { bottom: 2%; left: 50%; transform: translateX(-50%); }
.bot-badge { font-size: 0.6rem; background: rgba(255,255,255,0.1); padding: 1px 6px; border-radius: 6px; margin-top: 3px; }
.trick-center { position: relative; width: min(220px, 55vw); height: min(220px, 55vw); display: flex; align-items: center; justify-content: center; }
.trick-card-wrapper { position: absolute; transition: all 0.4s cubic-bezier(0.34, 1.56, 0.64, 1); }
.trick-card-wrapper.pos-0 { bottom: 0; left: 50%; transform: translateX(-50%) translateY(20%); }
.trick-card-wrapper.pos-1 { left: 0; top: 50%; transform: translateY(-50%) translateX(-20%); }
.trick-card-wrapper.pos-2 { top: 0; left: 50%; transform: translateX(-50%) translateY(-20%); }
.trick-card-wrapper.pos-3 { right: 0; top: 50%; transform: translateY(-50%) translateX(20%); }
.card { width: var(--card-width); height: var(--card-height); background: #fff; border-radius: clamp(6px, 1.8vw, 10px); display: flex; flex-direction: column; align-items: center; justify-content: center; box-shadow: var(--shadow-card); position: relative; user-select: none; cursor: pointer; transition: transform 0.2s, box-shadow 0.2s; animation: cardPopIn 0.4s cubic-bezier(0.34, 1.56, 0.64, 1) both; }
.card:hover:not(.disabled) { transform: translateY(-6px); box-shadow: 0 6px 20px rgba(0,0,0,0.4); }
.card.disabled { opacity: 0.45; cursor: not-allowed; filter: grayscale(0.3); }
.card.back { background: linear-gradient(135deg, #1e3a5f 0%, #2a5298 50%, #1e3a5f 100%); background-size: 8px 8px; border: 1px solid rgba(255,255,255,0.15); }
.card.back::after { content: ""; width: 60%; height: 60%; border: 2px solid rgba(255,255,255,0.15); border-radius: 6px; position: absolute; }
.card-rank { font-size: clamp(0.9rem, 3vw, 1.3rem); font-weight: 800; line-height: 1; }
.card-suit { font-size: clamp(0.9rem, 3vw, 1.3rem); line-height: 1; margin-top: 2px; }
.card.red { color: #c41e3a; } .card.black { color: #1a1a1a; }
.card-corner { position: absolute; font-size: clamp(0.5rem, 1.5vw, 0.7rem); font-weight: 700; line-height: 1; }
.card-corner.top-left { top: 5px; left: 6px; }
.card-corner.bottom-right { bottom: 5px; right: 6px; transform: rotate(180deg); }
.hand-strip { display: flex; justify-content: center; align-items: flex-end; padding: 10px 8px 14px; gap: 0; min-height: calc(var(--card-height) + 20px); flex-shrink: 0; background: rgba(0,0,0,0.15); border-top: 1px solid rgba(255,255,255,0.05); overflow-x: auto; scrollbar-width: none; }
.hand-strip::-webkit-scrollbar { display: none; }
.hand-card-wrapper { transition: margin 0.3s ease; }
.trump-flash-overlay { position: fixed; inset: 0; display: flex; align-items: center; justify-content: center; z-index: 100; pointer-events: none; animation: trumpFlash 1.8s ease both; }
.trump-flash-content { text-align: center; padding: 40px; border-radius: var(--radius-lg); background: rgba(0,0,0,0.6); backdrop-filter: blur(10px); border: 2px solid var(--accent-gold); }
.trump-flash-suit { font-size: clamp(4rem, 15vw, 7rem); animation: suitPulse 0.6s ease infinite; }
.trump-flash-text { font-size: clamp(1.2rem, 4vw, 1.8rem); font-weight: 800; color: var(--accent-gold); margin-top: 10px; }
.trump-flash-sub { font-size: 0.9rem; opacity: 0.8; margin-top: 6px; }
.reveal-btn { position: absolute; bottom: calc(var(--card-height) + 30px); left: 50%; transform: translateX(-50%); padding: 10px 24px; background: linear-gradient(135deg, #c41e3a, #8b0000); border: none; border-radius: var(--radius-lg); color: #fff; font-weight: 700; font-size: 0.95rem; cursor: pointer; box-shadow: 0 4px 15px rgba(196,30,58,0.4); animation: slideUp 0.3s ease; z-index: 20; }
.reveal-btn:active { transform: translateX(-50%) scale(0.95); }
.result-overlay { position: fixed; inset: 0; background: rgba(0,0,0,0.7); backdrop-filter: blur(8px); display: flex; align-items: center; justify-content: center; z-index: 90; animation: fadeIn 0.3s ease; }
.result-card { background: rgba(13,92,54,0.95); border: 2px solid var(--accent-gold); border-radius: var(--radius-lg); padding: 32px; text-align: center; width: min(320px, 85vw); animation: cardPopIn 0.5s ease both; }
.result-title { font-size: 1.6rem; font-weight: 800; color: var(--accent-gold); margin-bottom: 16px; }
.result-scores { display: flex; justify-content: center; gap: 30px; margin: 16px 0; }
.result-team { text-align: center; }
.result-team-name { font-size: 0.8rem; text-transform: uppercase; opacity: 0.7; }
.result-team-score { font-size: 2rem; font-weight: 800; margin-top: 4px; }
.result-mendi { display: flex; gap: 4px; justify-content: center; margin-top: 8px; flex-wrap: wrap; }
.result-btn { margin-top: 20px; padding: 12px 32px; background: var(--accent-gold); border: none; border-radius: var(--radius-lg); color: #1a1a1a; font-weight: 800; font-size: 1rem; cursor: pointer; }
.toast-container { position: fixed; top: 70px; left: 50%; transform: translateX(-50%); z-index: 80; display: flex; flex-direction: column; gap: 8px; pointer-events: none; }
.toast { background: rgba(0,0,0,0.75); backdrop-filter: blur(6px); color: #fff; padding: 10px 20px; border-radius: var(--radius-sm); font-size: 0.9rem; font-weight: 500; border-left: 3px solid var(--accent-gold); animation: slideUp 0.3s ease, fadeIn 0.3s ease; white-space: nowrap; }
.pause-indicator { position: absolute; top: 50%; left: 50%; transform: translate(-50%, -50%); background: rgba(0,0,0,0.5); padding: 8px 20px; border-radius: 20px; font-size: 0.8rem; opacity: 0.8; z-index: 15; pointer-events: none; }
.exit-btn { position: absolute; top: 8px; left: 8px; z-index: 30; background: rgba(0,0,0,0.3); border: 1px solid rgba(255,255,255,0.1); color: #fff; width: 32px; height: 32px; border-radius: 50%; display: flex; align-items: center; justify-content: center; cursor: pointer; font-size: 1.1rem; }
.dealer-chip { position: absolute; width: 18px; height: 18px; background: var(--accent-gold); border-radius: 50%; font-size: 0.6rem; font-weight: 800; color: #1a1a1a; display: flex; align-items: center; justify-content: center; box-shadow: 0 1px 4px rgba(0,0,0,0.4); z-index: 5; }
.trick-counter { position: absolute; top: 8px; right: 8px; background: rgba(0,0,0,0.3); padding: 4px 10px; border-radius: 10px; font-size: 0.75rem; font-weight: 600; z-index: 10; }
.confirm-overlay { position: fixed; inset: 0; background: rgba(0,0,0,0.6); backdrop-filter: blur(4px); display: flex; align-items: center; justify-content: center; z-index: 95; }
.confirm-box { background: var(--felt-green); border: 1px solid rgba(255,255,255,0.15); border-radius: var(--radius-lg); padding: 24px; width: min(300px, 80vw); text-align: center; }
.confirm-text { margin-bottom: 20px; font-size: 1rem; }
.confirm-buttons { display: flex; gap: 10px; }
.confirm-buttons button { flex: 1; padding: 10px; border-radius: var(--radius-sm); border: none; font-weight: 600; cursor: pointer; }
.btn-cancel { background: rgba(255,255,255,0.1); color: #fff; }
.btn-confirm { background: #c41e3a; color: #fff; }
@media (min-width: 600px) { :root { --card-width: 64px; } .seat-marker.left { left: 8%; } .seat-marker.right { right: 8%; } }
@media (max-height: 600px) { .score-cluster { min-height: 52px; padding: 4px 10px; } .hand-strip { min-height: calc(var(--card-height) + 10px); padding-bottom: 8px; } }
</style>
</head>
<body>
<div id="root"></div>
<script type="text/babel">
const { useState, useEffect, useRef, useCallback } = React;
const SUIT_COLORS = { "spades":"black","clubs":"black","hearts":"red","diamonds":"red" };

function Card({ card, faceDown, disabled, onClick, style, className }) {
  if (faceDown || !card) { return React.createElement("div", { className: "card back", style }); }
  const color = SUIT_COLORS[card.suit];
  return React.createElement("div", {
    className: `card ${color} ${disabled ? "disabled" : ""} ${className || ""}`,
    style, onClick: disabled ? undefined : onClick
  },
    React.createElement("span", { className: "card-corner top-left" }, card.rank, React.createElement("br"), card.symbol),
    React.createElement("span", { className: "card-rank" }, card.rank),
    React.createElement("span", { className: "card-suit" }, card.symbol),
    React.createElement("span", { className: "card-corner bottom-right" }, card.rank, React.createElement("br"), card.symbol)
  );
}

function TrumpFlash({ suit, symbol, onDone }) {
  useEffect(() => { const t = setTimeout(onDone, 1800); return () => clearTimeout(t); }, [onDone]);
  const color = SUIT_COLORS[suit] === "red" ? "#c41e3a" : "#1a1a1a";
  return React.createElement("div", { className: "trump-flash-overlay" },
    React.createElement("div", { className: "trump-flash-content" },
      React.createElement("div", { className: "trump-flash-suit", style: { color } }, symbol),
      React.createElement("div", { className: "trump-flash-text" }, "TRUMP REVEALED!"),
      React.createElement("div", { className: "trump-flash-sub" }, symbol + " is now trump")
    )
  );
}

function ResultOverlay({ result, scores, mendi, onRematch, onExit }) {
  const title = result === "draw" ? "Hand Drawn!" : `Team ${result} Wins!`;
  return React.createElement("div", { className: "result-overlay" },
    React.createElement("div", { className: "result-card" },
      React.createElement("div", { className: "result-title" }, title),
      React.createElement("div", { className: "result-scores" },
        React.createElement("div", { className: "result-team" },
          React.createElement("div", { className: "result-team-name" }, "Team A"),
          React.createElement("div", { className: "result-team-score score-team-a" }, scores.A),
          React.createElement("div", { className: "result-mendi" },
            mendi.A.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
          )
        ),
        React.createElement("div", { className: "result-team" },
          React.createElement("div", { className: "result-team-name" }, "Team B"),
          React.createElement("div", { className: "result-team-score score-team-b" }, scores.B),
          React.createElement("div", { className: "result-mendi" },
            mendi.B.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
          )
        )
      ),
      React.createElement("button", { className: "result-btn", onClick: onRematch }, "Rematch"),
      React.createElement("button", { className: "menu-btn secondary", style: {marginTop:10,width:"100%"}, onClick: onExit }, "Exit to Menu")
    )
  );
}

function ToastContainer({ toasts }) {
  return React.createElement("div", { className: "toast-container" },
    toasts.map(t => React.createElement("div", { key: t.id, className: "toast" }, t.msg))
  );
}

function ConfirmExit({ onConfirm, onCancel }) {
  return React.createElement("div", { className: "confirm-overlay" },
    React.createElement("div", { className: "confirm-box" },
      React.createElement("div", { className: "confirm-text" }, "Leave the game?"),
      React.createElement("div", { className: "confirm-buttons" },
        React.createElement("button", { className: "btn-cancel", onClick: onCancel }, "Stay"),
        React.createElement("button", { className: "btn-confirm", onClick: onConfirm }, "Leave")
      )
    )
  );
}
function App() {
  const [view, setView] = useState("menu");
  const [playerName, setPlayerName] = useState(localStorage.getItem("mendikot_name") || "");
  const [gameState, setGameState] = useState(null);
  const [showTrumpFlash, setShowTrumpFlash] = useState(false);
  const [flashSuit, setFlashSuit] = useState(null);
  const [flashSymbol, setFlashSymbol] = useState(null);
  const [toasts, setToasts] = useState([]);
  const [confirmExit, setConfirmExit] = useState(false);
  const [roomState, setRoomState] = useState(null);
  const wsRef = useRef(null);
  const reconnectTimer = useRef(null);

  const addToast = useCallback((msg) => {
    const id = Date.now() + Math.random();
    setToasts(prev => [...prev, {id, msg}]);
    setTimeout(() => setToasts(prev => prev.filter(t => t.id !== id)), 2500);
  }, []);

  const connectWS = useCallback(() => {
    const proto = window.location.protocol === "https:" ? "wss:" : "ws:";
    const ws = new WebSocket(`${proto}//${window.location.host}/ws`);
    wsRef.current = ws;
    ws.onopen = () => {
      const savedRoom = sessionStorage.getItem("mendikot_room");
      const savedName = localStorage.getItem("mendikot_name");
      if (savedRoom && savedName) {
        ws.send(JSON.stringify({type:"reconnect", room_id:savedRoom, name:savedName}));
      }
    };
    ws.onmessage = (ev) => {
      const msg = JSON.parse(ev.data);
      if (msg.type === "game_state") { setGameState(msg.data); setView("game"); }
      else if (msg.type === "lobby_update") { setRoomState(msg.data); setView("lobby"); }
      else if (msg.type === "room_created") { setRoomState(msg.data); sessionStorage.setItem("mendikot_room", msg.data.room_id); setView("lobby"); }
      else if (msg.type === "trump_revealed") { setFlashSuit(msg.data.suit); setFlashSymbol(msg.data.card.symbol); setShowTrumpFlash(true); }
      else if (msg.type === "room_cancelled") { addToast(msg.reason || "Room cancelled"); sessionStorage.removeItem("mendikot_room"); setView("menu"); }
      else if (msg.type === "error") { addToast(msg.data.message || "Error"); }
    };
    ws.onclose = () => { reconnectTimer.current = setTimeout(connectWS, 2000); };
  }, [addToast]);

  useEffect(() => {
    connectWS();
    return () => { if (reconnectTimer.current) clearTimeout(reconnectTimer.current); if (wsRef.current) wsRef.current.close(); };
  }, [connectWS]);

  const send = useCallback((obj) => {
    if (wsRef.current && wsRef.current.readyState === 1) wsRef.current.send(JSON.stringify(obj));
  }, []);

  const startSolo = useCallback((name, team) => { localStorage.setItem("mendikot_name", name); send({type:"start_solo", name, team}); }, [send]);
  const createRoom = useCallback((name, team) => { localStorage.setItem("mendikot_name", name); send({type:"create_room", name, team}); }, [send]);
  const joinRoom = useCallback((name, roomId, team) => { localStorage.setItem("mendikot_name", name); send({type:"join_room", name, room_id:roomId, team}); }, [send]);
  const startGame = useCallback(() => { send({type:"start_game"}); }, [send]);
  const playCard = useCallback((cardId) => { send({type:"play_card", card_id:cardId}); }, [send]);
  const rematch = useCallback(() => { send({type:"rematch"}); }, [send]);
  const exitGame = useCallback(() => { send({type:"exit"}); sessionStorage.removeItem("mendikot_room"); setGameState(null); setRoomState(null); setView("menu"); }, [send]);

  if (view === "menu") {
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "menu-title" }, "MENDIKOT"),
        React.createElement("div", { className: "menu-sub" }, "The Classic Indian Card Game"),
        React.createElement("button", { className: "menu-btn primary", onClick: () => setView("solo-setup") }, "Solo vs Bots"),
        React.createElement("button", { className: "menu-btn secondary", onClick: () => setView("hub") }, "Play with Friends")
      )
    );
  }

  if (view === "solo-setup") {
    const [name, setName] = useState(playerName);
    const [team, setTeam] = useState("A");
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "form-card" },
          React.createElement("div", { className: "form-title" }, "Solo Setup"),
          React.createElement("div", { className: "input-group" },
            React.createElement("label", null, "Your Name"),
            React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
          ),
          React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
          React.createElement("div", { className: "team-select" },
            React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
            React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
          ),
          React.createElement("div", { className: "form-actions" },
            React.createElement("button", { className: "btn-back", onClick: () => setView("menu") }, "Back"),
            React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim()) startSolo(name.trim(), team); } }, "Start Game")
          )
        )
      )
    );
  }

  if (view === "hub") {
    const [name, setName] = useState(playerName);
    const [roomId, setRoomId] = useState("");
    const [subView, setSubView] = useState("choice");
    const [team, setTeam] = useState("A");
    if (subView === "choice") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card", style: {textAlign:"center"} },
            React.createElement("div", { className: "form-title" }, "Play with Friends"),
            React.createElement("button", { className: "menu-btn primary", style: {width:"100%",margin:"12px 0"}, onClick: () => setSubView("create") }, "Create Room"),
            React.createElement("button", { className: "menu-btn secondary", style: {width:"100%",margin:"4px 0"}, onClick: () => setSubView("join") }, "Join Room"),
            React.createElement("button", { className: "btn-back", style: {width:"100%",marginTop:16,padding:10}, onClick: () => setView("menu") }, "Back")
          )
        )
      );
    }
    if (subView === "create") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card" },
            React.createElement("div", { className: "form-title" }, "Create Room"),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Your Name"),
              React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
            ),
            React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
            React.createElement("div", { className: "team-select" },
              React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
              React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
            ),
            React.createElement("div", { className: "form-actions" },
              React.createElement("button", { className: "btn-back", onClick: () => setSubView("choice") }, "Back"),
              React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim()) createRoom(name.trim(), team); } }, "Create")
            )
          )
        )
      );
    }
    if (subView === "join") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card" },
            React.createElement("div", { className: "form-title" }, "Join Room"),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Your Name"),
              React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
            ),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Room Code"),
              React.createElement("input", { value: roomId, onChange: e => setRoomId(e.target.value.toUpperCase()), placeholder: "Enter code", maxLength: 6 })
            ),
            React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
            React.createElement("div", { className: "team-select" },
              React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
              React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
            ),
            React.createElement("div", { className: "form-actions" },
              React.createElement("button", { className: "btn-back", onClick: () => setSubView("choice") }, "Back"),
              React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim() && roomId.trim()) joinRoom(name.trim(), roomId.trim(), team); } }, "Join")
            )
          )
        )
      );
    }
  }

  if (view === "lobby" && roomState) {
    const isHost = roomState.seats[0] && roomState.seats[0].is_host;
    const allFilled = roomState.seats.every(s => s.filled);
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "form-title" }, "Room Lobby"),
        React.createElement("div", { className: "room-code" }, roomState.room_id),
        React.createElement("div", { className: "seats-grid" },
          roomState.seats.map((s, i) =>
            React.createElement("div", { key: i, className: `seat ${s.filled ? "filled" : ""}` },
              React.createElement("div", { className: "seat-name" }, s.filled ? s.name : "Open"),
              React.createElement("div", { className: "seat-team" }, `Team ${s.team}`),
              React.createElement("div", { className: `seat-status ${s.is_host ? "status-host" : "status-waiting"}` }, s.is_host ? "Host" : (s.filled ? "Ready" : "Waiting"))
            )
          )
        ),
        isHost && React.createElement("button", { className: "start-btn", disabled: !allFilled, onClick: startGame }, "Start Game"),
        !isHost && React.createElement("div", { style: {color:"rgba(255,255,255,0.6)",fontSize:"0.9rem"} }, "Waiting for host..."),
        React.createElement("button", { className: "btn-back", style: {marginTop:16,padding:"10px 20px"}, onClick: exitGame }, "Leave")
      )
    );
  }

  if (view === "game" && gameState) {
    const mySeat = gameState.players.find(p => p.hand !== null)?.seat ?? 0;
    const me = gameState.players.find(p => p.seat === mySeat);
    const hand = me?.hand || [];
    const legal = gameState.turn === mySeat && !gameState.paused && !gameState.handComplete ? hand.map(() => true) : hand.map(() => false);
    const needsReveal = gameState.turn === mySeat && !gameState.trump_suit && gameState.phase === "phase1" && gameState.trick.length > 0;
    const seatPositions = ["bottom","left","top","right"];
    const handCount = hand.length;
    const overlap = handCount > 6 ? -(Math.min(28, (handCount-6)*4)) : 0;

    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "game-view" },
        React.createElement("button", { className: "exit-btn", onClick: () => setConfirmExit(true) }, "×"),
        React.createElement("div", { className: "trick-counter" }, `Trick ${Math.min(gameState.trick_number,13)} / 13`),

        React.createElement("div", { className: "score-cluster" },
          React.createElement("div", { className: "score-side" },
            React.createElement("span", { className: "score-label" }, "Team A"),
            React.createElement("span", { className: "score-number score-team-a" }, gameState.scores.A),
            React.createElement("div", { className: "mendi-strip" },
              gameState.mendi.A.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
            )
          ),
          React.createElement("div", { className: "trump-slot" },
            React.createElement("span", { className: "trump-label" }, "Trump"),
            gameState.trump_suit
              ? React.createElement("div", { className: "trump-card-mini", style: {color: SUIT_COLORS[gameState.trump_suit]==="red"?"#c41e3a":"#1a1a1a"} }, gameState.players[0].hand ? gameState.players[0].hand.find(h=>h.suit===gameState.trump_suit)?.symbol || SUIT_SYMBOLS[gameState.trump_suit] : SUIT_SYMBOLS[gameState.trump_suit])
              : React.createElement("div", { className: "trump-unknown" }, "?")
          ),
          React.createElement("div", { className: "score-side" },
            React.createElement("span", { className: "score-label" }, "Team B"),
            React.createElement("span", { className: "score-number score-team-b" }, gameState.scores.B),
            React.createElement("div", { className: "mendi-strip" },
              gameState.mendi.B.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
            )
          )
        ),

        React.createElement("div", { className: "table-felt" },
          React.createElement("div", { className: "felt-ellipse" }),
          [2,1,3,0].map(seat => {
            const pos = seatPositions[seat];
            const isActive = gameState.turn === seat && !gameState.paused && !gameState.handComplete;
            const isDealer = gameState.dealer === seat;
            const pl = gameState.players.find(p => p.seat === seat);
            return React.createElement("div", { key: seat, className: `seat-marker ${pos} ${isActive ? "active" : ""}` },
              React.createElement("div", { style: {position:"relative"} },
function App() {
  const [view, setView] = useState("menu");
  const [playerName, setPlayerName] = useState(localStorage.getItem("mendikot_name") || "");
  const [gameState, setGameState] = useState(null);
  const [showTrumpFlash, setShowTrumpFlash] = useState(false);
  const [flashSuit, setFlashSuit] = useState(null);
  const [flashSymbol, setFlashSymbol] = useState(null);
  const [toasts, setToasts] = useState([]);
  const [confirmExit, setConfirmExit] = useState(false);
  const [roomState, setRoomState] = useState(null);
  const wsRef = useRef(null);
  const reconnectTimer = useRef(null);

  const addToast = useCallback((msg) => {
    const id = Date.now() + Math.random();
    setToasts(prev => [...prev, {id, msg}]);
    setTimeout(() => setToasts(prev => prev.filter(t => t.id !== id)), 2500);
  }, []);

  const connectWS = useCallback(() => {
    const proto = window.location.protocol === "https:" ? "wss:" : "ws:";
    const ws = new WebSocket(`${proto}//${window.location.host}/ws`);
    wsRef.current = ws;
    ws.onopen = () => {
      const savedRoom = sessionStorage.getItem("mendikot_room");
      const savedName = localStorage.getItem("mendikot_name");
      if (savedRoom && savedName) {
        ws.send(JSON.stringify({type:"reconnect", room_id:savedRoom, name:savedName}));
      }
    };
    ws.onmessage = (ev) => {
      const msg = JSON.parse(ev.data);
      if (msg.type === "game_state") { setGameState(msg.data); setView("game"); }
      else if (msg.type === "lobby_update") { setRoomState(msg.data); setView("lobby"); }
      else if (msg.type === "room_created") { setRoomState(msg.data); sessionStorage.setItem("mendikot_room", msg.data.room_id); setView("lobby"); }
      else if (msg.type === "trump_revealed") { setFlashSuit(msg.data.suit); setFlashSymbol(msg.data.card.symbol); setShowTrumpFlash(true); }
      else if (msg.type === "room_cancelled") { addToast(msg.reason || "Room cancelled"); sessionStorage.removeItem("mendikot_room"); setView("menu"); }
      else if (msg.type === "error") { addToast(msg.data.message || "Error"); }
    };
    ws.onclose = () => { reconnectTimer.current = setTimeout(connectWS, 2000); };
  }, [addToast]);

  useEffect(() => {
    connectWS();
    return () => { if (reconnectTimer.current) clearTimeout(reconnectTimer.current); if (wsRef.current) wsRef.current.close(); };
  }, [connectWS]);

  const send = useCallback((obj) => {
    if (wsRef.current && wsRef.current.readyState === 1) wsRef.current.send(JSON.stringify(obj));
  }, []);

  const startSolo = useCallback((name, team) => { localStorage.setItem("mendikot_name", name); send({type:"start_solo", name, team}); }, [send]);
  const createRoom = useCallback((name, team) => { localStorage.setItem("mendikot_name", name); send({type:"create_room", name, team}); }, [send]);
  const joinRoom = useCallback((name, roomId, team) => { localStorage.setItem("mendikot_name", name); send({type:"join_room", name, room_id:roomId, team}); }, [send]);
  const startGame = useCallback(() => { send({type:"start_game"}); }, [send]);
  const playCard = useCallback((cardId) => { send({type:"play_card", card_id:cardId}); }, [send]);
  const rematch = useCallback(() => { send({type:"rematch"}); }, [send]);
  const exitGame = useCallback(() => { send({type:"exit"}); sessionStorage.removeItem("mendikot_room"); setGameState(null); setRoomState(null); setView("menu"); }, [send]);

  if (view === "menu") {
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "menu-title" }, "MENDIKOT"),
        React.createElement("div", { className: "menu-sub" }, "The Classic Indian Card Game"),
        React.createElement("button", { className: "menu-btn primary", onClick: () => setView("solo-setup") }, "Solo vs Bots"),
        React.createElement("button", { className: "menu-btn secondary", onClick: () => setView("hub") }, "Play with Friends")
      )
    );
  }

  if (view === "solo-setup") {
    const [name, setName] = useState(playerName);
    const [team, setTeam] = useState("A");
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "form-card" },
          React.createElement("div", { className: "form-title" }, "Solo Setup"),
          React.createElement("div", { className: "input-group" },
            React.createElement("label", null, "Your Name"),
            React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
          ),
          React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
          React.createElement("div", { className: "team-select" },
            React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
            React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
          ),
          React.createElement("div", { className: "form-actions" },
            React.createElement("button", { className: "btn-back", onClick: () => setView("menu") }, "Back"),
            React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim()) startSolo(name.trim(), team); } }, "Start Game")
          )
        )
      )
    );
  }

  if (view === "hub") {
    const [name, setName] = useState(playerName);
    const [roomId, setRoomId] = useState("");
    const [subView, setSubView] = useState("choice");
    const [team, setTeam] = useState("A");
    if (subView === "choice") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card", style: {textAlign:"center"} },
            React.createElement("div", { className: "form-title" }, "Play with Friends"),
            React.createElement("button", { className: "menu-btn primary", style: {width:"100%",margin:"12px 0"}, onClick: () => setSubView("create") }, "Create Room"),
            React.createElement("button", { className: "menu-btn secondary", style: {width:"100%",margin:"4px 0"}, onClick: () => setSubView("join") }, "Join Room"),
            React.createElement("button", { className: "btn-back", style: {width:"100%",marginTop:16,padding:10}, onClick: () => setView("menu") }, "Back")
          )
        )
      );
    }
    if (subView === "create") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card" },
            React.createElement("div", { className: "form-title" }, "Create Room"),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Your Name"),
              React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
            ),
            React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
            React.createElement("div", { className: "team-select" },
              React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
              React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
            ),
            React.createElement("div", { className: "form-actions" },
              React.createElement("button", { className: "btn-back", onClick: () => setSubView("choice") }, "Back"),
              React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim()) createRoom(name.trim(), team); } }, "Create")
            )
          )
        )
      );
    }
    if (subView === "join") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card" },
            React.createElement("div", { className: "form-title" }, "Join Room"),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Your Name"),
              React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
            ),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Room Code"),
              React.createElement("input", { value: roomId, onChange: e => setRoomId(e.target.value.toUpperCase()), placeholder: "Enter code", maxLength: 6 })
            ),
            React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
            React.createElement("div", { className: "team-select" },
              React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
              React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
            ),
            React.createElement("div", { className: "form-actions" },
              React.createElement("button", { className: "btn-back", onClick: () => setSubView("choice") }, "Back"),
              React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim() && roomId.trim()) joinRoom(name.trim(), roomId.trim(), team); } }, "Join")
            )
          )
        )
      );
    }
  }

  if (view === "lobby" && roomState) {
    const isHost = roomState.seats[0] && roomState.seats[0].is_host;
    const allFilled = roomState.seats.every(s => s.filled);
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "form-title" }, "Room Lobby"),
        React.createElement("div", { className: "room-code" }, roomState.room_id),
        React.createElement("div", { className: "seats-grid" },
          roomState.seats.map((s, i) =>
            React.createElement("div", { key: i, className: `seat ${s.filled ? "filled" : ""}` },
              React.createElement("div", { className: "seat-name" }, s.filled ? s.name : "Open"),
              React.createElement("div", { className: "seat-team" }, `Team ${s.team}`),
              React.createElement("div", { className: `seat-status ${s.is_host ? "status-host" : "status-waiting"}` }, s.is_host ? "Host" : (s.filled ? "Ready" : "Waiting"))
            )
          )
        ),
        isHost && React.createElement("button", { className: "start-btn", disabled: !allFilled, onClick: startGame }, "Start Game"),
        !isHost && React.createElement("div", { style: {color:"rgba(255,255,255,0.6)",fontSize:"0.9rem"} }, "Waiting for host..."),
        React.createElement("button", { className: "btn-back", style: {marginTop:16,padding:"10px 20px"}, onClick: exitGame }, "Leave")
      )
    );
  }

  if (view === "game" && gameState) {
    const mySeat = gameState.players.find(p => p.hand !== null)?.seat ?? 0;
    const me = gameState.players.find(p => p.seat === mySeat);
    const hand = me?.hand || [];
    const legal = gameState.turn === mySeat && !gameState.paused && !gameState.handComplete ? hand.map(() => true) : hand.map(() => false);
    const needsReveal = gameState.turn === mySeat && !gameState.trump_suit && gameState.phase === "phase1" && gameState.trick.length > 0;
    const seatPositions = ["bottom","left","top","right"];
    const handCount = hand.length;
    const overlap = handCount > 6 ? -(Math.min(28, (handCount-6)*4)) : 0;

    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "game-view" },
        React.createElement("button", { className: "exit-btn", onClick: () => setConfirmExit(true) }, "×"),
        React.createElement("div", { className: "trick-counter" }, `Trick ${Math.min(gameState.trick_number,13)} / 13`),

        React.createElement("div", { className: "score-cluster" },
          React.createElement("div", { className: "score-side" },
            React.createElement("span", { className: "score-label" }, "Team A"),
            React.createElement("span", { className: "score-number score-team-a" }, gameState.scores.A),
            React.createElement("div", { className: "mendi-strip" },
              gameState.mendi.A.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
            )
          ),
          React.createElement("div", { className: "trump-slot" },
            React.createElement("span", { className: "trump-label" }, "Trump"),
            gameState.trump_suit
              ? React.createElement("div", { className: "trump-card-mini", style: {color: SUIT_COLORS[gameState.trump_suit]==="red"?"#c41e3a":"#1a1a1a"} }, gameState.players[0].hand ? gameState.players[0].hand.find(h=>h.suit===gameState.trump_suit)?.symbol || SUIT_SYMBOLS[gameState.trump_suit] : SUIT_SYMBOLS[gameState.trump_suit])
              : React.createElement("div", { className: "trump-unknown" }, "?")
          ),
          React.createElement("div", { className: "score-side" },
            React.createElement("span", { className: "score-label" }, "Team B"),
            React.createElement("span", { className: "score-number score-team-b" }, gameState.scores.B),
            React.createElement("div", { className: "mendi-strip" },
              gameState.mendi.B.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
            )
          )
        ),

        React.createElement("div", { className: "table-felt" },
          React.createElement("div", { className: "felt-ellipse" }),
          [2,1,3,0].map(seat => {
            const pos = seatPositions[seat];
            const isActive = gameState.turn === seat && !gameState.paused && !gameState.handComplete;
            const isDealer = gameState.dealer === seat;
            const pl = gameState.players.find(p => p.seat === seat);
            return React.createElement("div", { key: seat, className: `seat-marker ${pos} ${isActive ? "active" : ""}` },
              React.createElement("div", { style: {position:"relative"} },
function App() {
  const [view, setView] = useState("menu");
  const [playerName, setPlayerName] = useState(localStorage.getItem("mendikot_name") || "");
  const [gameState, setGameState] = useState(null);
  const [showTrumpFlash, setShowTrumpFlash] = useState(false);
  const [flashSuit, setFlashSuit] = useState(null);
  const [flashSymbol, setFlashSymbol] = useState(null);
  const [toasts, setToasts] = useState([]);
  const [confirmExit, setConfirmExit] = useState(false);
  const [roomState, setRoomState] = useState(null);
  const wsRef = useRef(null);
  const reconnectTimer = useRef(null);

  const addToast = useCallback((msg) => {
    const id = Date.now() + Math.random();
    setToasts(prev => [...prev, {id, msg}]);
    setTimeout(() => setToasts(prev => prev.filter(t => t.id !== id)), 2500);
  }, []);

  const connectWS = useCallback(() => {
    const proto = window.location.protocol === "https:" ? "wss:" : "ws:";
    const ws = new WebSocket(`${proto}//${window.location.host}/ws`);
    wsRef.current = ws;
    ws.onopen = () => {
      const savedRoom = sessionStorage.getItem("mendikot_room");
      const savedName = localStorage.getItem("mendikot_name");
      if (savedRoom && savedName) {
        ws.send(JSON.stringify({type:"reconnect", room_id:savedRoom, name:savedName}));
      }
    };
    ws.onmessage = (ev) => {
      const msg = JSON.parse(ev.data);
      if (msg.type === "game_state") { setGameState(msg.data); setView("game"); }
      else if (msg.type === "lobby_update") { setRoomState(msg.data); setView("lobby"); }
      else if (msg.type === "room_created") { setRoomState(msg.data); sessionStorage.setItem("mendikot_room", msg.data.room_id); setView("lobby"); }
      else if (msg.type === "trump_revealed") { setFlashSuit(msg.data.suit); setFlashSymbol(msg.data.card.symbol); setShowTrumpFlash(true); }
      else if (msg.type === "room_cancelled") { addToast(msg.reason || "Room cancelled"); sessionStorage.removeItem("mendikot_room"); setView("menu"); }
      else if (msg.type === "error") { addToast(msg.data.message || "Error"); }
    };
    ws.onclose = () => { reconnectTimer.current = setTimeout(connectWS, 2000); };
  }, [addToast]);

  useEffect(() => {
    connectWS();
    return () => { if (reconnectTimer.current) clearTimeout(reconnectTimer.current); if (wsRef.current) wsRef.current.close(); };
  }, [connectWS]);

  const send = useCallback((obj) => {
    if (wsRef.current && wsRef.current.readyState === 1) wsRef.current.send(JSON.stringify(obj));
  }, []);

  const startSolo = useCallback((name, team) => { localStorage.setItem("mendikot_name", name); send({type:"start_solo", name, team}); }, [send]);
  const createRoom = useCallback((name, team) => { localStorage.setItem("mendikot_name", name); send({type:"create_room", name, team}); }, [send]);
  const joinRoom = useCallback((name, roomId, team) => { localStorage.setItem("mendikot_name", name); send({type:"join_room", name, room_id:roomId, team}); }, [send]);
  const startGame = useCallback(() => { send({type:"start_game"}); }, [send]);
  const playCard = useCallback((cardId) => { send({type:"play_card", card_id:cardId}); }, [send]);
  const rematch = useCallback(() => { send({type:"rematch"}); }, [send]);
  const exitGame = useCallback(() => { send({type:"exit"}); sessionStorage.removeItem("mendikot_room"); setGameState(null); setRoomState(null); setView("menu"); }, [send]);

  if (view === "menu") {
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "menu-title" }, "MENDIKOT"),
        React.createElement("div", { className: "menu-sub" }, "The Classic Indian Card Game"),
        React.createElement("button", { className: "menu-btn primary", onClick: () => setView("solo-setup") }, "Solo vs Bots"),
        React.createElement("button", { className: "menu-btn secondary", onClick: () => setView("hub") }, "Play with Friends")
      )
    );
  }

  if (view === "solo-setup") {
    const [name, setName] = useState(playerName);
    const [team, setTeam] = useState("A");
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "form-card" },
          React.createElement("div", { className: "form-title" }, "Solo Setup"),
          React.createElement("div", { className: "input-group" },
            React.createElement("label", null, "Your Name"),
            React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
          ),
          React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
          React.createElement("div", { className: "team-select" },
            React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
            React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
          ),
          React.createElement("div", { className: "form-actions" },
            React.createElement("button", { className: "btn-back", onClick: () => setView("menu") }, "Back"),
            React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim()) startSolo(name.trim(), team); } }, "Start Game")
          )
        )
      )
    );
  }

  if (view === "hub") {
    const [name, setName] = useState(playerName);
    const [roomId, setRoomId] = useState("");
    const [subView, setSubView] = useState("choice");
    const [team, setTeam] = useState("A");
    if (subView === "choice") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card", style: {textAlign:"center"} },
            React.createElement("div", { className: "form-title" }, "Play with Friends"),
            React.createElement("button", { className: "menu-btn primary", style: {width:"100%",margin:"12px 0"}, onClick: () => setSubView("create") }, "Create Room"),
            React.createElement("button", { className: "menu-btn secondary", style: {width:"100%",margin:"4px 0"}, onClick: () => setSubView("join") }, "Join Room"),
            React.createElement("button", { className: "btn-back", style: {width:"100%",marginTop:16,padding:10}, onClick: () => setView("menu") }, "Back")
          )
        )
      );
    }
    if (subView === "create") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card" },
            React.createElement("div", { className: "form-title" }, "Create Room"),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Your Name"),
              React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
            ),
            React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
            React.createElement("div", { className: "team-select" },
              React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
              React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
            ),
            React.createElement("div", { className: "form-actions" },
              React.createElement("button", { className: "btn-back", onClick: () => setSubView("choice") }, "Back"),
              React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim()) createRoom(name.trim(), team); } }, "Create")
            )
          )
        )
      );
    }
    if (subView === "join") {
      return React.createElement("div", { className: "app" },
        React.createElement("div", { className: "view" },
          React.createElement("div", { className: "form-card" },
            React.createElement("div", { className: "form-title" }, "Join Room"),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Your Name"),
              React.createElement("input", { value: name, onChange: e => setName(e.target.value), placeholder: "Enter name", maxLength: 12 })
            ),
            React.createElement("div", { className: "input-group" },
              React.createElement("label", null, "Room Code"),
              React.createElement("input", { value: roomId, onChange: e => setRoomId(e.target.value.toUpperCase()), placeholder: "Enter code", maxLength: 6 })
            ),
            React.createElement("label", { style: {fontSize:"0.85rem",color:"rgba(255,255,255,0.7)",marginBottom:"8px",display:"block"} }, "Choose Team"),
            React.createElement("div", { className: "team-select" },
              React.createElement("div", { className: `team-option team-a ${team==="A"?"active":""}`, onClick: () => setTeam("A") }, "Team A"),
              React.createElement("div", { className: `team-option team-b ${team==="B"?"active":""}`, onClick: () => setTeam("B") }, "Team B")
            ),
            React.createElement("div", { className: "form-actions" },
              React.createElement("button", { className: "btn-back", onClick: () => setSubView("choice") }, "Back"),
              React.createElement("button", { className: "btn-submit", onClick: () => { if(name.trim() && roomId.trim()) joinRoom(name.trim(), roomId.trim(), team); } }, "Join")
            )
          )
        )
      );
    }
  }

  if (view === "lobby" && roomState) {
    const isHost = roomState.seats[0] && roomState.seats[0].is_host;
    const allFilled = roomState.seats.every(s => s.filled);
    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "view" },
        React.createElement("div", { className: "form-title" }, "Room Lobby"),
        React.createElement("div", { className: "room-code" }, roomState.room_id),
        React.createElement("div", { className: "seats-grid" },
          roomState.seats.map((s, i) =>
            React.createElement("div", { key: i, className: `seat ${s.filled ? "filled" : ""}` },
              React.createElement("div", { className: "seat-name" }, s.filled ? s.name : "Open"),
              React.createElement("div", { className: "seat-team" }, `Team ${s.team}`),
              React.createElement("div", { className: `seat-status ${s.is_host ? "status-host" : "status-waiting"}` }, s.is_host ? "Host" : (s.filled ? "Ready" : "Waiting"))
            )
          )
        ),
        isHost && React.createElement("button", { className: "start-btn", disabled: !allFilled, onClick: startGame }, "Start Game"),
        !isHost && React.createElement("div", { style: {color:"rgba(255,255,255,0.6)",fontSize:"0.9rem"} }, "Waiting for host..."),
        React.createElement("button", { className: "btn-back", style: {marginTop:16,padding:"10px 20px"}, onClick: exitGame }, "Leave")
      )
    );
  }

  if (view === "game" && gameState) {
    const mySeat = gameState.players.find(p => p.hand !== null)?.seat ?? 0;
    const me = gameState.players.find(p => p.seat === mySeat);
    const hand = me?.hand || [];
    const legal = gameState.turn === mySeat && !gameState.paused && !gameState.handComplete ? hand.map(() => true) : hand.map(() => false);
    const needsReveal = gameState.turn === mySeat && !gameState.trump_suit && gameState.phase === "phase1" && gameState.trick.length > 0;
    const seatPositions = ["bottom","left","top","right"];
    const handCount = hand.length;
    const overlap = handCount > 6 ? -(Math.min(28, (handCount-6)*4)) : 0;

    return React.createElement("div", { className: "app" },
      React.createElement("div", { className: "game-view" },
        React.createElement("button", { className: "exit-btn", onClick: () => setConfirmExit(true) }, "×"),
        React.createElement("div", { className: "trick-counter" }, `Trick ${Math.min(gameState.trick_number,13)} / 13`),

        React.createElement("div", { className: "score-cluster" },
          React.createElement("div", { className: "score-side" },
            React.createElement("span", { className: "score-label" }, "Team A"),
            React.createElement("span", { className: "score-number score-team-a" }, gameState.scores.A),
            React.createElement("div", { className: "mendi-strip" },
              gameState.mendi.A.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
            )
          ),
          React.createElement("div", { className: "trump-slot" },
            React.createElement("span", { className: "trump-label" }, "Trump"),
            gameState.trump_suit
              ? React.createElement("div", { className: "trump-card-mini", style: {color: SUIT_COLORS[gameState.trump_suit]==="red"?"#c41e3a":"#1a1a1a"} }, gameState.players[0].hand ? gameState.players[0].hand.find(h=>h.suit===gameState.trump_suit)?.symbol || SUIT_SYMBOLS[gameState.trump_suit] : SUIT_SYMBOLS[gameState.trump_suit])
              : React.createElement("div", { className: "trump-unknown" }, "?")
          ),
          React.createElement("div", { className: "score-side" },
            React.createElement("span", { className: "score-label" }, "Team B"),
            React.createElement("span", { className: "score-number score-team-b" }, gameState.scores.B),
            React.createElement("div", { className: "mendi-strip" },
              gameState.mendi.B.map((c,i) => React.createElement("div", { key: i, className: "mendi-mini", style: {color: SUIT_COLORS[c.suit]==="red"?"#c41e3a":"#1a1a1a"} }, c.symbol))
            )
          )
        ),

        React.createElement("div", { className: "table-felt" },
          React.createElement("div", { className: "felt-ellipse" }),
          [2,1,3,0].map(seat => {
            const pos = seatPositions[seat];
            const isActive = gameState.turn === seat && !gameState.paused && !gameState.handComplete;
            const isDealer = gameState.dealer === seat;
            const pl = gameState.players.find(p => p.seat === seat);
            return React.createElement("div", { key: seat, className: `seat-marker ${pos} ${isActive ? "active" : ""}` },
              React.createElement("div", { style: {position:"relative"} },
                React.createElement("div", { className: "seat-avatar" }, seat === mySeat ? "👤" : "🤖"),
                isDealer && React.createElement("div", { className: "dealer-chip", style: {top:-4,right:-4} }, "D")
              ),
              React.createElement("div", { className: "seat-name-tag", style: {color: pl?.team==="A"?"#6bb5ff":"#ff8a8a"} }, pl?.name || ""),
              seat !== mySeat && React.createElement("div", { className: "bot-badge" }, pl?.is_bot ? "BOT" : ""),
              React.createElement("div", { style: {fontSize:"0.65rem",opacity:0.5,marginTop:2} }, `${pl?.hand_count || 0} cards`)
            );
          }),
          React.createElement("div", { className: "trick-center" },
            gameState.trick.map((t, i) => {
              const pos = (t.seat + 4 - mySeat) % 4;
              return React.createElement("div", { key: t.card.id, className: `trick-card-wrapper pos-${pos}` },
                React.createElement(Card, { card: t.card }),
                t.is_reveal && React.createElement("div", { style: {position:"absolute",top:-20,left:"50%",transform:"translateX(-50%)",background:"var(--accent-gold)",color:"#1a1a1a",padding:"2px 8px",borderRadius:"10px",fontSize:"0.65rem",fontWeight:"800",whiteSpace:"nowrap"} }, "TRUMP!")
              );
            })
          ),
          gameState.paused && React.createElement("div", { className: "pause-indicator" }, "Collecting trick...")
        ),

        needsReveal && React.createElement("button", { className: "reveal-btn", onClick: () => playCard(hand[0]?.id) }, "Reveal Trump (lowest card)"),

        React.createElement("div", { className: "hand-strip" },
          hand.map((card, i) =>
            React.createElement("div", { key: card.id, className: "hand-card-wrapper", style: {marginLeft: i>0 ? `${overlap}px` : 0, zIndex: i} },
              React.createElement(Card, { card, disabled: !legal[i] || gameState.paused || gameState.handComplete, onClick: () => playCard(card.id) })
            )
          )
        )
      ),

      showTrumpFlash && React.createElement(TrumpFlash, { suit: flashSuit, symbol: flashSymbol, onDone: () => setShowTrumpFlash(false) }),
      gameState.hand_complete && React.createElement(ResultOverlay, { result: gameState.result, scores: gameState.scores, mendi: gameState.mendi, onRematch: rematch, onExit: exitGame }),
      confirmExit && React.createElement(ConfirmExit, { onConfirm: exitGame, onCancel: () => setConfirmExit(false) }),
      React.createElement(ToastContainer, { toasts })
    );
  }

  return null;
}

const root = ReactDOM.createRoot(document.getElementById("root"));
root.render(React.createElement(App));
</script>
</body>
</html>
"""

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)
