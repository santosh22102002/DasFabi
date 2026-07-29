import asyncio
import json
import random
import time
import uuid
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse

# --- GAME ENGINE & DATACLASSES ---

SUITS = ['hearts', 'diamonds', 'clubs', 'spades']
RANKS = ['2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K', 'A']
RANK_VALUES = {r: i for i, r in enumerate(RANKS)}

@dataclass
class Card:
    suit: str
    rank: str
    
    def value(self):
        return RANK_VALUES[self.rank]
    
    def is_mendi(self):
        return self.rank == '10'

    def to_dict(self):
        return {"suit": self.suit, "rank": self.rank}

@dataclass
class Player:
    id: str
    name: str
    seat: int
    team: str
    is_bot: bool = False
    ws: Optional[WebSocket] = None
    hand: List[Card] = field(default_factory=list)

@dataclass
class Room:
    code: str
    players: Dict[str, Player] = field(default_factory=dict)
    state: str = "lobby"  # lobby, phase1, playing, finished
    trump_suit: Optional[str] = None
    deck: List[Card] = field(default_factory=list)
    current_trick: List[Dict[str, Any]] = field(default_factory=list)
    turn_seat: int = 0
    mendi_team_a: int = 0
    mendi_team_b: int = 0
    last_active: float = field(default_factory=time.time)
    
    def get_seat(self, seat_idx: int) -> Optional[Player]:
        for p in self.players.values():
            if p.seat == seat_idx:
                return p
        return None

class RoomManager:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}

    def create_room(self) -> Room:
        code = str(uuid.uuid4())[:6].upper()
        room = Room(code=code)
        self.rooms[code] = room
        return room

    def get_room(self, code: str) -> Optional[Room]:
        return self.rooms.get(code)

    def remove_room(self, code: str):
        if code in self.rooms:
            del self.rooms[code]

manager = RoomManager()

# --- FASTAPI APP ---

app = FastAPI()

@app.on_event("startup")
async def startup_event():
    async def gc_loop():
        while True:
            now = time.time()
            expired = [code for code, room in manager.rooms.items() if now - room.last_active > 600]
            for code in expired:
                manager.remove_room(code)
            await asyncio.sleep(60)
    asyncio.create_task(gc_loop())

# --- WEBSOCKET HANDLER ---

async def broadcast_room_state(room: Room):
    state_msg = {
        "type": "room_state",
        "state": room.state,
        "code": room.code,
        "trump_suit": room.trump_suit,
        "turn_seat": room.turn_seat,
        "mendi_team_a": room.mendi_team_a,
        "mendi_team_b": room.mendi_team_b,
        "current_trick": room.current_trick,
        "players": [
            {
                "id": p.id,
                "name": p.name,
                "seat": p.seat,
                "team": p.team,
                "is_bot": p.is_bot,
                "card_count": len(p.hand)
            } for p in sorted(room.players.values(), key=lambda x: x.seat)
        ]
    }
    
    for p in room.players.values():
        if not p.is_bot and p.ws:
            personal_msg = state_msg.copy()
            personal_msg["hand"] = [c.to_dict() for c in p.hand]
            try:
                await p.ws.send_json(personal_msg)
            except Exception:
                pass

async def bot_turn_handler(room: Room):
    if room.state not in ["phase1", "playing"]:
        return
        
    current_player = room.get_seat(room.turn_seat)
    if current_player and current_player.is_bot:
        await asyncio.sleep(1.5)  # Artificial bot thinking delay
        
        if not current_player.hand:
            return
            
        # Bot logic: play lowest legal card
        card_to_play = current_player.hand.pop(0) 
        room.current_trick.append({
            "seat": current_player.seat,
            "card": card_to_play.to_dict()
        })
        
        room.turn_seat = (room.turn_seat + 1) % 4
        await broadcast_room_state(room)
        
        if len(room.current_trick) == 4:
            await resolve_trick(room)

async def resolve_trick(room: Room):
    await asyncio.sleep(3) # 3 second trick resolution pause
    # Mendi tally logic placeholder
    for play in room.current_trick:
        if play["card"]["rank"] == "10":
            room.mendi_team_a += 1 # Simplified scoring for demo
    
    room.current_trick = []
    
    if len(room.deck) > 0 and room.trump_suit:
        # Phase 2 boot dealing
        for p in room.players.values():
            for _ in range(8):
                if room.deck:
                    p.hand.append(room.deck.pop())
        room.state = "playing"

    await broadcast_room_state(room)
    await bot_turn_handler(room)

@app.websocket("/ws")
async def websocket_endpoint(ws: WebSocket):
    await ws.accept()
    player_id = str(uuid.uuid4())
    current_room_code = None

    try:
        while True:
            data = await ws.receive_text()
            msg = json.loads(data)
            action = msg.get("action")
            
            if action == "solo_mode":
                room = manager.create_room()
                current_room_code = room.code
                
                # Human player
                p = Player(id=player_id, name="You", seat=0, team="A", ws=ws)
                room.players[player_id] = p
                
                # 3 Bots
                b1 = Player(id=str(uuid.uuid4()), name="Bot 1", seat=1, team="B", is_bot=True)
                b2 = Player(id=str(uuid.uuid4()), name="Bot 2", seat=2, team="A", is_bot=True)
                b3 = Player(id=str(uuid.uuid4()), name="Bot 3", seat=3, team="B", is_bot=True)
                room.players[b1.id] = b1
                room.players[b2.id] = b2
                room.players[b3.id] = b3
                
                room.deck = [Card(s, r) for s in SUITS for r in RANKS]
                random.shuffle(room.deck)
                
                # Phase 1 deal (5 cards)
                for player in room.players.values():
                    player.hand = [room.deck.pop() for _ in range(5)]
                
                room.state = "phase1"
                room.last_active = time.time()
                await broadcast_room_state(room)

            elif action == "play_card" and current_room_code:
                room = manager.get_room(current_room_code)
                if room and room.turn_seat == room.players[player_id].seat:
                    card_data = msg.get("card")
                    p = room.players[player_id]
                    
                    # Remove card from hand
                    p.hand = [c for c in p.hand if not (c.suit == card_data["suit"] and c.rank == card_data["rank"])]
                    
                    room.current_trick.append({
                        "seat": p.seat,
                        "card": card_data
                    })
                    
                    room.turn_seat = (room.turn_seat + 1) % 4
                    room.last_active = time.time()
                    await broadcast_room_state(room)
                    
                    if len(room.current_trick) == 4:
                        asyncio.create_task(resolve_trick(room))
                    else:
                        asyncio.create_task(bot_turn_handler(room))

            elif action == "reveal_trump" and current_room_code:
                room = manager.get_room(current_room_code)
                if room:
                    room.trump_suit = msg.get("suit")
                    room.last_active = time.time()
                    # Trigger TrumpFlash animation state broadcast
                    await broadcast_room_state(room)

    except WebSocketDisconnect:
        if current_room_code:
            room = manager.get_room(current_room_code)
            if room:
                room.state = "cancelled"
                manager.remove_room(current_room_code)

# --- FRONTEND (REACT + BABEL + CSS) ---

FRONTEND_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
    <title>Mendikot Web</title>
    <!-- React & Babel -->
    <script src="https://unpkg.com/react@18/umd/react.production.min.js" crossorigin></script>
    <script src="https://unpkg.com/react-dom@18/umd/react-dom.production.min.js" crossorigin></script>
    <script src="https://unpkg.com/@babel/standalone/babel.min.js"></script>
    
    <style>
        :root {
            --poker-green: #0a5c27;
            --felt-dark: #07471d;
            --gold: #f4d03f;
        }
        
        * { box-sizing: border-box; margin: 0; padding: 0; user-select: none; }
        
        body, html {
            height: 100%;
            background-color: var(--poker-green);
            background-image: radial-gradient(circle, var(--poker-green), var(--felt-dark));
            font-family: -apple-system, system-ui, sans-serif;
            color: white;
            overflow: hidden;
        }

        #root {
            height: 100%;
            display: flex;
            flex-direction: column;
        }

        /* Views */
        .menu-view {
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            height: 100%;
            gap: 20px;
        }

        .btn {
            background: #fff;
            color: var(--felt-dark);
            border: none;
            padding: 15px 30px;
            font-size: 1.2rem;
            font-weight: bold;
            border-radius: 8px;
            cursor: pointer;
            box-shadow: 0 4px 6px rgba(0,0,0,0.3);
            transition: transform 0.1s;
        }
        
        .btn:active { transform: scale(0.95); }

        /* Game Layout */
        .score-cluster {
            padding: 10px;
            background: rgba(0,0,0,0.3);
            display: flex;
            justify-content: space-between;
            align-items: center;
            z-index: 10;
        }

        .table-felt {
            flex: 1;
            position: relative;
            display: flex;
            align-items: center;
            justify-content: center;
        }

        .hand-strip {
            height: 120px;
            background: rgba(0,0,0,0.4);
            display: flex;
            justify-content: center;
            align-items: flex-end;
            padding-bottom: 10px;
            gap: -20px;
            z-index: 10;
        }

        /* Cards */
        .card {
            width: 70px;
            height: 100px;
            background: white;
            border-radius: 8px;
            color: black;
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            font-size: 1.5rem;
            font-weight: bold;
            box-shadow: 0 2px 5px rgba(0,0,0,0.4);
            position: relative;
            cursor: pointer;
            transition: transform 0.3s cubic-bezier(0.175, 0.885, 0.32, 1.275);
            margin: 0 -15px; 
        }

        .card:hover { transform: translateY(-15px); }
        .card.red { color: #d32f2f; }
        .card.black { color: #212121; }
        
        /* Table Layout for players */
        .seat-marker {
            position: absolute;
            background: rgba(0,0,0,0.5);
            padding: 5px 15px;
            border-radius: 20px;
            font-size: 0.9rem;
        }
        .seat-top { top: 20px; }
        .seat-left { left: 20px; transform: rotate(90deg); }
        .seat-right { right: 20px; transform: rotate(-90deg); }
        .active-turn { box-shadow: 0 0 10px 2px var(--gold); border: 2px solid var(--gold); }

        .trick-center {
            position: relative;
            width: 150px;
            height: 150px;
        }
        .trick-card {
            position: absolute;
            top: 25px; left: 40px;
            animation: cardPopIn 0.3s ease forwards;
        }

        /* Animations */
        @keyframes cardPopIn {
            0% { transform: scale(0) rotate(-20deg); opacity: 0; }
            100% { transform: scale(1) rotate(0deg); opacity: 1; }
        }

        @keyframes trumpFlashAnim {
            0% { background: rgba(255, 215, 0, 0); }
            50% { background: rgba(255, 215, 0, 0.4); }
            100% { background: rgba(255, 215, 0, 0); }
        }

        .trump-flash {
            position: absolute;
            inset: 0;
            pointer-events: none;
            z-index: 100;
        }
        .flash-active {
            animation: trumpFlashAnim 1s ease-out forwards;
        }
    </style>
</head>
<body>
    <div id="root"></div>

    <script type="text/babel">
        const { useState, useEffect, useRef } = React;

        const SUIT_SYMBOLS = { 'hearts': '♥', 'diamonds': '♦', 'clubs': '♣', 'spades': '♠' };

        const Card = ({ suit, rank, onClick }) => {
            const isRed = suit === 'hearts' || suit === 'diamonds';
            return (
                <div className={`card ${isRed ? 'red' : 'black'}`} onClick={onClick}>
                    <div style={{ position: 'absolute', top: 5, left: 5, fontSize: '1rem' }}>{rank}</div>
                    <div style={{ fontSize: '2rem' }}>{SUIT_SYMBOLS[suit]}</div>
                    <div style={{ position: 'absolute', bottom: 5, right: 5, fontSize: '1rem', transform: 'rotate(180deg)' }}>{rank}</div>
                </div>
            );
        };

        const App = () => {
            const [view, setView] = useState("menu");
            const [gameState, setGameState] = useState(null);
            const [ws, setWs] = useState(null);
            const [flash, setFlash] = useState(false);

            useEffect(() => {
                const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
                const socket = new WebSocket(`${protocol}//${window.location.host}/ws`);
                
                socket.onmessage = (event) => {
                    const data = JSON.parse(event.data);
                    if (data.type === "room_state") {
                        if(gameState && data.trump_suit && !gameState.trump_suit) {
                            setFlash(true);
                            setTimeout(() => setFlash(false), 1000);
                        }
                        setGameState(data);
                        if(data.state !== "cancelled") setView("game");
                    }
                };

                setWs(socket);
                return () => socket.close();
            }, []);

            const startSolo = () => {
                if (ws) ws.send(JSON.stringify({ action: "solo_mode" }));
            };

            const playCard = (card) => {
                if (ws && gameState.turn_seat === gameState.players.find(p => p.id === gameState.players[0].id).seat) {
                     ws.send(JSON.stringify({ action: "play_card", card }));
                }
            };

            if (view === "menu") {
                return (
                    <div className="menu-view">
                        <h1 style={{ fontSize: '3rem', color: 'var(--gold)', marginBottom: '40px', textShadow: '2px 2px 4px #000' }}>
                            Mendikot
                        </h1>
                        <button className="btn" onClick={startSolo}>Play Solo (Bots)</button>
                        <button className="btn" onClick={() => alert("Multiplayer UI disabled in simple demo")}>Play with Friends</button>
                    </div>
                );
            }

            if (!gameState) return <div>Loading...</div>;

            const mySeat = gameState.players.find(p => !p.is_bot)?.seat || 0;
            const topSeat = (mySeat + 2) % 4;
            const leftSeat = (mySeat + 1) % 4;
            const rightSeat = (mySeat + 3) % 4;

            const getPlayerInfo = (seatIndex) => gameState.players.find(p => p.seat === seatIndex);

            return (
                <div style={{ height: '100%', display: 'flex', flexDirection: 'column' }}>
                    <div className={`trump-flash ${flash ? 'flash-active' : ''}`}></div>
                    
                    {/* Score Cluster */}
                    <div className="score-cluster">
                        <div>Team A Mendi: {gameState.mendi_team_a}</div>
                        <div style={{ color: 'var(--gold)', fontWeight: 'bold' }}>
                            Trump: {gameState.trump_suit ? SUIT_SYMBOLS[gameState.trump_suit] : "?"}
                        </div>
                        <div>Team B Mendi: {gameState.mendi_team_b}</div>
                    </div>

                    {/* Table Felt */}
                    <div className="table-felt">
                        {getPlayerInfo(topSeat) && (
                            <div className={`seat-marker seat-top ${gameState.turn_seat === topSeat ? 'active-turn' : ''}`}>
                                {getPlayerInfo(topSeat).name} ({getPlayerInfo(topSeat).card_count})
                            </div>
                        )}
                        {getPlayerInfo(leftSeat) && (
                            <div className={`seat-marker seat-left ${gameState.turn_seat === leftSeat ? 'active-turn' : ''}`}>
                                {getPlayerInfo(leftSeat).name} ({getPlayerInfo(leftSeat).card_count})
                            </div>
                        )}
                        {getPlayerInfo(rightSeat) && (
                            <div className={`seat-marker seat-right ${gameState.turn_seat === rightSeat ? 'active-turn' : ''}`}>
                                {getPlayerInfo(rightSeat).name} ({getPlayerInfo(rightSeat).card_count})
                            </div>
                        )}
                        
                        <div className="trick-center">
                            {gameState.current_trick.map((play, idx) => {
                                // Calculate offset based on seat relative to player to make it look like they played it
                                let x = 0, y = 0;
                                if(play.seat === leftSeat) { x = -40; y = 0; }
                                if(play.seat === rightSeat) { x = 40; y = 0; }
                                if(play.seat === topSeat) { x = 0; y = -40; }
                                if(play.seat === mySeat) { x = 0; y = 40; }
                                
                                return (
                                    <div key={idx} className="trick-card" style={{ transform: `translate(${x}px, ${y}px)` }}>
                                        <Card suit={play.card.suit} rank={play.card.rank} />
                                    </div>
                                )
                            })}
                        </div>
                    </div>

                    {/* Hand Strip */}
                    <div className="hand-strip">
                        {gameState.hand?.map((c, i) => (
                            <Card key={i} suit={c.suit} rank={c.rank} onClick={() => playCard(c)} />
                        ))}
                    </div>
                </div>
            );
        };

        const root = ReactDOM.createRoot(document.getElementById('root'));
        root.render(<App />);
    </script>
</body>
</html>
"""

@app.get("/")
async def get_index():
    return HTMLResponse(content=FRONTEND_HTML, status_code=200)
