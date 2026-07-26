#!/usr/bin/env python3
"""
Mendikot - Classic Indian Card Game
Run: python main.py   then open http://localhost:8000
Requires: pip install fastapi uvicorn
"""
import asyncio, json, random, uuid
from typing import Dict, List, Optional
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
import uvicorn

# ════ GAME ENGINE ════
SUITS = ['S','H','D','C']
SNAME = {'S':'Spades','H':'Hearts','D':'Diamonds','C':'Clubs'}

def make_deck():
    return [{'s':s,'r':r} for s in SUITS for r in range(2,15)]

def shuf(d):
    x=d[:]; random.shuffle(x); return x

def ckey(c): return f"{c['r']}{c['s']}"

def valid_plays(hand, led, trump, ph1, tout):
    if not led: return [dict(**c,mr=False) for c in hand]
    can = any(c['s']==led for c in hand)
    if can: return [dict(**c,mr=False) for c in hand if c['s']==led]
    if ph1 and not tout: return [dict(**c,mr=True) for c in hand]
    return [dict(**c,mr=False) for c in hand]

def trick_win(tcs, led, trump):
    best=tcs[0]
    for cur in tcs[1:]:
        if trump:
            cb=best['c']['s']==trump; cc=cur['c']['s']==trump
            if cc and not cb: best=cur; continue
            if cc and cb:
                if cur['c']['r']>best['c']['r']: best=cur; continue
            if not cc and not cb:
                if cur['c']['s']==led and (best['c']['s']!=led or cur['c']['r']>best['c']['r']): best=cur
        else:
            if cur['c']['s']==led and (best['c']['s']!=led or cur['c']['r']>best['c']['r']): best=cur
    return best['seat']

class Game:
    def __init__(self, players):
        self.players=players
        deck=shuf(make_deck())
        self.hands=[deck[i*5:(i+1)*5] for i in range(4)]
        self.boot=deck[20:]
        self.ph1=True; self.trump=None; self.tout=False
        self.trick={'cards':[],'led':None}
        self.tnum=0; self.boot_dealt=False; self.paused=False
        self.whose=1; self.taken=[[],[],[],[]]; self.team_mn=[0,0]; self.seat_mn=[0,0,0,0]; self.done=False

    def _mn_suits(self):
        res={'A':[],'B':[]}
        for seat,tricks in enumerate(self.taken):
            team='A' if self.players[seat]['team']=='A' else 'B'
            for trick in tricks:
                for c in trick:
                    if c['r']==10: res[team].append(c['s'])
        return res

    def state(self, seat=0):
        ts=self.trump['s'] if self.tout else None
        vp=[]
        if self.whose==seat and not self.paused and not self.done:
            vp=valid_plays(self.hands[seat],self.trick['led'],ts,self.ph1,self.tout)
        return {
            'players':self.players,'hand':self.hands[seat],'trick':self.trick,
            'tout':self.tout,'trump':self.trump if self.tout else None,
            'whose':self.whose,'tnum':self.tnum,'ph1':self.ph1,'paused':self.paused,
            'team_mn':self.team_mn,'opp_sizes':[len(self.hands[s]) for s in range(4)],
            'vplays':vp,'must_reveal':bool(vp and all(c['mr'] for c in vp)),
            'mendi_suits':self._mn_suits(),'done':self.done,
        }

    def play(self, seat, card, reveal=False):
        evts=[]
        if not reveal and not self.tout and self.ph1 and self.trick['led']:
            if not any(c['s']==self.trick['led'] for c in self.hands[seat]): reveal=True
        if reveal and not self.tout:
            self.trump={'s':card['s'],'c':card,'by':seat,'by_name':self.players[seat]['name']}
            self.tout=True; evts.append('trump_revealed')
        self.hands[seat]=[c for c in self.hands[seat] if ckey(c)!=ckey(card)]
        if not self.trick['led']: self.trick['led']=card['s']
        self.trick['cards'].append({'seat':seat,'c':card})
        if len(self.trick['cards'])==4: evts.append('trick_complete')
        return evts

    def resolve(self):
        evts=[]; ts=self.trump['s'] if self.tout else None
        ws=trick_win(self.trick['cards'],self.trick['led'],ts)
        tc=[x['c'] for x in self.trick['cards']]; self.taken[ws].append(tc)
        nm=sum(1 for c in tc if c['r']==10)
        if nm:
            self.seat_mn[ws]+=nm; self.team_mn[0]=self.seat_mn[0]+self.seat_mn[2]; self.team_mn[1]=self.seat_mn[1]+self.seat_mn[3]
            evts.append(f"mendi:{self.players[ws]['name']}:{nm}")
        self.tnum+=1
        nb=not self.boot_dealt and ((self.tout and self.ph1) or (self.ph1 and self.tnum==5))
        if nb:
            self.boot_dealt=True; self.ph1=False
            boot=shuf(self.boot)
            for i in range(4): self.hands[i].extend(boot[i*8:(i+1)*8])
            self.boot=[]; evts.append('boot_dealt')
        if self.tnum==13:
            self.done=True; evts.append('game_done'); return ws,evts
        self.trick={'cards':[],'led':None}; self.paused=False; self.whose=ws
        return ws,evts

    def bot_card(self, seat):
        ts=self.trump['s'] if self.tout else None
        vp=valid_plays(self.hands[seat],self.trick['led'],ts,self.ph1,self.tout)
        if not vp: return None,False
        mr=all(c['mr'] for c in vp)
        ch=min(vp,key=lambda c:c['r'])
        return {'s':ch['s'],'r':ch['r']},mr

HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no">
<title>Mendikot - Classic Indian Card Game</title>
<meta name="description" content="Play Mendikot - the classic 4-player Indian card game. Capture the four 10s to win!">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700;900&family=Inter:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
:root{--g0:#030f06;--g1:#0a2b14;--g2:#10431f;--g3:#1a6b35;--gold:#d4af37;--gold2:#f5d86e;--gold3:#a07c1e;--red:#c0392b;--dark:#1a1a2e;--txt:#f0e6d3;--muted:rgba(240,230,211,.6);--bdr:rgba(212,175,55,.22);--bdrS:rgba(212,175,55,.6);--panel:rgba(6,20,10,.94);--glass:rgba(14,60,30,.5);--sh1:0 4px 14px rgba(0,0,0,.55);--sh2:0 10px 32px rgba(0,0,0,.65);--sh3:0 20px 56px rgba(0,0,0,.8);--r1:8px;--r2:12px;--r3:20px;--rc:9px;--tf:140ms ease;--tm:280ms cubic-bezier(.4,0,.2,1);--ts:500ms cubic-bezier(.34,1.56,.64,1)}
*,*::before,*::after{box-sizing:border-box;margin:0;padding:0;-webkit-tap-highlight-color:transparent}
html,body{height:100%;overflow:hidden;font-family:'Inter',sans-serif;background:var(--g0);color:var(--txt);user-select:none;-webkit-user-select:none}
body{background:radial-gradient(ellipse 110% 55% at 50% 0%,rgba(39,174,96,.1),transparent 68%),radial-gradient(ellipse 70% 70% at 50% 105%,rgba(0,0,0,.5),transparent 68%),linear-gradient(175deg,#051209,#0a2b14 45%,#07200f)}
body::after{content:'';position:fixed;inset:0;pointer-events:none;z-index:0;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='200' height='200'%3E%3Cfilter id='n'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='.9' numOctaves='4' stitchTiles='stitch'/%3E%3C/filter%3E%3Crect width='200' height='200' filter='url(%23n)' opacity='.04'/%3E%3C/svg%3E")}
#app{position:relative;z-index:1;height:100%;display:flex;flex-direction:column}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:.55rem;padding:.85rem 1.6rem;border:none;border-radius:var(--r2);font-family:'Inter',sans-serif;font-size:.93rem;font-weight:600;cursor:pointer;transition:all var(--tm);position:relative;overflow:hidden;letter-spacing:.03em}
.btn:active{transform:scale(.96)}
.btn-gold{background:linear-gradient(135deg,var(--gold2),var(--gold) 50%,var(--gold3));color:#180700;font-weight:700;box-shadow:0 4px 22px rgba(212,175,55,.35)}
.btn-gold:hover{transform:translateY(-2px);box-shadow:0 8px 36px rgba(212,175,55,.55)}
.btn-ghost{background:var(--glass);color:var(--txt);border:1px solid var(--bdr);backdrop-filter:blur(10px)}
.btn-ghost:hover{background:rgba(39,174,96,.22);border-color:var(--bdrS);transform:translateY(-2px)}
.btn-w{width:100%}.btn-sm{padding:.52rem 1.1rem;font-size:.8rem;border-radius:var(--r1)}
.btn-ico{width:20px;height:20px;flex-shrink:0;fill:none;stroke:currentColor;stroke-width:2}
.back-btn{display:inline-flex;align-items:center;gap:.4rem;background:rgba(0,0,0,.25);border:1px solid var(--bdr);border-radius:var(--r1);padding:.38rem .8rem;color:var(--muted);font-size:.78rem;font-weight:600;cursor:pointer;transition:all var(--tf)}.back-btn:hover{color:var(--txt)}
.flbl{display:block;font-size:.7rem;font-weight:700;letter-spacing:.1em;text-transform:uppercase;color:var(--gold);margin-bottom:.32rem}
.finp{width:100%;padding:.7rem 1rem;background:rgba(0,0,0,.28);border:1px solid var(--bdr);border-radius:var(--r1);color:var(--txt);font-family:'Inter',sans-serif;font-size:.93rem;outline:none;transition:border-color var(--tf),box-shadow var(--tf)}
.finp:focus{border-color:var(--gold);box-shadow:0 0 0 3px rgba(212,175,55,.16)}.finp::placeholder{color:var(--muted)}
.menu-v{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center;padding:2rem 1.5rem;gap:1.6rem;overflow-y:auto}
.brand{display:flex;flex-direction:column;align-items:center;gap:.55rem}
.chip{width:86px;height:86px;border-radius:50%;background:conic-gradient(var(--gold) 0 36deg,var(--g0) 36deg 72deg,var(--gold) 72deg 108deg,var(--g0) 108deg 144deg,var(--gold) 144deg 180deg,var(--g0) 180deg 216deg,var(--gold) 216deg 252deg,var(--g0) 252deg 288deg,var(--gold) 288deg 324deg,var(--g0) 324deg 360deg);border:4px solid var(--gold);display:flex;align-items:center;justify-content:center;box-shadow:0 0 0 2px var(--g0),0 0 28px rgba(212,175,55,.45),var(--sh2);animation:chipSpin 28s linear infinite;flex-shrink:0}
.chip-in{width:56px;height:56px;border-radius:50%;background:var(--g0);border:3px solid var(--gold);display:flex;align-items:center;justify-content:center;font-family:'Playfair Display',serif;font-size:1.55rem;font-weight:900;color:var(--gold)}
@keyframes chipSpin{to{transform:rotate(360deg)}}
.brand-t{font-family:'Playfair Display',serif;font-size:clamp(2.6rem,11vw,4.2rem);font-weight:900;background:linear-gradient(135deg,var(--gold2),var(--gold) 50%,var(--gold3));-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;letter-spacing:.08em;line-height:1;animation:gPulse 4s ease-in-out infinite alternate}
@keyframes gPulse{from{filter:drop-shadow(0 0 8px rgba(212,175,55,.3))}to{filter:drop-shadow(0 0 22px rgba(212,175,55,.7))}}
.brand-s{font-size:.7rem;color:var(--muted);letter-spacing:.24em;text-transform:uppercase}
.card-fan{position:relative;width:158px;height:78px;flex-shrink:0}
.fc{position:absolute;bottom:0;width:46px;height:64px;border-radius:6px;background:#fff;box-shadow:var(--sh2);display:flex;align-items:center;justify-content:center;font-size:1.4rem;transform-origin:bottom center;transition:transform var(--tm)}
.fc:nth-child(1){left:0;transform:rotate(-22deg);z-index:1}.fc:nth-child(2){left:28px;transform:rotate(-11deg);z-index:2}.fc:nth-child(3){left:56px;transform:rotate(0);z-index:3}.fc:nth-child(4){left:84px;transform:rotate(11deg);z-index:2}.fc:nth-child(5){left:112px;transform:rotate(22deg);z-index:1}
.card-fan:hover .fc:nth-child(1){transform:rotate(-28deg) translateY(-8px)}.card-fan:hover .fc:nth-child(2){transform:rotate(-14deg) translateY(-11px)}.card-fan:hover .fc:nth-child(3){transform:rotate(0) translateY(-15px)}.card-fan:hover .fc:nth-child(4){transform:rotate(14deg) translateY(-11px)}.card-fan:hover .fc:nth-child(5){transform:rotate(28deg) translateY(-8px)}
.menu-form{width:100%;max-width:295px}.menu-btns{display:flex;flex-direction:column;gap:.7rem;width:100%;max-width:295px}
.hub-v{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center;padding:2rem 1.5rem;gap:1.75rem;position:relative}
.view-t{font-family:'Playfair Display',serif;font-size:clamp(1.5rem,7vw,2.1rem);color:var(--gold);text-align:center}
.hub-row{display:flex;gap:.9rem;width:100%;max-width:350px}
.hub-c{flex:1;background:var(--glass);border:1px solid var(--bdr);border-radius:var(--r3);padding:1.4rem .9rem;display:flex;flex-direction:column;align-items:center;gap:.7rem;cursor:pointer;transition:all var(--tm);backdrop-filter:blur(12px)}
.hub-c:hover{background:rgba(39,174,96,.2);border-color:var(--bdrS);transform:translateY(-5px);box-shadow:0 16px 48px rgba(0,0,0,.35)}
.hub-ico{width:52px;height:52px;border-radius:50%;background:rgba(212,175,55,.1);border:1px solid var(--bdr);display:flex;align-items:center;justify-content:center;color:var(--gold)}
.hub-ct{font-weight:700;font-size:.95rem;text-align:center}.hub-cd{font-size:.73rem;color:var(--muted);text-align:center}
.form-v{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center;padding:2rem 1.5rem;gap:1.4rem;position:relative}
.fpanel{width:100%;max-width:350px;background:var(--panel);border:1px solid var(--bdr);border-radius:var(--r3);padding:1.9rem 1.7rem;backdrop-filter:blur(20px);display:flex;flex-direction:column;gap:1.2rem}
.card{width:100%;height:100%;background:#fefefe;border-radius:var(--rc);border:1px solid #ddd;box-shadow:var(--sh1);display:flex;flex-direction:column;padding:3px;position:relative;cursor:default;transition:transform var(--tm),box-shadow var(--tm);will-change:transform}
.card.play{cursor:pointer}.card.play:hover{transform:translateY(-11px) scale(1.08);box-shadow:var(--sh3),0 0 0 2px rgba(212,175,55,.4);z-index:100}
.card.dis{opacity:.35;filter:saturate(.18);cursor:default}.card.istr{box-shadow:var(--sh1),0 0 14px rgba(212,175,55,.6)}.card.ismn{box-shadow:var(--sh1),0 0 10px rgba(212,175,55,.45)}
.card.red .cr,.card.red .cs{color:var(--red)}.card.black .cr,.card.black .cs{color:var(--dark)}
.cr{font-family:'Playfair Display',serif;font-weight:700;font-size:clamp(.5rem,1.8vw,.75rem);line-height:1.1;display:flex;flex-direction:column;align-items:flex-start}.cr .sm{font-size:.65em;line-height:1}
.crb{position:absolute;bottom:3px;right:3px;font-family:'Playfair Display',serif;font-weight:700;font-size:clamp(.5rem,1.8vw,.75rem);line-height:1.1;transform:rotate(180deg);display:flex;flex-direction:column;align-items:flex-start}.crb .sm{font-size:.65em;line-height:1}
.cs{flex:1;display:flex;align-items:center;justify-content:center;font-size:clamp(.9rem,3.2vw,1.35rem)}
.game-v{flex:1;display:flex;flex-direction:column;overflow:hidden;position:relative}
.sbar{background:rgba(2,8,4,.97);border-bottom:1px solid var(--bdr);padding:.42rem .8rem;display:flex;align-items:center;justify-content:space-between;gap:.45rem;flex-shrink:0;z-index:20}
.sside{display:flex;align-items:center;gap:.45rem;flex:1}.sside.r{justify-content:flex-end;flex-direction:row-reverse}
.slbl{font-size:.6rem;font-weight:700;letter-spacing:.1em;text-transform:uppercase;color:var(--muted)}
.mtrack{display:flex;gap:3px}
.mpip{width:clamp(22px,6vw,28px);height:clamp(31px,8.5vw,40px);background:rgba(0,0,0,.35);border:1px solid rgba(255,255,255,.07);border-radius:4px;display:flex;align-items:center;justify-content:center;font-size:clamp(.7rem,2.3vw,.95rem);transition:all var(--tm)}
.mpip.won{background:rgba(212,175,55,.13);border-color:rgba(212,175,55,.48);animation:pipPop var(--ts)}
@keyframes pipPop{0%{transform:scale(0) rotate(-20deg)}60%{transform:scale(1.25) rotate(5deg)}100%{transform:scale(1) rotate(0)}}
.mnum{font-family:'Playfair Display',serif;font-size:clamp(1rem,3.8vw,1.35rem);font-weight:900;color:var(--gold);min-width:22px;text-align:center;line-height:1}
.twrap{display:flex;flex-direction:column;align-items:center;gap:2px;flex-shrink:0}
.tlbl{font-size:.5rem;letter-spacing:.12em;text-transform:uppercase;color:var(--muted)}
.tmini{width:28px;height:40px;border-radius:4px;box-shadow:var(--sh1);position:relative;overflow:hidden;display:flex;align-items:center;justify-content:center}
.tmini.hid{background:linear-gradient(135deg,#0e3a1f,#051910);border:1px solid rgba(212,175,55,.28);animation:hidPulse 2.8s ease-in-out infinite}
.tmini.hid::after{content:'?';font-family:'Playfair Display',serif;font-size:1.05rem;font-weight:900;color:rgba(212,175,55,.55)}
@keyframes hidPulse{0%,100%{box-shadow:0 0 6px rgba(212,175,55,.18)}50%{box-shadow:0 0 14px rgba(212,175,55,.45)}}
.tmini.sho{background:#fefefe;border:1px solid #ddd;animation:tRevMini var(--ts)}
@keyframes tRevMini{0%{transform:scale(0) rotateY(90deg)}100%{transform:scale(1) rotateY(0)}}
.tface{display:flex;flex-direction:column;align-items:center;font-size:.52rem;font-weight:800;font-family:'Playfair Display',serif;line-height:1.1}.tface .ts{font-size:.88rem}
.felt{flex:1;position:relative;display:flex;align-items:center;justify-content:center;overflow:hidden;min-height:0}
.deco{position:absolute;font-size:5rem;opacity:.032;color:#fff;pointer-events:none;line-height:1}.deco.tl{top:4px;left:8px}.deco.tr{top:4px;right:8px}.deco.bl{bottom:4px;left:8px}.deco.br{bottom:4px;right:8px}
.seat{position:absolute;display:flex;flex-direction:column;align-items:center;gap:4px;transition:all var(--tm)}.seat.top{top:8px;left:50%;transform:translateX(-50%)}.seat.left{left:6px;top:50%;transform:translateY(-50%)}.seat.right{right:6px;top:50%;transform:translateY(-50%)}
.sav{width:clamp(40px,10.5vw,52px);height:clamp(40px,10.5vw,52px);border-radius:50%;background:linear-gradient(145deg,var(--g3),var(--g1));border:2px solid rgba(255,255,255,.1);display:flex;align-items:center;justify-content:center;font-weight:700;font-size:clamp(.82rem,2.8vw,1.05rem);color:#fff;box-shadow:var(--sh1);transition:all var(--tm);position:relative}
.sav.bot{background:linear-gradient(145deg,#2c3e50,#1a252f)}.sav.act{border-color:var(--gold);box-shadow:0 0 22px rgba(212,175,55,.55),var(--sh1);animation:pulseAct 1.8s ease-in-out infinite}
@keyframes pulseAct{0%,100%{box-shadow:0 0 18px rgba(212,175,55,.45),var(--sh1)}50%{box-shadow:0 0 34px rgba(212,175,55,.85),var(--sh1)}}
.thdot-wrap{position:absolute;bottom:-3px;right:-3px;width:17px;height:17px;background:var(--gold);border-radius:50%;border:2px solid var(--g0);display:flex;align-items:center;justify-content:center;gap:1.5px}
.td{width:2px;height:2px;background:#180700;border-radius:50%;animation:tdBnc .9s ease-in-out infinite}.td:nth-child(2){animation-delay:.18s}.td:nth-child(3){animation-delay:.36s}
@keyframes tdBnc{0%,80%,100%{transform:scaleY(1)}40%{transform:scaleY(1.9)}}
.snm{font-size:clamp(.58rem,1.9vw,.7rem);font-weight:600;color:var(--muted);white-space:nowrap;max-width:70px;overflow:hidden;text-overflow:ellipsis;text-align:center}
.sbadge{font-size:.56rem;font-weight:700;padding:1px 6px;border-radius:8px;text-transform:uppercase;letter-spacing:.06em}.sbadge.a{background:rgba(41,128,185,.22);color:#5dade2;border:1px solid rgba(41,128,185,.32)}.sbadge.b{background:rgba(192,57,43,.22);color:#e87;border:1px solid rgba(192,57,43,.32)}
.opips{display:flex;margin-top:2px}.opip{width:12px;height:18px;background:linear-gradient(135deg,#0e3a1f,#051910);border:1px solid rgba(212,175,55,.15);border-radius:2px;margin-left:-5px;box-shadow:1px 1px 3px rgba(0,0,0,.4)}.opip:first-child{margin-left:0}
.trickc{position:relative;width:min(205px,47vw);height:min(205px,47vw);display:flex;align-items:center;justify-content:center}
.tslot{position:absolute;width:min(56px,13vw);height:min(80px,18.5vw)}.tslot.T{top:0;left:50%;transform:translateX(-50%)}.tslot.B{bottom:0;left:50%;transform:translateX(-50%)}.tslot.L{left:0;top:50%;transform:translateY(-50%)}.tslot.R{right:0;top:50%;transform:translateY(-50%)}
.tsin{width:100%;height:100%;animation:cpIn .36s cubic-bezier(.4,0,.2,1) both}
@keyframes cpIn{from{transform:scale(1.4) translateY(-16px);opacity:0}to{transform:scale(1) translateY(0);opacity:1}}
.ppill{font-size:.58rem;font-weight:700;letter-spacing:.08em;text-transform:uppercase;padding:2px 9px;border-radius:8px;background:rgba(0,0,0,.44);border:1px solid var(--bdr);color:var(--muted)}
.tcnt{font-size:.6rem;color:var(--muted);background:rgba(0,0,0,.34);padding:2px 10px;border-radius:8px}
.finfo{position:absolute;display:flex;flex-direction:column;align-items:center;gap:4px}.finfo.tr{top:8px;right:8px}.finfo.bc{bottom:8px;left:50%;transform:translateX(-50%)}
.turn-b{position:absolute;left:50%;transform:translateX(-50%);font-size:.72rem;font-weight:600;color:var(--gold);background:rgba(0,0,0,.55);border:1px solid rgba(212,175,55,.28);padding:4px 14px;border-radius:10px;white-space:nowrap;z-index:10;transition:all var(--tm);bottom:calc(clamp(76px,21.5vw,108px) + 10px)}
.turn-b.d{color:#e87;border-color:rgba(220,80,60,.38)}
.hstrip{background:rgba(1,7,3,.97);border-top:1px solid var(--bdr);padding:7px 5px 9px;flex-shrink:0;position:relative;z-index:10}
.hlbl{text-align:center;font-size:.6rem;color:var(--muted);margin-bottom:4px}
.hinner{display:flex;align-items:flex-end;justify-content:center;gap:3px;overflow:visible;height:clamp(76px,21.5vw,108px);flex-wrap:nowrap}
.hcw{flex-shrink:0;width:clamp(44px,12vw,62px);height:clamp(62px,17vw,88px);transition:margin var(--tm),transform var(--tm);transform-origin:bottom center;animation:hcIn var(--ts) both}
@keyframes hcIn{from{transform:scale(.6) translateY(28px) rotate(5deg);opacity:0}to{transform:scale(1) translateY(0) rotate(0);opacity:1}}
.hcw:hover .card.play{transform:translateY(-13px) scale(1.11);box-shadow:0 22px 55px rgba(0,0,0,.7)}
#tflash{position:fixed;inset:0;z-index:2000;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:.9rem;pointer-events:none;opacity:0}
#tflash.show{animation:tflashFade 3s ease forwards}
@keyframes tflashFade{0%{opacity:0}8%{opacity:1}75%{opacity:.88}100%{opacity:0}}
.fsym{font-size:clamp(5.5rem,27vw,11rem);line-height:1;animation:symStamp 3s cubic-bezier(.34,1.56,.64,1) forwards;opacity:0}
@keyframes symStamp{0%{transform:scale(5) rotate(-22deg);opacity:0;filter:blur(12px)}14%{transform:scale(.87) rotate(4deg);opacity:1;filter:blur(0)}35%{transform:scale(1) rotate(0);opacity:1}80%{transform:scale(1.06);opacity:.9}100%{transform:scale(1.6);opacity:0}}
.ftxt{font-family:'Playfair Display',serif;font-size:clamp(1.3rem,5.5vw,2.4rem);color:#fff;text-shadow:0 2px 18px rgba(0,0,0,.6);animation:ftIn 3s ease forwards;opacity:0}
.fsub{font-size:.85rem;color:rgba(255,255,255,.65);animation:ftIn 3s ease .1s forwards;opacity:0}
@keyframes ftIn{0%{opacity:0;transform:translateY(22px)}14%{opacity:1;transform:translateY(0)}80%{opacity:1}100%{opacity:0}}
.boot-ov{position:fixed;inset:0;z-index:1500;background:rgba(3,11,5,.88);backdrop-filter:blur(4px);display:flex;flex-direction:column;align-items:center;justify-content:center;gap:1.1rem;animation:ovFIn .3s ease}
@keyframes ovFIn{from{opacity:0}to{opacity:1}}
.boot-t{font-family:'Playfair Display',serif;font-size:1.45rem;color:var(--gold)}.boot-cards{display:flex;gap:4px;align-items:flex-end}
.bca{width:22px;height:32px;background:linear-gradient(135deg,#0e3a1f,#051910);border:1px solid rgba(212,175,55,.22);border-radius:3px;animation:bcPop var(--ts) both}
@keyframes bcPop{from{transform:translateY(-45px) scale(.5);opacity:0}to{transform:translateY(0) scale(1);opacity:1}}
.tsel{position:fixed;inset:0;z-index:1800;background:rgba(3,11,5,.92);backdrop-filter:blur(6px);display:flex;flex-direction:column;align-items:center;justify-content:flex-end;padding:1.5rem;gap:.9rem;animation:ovFIn .2s ease}
.tsel-t{font-family:'Playfair Display',serif;font-size:1.2rem;color:var(--gold)}.tsel-s{font-size:.78rem;color:var(--muted);text-align:center;max-width:270px}
.tsel-grid{display:flex;flex-wrap:wrap;gap:7px;justify-content:center;max-width:370px}
.tsel-c{width:clamp(46px,12.5vw,58px);height:clamp(64px,17.5vw,82px);cursor:pointer;transition:transform var(--tm)}.tsel-c:hover{transform:translateY(-10px) scale(1.1)}
.res-v{position:fixed;inset:0;z-index:1200;background:rgba(3,11,5,.97);display:flex;flex-direction:column;align-items:center;justify-content:center;gap:1.4rem;padding:2rem;animation:ovFIn .5s ease}
.rtrophy{font-size:5rem;animation:trPop var(--ts) .3s both}
@keyframes trPop{from{transform:scale(0) rotate(-25deg);opacity:0}to{transform:scale(1) rotate(0);opacity:1}}
.rtitle{font-family:'Playfair Display',serif;font-size:clamp(1.9rem,9vw,3.4rem);font-weight:900;background:linear-gradient(135deg,var(--gold2),var(--gold));-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;text-align:center}
.rscores{display:flex;align-items:center;gap:1.8rem}.rteam{display:flex;flex-direction:column;align-items:center;gap:.45rem}
.rteam-l{font-size:.72rem;font-weight:700;letter-spacing:.1em;text-transform:uppercase;color:var(--muted)}.rmrow{display:flex;gap:4px}
.rmc{width:28px;height:40px;background:#fff;border-radius:4px;box-shadow:var(--sh1);display:flex;align-items:center;justify-content:center;font-size:.95rem}.rnum{font-family:'Playfair Display',serif;font-size:2.4rem;font-weight:900;color:var(--gold);line-height:1}.rvs{font-size:1.1rem;color:var(--muted)}.rbtns{display:flex;gap:.7rem;flex-wrap:wrap;justify-content:center}
#toasts{position:fixed;top:68px;left:50%;transform:translateX(-50%);z-index:3000;display:flex;flex-direction:column;align-items:center;gap:6px;pointer-events:none}
.toast{background:rgba(6,20,10,.96);border:1px solid var(--bdr);border-radius:10px;padding:6px 17px;font-size:.8rem;font-weight:600;color:var(--txt);backdrop-filter:blur(12px);box-shadow:var(--sh2);white-space:nowrap;animation:tIn .3s var(--ts),tOut .3s ease 2.6s forwards}
@keyframes tIn{from{transform:translateY(-15px) scale(.9);opacity:0}to{transform:translateY(0) scale(1);opacity:1}}
@keyframes tOut{to{transform:translateY(-15px);opacity:0}}
.conf{position:fixed;z-index:1100;top:-20px;width:8px;height:8px;border-radius:2px;animation:cFall linear forwards;pointer-events:none}
@keyframes cFall{to{transform:translateY(115vh) rotate(800deg);opacity:0}}
.ws-badge{position:fixed;bottom:8px;right:8px;font-size:.6rem;padding:3px 8px;border-radius:6px;z-index:100;font-weight:700;letter-spacing:.08em}
.ws-badge.ok{background:rgba(39,174,96,.2);color:#5eead4;border:1px solid rgba(39,174,96,.3)}
.ws-badge.err{background:rgba(192,57,43,.2);color:#f87171;border:1px solid rgba(192,57,43,.3)}
@media(max-width:380px){.trickc{width:180px;height:180px}.tslot{width:50px;height:71px}}
@media(min-width:600px){.trickc{width:245px;height:245px}.tslot{width:65px;height:92px}}
@media(min-width:900px){.trickc{width:285px;height:285px}.tslot{width:75px;height:107px}.hcw{width:70px;height:100px}}
@media(min-width:1100px){.game-v,.menu-v,.hub-v,.form-v{max-width:510px;margin:0 auto;border-left:1px solid var(--bdr);border-right:1px solid var(--bdr)}}
@media(prefers-reduced-motion:reduce){*,*::before,*::after{animation-duration:.01ms!important;transition-duration:.01ms!important}}
</style>
</head>
<body>
<div id="app"></div>
<div id="tflash"><div class="fsym" id="fsym"></div><div class="ftxt" id="ftxt"></div><div class="fsub" id="fsub"></div></div>
<div id="toasts"></div>
<div class="ws-badge err" id="wsbadge">Connecting...</div><script>
'use strict';
const SUITS=['S','H','D','C'];
const SYM={S:'\u2660',H:'\u2665',D:'\u2666',C:'\u2663'};
const SNAME={S:'Spades',H:'Hearts',D:'Diamonds',C:'Clubs'};
const RD=new Set(['H','D']);
const RDSP={11:'J',12:'Q',13:'K',14:'A'};
const FBGS={H:'rgba(155,28,18,.9)',D:'rgba(160,38,22,.9)',S:'rgba(12,12,46,.92)',C:'rgba(8,46,18,.92)'};
function rd(r){return RDSP[r]||String(r)}
function ck(c){return c.r+''+c.s}
function isRed(c){return RD.has(c.s)}
function isMn(c){return c.r===10}
function h(str){return String(str).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');}

const ST={view:'menu',name:localStorage.getItem('mdk_n')||'',gs:null};
let WS=null;

function initWS(){
  const proto=location.protocol==='https:'?'wss:':'ws:';
  WS=new WebSocket(proto+'//'+location.host+'/ws');
  WS.onopen=function(){setBadge(true);};
  WS.onclose=function(){WS=null;setBadge(false);setTimeout(initWS,3000);};
  WS.onerror=function(){setBadge(false);};
  WS.onmessage=function(ev){handleMsg(JSON.parse(ev.data));};
}

function setBadge(ok){
  var b=document.getElementById('wsbadge');
  if(!b)return;
  b.className='ws-badge '+(ok?'ok':'err');
  b.textContent=ok?'Connected':'Reconnecting...';
}

function wsSend(data){if(WS&&WS.readyState===1)WS.send(JSON.stringify(data));}

function handleMsg(msg){
  if(msg.type==='state'){
    ST.gs=msg.state;
    var evts=msg.events||[];
    if(evts.indexOf('trump_revealed')>=0&&ST.gs.trump){showTFlash(ST.gs.trump.s,ST.gs.trump.by_name);}
    if(evts.indexOf('boot_dealt')>=0){bootAnim();}
    evts.forEach(function(e){
      if(e.indexOf('mendi:')==0){var p=e.split(':');toast(p[1]+' captured '+p[2]+' mendi! \u2736');}
    });
    if(evts.indexOf('game_started')>=0){toast('Game started! '+ST.gs.players[ST.gs.whose].name+' leads.');}
    if(ST.gs.done){ST.view='result';render();if(ST.gs.team_mn[0]!==ST.gs.team_mn[1])confetti();return;}
    if(ST.gs.players){ST.view='game';}
    render();
  }
}

function render(){
  var app=document.getElementById('app');
  if(ST.view==='menu')app.innerHTML=menuH();
  else if(ST.view==='hub')app.innerHTML=hubH();
  else if(ST.view==='create'||ST.view==='join')app.innerHTML=cjH();
  else if(ST.view==='game')app.innerHTML=gameH();
  else if(ST.view==='result')app.innerHTML=resultH();
  if(ST.view==='game')requestAnimationFrame(adjustH);
}

function menuH(){
  return '<div class="menu-v"><div class="brand"><div class="chip"><div class="chip-in">M</div></div><div class="brand-t">MENDIKOT</div><div class="brand-s">Classic Indian Card Game</div></div>'
  +'<div class="card-fan" aria-hidden="true"><div class="fc" style="color:var(--red)">'+SYM.H+'</div><div class="fc" style="color:var(--dark)">'+SYM.S+'</div><div class="fc" style="color:var(--red)">'+SYM.D+'</div><div class="fc" style="color:var(--dark)">'+SYM.C+'</div><div class="fc" style="color:var(--red)">'+SYM.H+'</div></div>'
  +'<div class="menu-form"><label class="flbl" for="pn">Your Name</label>'
  +'<input class="finp" id="pn" type="text" maxlength="16" placeholder="Enter your name" value="'+h(ST.name)+'" autocomplete="off" oninput="ST.name=this.value;localStorage.setItem(\'mdk_n\',this.value)"></div>'
  +'<div class="menu-btns">'
  +'<button class="btn btn-gold btn-w" id="btn-solo" onclick="startSolo()"><svg class="btn-ico" viewBox="0 0 24 24"><path d="M12 2L2 7l10 5 10-5-10-5z"/><path d="M2 17l10 5 10-5"/><path d="M2 12l10 5 10-5"/></svg>Solo vs Bots</button>'
  +'<button class="btn btn-ghost btn-w" id="btn-fr" onclick="goTo(\'hub\')"><svg class="btn-ico" viewBox="0 0 24 24"><path d="M17 21v-2a4 4 0 00-4-4H5a4 4 0 00-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M23 21v-2a4 4 0 00-3-3.87"/><path d="M16 3.13a4 4 0 010 7.75"/></svg>Play with Friends</button>'
  +'</div><p style="color:var(--muted);font-size:.78rem;text-align:center;max-width:250px">Capture the four 10s (mendi) to win &middot; 4 players &middot; 2 teams &middot; 13 tricks</p></div>';
}

function hubH(){return '<div class="hub-v"><button class="back-btn" onclick="goTo(\'menu\')">&larr; Back</button><div><div class="view-t">Play with Friends</div><p style="color:var(--muted);font-size:.78rem;text-align:center">Create or join a room</p></div><div class="hub-row"><div class="hub-c" onclick="goTo(\'create\')" role="button" tabindex="0"><div class="hub-ico"><svg width="26" height="26" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><line x1="12" y1="8" x2="12" y2="16"/><line x1="8" y1="12" x2="16" y2="12"/></svg></div><div class="hub-ct">Create Room</div><div class="hub-cd">Host a new game</div></div><div class="hub-c" onclick="goTo(\'join\')" role="button" tabindex="0"><div class="hub-ico"><svg width="26" height="26" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M15 3h4a2 2 0 012 2v14a2 2 0 01-2 2h-4"/><polyline points="10 17 15 12 10 7"/><line x1="15" y1="12" x2="3" y2="12"/></svg></div><div class="hub-ct">Join Room</div><div class="hub-cd">Enter a code</div></div></div><div style="max-width:290px;background:rgba(0,0,0,.2);border:1px solid var(--bdr);border-radius:var(--r2);padding:.9rem;text-align:center"><div style="color:var(--gold);font-family:\'Playfair Display\',serif;font-size:.95rem;margin-bottom:.35rem">Multiplayer Coming Soon</div><p style="color:var(--muted);font-size:.75rem">Server is ready &mdash; multiplayer support in next update!</p></div><button class="btn btn-gold btn-sm" onclick="startSolo()">&#9654; Play Solo vs Bots</button></div>';}

function cjH(){return '<div class="form-v"><button class="back-btn" onclick="goTo(\'hub\')">&larr; Back</button><div class="view-t">Coming Soon</div><div class="fpanel" style="text-align:center;gap:1rem"><div style="font-size:2.4rem">&#128679;</div><div style="color:var(--gold);font-family:\'Playfair Display\',serif">Multiplayer Under Development</div><p style="color:var(--muted);font-size:.8rem">WebSocket server is ready &mdash; room system coming next!</p><button class="btn btn-gold btn-w" onclick="startSolo()">Play Solo vs Bots</button><button class="btn btn-ghost btn-sm btn-w" onclick="goTo(\'hub\')">&larr; Back</button></div></div>';}

function gameH(){
  var g=ST.gs;if(!g)return'<div class="game-v"></div>';
  var hand=g.hand||[];
  var tsStr=g.tout&&g.trump?g.trump.s:null;
  var vset=new Set((g.vplays||[]).map(function(c){return ck(c);}));
  var mr=g.must_reveal;
  var hturn=g.whose===0&&!g.paused&&!g.done;
  var bsl={};
  (g.trick.cards||[]).forEach(function(tc){bsl[tc.seat]=tc.c;});
  var mnA=g.mendi_suits?g.mendi_suits.A:[];
  var mnB=g.mendi_suits?g.mendi_suits.B:[];
  var btxt='',bdng=false;
  if(g.paused)btxt='Trick complete\u2026';
  else if(hturn&&mr){btxt='You\'re void \u2014 tap any card to reveal trump!';bdng=true;}
  else if(hturn)btxt='Your turn \u2014 pick a card';
  else btxt=h(g.players[g.whose].name)+'\'s turn\u2026';
  return '<div class="game-v">'+sbarH(g,mnA,mnB)
  +'<div class="felt"><div class="deco tl">'+SYM.S+'</div><div class="deco tr">'+SYM.H+'</div><div class="deco bl">'+SYM.C+'</div><div class="deco br">'+SYM.D+'</div>'
  +seatH(g,2,'top')+seatH(g,3,'left')+seatH(g,1,'right')
  +'<div class="trickc">'+tslH(bsl,2,'T',tsStr)+tslH(bsl,0,'B',tsStr)+tslH(bsl,3,'L',tsStr)+tslH(bsl,1,'R',tsStr)+'</div>'
  +'<div class="finfo tr"><div class="ppill">'+(g.ph1?'Phase 1':'Phase 2')+' &middot; Trick '+(g.tnum+1)+'/13</div></div>'
  +'<div class="finfo bc"><div class="tcnt">A: '+g.team_mn[0]+' mendi &nbsp;&middot;&nbsp; B: '+g.team_mn[1]+' mendi</div></div>'
  +'<div class="turn-b'+(bdng?' d':'')+'" id="tnbanner">'+btxt+'</div></div>'
  +'<div class="hstrip"><div class="hlbl">'+h(g.players[0].name)+' &middot; Team A</div>'
  +'<div class="hinner" id="hinner">'+handH(hand,vset,mr,hturn,tsStr)+'</div></div></div>';
}

function sbarH(g,mnA,mnB){
  var ts=g.tout&&g.trump?g.trump.s:null;
  return '<div class="sbar"><div class="sside"><div><div class="slbl">Team A</div><div class="mtrack">'+pipsH(mnA)+'</div></div><div class="mnum">'+g.team_mn[0]+'</div></div>'
  +'<div class="twrap"><div class="tlbl">Trump</div>'
  +'<div class="tmini '+(ts?'sho':'hid')+'">'+(ts?'<div class="tface" style="color:'+(isRed({s:ts})?'var(--red)':'var(--dark)')+'"><span>'+rd(g.trump.c.r)+'</span><span class="ts">'+SYM[ts]+'</span></div>':'')+'</div></div>'
  +'<div class="sside r"><div class="mnum">'+g.team_mn[1]+'</div><div><div class="slbl" style="text-align:right">Team B</div><div class="mtrack" style="flex-direction:row-reverse">'+pipsH(mnB)+'</div></div></div></div>';
}

function pipsH(suits){return SUITS.map(function(s){var w=suits&&suits.indexOf(s)>=0;return'<div class="mpip'+(w?' won':'')+'" title="'+SNAME[s]+' 10"><span style="color:'+(w?(isRed({s:s})?'var(--red)':'var(--dark)'):'rgba(255,255,255,.1)')+'">'+SYM[s]+'</span></div>';}).join('');}

function seatH(g,seat,pos){
  var p=g.players[seat];var act=g.whose===seat&&!g.paused&&!g.done;var init=p.name.substring(0,2).toUpperCase();var thinking=act&&p.bot;
  var pips=Math.min(g.opp_sizes?g.opp_sizes[seat]:0,8);
  var ph='';for(var i=0;i<pips;i++)ph+='<div class="opip" style="z-index:'+i+'"></div>';
  return '<div class="seat '+pos+'"><div class="sav'+(p.bot?' bot':'')+(act?' act':'')+'">'+init+(thinking?'<div class="thdot-wrap"><div class="td"></div><div class="td"></div><div class="td"></div></div>':'')+'</div><div class="snm">'+h(p.name)+'</div><div class="sbadge '+p.team.toLowerCase()+'">'+p.team+'</div>'+(ph?'<div class="opips">'+ph+'</div>':'')+'</div>';
}

function tslH(bsl,seat,pos,ts){var c=bsl[seat];return'<div class="tslot '+pos+'">'+(c?'<div class="tsin">'+cFaceH(c,false,ts)+'</div>':'')+'</div>';}

function cFaceH(c,dis,ts){
  var col=isRed(c)?'red':'black';
  var cls=['card',col,dis?'dis':'',ts&&c.s===ts?'istr':'',isMn(c)?'ismn':''].filter(Boolean).join(' ');
  return '<div class="'+cls+'"><div class="cr"><span>'+rd(c.r)+'</span><span class="sm">'+SYM[c.s]+'</span></div><div class="cs">'+SYM[c.s]+'</div><div class="crb"><span>'+rd(c.r)+'</span><span class="sm">'+SYM[c.s]+'</span></div></div>';
}

function handH(hand,vset,mr,hturn,ts){
  if(!hand.length)return'';
  var sorted=[...hand].sort(function(a,b){var sd=SUITS.indexOf(a.s)-SUITS.indexOf(b.s);return sd!==0?sd:a.r-b.r;});
  return sorted.map(function(c,i){
    var key=ck(c);var valid=vset.has(key);var play=hturn&&valid,dis=hturn&&!valid;
    var col=isRed(c)?'red':'black';var cls=['card',col,play?'play':'',dis?'dis':'',ts&&c.s===ts?'istr':'',isMn(c)?'ismn':''].filter(Boolean).join(' ');
    var oc=play?'onclick="onCC(\''+key+'\','+mr+')"':' ';
    return '<div class="hcw" style="animation-delay:'+(i*.04)+'s"><div class="'+cls+'" '+oc+' role="'+(play?'button':'')+'" aria-label="'+rd(c.r)+' of '+SNAME[c.s]+'">'
    +'<div class="cr"><span>'+rd(c.r)+'</span><span class="sm">'+SYM[c.s]+'</span></div><div class="cs">'+SYM[c.s]+'</div><div class="crb"><span>'+rd(c.r)+'</span><span class="sm">'+SYM[c.s]+'</span></div></div></div>';
  }).join('');
}

function resultH(){
  var g=ST.gs;var tA=g.team_mn[0],tB=g.team_mn[1];
  var mA=g.mendi_suits?g.mendi_suits.A:[];var mB=g.mendi_suits?g.mendi_suits.B:[];
  var title=tA>tB?'Team A Wins!':tB>tA?'Team B Wins!':"It's a Draw!";var trophy=tA===tB?'\uD83E\uDD1D':'\uD83C\uDFC6';
  function mrow(suits){return suits&&suits.length?suits.map(function(s){return'<div class="rmc" style="color:'+(isRed({s:s})?'var(--red)':'var(--dark)')+'">'+SYM[s]+'</div>';}).join(''):'<span style="color:var(--muted);font-size:.75rem;padding:.4rem">None</span>';}
  var desc=tA===4?'Perfect sweep! Team A got all 4 mendi!':tB===4?'Perfect sweep! Team B got all 4!':tA===tB?'Equal mendi \u2014 dead heat!':'Team '+(tA>tB?'A':'B')+' captured more mendi';
  return '<div class="res-v"><div class="rtrophy">'+trophy+'</div><h1 class="rtitle">'+title+'</h1>'
  +'<div class="rscores"><div class="rteam"><div class="rteam-l">Team A</div><div class="rmrow">'+mrow(mA)+'</div><div class="rnum">'+tA+'</div></div><div class="rvs">vs</div><div class="rteam"><div class="rteam-l">Team B</div><div class="rmrow">'+mrow(mB)+'</div><div class="rnum">'+tB+'</div></div></div>'
  +'<p style="color:var(--muted);font-size:.82rem;text-align:center">'+desc+'</p>'
  +'<div class="rbtns"><button class="btn btn-gold" onclick="startSolo()">Play Again</button><button class="btn btn-ghost" onclick="goTo(\'menu\')">Menu</button></div></div>';
}

function adjustH(){var inner=document.getElementById('hinner');if(!inner)return;var cards=inner.querySelectorAll('.hcw');if(cards.length<2)return;var avail=inner.offsetWidth-10;var cw=cards[0].offsetWidth;var total=cards.length*cw+(cards.length-1)*3;if(total>avail){var ov=(total-avail)/(cards.length-1);cards.forEach(function(c,i){if(i>0)c.style.marginLeft='-'+ov+'px';});}}

function onCC(key,mr){
  var g=ST.gs;if(!g||g.whose!==0||g.paused||g.done)return;
  var card=g.hand.find(function(c){return ck(c)===key;});if(!card)return;
  if(mr)showTSel();else wsSend({type:'play_card',card:{s:card.s,r:card.r},is_reveal:false});
}

function showTSel(){
  var g=ST.gs;var old=document.getElementById('tsel');if(old)old.remove();
  var el=document.createElement('div');el.id='tsel';el.className='tsel';
  var ledName=g.trick.led?SNAME[g.trick.led]:'that suit';
  var grid=(g.hand||[]).map(function(c){return'<div class="tsel-c" onclick="pickT(\''+ck(c)+'\')" role="button" aria-label="'+rd(c.r)+' of '+SNAME[c.s]+'">'+cFaceH(c,false,null)+'</div>';}).join('');
  el.innerHTML='<div class="tsel-t">Reveal Trump</div><div class="tsel-s">No '+ledName+' cards &mdash; pick any card as trump. It is immediately played.</div><div class="tsel-grid">'+grid+'</div><button class="btn btn-ghost btn-sm" style="margin-bottom:1rem" onclick="document.getElementById(\'tsel\').remove()">Cancel</button>';
  document.body.appendChild(el);
}

function pickT(key){
  var el=document.getElementById('tsel');if(el)el.remove();
  var g=ST.gs;var card=g.hand.find(function(c){return ck(c)===key;});if(!card)return;
  wsSend({type:'play_card',card:{s:card.s,r:card.r},is_reveal:true});
}

function showTFlash(suit,pname){
  var ov=document.getElementById('tflash');var se=document.getElementById('fsym');var te=document.getElementById('ftxt');var su=document.getElementById('fsub');if(!ov)return;
  ov.style.background=FBGS[suit]||'rgba(40,40,100,.9)';se.textContent=SYM[suit];se.style.color=isRed({s:suit})?'#ff8888':'#ccccff';te.textContent=SNAME[suit]+' is Trump!';su.textContent=pname+' revealed the trump suit';
  ov.classList.remove('show');void ov.offsetWidth;ov.classList.add('show');setTimeout(function(){ov.classList.remove('show');},3100);
}

function bootAnim(){
  var el=document.createElement('div');el.className='boot-ov';
  var bc='';for(var i=0;i<8;i++)bc+='<div class="bca" style="animation-delay:'+(i*.07)+'s"></div>';
  el.innerHTML='<div class="boot-t">Dealing Cards</div><p style="color:var(--muted);font-size:.8rem">8 more cards each!</p><div class="boot-cards">'+bc+'</div>';
  document.body.appendChild(el);setTimeout(function(){el.remove();},2000);
}

function toast(msg){var c=document.getElementById('toasts');if(!c)return;var t=document.createElement('div');t.className='toast';t.textContent=msg;c.appendChild(t);setTimeout(function(){t.remove();},3000);}

function confetti(){
  var cols=['#d4af37','#f5d86e','#27ae60','#e74c3c','#5dade2','#af7ac5','#fff'];
  for(var i=0;i<90;i++){var p=document.createElement('div');p.className='conf';p.style.left=Math.random()*100+'vw';p.style.background=cols[0|Math.random()*cols.length];p.style.width=(5+Math.random()*7)+'px';p.style.height=(5+Math.random()*7)+'px';p.style.animationDuration=(1.8+Math.random()*2.4)+'s';p.style.animationDelay=(Math.random()*.9)+'s';document.body.appendChild(p);setTimeout(function(){p.remove();},5000);}
}

function goTo(v){ST.view=v;render();}
function startSolo(){var name=ST.name.trim()||'You';wsSend({type:'solo_start',name:name});}

render();
initWS();
window.addEventListener('resize',function(){if(ST.view==='game')requestAnimationFrame(adjustH);});
</script>
</body>
</html>
"""

# ════ ROOM MANAGER ════
rooms: Dict[str,dict]={}; ws_map: Dict[str,WebSocket]={}; pid_room: Dict[str,str]={}

def gen_code():
    chars='ABCDEFGHJKLMNPQRSTUVWXYZ23456789'
    while True:
        c=''.join(random.choices(chars,k=4))
        if c not in rooms: return c

async def push(pid,data):
    w=ws_map.get(pid)
    if w:
        try: await w.send_json(data)
        except: pass

async def push_state(rc,evts=None):
    room=rooms.get(rc)
    if not room or not room.get('game'): return
    g=room['game']
    for pid,info in room['players'].items():
        if not info.get('bot'):
            st=g.state(info['seat'])
            await push(pid,{'type':'state','state':st,'events':evts or []})

async def bot_loop(rc):
    while True:
        await asyncio.sleep(0.08)
        room=rooms.get(rc)
        if not room or not room.get('game'): break
        g=room['game']
        if g.done or g.paused: break
        bot_pid=next((pid for pid,info in room['players'].items() if info['seat']==g.whose and info.get('bot')),None)
        if not bot_pid: break
        await asyncio.sleep(0.65+random.random()*0.45)
        room=rooms.get(rc)
        if not room or not room.get('game'): break
        g=room['game']
        card,rev=g.bot_card(g.whose)
        if not card: break
        evts=g.play(g.whose,card,rev)
        if 'trick_complete' in evts:
            g.paused=True
            await push_state(rc,evts)
            await asyncio.sleep(2.2)
            room=rooms.get(rc)
            if not room or not room.get('game'): break
            g=room['game']
            _,more=g.resolve()
            if 'game_done' in more:
                await push_state(rc,more); break
            await push_state(rc,more)
        else:
            await push_state(rc,evts)

# ════ FASTAPI ════
app=FastAPI()

@app.get('/')
async def index(): return HTMLResponse(HTML)

@app.websocket('/ws')
async def ws_ep(ws:WebSocket):
    await ws.accept()
    pid=str(uuid.uuid4()); ws_map[pid]=ws
    try:
        while True:
            raw=await ws.receive_text()
            msg=json.loads(raw); mt=msg.get('type')

            if mt=='solo_start':
                name=str(msg.get('name','You'))[:16]
                rc=gen_code()
                players={
                    pid:{'seat':0,'name':name,'bot':False,'team':'A'},
                    'b1':{'seat':1,'name':'Rajan','bot':True,'team':'B'},
                    'b2':{'seat':2,'name':'Deepak','bot':True,'team':'A'},
                    'b3':{'seat':3,'name':'Priya','bot':True,'team':'B'},
                }
                gp=[{'name':v['name'],'seat':v['seat'],'bot':v['bot'],'team':v['team']} for v in sorted(players.values(),key=lambda x:x['seat'])]
                game=Game(gp); rooms[rc]={'players':players,'game':game,'mode':'solo'}; pid_room[pid]=rc
                await push_state(rc,['game_started'])
                if game.players[game.whose]['bot']: asyncio.create_task(bot_loop(rc))

            elif mt=='play_card':
                rc=pid_room.get(pid)
                if not rc: continue
                room=rooms.get(rc)
                if not room or not room.get('game'): continue
                g=room['game']; seat=room['players'].get(pid,{}).get('seat',-1)
                if g.whose!=seat or g.paused or g.done: continue
                cd=msg.get('card')
                if not cd: continue
                hc=next((c for c in g.hands[seat] if c['s']==cd.get('s') and c['r']==cd.get('r')),None)
                if not hc: continue
                evts=g.play(seat,hc,bool(msg.get('is_reveal',False)))
                if 'trick_complete' in evts:
                    g.paused=True
                    await push_state(rc,evts)
                    await asyncio.sleep(2.2)
                    room=rooms.get(rc)
                    if not room: continue
                    g=room['game']; _,more=g.resolve()
                    if 'game_done' in more:
                        await push_state(rc,more); continue
                    await push_state(rc,more)
                    if g.players[g.whose]['bot']: asyncio.create_task(bot_loop(rc))
                else:
                    await push_state(rc,evts)
                    if not g.done and g.players[g.whose]['bot']: asyncio.create_task(bot_loop(rc))

    except WebSocketDisconnect: pass
    finally:
        ws_map.pop(pid,None); rc=pid_room.pop(pid,None)
        if rc and rc in rooms and rooms[rc].get('mode')=='solo': rooms.pop(rc,None)

if __name__=='__main__':
    print('\n  Mendikot server starting...')
    print('  Open http://localhost:8000 in your browser\n')
    uvicorn.run(app,host='0.0.0.0',port=8000,log_level='warning')
