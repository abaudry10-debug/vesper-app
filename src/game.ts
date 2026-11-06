// Cœur du jeu : état du personnage, déplacements case par case, interactions, rendu.
import { heartbeat, playTheme, setHeatSound, sfx } from './audio.js';
import { heldDir, releaseAll } from './input.js';
import { MAPS, START, SOLID, charAt, type GameMap, type MapObject } from './maps.js';
import { T, bigTree, cutout, dish, dogSprite, iconCanvas, dogAsleep, type DogLook, frozenTrain, hash, hero, radioTower, shuttleWreck, solarTower, tile, type Dir } from './sprites.js';
import { ACHIEVEMENTS, ARCHIVE_CODE, ARCHIVES, CLUES, FINALE, ITEMS, QUESTIONS, RADIO_FREQ, RESTART_ORDER, SCRIPTS, SIGNAL_KEY, SWITCHES, type Api } from './story.js';
import * as ui from './ui.js';

/** Taille de la vue en pixels de jeu ; recalculée selon l'écran (voir main.ts). */
export const view = { w: 12 * T, h: 16 * T, padBottom: 0 }; // padBottom : zone cachée par les commandes
const HEAT_WARN = 17;
const HEAT_WAVE = 24;
const HEAT_FADE = 4;
const MOVE_TIME = 0.19; // secondes pour traverser une case
// Copie figée de Vesper : sa propre sauvegarde, séparée de celle du dépôt vesper (même site GitHub).
const SAVE_KEY = 'vesper-app-save-v2';

const DELTA: Record<Dir, [number, number]> = { up: [0, -1], down: [0, 1], left: [-1, 0], right: [1, 0] };

interface Save {
  map: string;
  x: number;
  y: number;
  dir: Dir;
  flags: string[];
  clues: string[];
  items: string[];
  fresh?: string[];
  counters?: Record<string, number>;
}

interface Particle {
  x: number;
  y: number;
  vx: number;
  vy: number;
  a: number;
}

interface Follower {
  x: number;
  y: number;
  dir: Dir;
  moving: { fx: number; fy: number } | null;
  /** Déplacement autonome de Pixel (venir s'asseoir, rapporter l'écrou) : suite de cases à parcourir. */
  walk?: { from: [number, number]; path: [number, number][]; t: number; speed: number } | null;
}

/** Ce que fait Pixel quand il ne se contente pas de suivre. */
type PixelMode = 'follow' | 'come' | 'sit' | 'pet' | 'rest' | 'fetch' | 'dig' | 'cut' | 'rescue' | 'stay';

/** Petits effets dessinés dans le monde : cœurs, « z », reflets de soleil, poussière, l'écrou lancé. */
interface Fx {
  kind: 'heart' | 'z' | 'spark' | 'dust' | 'smoke' | 'zap' | 'steam' | 'ember';
  x: number;
  y: number;
  vx: number;
  vy: number;
  life: number;
  max: number;
}

export class Game {
  map: GameMap = MAPS[START.map];
  x = START.x;
  y = START.y;
  dir: Dir = START.dir;
  moving: { fx: number; fy: number; t: number } | null = null;
  steps = 0;
  flags = new Set<string>();
  clues = new Set<string>();
  items = new Set<string>();
  fresh = new Set<string>();
  time = 0;
  blackout = false; // écran noir pendant l'introduction
  locked = false; // bloque le joueur (fondu…)
  particles: Particle[] = [];
  pixel: Follower | null = null;
  pixelMode: PixelMode = 'follow';
  /** Compteurs pour les succès (écrous lancés…). */
  counters: Record<string, number> = {};
  private pixelTimer = 0;
  private idle = 0;
  private turnHold = 0;
  private heroCrouch = 0;
  private whineTimer = 3;
  private homeBeep = 2;
  private fx: Fx[] = [];
  /** L'écrou en vol ou posé au sol (coordonnées en pixels du monde). */
  private nut: { fx: number; fy: number; tx: number; ty: number; t: number; dur: number; landed: boolean } | null = null;
  private fetch: { stage: 'flying' | 'run' | 'pick' | 'back'; tx: number; ty: number } | null = null;
  private fxTimer = 0;
  // ---- effets visuels ----
  /** Empreintes dans le sable, qui s'effacent peu à peu. */
  private prints: { x: number; y: number; dir: Dir; life: number; drag?: boolean }[] = [];
  /** Objet ramassé ou indice trouvé : une petite animation au-dessus du héros. */
  private pop: { kind: 'item' | 'clue'; id: string; t: number } | null = null;
  /** Scène où Pixel passe par un endroit où l'on ne peut pas aller. */
  private cut: { kind: 'pixelFlap' | 'pixelVent' | 'pixelPower' | 'pixelCar'; obj: MapObject; stage: 'go' | 'act' | 'back'; t: number; snd: number; then?: () => void } | null = null;
  private smokeTimer = 0;
  // ---- vagues de chaleur ----
  heatPhase: 'none' | 'warn' | 'wave' | 'fade' = 'none';
  heatT = 0;
  heatKind = '';
  private heatStrength = 1;
  heatGauge = 0;
  private outdoorTime = 0;
  private outdoorSteps = 0;
  cycleTimer = 200;
  private heatSaid = false;
  private beatTimer = 0;
  private heatSoundTimer = 0;
  private steamTimer = 0;
  /** Sauvetage : Pixel traîne le héros évanoui jusqu'à l'abri le plus proche. */
  private rescue: {
    stage: 'fall' | 'fetch' | 'drag' | 'out'; t: number; path: [number, number][]; i: number; max: number;
    door: MapObject | null; quick: boolean;
  } | null = null;
  private drag: { fx: number; fy: number; t: number; dur: number } | null = null;
  /** La toute fin : le héros va jusqu'à la capsule 07, y glisse la batterie et s'y allonge. */
  private endSeq: { stage: 'unplug' | 'walk' | 'prime' | 'enter' | 'glow'; t: number; path: [number, number][] } | null = null;
  private podGlow = 0;
  private heroAlpha = 1;
  private wake: { t: number; first: boolean; stood: number } | null = null;
  private saveTimer = 0;
  private bumpCooldown = 0;
  private beepTimer = 0;
  private openQ = new Set<string>();
  private solvedQ = new Set<string>();
  private ctx: CanvasRenderingContext2D;
  private decalShuttle = shuttleWreck();
  private decalDish = dish();
  private decalTower = solarTower();
  private decalRadio = radioTower();
  private decalTrain = frozenTrain();
  private decalBigTree = bigTree();

  constructor(ctx: CanvasRenderingContext2D) {
    this.ctx = ctx;
    for (let i = 0; i < 40; i++) this.particles.push(this.newParticle(true));
  }

  // ---------- sauvegarde ----------
  static hasSave(): boolean {
    try {
      return !!localStorage.getItem(SAVE_KEY);
    } catch {
      return false;
    }
  }

  load(): boolean {
    try {
      const raw = localStorage.getItem(SAVE_KEY);
      if (!raw) return false;
      const s = JSON.parse(raw) as Save;
      if (!MAPS[s.map]) return false;
      this.map = MAPS[s.map];
      this.x = s.x;
      this.y = s.y;
      this.dir = s.dir;
      this.flags = new Set(s.flags);
      this.clues = new Set(s.clues);
      this.items = new Set(s.items);
      this.fresh = new Set(s.fresh ?? []);
      this.counters = s.counters ?? {};
      if (this.flags.has('batteryFound')) this.flags.delete('sondeOn'); // anciennes sauvegardes
      this.refreshQuestions(true);
      if (this.fresh.size) document.getElementById('btn-journal')?.classList.add('fresh');
      if (this.flags.has('pixelOn')) this.placePixelBehind();
      return true;
    } catch {
      return false;
    }
  }

  /** Sauvegarde puis relit le stockage pour confirmer que tout est bien écrit. */
  saveVerified(): boolean {
    this.save();
    try {
      const raw = localStorage.getItem(SAVE_KEY);
      if (!raw) return false;
      const s = JSON.parse(raw) as Save;
      return (
        s.map === this.map.id && s.x === this.x && s.y === this.y &&
        s.clues.length === this.clues.size && s.items.length === this.items.size && s.flags.length === this.flags.size
      );
    } catch {
      return false;
    }
  }

  save() {
    const s: Save = {
      map: this.map.id, x: this.x, y: this.y, dir: this.dir,
      flags: [...this.flags], clues: [...this.clues], items: [...this.items], fresh: [...this.fresh], counters: this.counters,
    };
    try {
      localStorage.setItem(SAVE_KEY, JSON.stringify(s));
    } catch {
      /* stockage indisponible (navigation privée) : on continue sans sauvegarde */
    }
  }

  static clearSave() {
    try {
      localStorage.removeItem(SAVE_KEY);
    } catch {
      /* rien */
    }
  }

  // ---------- objets et règles de déplacement ----------
  /** Objet visible sur une case (les objets masqués par un drapeau sont ignorés). */
  objAt(x: number, y: number): MapObject | undefined {
    return this.map.objects.find(
      (o) => o.x === x && o.y === y && !(o.hideWhen && this.flags.has(o.hideWhen)) && !(o.hiddenUntil && !this.flags.has(o.hiddenUntil)),
    );
  }

  /** Comme objAt, mais trouve aussi les objets encore cachés (on peut les examiner sans les voir). */
  private anyObjAt(x: number, y: number): MapObject | undefined {
    return this.objAt(x, y) ?? this.map.objects.find((o) => o.x === x && o.y === y && o.hiddenUntil && !this.flags.has(o.hiddenUntil));
  }

  blocked(x: number, y: number): boolean {
    // Pixel qui attend au pied de la capsule ne se laisse pas enjamber
    if (this.pixelMode === 'stay' && this.pixel && this.pixel.x === x && this.pixel.y === y) return true;
    const obj = this.objAt(x, y);
    if (obj) {
      if (obj.door) return !this.doorOpen(obj);
      if (obj.passWhen) return !this.flags.has(obj.passWhen);
      return true;
    }
    return this.solidChar(x, y);
  }

  /** Case pleine (mur, eau…) ; l'eau toxique asséchée devient praticable. */
  private solidChar(x: number, y: number): boolean {
    const ch = charAt(this.map, x, y);
    if (ch === '~' && this.map.dryFlag && this.flags.has(this.map.dryFlag)) return false;
    return SOLID.has(ch);
  }

  doorOpen(obj: MapObject): boolean {
    return !!obj.door && (!obj.door.needs || this.flags.has(obj.door.needs));
  }

  get busy(): boolean {
    return (
      this.locked || this.blackout || ui.dialogOpen() || ui.journalOpen() || ui.keypadOpen() || ui.overlayOpen() || ui.bagOpen() ||
      ui.radioOpen()
    );
  }

  update(dt: number) {
    this.time += dt;
    this.updateParticles(dt);
    this.saveTimer += dt;
    this.bumpCooldown -= dt;
    if (this.saveTimer > 10) {
      this.saveTimer = 0;
      if (!this.blackout) this.save();
    }
    this.updateDetector(dt);
    this.updatePixel(dt);
    this.updateHeat(dt);

    if (this.moving) {
      this.moving.t += dt / MOVE_TIME;
      if (this.moving.t < 1) return;
      this.moving = null;
      if (this.pixel) this.pixel.moving = null;
    }
    if (this.busy) return;
    if (this.turnHold > 0) {
      this.turnHold -= dt;
      return;
    }
    const d = heldDir();
    if (!d) {
      this.idle += dt;
      return;
    }
    const [dx, dy] = DELTA[d];
    const nx = this.x + dx;
    const ny = this.y + dy;
    // Pixel juste là (derrière ou à côté) : on se tourne d'abord vers lui, sans bouger,
    // pour pouvoir le caresser avec A. Garder la flèche appuyée fait ensuite avancer.
    const p0 = this.pixel;
    if (p0 && !p0.walk && p0.x === nx && p0.y === ny && this.dir !== d && this.pixelMode !== 'fetch' && this.pixelMode !== 'cut') {
      this.dir = d;
      this.turnHold = 0.28;
      if (this.pixelMode === 'follow') this.facePixelToHero();
      return;
    }
    this.dir = d;
    this.idle = 0;
    if (this.pixelMode !== 'follow' && this.pixelMode !== 'fetch' && this.pixelMode !== 'stay') {
      this.pixelMode = 'follow';
      if (this.pixel) this.pixel.walk = null;
    }
    const obj = this.objAt(nx, ny);
    if (obj?.door && this.doorOpen(obj)) {
      sfx.door();
      this.warp(obj.door.to, obj.door.x, obj.door.y, obj.door.dir);
      return;
    }
    if (this.blocked(nx, ny)) {
      if (this.bumpCooldown <= 0) {
        sfx.bump();
        this.bumpCooldown = 0.35;
      }
      return;
    }
    if (this.pixel && this.pixelMode !== 'stay') {
      // Pixel prend la place que le joueur vient de quitter
      const p = this.pixel;
      if (p.x !== this.x || p.y !== this.y) {
        p.dir = this.x > p.x ? 'right' : this.x < p.x ? 'left' : this.y > p.y ? 'down' : 'up';
      }
      p.moving = { fx: p.x, fy: p.y };
      p.walk = null;
      p.x = this.x;
      p.y = this.y;
    }
    this.moving = { fx: this.x, fy: this.y, t: 0 };
    if (this.map.outdoor) this.outdoorSteps += 1;
    if (this.map.outdoor) {
      const ground = charAt(this.map, this.x, this.y);
      if (ground === 'S' || ground === '.') {
        for (let i = 0; i < 2; i++)
          this.fx.push({ kind: 'dust', x: this.x * T + 5 + Math.random() * 6, y: this.y * T + 14, vx: (Math.random() - 0.5) * 16, vy: -10 - Math.random() * 8, life: 0.35, max: 0.35 });
        if (ground === 'S') this.prints.push({ x: this.x, y: this.y, dir: this.dir, life: 9 });
        if (this.prints.length > 40) this.prints.shift();
      }
    }
    this.x = nx;
    this.y = ny;
    this.steps += 1;
    sfx.step();
  }

  warp(mapId: string, x: number, y: number, dir: Dir) {
    this.locked = true;
    releaseAll();
    ui.fade(() => {
      this.map = MAPS[mapId];
      this.x = x;
      this.y = y;
      this.dir = dir;
      this.moving = null;
      this.locked = false;
      this.pixelMode = 'follow';
      this.nut = null;
      this.idle = 0;
      this.outdoorTime = 0;
      if (this.flags.has('pixelOn')) this.placePixelBehind();
      if (mapId === 'vesper' && this.flags.has('pondDry') && !this.flags.has('pondSeen')) {
        this.flags.add('pondSeen');
        ui.say(['Le lac toxique… il s’est évaporé pendant la vague.', 'Il ne reste qu’une vase craquelée. On peut passer à pied jusqu’à l’abri de chantier.']);
      }
      ui.showPlace(this.map.name);
      this.startMusic();
      this.save();
      if (mapId === 'maisonLea' && this.pixel && !this.flags.has('pixelHome')) {
        this.flags.add('pixelHome');
        sfx.pixelHappy();
        ui.say(['Pixel file droit vers un vieux panier, dans un coin.', 'Il le renifle, tourne trois fois sur lui-même… Sa queue ne s’arrête plus.']);
      }
      if (mapId === 'vesper' && !this.flags.has('firstOutside')) {
        this.flags.add('firstOutside');
        ui.say(['Le ciel… il est orange.', 'La ville est en ruine. Il n’y a personne.', 'Il faut que je comprenne ce qui s’est passé ici.']);
      }
    });
  }

  private placePixelBehind() {
    const [dx, dy] = DELTA[this.dir];
    let px = this.x - dx;
    let py = this.y - dy;
    if (this.blocked(px, py)) {
      px = this.x;
      py = this.y;
    }
    this.pixel = { x: px, y: py, dir: this.dir, moving: null };
  }

  facing(): [number, number] {
    const [dx, dy] = DELTA[this.dir];
    return [this.x + dx, this.y + dy];
  }

  interact() {
    if (this.busy || this.moving) return;
    const [fx, fy] = this.facing();
    const obj = this.anyObjAt(fx, fy);
    if (obj?.id === 'capsule07' && this.flags.has('plansRead')) return this.podInteract();
    if (this.pixel && this.pixel.x === fx && this.pixel.y === fy && this.pixelMode === 'stay' && this.flags.has('podNeedsPrime') && this.map.id === 'lab') {
      return this.askPrime();
    }
    if (this.pixel && this.pixel.x === fx && this.pixel.y === fy && !this.pixel.walk && !obj) return this.petPixel();
    if (this.nearCabin() && (!obj || obj.id === 'cabinHatch')) {
      return ui.say(['« Sous le potager, à deux pas à droite du grand arbre »… C’est par ici.', 'La terre est meuble. Avec la pelle, je pourrais creuser.']);
    }
    if (obj?.script) {
      SCRIPTS[obj.script]?.(this.api);
      return;
    }
    if (this.pixel && this.pixel.x === fx && this.pixel.y === fy && !this.pixel.walk) return this.petPixel();
    const ch = charAt(this.map, fx, fy);
    if (ch === '~') ui.say(['Une eau verte, tiède, qui sent le métal brûlé.', 'Mieux vaut ne pas y toucher.']);
    else if (ch === 'C') ui.say(['Une épave de voiture, mangée par la rouille. Vide.']);
    else if (ch === 'T') ui.say(['Un arbre mort, calciné d’un seul côté.']);
    else if (ch === 'P') ui.say(['Un panneau solaire brisé, à moitié enfoui dans le sable.']);
    else if (ch === 'v') ui.say(['Des plants desséchés.']);
    else if (ch === 'N' && this.map.id === 'vesper') SCRIPTS.shuttle?.(this.api);
    else if (ch === 'N' && this.map.id === 'quartier') ui.say(['Un arbre immense, bien plus grand que les autres. Mort, lui aussi.']);
    else if (ch === 'N') ui.say(['Une tour solaire. Son capteur doré fixe encore le ciel.']);
  }

  // ---------- Pixel ----------
  /** Une case où Pixel peut marcher (ni mur, ni objet, ni le héros sauf permission). */
  private pixelFree(x: number, y: number, allowHero = false) {
    if (x < 0 || y < 0 || x >= this.map.width || y >= this.map.height) return false;
    if (!allowHero && x === this.x && y === this.y) return false;
    if (this.objAt(x, y)) return false;
    return !this.solidChar(x, y);
  }

  /** Plus court chemin (quelques cases au plus) pour Pixel. */
  private pixelPath(from: [number, number], to: [number, number], allowHero = false, max = 8): [number, number][] | null {
    const key = (x: number, y: number) => `${x},${y}`;
    const prev = new Map<string, string | null>([[key(...from), null]]);
    const queue: [number, number, number][] = [[from[0], from[1], 0]];
    while (queue.length) {
      const [x, y, d] = queue.shift()!;
      if (x === to[0] && y === to[1]) {
        const path: [number, number][] = [];
        let k: string | null = key(x, y);
        while (k && k !== key(...from)) {
          const [a, b] = k.split(',').map(Number);
          path.unshift([a, b]);
          k = prev.get(k) ?? null;
        }
        return path;
      }
      if (d >= max) continue;
      for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
        const nx = x + dx, ny = y + dy;
        if (prev.has(key(nx, ny)) || !this.pixelFree(nx, ny, allowHero)) continue;
        prev.set(key(nx, ny), key(x, y));
        queue.push([nx, ny, d + 1]);
      }
    }
    return null;
  }

  private walkPixel(path: [number, number][], tilesPerSec: number) {
    const p = this.pixel!;
    p.moving = null;
    p.walk = path.length ? { from: [p.x, p.y], path, t: 0, speed: tilesPerSec } : null;
    if (!path.length) this.onPixelArrived();
  }

  private facePixelToHero() {
    const p = this.pixel!;
    if (this.x !== p.x) p.dir = this.x > p.x ? 'right' : 'left';
  }

  /** Quand on s'arrête un moment, Pixel vient s'asseoir devant nous. */
  private pixelCome() {
    const p = this.pixel!;
    const [dx, dy] = DELTA[this.dir];
    const spots: [number, number][] = [[this.x + dx, this.y + dy], [this.x + dy, this.y + dx], [this.x - dy, this.y - dx]];
    for (const spot of spots) {
      if (spot[0] === p.x && spot[1] === p.y) {
        this.pixelMode = 'sit';
        this.facePixelToHero();
        return;
      }
      if (!this.pixelFree(spot[0], spot[1])) continue;
      const path = this.pixelPath([p.x, p.y], spot, false, 5);
      if (!path) continue;
      this.pixelMode = 'come';
      this.walkPixel(path, 3.6);
      return;
    }
    this.pixelMode = 'sit'; // pas de place : il s'assoit là où il est
    this.facePixelToHero();
  }

  private onPixelArrived() {
    if (this.pixelMode === 'stay') {
      this.facePixelToHero();
      return;
    }
    if (this.pixelMode === 'come') {
      this.pixelMode = 'sit';
      this.facePixelToHero();
      return;
    }
    if (this.pixelMode !== 'fetch' || !this.fetch) return;
    if (this.fetch.stage === 'run') {
      this.fetch.stage = 'pick';
      this.pixelTimer = 0.35;
      this.nut = null;
      sfx.key();
    } else if (this.fetch.stage === 'back') {
      this.fetch = null;
      this.items.add('ecrou');
      this.counters.nut = (this.counters.nut ?? 0) + 1;
      this.unlockCheck();
      this.locked = false;
      this.facePixelToHero();
      this.pixelMode = 'pet';
      this.pixelTimer = 1.4;
      this.idle = 3;
      sfx.pixelHappy();
      ui.toast('Pixel rapporte l’écrou !');
    }
  }

  // ---------- les souvenirs de Pixel ----------
  /** Temps restant de la projection en jeu (le cône de lumière depuis l'œil de Pixel). */
  private projecting = 0;

  private plugMemory(n: number) {
    const p = this.pixel;
    if (!p) return ui.say(['Une carte mémoire abîmée. Le connecteur a une forme étrange…', 'On dirait une prise faite pour un robot.']);
    if (this.map.dark) return ui.say(['Pas ici. Pixel tremble trop.']);
    if (this.map.outdoor && (this.heatPhase === 'warn' || this.heatPhase === 'wave')) return ui.say(['Pas maintenant : la chaleur affole Pixel.']);
    this.locked = true;
    releaseAll();
    p.walk = null;
    this.pixelMode = 'sit';
    this.facePixelToHero();
    this.heroCrouch = 1.2;
    sfx.door();
    // la petite trappe s'ouvre, l'œil s'éteint, puis projette
    window.setTimeout(() => {
      sfx.projector();
      this.projecting = 1.3;
    }, 600);
    window.setTimeout(() => {
      playTheme('home');
      ui.openMemory(n, () => {
        this.items.delete(`memo${n}`);
        this.flags.add(`memo${n}Seen`);
        this.locked = false;
        this.projecting = 0;
        this.startMusic();
        this.addClue(`memo${n}`);
        // Pixel secoue la tête, comme au sortir d'un rêve
        this.pixelMode = 'pet';
        this.pixelTimer = 1.2;
        this.save();
      });
    }, 1900);
  }

  /** Revoir un souvenir depuis le journal (Pixel n'a pas besoin d'être là). */
  replayMemory(n: number) {
    playTheme('home');
    ui.openMemory(n, () => this.startMusic());
  }

  /** Succès : on vérifie ceux qui viennent d'être atteints. */
  private unlockCheck() {
    for (const a of ACHIEVEMENTS) {
      if (this.flags.has(`ach_${a.id}`)) continue;
      if ((this.counters[a.counter] ?? 0) >= a.goal) {
        this.flags.add(`ach_${a.id}`);
        ui.achievement(a.title, a.text);
        this.save();
      }
    }
  }

  private petPixel() {
    if (!this.pixel || this.pixelMode === 'fetch') return;
    this.pixelMode = 'pet';
    this.pixelTimer = 1.8;
    this.heroCrouch = 1.5;
    this.idle = Math.max(this.idle, 3);
    this.facePixelToHero();
    this.flags.add('petPixel');
    sfx.pixelHappy();
    const hx = this.pixel.x * T + 8;
    const hy = this.pixel.y * T + 2;
    for (let i = 0; i < 3; i++) this.fx.push({ kind: 'heart', x: hx - 3 + i * 3, y: hy, vx: (i - 1) * 3, vy: -14, life: 1.3 + i * 0.35, max: 1.3 + i * 0.35 });
  }

  private throwNut() {
    const p = this.pixel;
    if (!p) return ui.say(['Tu fais sauter l’écrou dans ta main. Personne pour courir après…']);
    if (this.map.dark) return ui.say(['Pixel se colle à tes jambes. Pas question de courir dans le noir.']);
    const [dx, dy] = DELTA[this.dir];
    let n = 0;
    for (let i = 1; i <= 4; i++) {
      if (!this.pixelFree(this.x + dx * i, this.y + dy * i)) break;
      n = i;
    }
    if (n < 2) return ui.say(['Pas assez de place pour lancer l’écrou par ici.']);
    const tx = this.x + dx * n, ty = this.y + dy * n;
    this.items.delete('ecrou');
    this.locked = true;
    releaseAll();
    p.walk = null;
    this.nut = { fx: this.x * T + 8, fy: this.y * T + 4, tx: tx * T + 8, ty: ty * T + 11, t: 0, dur: 0.14 * n + 0.2, landed: false };
    this.fetch = { stage: 'flying', tx, ty };
    this.pixelMode = 'fetch';
    sfx.throwNut();
  }

  /** Pixel est chez lui : près de la maison de Betti, ou dedans. */
  private atPixelHome() {
    const p = this.pixel;
    if (!p) return false;
    return this.map.id === 'maisonLea' || (this.map.id === 'quartier' && Math.abs(p.x - 6) <= 4 && Math.abs(p.y - 7) <= 4);
  }

  private updatePixel(dt: number) {
    for (const f of this.fx) {
      f.life -= dt;
      f.x += f.vx * dt;
      f.y += f.vy * dt;
      if (f.kind === 'dust') f.vy += 40 * dt;
    }
    this.fx = this.fx.filter((f) => f.life > 0);
    this.heroCrouch -= dt;
    if (this.projecting > 0) this.projecting -= dt;
    if (this.endSeq) this.updateEnding(dt);
    for (const pr of this.prints) pr.life -= dt;
    this.prints = this.prints.filter((pr) => pr.life > 0);
    if (this.pop) {
      this.pop.t += dt;
      if (this.pop.t > 1.4) this.pop = null;
    }
    // fumée de l'épave de navette
    this.smokeTimer -= dt;
    if (this.smokeTimer <= 0) {
      this.smokeTimer = 0.35;
      for (const d of this.map.decals ?? []) {
        if (d.kind !== 'shuttle') continue;
        const x = (d.x + d.w * 0.55) * T + (Math.random() - 0.5) * 8;
        const y = (d.y + d.h * 0.35) * T;
        this.fx.push({ kind: 'smoke', x, y, vx: 4 + Math.random() * 4, vy: -6 - Math.random() * 4, life: 3.2, max: 3.2 });
      }
    }
    this.updateCut(dt);
    const p = this.pixel;
    if (!p) return;
    this.pixelTimer -= dt;
    this.fxTimer -= dt;

    // marche autonome
    if (p.walk) {
      const w = p.walk;
      w.t += dt * w.speed;
      const next = w.path[0];
      if (next && next[0] !== w.from[0]) p.dir = next[0] > w.from[0] ? 'right' : 'left';
      while (w.t >= 1 && w.path.length) {
        w.from = w.path.shift()!;
        p.x = w.from[0];
        p.y = w.from[1];
        w.t -= 1;
      }
      if (!w.path.length) {
        p.walk = null;
        this.onPixelArrived();
      }
    }

    // l'écrou lancé
    if (this.nut && !this.nut.landed) {
      this.nut.t += dt / this.nut.dur;
      if (this.nut.t >= 1) {
        this.nut.landed = true;
        for (let i = 0; i < 4; i++) this.fx.push({ kind: 'dust', x: this.nut.tx, y: this.nut.ty, vx: (Math.random() - 0.5) * 30, vy: -20, life: 0.4, max: 0.4 });
        if (this.fetch) {
          this.fetch.stage = 'run';
          const path = this.pixelPath([p.x, p.y], [this.fetch.tx, this.fetch.ty], true, 10) ?? [[this.fetch.tx, this.fetch.ty]];
          this.walkPixel(path, 7);
        }
      }
    }
    if (this.fetch?.stage === 'pick' && this.pixelTimer <= 0) {
      this.fetch.stage = 'back';
      const [dx, dy] = DELTA[this.dir];
      const back: [number, number] = [this.x + dx, this.y + dy];
      this.walkPixel(this.pixelPath([p.x, p.y], back, false, 10) ?? [back], 5);
    }

    // humeurs
    if (this.pixelMode === 'pet' && this.pixelTimer <= 0) this.pixelMode = 'sit';
    if (this.pixelMode === 'dig' && this.pixelTimer <= 0) this.pixelMode = this.idle > 2.5 ? 'sit' : 'follow';
    if (this.pixelMode === 'follow' && !p.walk && !this.moving && !this.busy && this.idle > 2.5) this.pixelCome();
    if (this.pixelMode === 'sit' && !this.map.dark && this.idle > 9 && this.heatPhase === 'none') this.pixelMode = 'rest';
    if (this.pixelMode === 'rest' && this.heatPhase !== 'none' && this.map.outdoor) this.pixelMode = 'sit';

    // petits effets
    if (this.pixelMode === 'dig' && this.fxTimer <= 0) {
      this.fxTimer = 0.12;
      const fxX = p.x * T + (p.dir === 'left' ? 2 : 14);
      this.fx.push({ kind: 'dust', x: fxX, y: p.y * T + 13, vx: (p.dir === 'left' ? 1 : -1) * (10 + Math.random() * 25), vy: -25 - Math.random() * 15, life: 0.45, max: 0.45 });
    }
    if (this.pixelMode === 'rest' && this.fxTimer <= 0) {
      if (this.map.outdoor) {
        this.fxTimer = 0.45;
        this.fx.push({ kind: 'spark', x: p.x * T + 5 + Math.random() * 6, y: p.y * T + 9, vx: 0, vy: -9, life: 0.9, max: 0.9 });
      } else {
        this.fxTimer = 1.5;
        this.fx.push({ kind: 'z', x: p.x * T + (p.dir === 'left' ? 2 : 13), y: p.y * T + 6, vx: p.dir === 'left' ? -3 : 3, vy: -7, life: 1.6, max: 1.6 });
      }
    }
    // dans le noir, il gémit de temps en temps ; chez lui, il jappe de joie
    if (this.map.dark) {
      this.whineTimer -= dt;
      if (this.whineTimer <= 0) {
        this.whineTimer = 6 + Math.random() * 5;
        sfx.pixelWhine();
      }
    } else if (this.atPixelHome()) {
      this.homeBeep -= dt;
      if (this.homeBeep <= 0) {
        this.homeBeep = 5 + Math.random() * 4;
        sfx.pixelHappy();
      }
    }
  }

  private pixelLook(): DogLook {
    const p = this.pixel!;
    const t = this.time;
    const dark = !!this.map.dark;
    const happy = this.atPixelHome();
    const wag = happy ? Math.floor(t * 11) % 2 : Math.floor(t * 2.2) % 2 ? 1 : 2;
    const eye = t % 3.7 < 0.12 ? 'closed' : dark ? 'wide' : 'on';
    if (this.rescue) {
      const flick = Math.floor(t * 7) % 3 === 0 ? 'closed' : 'wide';
      if (this.rescue.stage === 'drag') return { pose: 'stand', frame: Math.floor(t * (this.rescue.quick ? 14 : 6)) % 4, eye: flick, tail: 3, earsDown: true };
      if (p.walk) return { pose: 'stand', frame: Math.floor(t * 16) % 4, eye: 'wide', tail: 3, earsDown: true };
      return { pose: 'sit', eye: 'wide', tail: 3, earsDown: true };
    }
    if (this.wake) {
      // épuisé, couché ; son œil vacille, puis se rallume
      const recovering = this.wake.stood > 0 && this.wake.t > this.wake.stood + 1.2;
      return { pose: 'lie', eye: recovering ? (t % 2 < 0.15 ? 'closed' : 'on') : Math.floor(t * 3) % 4 === 0 ? 'on' : 'closed', tail: 2 };
    }
    if (this.map.outdoor && (this.heatPhase === 'warn' || this.heatPhase === 'wave')) {
      // la chaleur l'affole : oreilles basses, queue rentrée, l'œil écarquillé
      if (p.walk || (this.moving && p.moving)) return { pose: 'stand', frame: Math.floor(t * 10) % 4, eye: 'wide', tail: 3, earsDown: true };
      if (this.pixelMode === 'pet') return { pose: 'sit', eye: 'happy', tail: 2, earsDown: true };
      return { pose: this.pixelMode === 'sit' || this.pixelMode === 'come' ? 'sit' : 'stand', eye: t % 1.6 < 0.1 ? 'closed' : 'wide', tail: 3, earsDown: true };
    }
    if (this.cut?.stage === 'act' && this.cut.kind === 'pixelPower') {
      return { pose: 'sit', eye: this.cut.t > 1.6 ? 'closed' : 'wide', tail: 2, earsDown: true };
    }
    if (p.walk) {
      const run = this.pixelMode === 'fetch';
      return { pose: dark ? 'scared' : 'stand', frame: Math.floor(t * (run ? 16 : 10)) % 4, tail: dark ? 3 : Math.floor(t * 9) % 2, earsDown: dark || run };
    }
    if (this.pixelMode === 'dig' || this.fetch?.stage === 'pick') return { pose: 'dig', frame: Math.floor(t * 9) % 2, tail: Math.floor(t * 7) % 2 };
    if (this.pixelMode === 'pet') return { pose: 'sit', eye: 'happy', tail: Math.floor(t * 13) % 2 };
    if (this.pixelMode === 'rest') {
      return this.map.outdoor
        ? { pose: 'sun', frame: Math.floor(t * 2.5) % 4, eye: 'closed', tail: t % 5 < 0.5 ? 1 : 2 }
        : { pose: 'lie', eye: 'closed', tail: 2 };
    }
    if (dark) return { pose: 'scared', eye, tail: 3 };
    if (this.pixelMode === 'stay') return { pose: 'sit', eye, tail: Math.floor(t * 1.2) % 2 ? 1 : 2 };
    if (this.pixelMode === 'sit' || this.pixelMode === 'come') return { pose: 'sit', eye, tail: wag };
    // il suit : il trottine quand on marche
    const moving = this.moving && p.moving;
    const frame = moving ? (this.moving!.t < 0.5 ? (this.steps % 2 ? 1 : 3) : 0) : 0;
    return { pose: 'stand', frame, eye, tail: moving ? Math.floor(t * 8) % 2 : wag };
  }

  /** La vague à l'écran : ciel qui rougit, éblouissement, air qui ondule, thermomètre, éclair blanc. */
  private renderHeat() {
    const c = this.ctx;
    const outside = this.map.outdoor && !this.map.dark;
    const k = this.heatK();
    if (k > 0 && outside) {
      c.fillStyle = `rgba(255,70,20,${0.22 * k})`;
      c.fillRect(0, 0, view.w, view.h);
      const g = c.createRadialGradient(view.w * 0.85, 0, 0, view.w * 0.85, 0, view.h * 0.9);
      g.addColorStop(0, `rgba(255,245,210,${0.5 * k})`);
      g.addColorStop(1, 'rgba(255,245,210,0)');
      c.fillStyle = g;
      c.fillRect(0, 0, view.w, view.h);
      // l'air qui ondule : des bandes de l'image décalées
      const amp = k * 1.7;
      for (let y = 0; y < view.h; y += 2) {
        const off = Math.round(Math.sin(y * 0.11 + this.time * 7) * amp);
        if (off) c.drawImage(c.canvas, 0, y, view.w, 2, off, y, view.w, 2);
      }
      if (this.heatPhase === 'wave') {
        const pulse = 0.06 + 0.05 * Math.sin(this.time * 5);
        c.fillStyle = `rgba(255,220,160,${pulse})`;
        c.fillRect(0, 0, view.w, view.h);
      }
    } else if (k > 0) {
      c.fillStyle = `rgba(255,90,30,${0.07 * k})`; // dedans, une lueur chaude passe sous les portes
      c.fillRect(0, 0, view.w, view.h);
    }
    // l'éclair blanc quand le héros s'effondre
    if (this.rescue?.stage === 'fall') {
      const a = Math.max(0, 1 - this.rescue.t / (this.rescue.quick ? 0.5 : 1.2));
      c.fillStyle = `rgba(255,250,235,${a})`;
      c.fillRect(0, 0, view.w, view.h);
    }
    // thermomètre de chaleur
    if ((this.heatPhase !== 'none' && outside) || this.heatGauge > 0.01) {
      const x = view.w - 12, y = 8, h = 30;
      const danger = this.heatGauge > 0.7 && Math.floor(this.time * 6) % 2 === 0;
      c.fillStyle = '#14101c';
      c.fillRect(x - 1, y - 1, 7, h + 2);
      c.fillRect(x - 3, y + h - 1, 11, 9);
      c.fillStyle = '#efe6d2';
      c.fillRect(x, y, 5, h);
      c.fillRect(x - 2, y + h, 9, 7);
      const fillH = Math.round(h * Math.min(1, this.heatGauge));
      c.fillStyle = danger ? '#ffef9a' : '#e8442c';
      c.fillRect(x + 1, y + h - fillH, 3, fillH);
      c.fillRect(x - 1, y + h + 1, 7, 5);
      c.fillStyle = 'rgba(255,255,255,0.6)';
      c.fillRect(x + 1, y + 1, 1, h - 2);
      if (this.items.has('combinaison')) {
        c.fillStyle = '#c9ced6';
        c.fillRect(x - 6, y + 2, 3, 3);
      }
    }
  }

  /** Une case qui fait de l'ombre : mur, décor plein, objet qui bloque (pas les portes). */
  private castsShadow(x: number, y: number): boolean {
    if (x < 0 || y < 0 || x >= this.map.width || y >= this.map.height) return false;
    const obj = this.objAt(x, y);
    if (obj) return !obj.door && !obj.passWhen;
    if (charAt(this.map, x, y) === '~') return false; // l'eau ne fait pas d'ombre
    return this.solidChar(x, y);
  }

  /**
   * Ombres portées, lumière venant d'en haut à gauche :
   * - au pied des murs et des bâtiments, une bande d'ombre douce ;
   * - les autres objets (arbres, voitures, caisses, panneaux…) projettent une ombre à leur forme.
   */
  private renderShadows(vis: [string, number, number][], ox: number, oy: number) {
    const c = this.ctx;
    const names = new Map<string, string>();
    for (const [n, x, y] of vis) names.set(`${x},${y}`, n);
    const isWall = (n: string | undefined) => !!n && /(Top|Front)$/.test(n);
    const shaped: [string, number, number][] = [];
    for (const [name, x, y] of vis) {
      const sx = x * T - ox, sy = y * T - oy;
      if (this.castsShadow(x, y)) {
        if (!isWall(name)) shaped.push([name, x, y]);
        continue;
      }
      if (isWall(names.get(`${x},${y - 1}`))) {
        const a = [0.26, 0.18, 0.11, 0.05];
        for (let i = 0; i < a.length; i++) {
          c.fillStyle = `rgba(10,6,20,${a[i]})`;
          c.fillRect(sx, sy + i, T, 1);
        }
      }
      if (isWall(names.get(`${x - 1},${y}`))) {
        c.fillStyle = 'rgba(10,6,20,0.12)';
        c.fillRect(sx, sy, 2, T);
      }
    }
    // ombre à la forme de l'objet, puis l'objet redessiné par-dessus son ombre
    for (const [name, x, y] of shaped) {
      const co = cutout(name, hash(x, y));
      if (!co) continue;
      const obj = this.objAt(x, y);
      const sh = obj ? this.shakeOf(obj) : 0;
      const sx = x * T - ox + sh, sy = y * T - oy;
      c.globalAlpha = 0.26;
      c.drawImage(co.shadow, sx + 2, sy + 2);
      c.globalAlpha = 1;
      c.drawImage(co.img, sx, sy);
    }
  }

  private renderPrints(ox: number, oy: number) {
    const c = this.ctx;
    for (const pr of this.prints) {
      c.fillStyle = `rgba(90,50,20,${Math.min(0.35, pr.life / 9 * 0.35)})`;
      const sx = pr.x * T - ox, sy = pr.y * T - oy;
      if (pr.drag) {
        c.fillStyle = `rgba(80,45,20,${Math.min(0.4, (pr.life / 12) * 0.4)})`;
        c.fillRect(sx + 3, sy + 7, 10, 3);
        continue;
      }
      if (pr.dir === 'left' || pr.dir === 'right') {
        c.fillRect(sx + 4, sy + 9, 2, 1);
        c.fillRect(sx + 9, sy + 12, 2, 1);
      } else {
        c.fillRect(sx + 5, sy + 6, 1, 2);
        c.fillRect(sx + 9, sy + 10, 1, 2);
      }
    }
  }

  /** Le décor qui vit : écrans, capsules, cuves, turbines, robot, emblèmes. */
  private renderAmbient(vis: [string, number, number][], ox: number, oy: number) {
    const c = this.ctx;
    const t = this.time;
    for (const [name, x, y] of vis) {
      const sx = x * T - ox, sy = y * T - oy;
      const ph = (x * 7 + y * 13) % 10; // chaque objet a son propre rythme
      if (this.podGlow > 0 && x === 2 && y === 2 && this.map.id === 'lab') {
        // la capsule 07 s'illumine : la vitre devient lumière, une lueur bleue au sol
        const a = this.podGlow * (0.55 + 0.25 * Math.sin(t * 6));
        c.fillStyle = `rgba(94,240,255,${a})`;
        c.fillRect(sx + 4, sy + 3, 8, 9);
        c.fillStyle = `rgba(200,250,255,${a * 0.8})`;
        c.fillRect(sx + 5, sy + 4, 2, 7);
        c.fillStyle = `rgba(94,240,255,${this.podGlow * 0.18})`;
        c.fillRect(sx - 6, sy + 14, 28, 10);
      }
      if (name === 'terminal') {
        // une ligne de balayage et un curseur qui clignote
        c.fillStyle = 'rgba(120,255,190,0.18)';
        c.fillRect(sx + 4, sy + 6 + Math.floor((t * 6 + ph) % 5), 8, 1);
        if (Math.floor(t * 2 + ph) % 2) { c.fillStyle = '#9dffcf'; c.fillRect(sx + 9, sy + 9, 2, 1); }
      } else if (name === 'archiveTerm') {
        if (Math.floor(t * 2 + ph) % 2) { c.fillStyle = '#7dff9d'; c.fillRect(sx + 10, sy + 6, 1, 1); }
        c.fillStyle = 'rgba(70,224,138,0.12)';
        c.fillRect(sx + 4, sy + 3 + Math.floor((t * 5 + ph) % 5), 8, 1);
      } else if (name === 'capsule' || name === 'capsuleEmpty' || name === 'cultureTankEmpty') {
        // un reflet qui glisse sur la vitre de temps en temps
        const k = ((t + ph * 0.7) % 6) / 0.9;
        if (k < 1) {
          const gx = sx + 4 + Math.floor(k * 9);
          c.fillStyle = 'rgba(220,250,255,0.45)';
          c.fillRect(gx, sy + 3, 1, 9);
          c.fillStyle = 'rgba(220,250,255,0.2)';
          c.fillRect(gx + 1, sy + 3, 1, 9);
        }
      } else if (name === 'capsuleFrost') {
        if (Math.floor(t * 3 + ph) % 7 === 0) { c.fillStyle = '#ffffff'; c.fillRect(sx + 5 + (ph % 6), sy + 4 + (ph % 7), 1, 1); }
      } else if (name === 'cultureTank') {
        // des bulles qui montent dans le liquide
        for (let i = 0; i < 3; i++) {
          const k = (t * 0.6 + i * 0.33 + ph * 0.1) % 1;
          c.fillStyle = 'rgba(255,240,200,0.55)';
          c.fillRect(sx + 5 + ((i * 3 + ph) % 6), sy + 11 - Math.floor(k * 8), 1, 1);
        }
      } else if (name === 'turbine' && this.flags.has('heliosOn')) {
        // les pales tournent
        const f = Math.floor(t * 10) % 2;
        c.fillStyle = '#3a3f48';
        c.fillRect(sx + 4, sy + 6, 8, 6);
        c.fillStyle = '#8a93a2';
        if (f) { c.fillRect(sx + 7, sy + 6, 2, 6); c.fillRect(sx + 4, sy + 8, 8, 2); }
        else { for (let i = 0; i < 6; i++) { c.fillRect(sx + 4 + i + 1, sy + 6 + i, 1, 1); c.fillRect(sx + 10 - i, sy + 6 + i, 1, 1); } }
        c.fillStyle = '#5ef0ff';
        c.fillRect(sx + 12, sy + 4, 1, 1);
      } else if (name === 'robot') {
        if (Math.floor(t * 1.3 + ph) % 3 === 0) { c.fillStyle = '#4a1010'; c.fillRect(sx + 11, sy + 6, 2, 1); }
      } else if (name.endsWith('Emblem')) {
        c.fillStyle = `rgba(94,240,255,${0.06 + 0.06 * Math.sin(t * 2 + ph)})`;
        c.fillRect(sx + 2, sy + 1, 12, 11);
      } else if (name === 'toxic0' || name === 'toxic1') {
        // reflets qui scintillent sur l'eau
        if (Math.floor(t * 4 + ph) % 5 === 0) { c.fillStyle = 'rgba(220,255,200,0.6)'; c.fillRect(sx + 3 + (ph % 9), sy + 4 + (ph % 7), 2, 1); }
      }
    }
  }

  /** Les grands décors s'animent : balise de la tour radio, reflet des tours solaires. */
  private animateDecal(kind: string, left: number, top: number, w: number, _h: number) {
    const c = this.ctx;
    const t = this.time;
    if (kind === 'radioTower') {
      if (Math.floor(t * 1.2) % 2) {
        c.fillStyle = 'rgba(255,60,60,0.3)';
        c.fillRect(left + w / 2 - 3, top - 1, 6, 5);
        c.fillStyle = '#ff4040';
        c.fillRect(left + w / 2 - 1, top + 1, 2, 2);
      }
    } else if (kind === 'tower') {
      const a = 0.25 + 0.25 * Math.sin(t * 1.5);
      c.fillStyle = `rgba(255,236,160,${a})`;
      c.fillRect(left + w / 2 - 2, top + 1, 4, 3);
    } else if (kind === 'dish') {
      if (Math.floor(t * 0.8) % 2) { c.fillStyle = '#ffcf4a'; c.fillRect(left + w / 2, top + 2, 1, 1); }
    }
  }

  /** Les arcs électriques entre Pixel et le boîtier de la porte. */
  private renderZap(ox: number, oy: number) {
    const cut = this.cut;
    if (!cut || cut.stage !== 'act' || cut.kind !== 'pixelPower' || !this.pixel) return;
    const c = this.ctx;
    const [px, py] = this.pixelPixel();
    const ax = px - ox + 8, ay = py - oy + 6;
    const bx = cut.obj.x * T - ox + 8, by = cut.obj.y * T - oy + 8;
    for (let arc = 0; arc < 2; arc++) {
      let x = ax, y = ay;
      c.strokeStyle = arc ? '#ffffff' : 'rgba(94,240,255,0.9)';
      c.lineWidth = 1;
      c.beginPath();
      c.moveTo(x, y);
      for (let i = 1; i <= 6; i++) {
        const k = i / 6;
        x = ax + (bx - ax) * k + (i < 6 ? (Math.random() - 0.5) * 6 : 0);
        y = ay + (by - ay) * k + (i < 6 ? (Math.random() - 0.5) * 6 : 0);
        c.lineTo(Math.round(x) + 0.5, Math.round(y) + 0.5);
      }
      c.stroke();
    }
    // le boîtier s'illumine peu à peu
    c.fillStyle = `rgba(94,240,255,${0.15 + 0.25 * Math.min(1, cut.t / 2)})`;
    c.fillRect(bx - 6, by - 6, 12, 12);
  }

  /** L'objet ramassé brandi au-dessus de la tête, ou un « ! » pour un indice. */
  private renderPop(hx: number, hy: number) {
    const pop = this.pop;
    if (!pop) return;
    const c = this.ctx;
    const k = Math.min(1, pop.t / 0.35);
    const fade = pop.t > 1.1 ? Math.max(0, 1 - (pop.t - 1.1) / 0.3) : 1;
    c.globalAlpha = fade;
    if (pop.kind === 'item') {
      const y = Math.round(hy - 6 - k * 12);
      // rayons de lumière
      c.fillStyle = 'rgba(255,236,160,0.5)';
      const spin = pop.t * 3;
      for (let i = 0; i < 8; i++) {
        const a = spin + (i * Math.PI) / 4;
        c.fillRect(Math.round(hx + 8 + Math.cos(a) * 11), Math.round(y + 8 + Math.sin(a) * 11), 1, 1);
      }
      c.drawImage(iconCanvas(pop.id), Math.round(hx), y);
    } else {
      const y = Math.round(hy - 10 - k * 4);
      c.fillStyle = '#14101c';
      c.fillRect(hx + 5, y, 6, 9);
      c.fillStyle = '#fff4d6';
      c.fillRect(hx + 6, y + 1, 4, 7);
      c.fillStyle = '#e8622c';
      c.fillRect(hx + 7, y + 2, 2, 3);
      c.fillRect(hx + 7, y + 6, 2, 1);
    }
    c.globalAlpha = 1;
  }

  private renderFx(ox: number, oy: number) {
    const c = this.ctx;
    for (const f of this.fx) {
      const a = Math.min(1, f.life / (f.max * 0.5));
      if (f.life > f.max) continue;
      c.globalAlpha = a;
      const x = Math.round(f.x - ox), y = Math.round(f.y - oy);
      if (f.kind === 'heart') {
        c.fillStyle = '#1c1020';
        c.fillRect(x - 1, y, 7, 3); c.fillRect(x, y + 3, 5, 1); c.fillRect(x + 1, y + 4, 3, 1); c.fillRect(x + 2, y + 5, 1, 1);
        c.fillRect(x, y - 1, 2, 1); c.fillRect(x + 3, y - 1, 2, 1);
        c.fillStyle = '#ff6b8a';
        c.fillRect(x, y, 2, 3); c.fillRect(x + 3, y, 2, 3); c.fillRect(x + 1, y + 1, 3, 3); c.fillRect(x + 2, y + 4, 1, 1);
        c.fillStyle = '#ffc2d0';
        c.fillRect(x, y, 1, 1);
      } else if (f.kind === 'z') {
        c.fillStyle = '#e8f4ff';
        c.fillRect(x, y, 3, 1); c.fillRect(x + 1, y + 1, 1, 1); c.fillRect(x, y + 2, 3, 1);
      } else if (f.kind === 'spark') {
        c.fillStyle = '#fff2a0';
        c.fillRect(x, y - 1, 1, 3); c.fillRect(x - 1, y, 3, 1);
      } else if (f.kind === 'smoke') {
        const age = 1 - f.life / f.max;
        const size = 2 + Math.floor(age * 5);
        c.globalAlpha = 0.28 * (1 - age);
        c.fillStyle = '#5a5560';
        c.fillRect(x - (size >> 1), y - (size >> 1), size, size);
      } else if (f.kind === 'steam') {
        const age = 1 - f.life / f.max;
        const size = 1 + Math.floor(age * 4);
        c.globalAlpha = 0.45 * (1 - age);
        c.fillStyle = '#f2f4f8';
        c.fillRect(x - (size >> 1), y - (size >> 1), size, size);
      } else if (f.kind === 'ember') {
        c.fillStyle = Math.random() < 0.3 ? '#fff0a0' : '#ff8a3d';
        c.fillRect(x, y, 1, 1);
      } else if (f.kind === 'zap') {
        c.fillStyle = Math.random() < 0.5 ? '#ffffff' : '#5ef0ff';
        c.fillRect(x, y, 1, 1);
      } else {
        c.fillStyle = '#c9a26a';
        c.fillRect(x, y, 1, 1);
      }
    }
    c.globalAlpha = 1;
    // l'écrou en vol, ou posé au sol
    if (this.nut) {
      const n = this.nut;
      const t = Math.min(1, n.t);
      const x = n.fx + (n.tx - n.fx) * t;
      const y = n.fy + (n.ty - n.fy) * t - Math.sin(Math.PI * t) * 14;
      c.fillStyle = '#1c1020';
      c.fillRect(Math.round(x - ox) - 2, Math.round(y - oy) - 2, 4, 4);
      c.fillStyle = '#c3c9d3';
      c.fillRect(Math.round(x - ox) - 1, Math.round(y - oy) - 1, 2, 2);
    }
  }

  // ---------- vagues de chaleur ----------
  /** Intensité visuelle de la vague, de 0 à 1. */
  heatK(): number {
    const t = this.heatT;
    let k = 0;
    if (this.heatPhase === 'warn') k = 0.12 + 0.45 * (t / HEAT_WARN);
    else if (this.heatPhase === 'wave') k = 0.6 + 0.4 * Math.min(1, t / 3);
    else if (this.heatPhase === 'fade') k = 0.6 * (1 - t / HEAT_FADE);
    return Math.max(0, Math.min(1, k * (0.75 + 0.25 * this.heatStrength)));
  }

  private startHeat(kind: string, strength: number) {
    this.heatPhase = 'warn';
    this.heatT = 0;
    this.heatKind = kind;
    this.heatStrength = strength;
    this.heatSaid = false;
    if (this.pixelMode === 'rest') this.pixelMode = 'sit';
    if (this.pixel) sfx.pixelWhine();
  }

  private maybeStartHeat(dt: number) {
    if (this.heatPhase !== 'none' || !this.map.outdoor || this.cut || this.rescue || this.wake || this.fetch) return;
    const f = this.flags;
    if (this.map.id === 'vesper' && f.has('firstOutside') && !f.has('wave1Done') && this.outdoorSteps >= 6) return this.startHeat('wave1', 0.55);
    if (f.has('pixelOn') && !f.has('wave2Done') && this.outdoorTime > 6) return this.startHeat('wave2', 0.8);
    if (f.has('readLeaDiary') && f.has('wave2Done') && !f.has('wave3Done') && this.outdoorTime > 6) return this.startHeat('wave3', 0.85);
    if (f.has('heliosOn')) {
      this.cycleTimer -= dt;
      if (this.cycleTimer <= 0) {
        this.cycleTimer = 180 + Math.random() * 60;
        this.startHeat('cycle', 1);
      }
    }
  }

  private endHeat() {
    const kind = this.heatKind;
    this.heatPhase = 'none';
    this.heatT = 0;
    if (kind === 'wave1' || kind === 'wave2' || kind === 'wave3') this.flags.add(`${kind}Done`);
    if (kind === 'wave2') {
      this.flags.add('pondDry');
      if (this.map.id === 'vesper' && this.map.outdoor) {
        this.flags.add('pondSeen');
        ui.say(['La vague est passée… Le lac toxique s’est évaporé !', 'Il ne reste qu’une vase craquelée. On peut passer à pied jusqu’à l’abri de chantier.']);
      }
    }
    this.save();
  }

  /** À l'ombre d'un mur ou d'un bâtiment (la case juste au-dessus est un mur). */
  private inShade(): boolean {
    return ['#', 'K', 'X', 'Y', 'W', 'N'].includes(charAt(this.map, this.x, this.y - 1));
  }

  private updateHeat(dt: number) {
    if (this.rescue) this.updateRescue(dt);
    if (this.wake) this.updateWake(dt);
    const frozen = this.busy;
    const outside = this.map.outdoor && !this.map.dark;
    if (!frozen) {
      if (outside) this.outdoorTime += dt;
      this.maybeStartHeat(dt);
      if (this.heatPhase !== 'none') {
        this.heatT += dt;
        if (this.heatPhase === 'warn' && this.heatT >= HEAT_WARN) { this.heatPhase = 'wave'; this.heatT = 0; }
        else if (this.heatPhase === 'wave' && this.heatT >= HEAT_WAVE) { this.heatPhase = 'fade'; this.heatT = 0; }
        else if (this.heatPhase === 'fade' && this.heatT >= HEAT_FADE) this.endHeat();
      }
    }
    // la jauge : elle monte au soleil pendant la vague, redescend à l'abri
    if (this.heatPhase === 'wave' && outside && !frozen && !this.rescue) {
      let rate = 0.085 * this.heatStrength;
      if (this.items.has('combinaison')) rate *= this.flags.has('heliosOn') ? 0.75 : 0.35;
      if (this.inShade()) rate *= 0.5;
      this.heatGauge += rate * dt;
    } else if (!this.rescue && (!frozen || !outside)) {
      this.heatGauge = Math.max(0, this.heatGauge - (outside ? 0.1 : 0.3) * dt);
    }
    if (this.heatKind === 'wave1' || !this.pixel) {
      // pas encore de Pixel pour te ramener : on ne peut pas s'évanouir
      this.heatGauge = Math.min(this.heatGauge, 0.93);
      if (this.heatKind === 'wave1' && this.heatGauge > 0.7 && !this.heatSaid && !frozen) {
        this.heatSaid = true;
        ui.say(['Il fait trop chaud… Je dois rentrer au labo, vite !']);
      }
    }
    if (this.heatGauge >= 1 && this.pixel && !this.rescue && !frozen) this.startRescue();
    // le cœur qui cogne
    if (this.heatGauge > 0.55 && !this.rescue) {
      this.beatTimer -= dt;
      if (this.beatTimer <= 0) {
        this.beatTimer = 1.15 - this.heatGauge * 0.5;
        heartbeat(this.heatGauge);
      }
    }
    // sons
    this.heatSoundTimer -= dt;
    if (this.heatSoundTimer <= 0) {
      this.heatSoundTimer = 0.2;
      const muffle = outside ? 1 : 0.35;
      let siren = 0, rumble = 0;
      if (this.heatPhase === 'warn') { siren = 0.35 + 0.65 * (this.heatT / HEAT_WARN); rumble = 0.4 * (this.heatT / HEAT_WARN); }
      else if (this.heatPhase === 'wave') { siren = Math.max(0, 0.6 - this.heatT / 10); rumble = 1; }
      else if (this.heatPhase === 'fade') rumble = 1 - this.heatT / HEAT_FADE;
      setHeatSound(siren * muffle, rumble * muffle);
    }
    // vapeur sur le lac pendant la vague qui l'assèche, braises dans l'air
    const k = this.heatK();
    this.steamTimer -= dt;
    if (this.steamTimer <= 0 && outside && k > 0.3) {
      this.steamTimer = 0.08;
      if (this.heatKind === 'wave2' && this.map.dryFlag && this.heatPhase !== 'warn') {
        for (let n = 0; n < 6; n++) {
          const x = this.x + Math.floor(Math.random() * 21) - 10, y = this.y + Math.floor(Math.random() * 15) - 7;
          if (charAt(this.map, x, y) === '~') {
            this.fx.push({ kind: 'steam', x: x * T + Math.random() * T, y: y * T + 8, vx: (Math.random() - 0.5) * 6, vy: -10 - Math.random() * 8, life: 1.6, max: 1.6 });
            break;
          }
        }
      }
      if (this.heatPhase === 'wave' && Math.random() < 0.6) {
        this.fx.push({ kind: 'ember', x: this.x * T + (Math.random() - 0.5) * view.w, y: this.y * T + (Math.random() - 0.3) * view.h, vx: 8 + Math.random() * 12, vy: -6 - Math.random() * 10, life: 1.4, max: 1.4 });
      }
      // Pixel surchauffe : de la vapeur sort de son panneau
      if (this.pixel && this.heatPhase === 'wave' && Math.random() < 0.5) {
        const [px, py] = this.pixelPixel();
        this.fx.push({ kind: 'steam', x: px + 6 + Math.random() * 4, y: py + 5, vx: (Math.random() - 0.5) * 4, vy: -12, life: 0.8, max: 0.8 });
      }
    }
    // Pixel gémit plus souvent quand la chaleur monte
    if (this.pixel && outside && this.heatPhase !== 'none' && !this.rescue) {
      this.whineTimer -= dt;
      if (this.whineTimer <= 0) {
        this.whineTimer = this.heatPhase === 'wave' ? 2.5 + Math.random() * 2 : 4 + Math.random() * 3;
        sfx.pixelWhine();
      }
    }
    this.updateHeatBanner(outside);
  }

  private updateHeatBanner(outside: boolean) {
    if (this.rescue || this.wake) return ui.setHeatBanner(null);
    if (this.heatPhase === 'warn') {
      const left = Math.ceil(HEAT_WARN - this.heatT);
      return outside ? ui.setHeatBanner(`⚠ Abrite-toi ! ${left} s`, 'warn') : ui.setHeatBanner('Une sirène, dehors… Reste à l’abri.', 'safe');
    }
    if (this.heatPhase === 'wave') return outside ? ui.setHeatBanner('☀ VAGUE DE CHALEUR !', 'wave') : ui.setHeatBanner('À l’abri. La vague passe dehors.', 'safe');
    if (this.heatPhase === 'none' && this.flags.has('heatForecast') && this.flags.has('heliosOn') && this.cycleTimer < 28 && outside) {
      return ui.setHeatBanner('Indice de chaleur en hausse…', 'info');
    }
    ui.setHeatBanner(null);
  }

  // ---------- le sauvetage par Pixel ----------
  private startRescue() {
    const p = this.pixel!;
    this.locked = true;
    releaseAll();
    this.heatGauge = 1;
    this.pixelMode = 'rescue';
    p.walk = null;
    const quick = this.flags.has('rescued');
    // l'abri ouvert le plus proche, à pied
    let best: { path: [number, number][]; door: MapObject } | null = null;
    for (const o of this.map.objects) {
      if (!o.door || !this.doorOpen(o) || MAPS[o.door.to]?.outdoor !== false) continue;
      for (const [dx, dy] of [[0, 1], [0, -1], [1, 0], [-1, 0]]) {
        const tx = o.x + dx, ty = o.y + dy;
        if (this.blocked(tx, ty)) continue;
        const path = tx === this.x && ty === this.y ? [] : this.pixelPath([this.x, this.y], [tx, ty], true, 80);
        if (path && (!best || path.length < best.path.length)) best = { path, door: o };
      }
    }
    this.rescue = { stage: 'fall', t: 0, path: best?.path ?? [], i: 0, max: quick ? 5 : 8, door: best?.door ?? null, quick };
    sfx.bump();
    heartbeat(1);
  }

  private updateRescue(dt: number) {
    const r = this.rescue!;
    const p = this.pixel!;
    r.t += dt;
    if (r.stage === 'fall' && r.t > (r.quick ? 0.6 : 1.8)) {
      // Pixel accourt : il se place sur la première case du chemin, face au héros
      r.stage = 'fetch';
      r.t = 0;
      const first = r.path[0];
      if (first && !(p.x === first[0] && p.y === first[1])) {
        const way = this.pixelPath([p.x, p.y], first, false, 12) ?? [first];
        this.walkPixel(way, r.quick ? 8 : 5);
      }
    }
    if (r.stage === 'fetch' && !p.walk && r.t > (r.quick ? 0.1 : 0.5)) {
      r.stage = 'drag';
      r.t = 0;
      r.i = 0;
      if (!r.path.length) r.stage = 'out';
      else this.dragStep();
    }
    if (r.stage === 'drag') {
      const d = this.drag;
      if (d) {
        d.t += dt / d.dur;
        if (d.t >= 1) {
          this.drag = null;
          r.i += 1;
          if (r.i >= r.path.length || r.i >= r.max) r.stage = 'out';
          else this.dragStep();
        }
      }
    }
    if (r.stage === 'out' && r.t >= 0) {
      r.t = -999; // une seule fois
      const door = r.door;
      ui.fade(() => {
        const to = door?.door ? door.door : { to: 'lab', x: 5, y: 8, dir: 'up' as Dir };
        this.map = MAPS[to.to];
        this.x = to.x;
        this.y = to.y;
        this.dir = 'down';
        this.moving = null;
        this.drag = null;
        this.outdoorTime = 0;
        this.heatGauge = 0;
        // Pixel s'effondre à côté du héros
        const spots: [number, number][] = [[this.x + 1, this.y], [this.x - 1, this.y], [this.x, this.y - 1], [this.x, this.y + 1]];
        const spot = spots.find(([x, y]) => this.pixelFree(x, y)) ?? [this.x, this.y];
        this.pixel = { x: spot[0], y: spot[1], dir: spot[0] < this.x ? 'right' : 'left', moving: null };
        this.prints = [];
        ui.showPlace(this.map.name);
        this.startMusic();
        this.rescue = null;
        this.wake = { t: 0, first: !r.quick, stood: -1 };
      });
    }
  }

  /** Un pas du sauvetage : Pixel recule d'une case en tirant, le héros glisse derrière lui. */
  private dragStep() {
    const r = this.rescue!;
    const p = this.pixel!;
    const to = r.path[r.i];
    const dur = r.quick ? 0.17 : 0.6;
    // traînée dans la poussière
    this.prints.push({ x: this.x, y: this.y, dir: this.dir, life: 12, drag: true });
    this.drag = { fx: this.x, fy: this.y, t: 0, dur };
    this.x = to[0];
    this.y = to[1];
    const next = r.path[r.i + 1] ?? (r.door ? [r.door.x, r.door.y] as [number, number] : null);
    if (next) {
      p.walk = { from: [p.x, p.y], path: [next], t: 0, speed: 1 / dur };
      p.dir = next[0] > p.x ? 'left' : next[0] < p.x ? 'right' : this.x > p.x ? 'right' : 'left'; // il recule, la tête vers le héros
    }
    for (let n = 0; n < 2; n++)
      this.fx.push({ kind: 'dust', x: this.x * T + 4 + Math.random() * 8, y: this.y * T + 13, vx: (Math.random() - 0.5) * 20, vy: -12, life: 0.4, max: 0.4 });
  }

  private updateWake(dt: number) {
    const w = this.wake!;
    w.t += dt;
    if (w.stood < 0 && w.t > 1.6 && !ui.dialogOpen()) {
      const stand = () => {
        this.wake!.stood = this.wake!.t;
        this.locked = false;
      };
      if (w.first) {
        w.stood = 0; // en attente du dialogue
        ui.say(
          ['…', 'J’ai perdu connaissance. Il faisait si chaud…', 'Pixel m’a traîné jusqu’ici, à l’abri.', 'Il est à bout de forces. Son œil vacille.'],
          () => { this.wake!.stood = this.wake!.t; this.locked = false; },
        );
      } else {
        ui.toast('Pixel t’a ramené à l’abri.');
        stand();
      }
    }
    if (w.stood > 0 && w.t > w.stood + 2.6) {
      this.wake = null;
      this.pixelMode = 'follow';
      this.flags.add('rescued');
      sfx.pixelHappy();
      this.save();
    }
  }

  // ---------- scènes de Pixel : chatière, conduit, énergie ----------
  private startCut(kind: 'pixelFlap' | 'pixelVent' | 'pixelPower' | 'pixelCar', then?: () => void) {
    const id = kind === 'pixelFlap' ? 'leaHouse' : kind === 'pixelVent' ? 'vent' : kind === 'pixelCar' ? 'shinyCar' : 'heliosDoor';
    const obj = this.map.objects.find((o) => o.id === id);
    const p = this.pixel;
    if (!p || !obj) return then?.();
    // la case libre la plus proche devant l'objet (de préférence juste en dessous)
    const spots: [number, number][] = [[obj.x, obj.y + 1], [obj.x - 1, obj.y], [obj.x + 1, obj.y], [obj.x - 1, obj.y + 1], [obj.x + 1, obj.y + 1]];
    let path: [number, number][] | null = null;
    for (const s of spots) {
      if (s[0] === p.x && s[1] === p.y) { path = []; break; }
      if (!this.pixelFree(s[0], s[1])) continue;
      path = this.pixelPath([p.x, p.y], s, false, 12);
      if (path) break;
    }
    if (!path) return then?.();
    this.locked = true;
    releaseAll();
    this.idle = 0;
    this.pixelMode = 'cut';
    this.cut = { kind, obj, stage: 'go', t: 0, snd: 0, then };
    this.walkPixel(path, 3.4);
  }

  private updateCut(dt: number) {
    const cut = this.cut;
    const p = this.pixel;
    if (!cut || !p) return;
    if (cut.stage === 'go' && !p.walk) {
      cut.stage = 'act';
      cut.t = 0;
      if (cut.obj.x !== p.x) p.dir = cut.obj.x > p.x ? 'right' : 'left';
      if (cut.kind === 'pixelPower') sfx.zap();
    }
    if (cut.stage === 'act') {
      cut.t += dt;
      cut.snd -= dt;
      const ox = cut.obj.x * T + 8, oy = cut.obj.y * T + 8;
      if (cut.kind === 'pixelPower') {
        if (cut.snd <= 0) {
          cut.snd = 0.07;
          this.fx.push({ kind: 'zap', x: ox + (Math.random() - 0.5) * 12, y: oy + (Math.random() - 0.5) * 10, vx: (Math.random() - 0.5) * 40, vy: -20 - Math.random() * 30, life: 0.35, max: 0.35 });
        }
        if (cut.t > 2.3) this.endCutAct();
      } else {
        // il disparaît dans la chatière ou le conduit… on l'entend s'activer… il revient
        if (cut.t > 0.6 && cut.t < 2.5 && cut.snd <= 0) {
          cut.snd = cut.kind === 'pixelVent' ? 0.32 + Math.random() * 0.2 : 0.22;
          if (cut.kind === 'pixelVent') {
            sfx.clank();
            this.fx.push({ kind: 'dust', x: ox + (Math.random() - 0.5) * 10, y: oy + 4, vx: (Math.random() - 0.5) * 20, vy: -6, life: 0.6, max: 0.6 });
          } else sfx.scratch();
        }
        if (cut.t > 3.2) this.endCutAct();
      }
    }
    if (cut.stage === 'back' && !p.walk) {
      this.cut = null;
      this.locked = false;
      this.pixelMode = 'follow';
      this.facePixelToHero();
      sfx.pixelHappy();
      cut.then?.();
    }
  }

  private endCutAct() {
    const cut = this.cut!;
    const p = this.pixel!;
    cut.stage = 'back';
    const [dx, dy] = DELTA[this.dir];
    const spots: [number, number][] = [[this.x - dx, this.y - dy], [this.x + dy, this.y + dx], [this.x - dy, this.y - dx], [this.x + dx, this.y + dy]];
    for (const s of spots) {
      if (s[0] === p.x && s[1] === p.y) return this.walkPixel([], 3.4);
      if (!this.pixelFree(s[0], s[1])) continue;
      const path = this.pixelPath([p.x, p.y], s, false, 12);
      if (path) return this.walkPixel(path, 3.4);
    }
    this.walkPixel([], 3.4);
  }

  /** Visibilité de Pixel pendant qu'il passe par la chatière ou le conduit (0 caché, 1 visible). */
  private pixelVisibility(): number {
    const cut = this.cut;
    if (!cut || cut.stage !== 'act' || cut.kind === 'pixelPower') return 1;
    if (cut.t < 0.6) return 1 - cut.t / 0.6;
    if (cut.t < 2.6) return 0;
    return Math.min(1, (cut.t - 2.6) / 0.5);
  }

  /** L'objet qui tremble (porte, conduit) pendant que Pixel s'y affaire. */
  private shakeOf(obj: MapObject): number {
    const cut = this.cut;
    if (!cut || cut.stage !== 'act' || cut.obj !== obj || cut.kind === 'pixelPower') return 0;
    if (cut.t < 0.7 || cut.t > 2.5) return 0;
    return Math.floor(this.time * 18) % 3 === 0 ? 1 : 0;
  }

  // ---------- sac à dos ----------
  useItem(id: string) {
    ui.setBag(false);
    if (id === 'sonde') {
      if (this.flags.has('sondeOn')) {
        this.flags.delete('sondeOn');
        ui.toast('Sonde éteinte');
      } else if (this.flags.has('batteryFound')) {
        // la seule source qu'elle cherchait est trouvée : elle ne capte plus rien
        return ui.say(['Tu allumes la Sonde… Plus aucune source d’énergie à capter.', 'Tu l’éteins.']);
      } else {
        this.flags.add('sondeOn');
        ui.toast('Sonde allumée');
      }
      sfx.select();
      this.save();
      return;
    }
    if (id === 'pelle') return this.dig();
    if (id === 'ecrou') return this.throwNut();
    if (/^memo[1-5]$/.test(id)) return this.plugMemory(Number(id.slice(4)));
    if (id === 'capteur') {
      if (this.map.id === 'sommet') {
        releaseAll();
        ui.openRadio(RADIO_FREQ, () => this.onSignal());
        return;
      }
      if (this.map.dark) return ui.say(['Sous terre, le récepteur ne capte que du silence.']);
      if (this.map.id === 'colline') return ui.say(['Des grésillements, très faibles. Il faudrait prendre de la hauteur… la tour radio ?']);
      return ui.say(['Des grésillements. Rien d’autre. Il faudrait un point très haut.']);
    }
    if (id === 'battery') {
      const target = this.map.objects.find(
        (o) => o.id === 'pixelOff' && !this.flags.has('pixelOn') && Math.max(Math.abs(o.x - this.x), Math.abs(o.y - this.y)) <= 1,
      );
      if (!target) return ui.say(['Il faudrait la brancher sur quelque chose qui manque d’énergie.']);
      ui.say(
        ['Tu branches la batterie BS-1 sur le dos de Pixel.', 'Un ronronnement… ses yeux s’allument d’un bleu vif.', 'Pixel se lève, s’étire, et vient se coller à tes jambes.'],
        () => {
          this.items.delete('battery');
          this.flags.add('pixelOn');
          this.pixel = { x: target.x, y: target.y, dir: 'down', moving: null };
          sfx.success();
          this.refreshQuestions(false);
          this.save();
          // s'il porte déjà la carte tombée de son flanc, Pixel la réclame tout de suite
          if (this.items.has('memo1')) {
            ui.say(['Pixel renifle ton sac. Une petite trappe clignote sur son flanc…'], () => this.plugMemory(1));
          }
        },
      );
      return;
    }
    const it = ITEMS[id];
    ui.say([it ? it.text : '…']);
  }

  // ---------- le transporteur (capsule 07) ----------
  private podInteract() {
    const f = this.flags;
    if (!f.has('heliosOn')) return ui.say(['La capsule 07 est éteinte. Pour un transfert, il faudrait énormément d’énergie… Hélios ?']);
    if (!f.has('podAssembled')) {
      const parts: [string, string][] = [['matrice', 'la Matrice vierge'], ['noyau', 'le Noyau de transfert'], ['antenne', 'l’antenne de synchronisation']];
      const missing = parts.filter(([id]) => !this.items.has(id)).map(([, name]) => name);
      if (missing.length) return ui.say(['D’après les plans, il me manque encore :', `${missing.join(', ')}.`]);
      ui.say(
        ['Tu poses la Matrice vierge dans son logement.', 'Tu insères le Noyau de transfert. Il s’illumine.', 'Tu fixes l’antenne de synchronisation sur le capot.', 'La capsule 07 s’éveille dans un bourdonnement.'],
        () => {
          for (const id of ['matrice', 'noyau', 'antenne']) this.items.delete(id);
          f.add('podAssembled');
          sfx.success();
          this.save();
        },
      );
      return;
    }
    if (!f.has('podTuned')) {
      if (!this.items.has('capteur')) return ui.say(['L’antenne doit être accordée sur la balise d’Azura. Il me faudrait le récepteur.']);
      ui.say(['L’antenne doit être accordée sur la balise d’Azura.', '« SAISIR LA FRÉQUENCE DE LA BALISE ».'], () => {
        releaseAll();
        ui.openKeypad(
          'FRÉQUENCE',
          (code) => {
            if (code !== String(Math.round(RADIO_FREQ * 10)).padStart(3, '0')) {
              sfx.wrong();
              return ui.say(['« AUCUNE BALISE SUR CETTE FRÉQUENCE. »']);
            }
            f.add('podTuned');
            sfx.success();
            this.save();
            ui.say(['« BALISE D’AZURA ACQUISE. »', 'L’antenne capte le signal. Synchronisation possible.']);
          },
          'Fréquence en MHz',
          3,
          1,
        );
      });
      return;
    }
    if (!f.has('podKeyed')) {
      ui.say(['« SAISIR LA CLÉ DE SYNCHRONISATION ».'], () =>
        ui.openKeypad(
          'CLÉ DE SYNCHRONISATION',
          (code) => {
            if (code !== SIGNAL_KEY) {
              sfx.wrong();
              return ui.say(['« CLÉ REFUSÉE. »', 'La clé est cachée dans le signal d’Azura…']);
            }
            f.add('podKeyed');
            f.add('podNeedsPrime');
            sfx.success();
            this.save();
            ui.say(['« CLÉ ACCEPTÉE. »', '« TRANSFERT PRÊT. »', '« AMORCE : SOURCE ISOLÉE REQUISE — TYPE BS-1. »']);
          },
          'Clé à 4 chiffres',
        ),
      );
      return;
    }
    const lines = f.has('primeHint')
      ? ['« AMORCE : SOURCE ISOLÉE REQUISE — TYPE BS-1. »', 'Pixel vient s’asseoir à côté de toi, au pied de la capsule.']
      : [
          '« AMORCE : SOURCE ISOLÉE REQUISE — TYPE BS-1. »',
          'Une BS-1… Il n’en existe qu’une.',
          'Pixel vient s’asseoir à côté de toi, au pied de la capsule. Il ne bouge plus. Il te regarde.',
        ];
    f.add('primeHint');
    ui.say(lines, () => this.pixelWaitAtPod());
  }

  /** Pixel s'assoit tout près, au pied de la capsule, et attend. */
  private pixelWaitAtPod() {
    const p = this.pixel;
    if (!p) return;
    const pod = this.map.objects.find((o) => o.id === 'capsule07');
    const spots: [number, number][] = [[this.x + 1, this.y], [this.x - 1, this.y], [this.x, this.y + 1], [this.x + 1, this.y + 1], [this.x - 1, this.y + 1]];
    if (pod) spots.sort((a, b) => Math.abs(a[0] - pod.x) + Math.abs(a[1] - pod.y) - (Math.abs(b[0] - pod.x) + Math.abs(b[1] - pod.y)));
    for (const s of spots) {
      if (s[0] === p.x && s[1] === p.y) {
        this.pixelMode = 'stay';
        this.facePixelToHero();
        return;
      }
      if (!this.pixelFree(s[0], s[1])) continue;
      const path = this.pixelPath([p.x, p.y], s, false, 8);
      if (!path) continue;
      this.pixelMode = 'stay';
      this.walkPixel(path, 3.2);
      return;
    }
    this.pixelMode = 'stay';
    this.facePixelToHero();
  }

  /** La dernière décision : débrancher la batterie de Pixel… ou une dernière balade. */
  private askPrime() {
    ui.confirm(
      'Pixel te regarde, assis au pied de la capsule.',
      () => this.finale(),
      () => {
        this.pixelMode = 'follow';
        sfx.pixelHappy();
        const hx = this.pixel!.x * T + 8, hy = this.pixel!.y * T + 2;
        for (let i = 0; i < 2; i++) this.fx.push({ kind: 'heart', x: hx - 2 + i * 4, y: hy, vx: (i - 0.5) * 4, vy: -14, life: 1.3, max: 1.3 });
        ui.say(['Pixel bondit sur ses pattes, la queue battante.', 'Allez… encore une balade, tous les deux.']);
      },
      ['Débrancher la batterie de Pixel', 'Encore une dernière balade'],
    );
  }

  private finale() {
    this.locked = true;
    releaseAll();
    this.heroCrouch = 999;
    ui.say(
      [
        'Tu t’agenouilles près de Pixel.',
        'Il s’assoit de lui-même, et tend son dos.',
        'Tu débranches doucement la batterie BS-1.',
        'Ses yeux bleus faiblissent… puis s’éteignent.',
      ],
      () => {
        this.flags.delete('pixelOn');
        this.flags.add('pixelSleep');
        this.pixel = null;
        playTheme('none');
        sfx.key();
        this.pop = { kind: 'item', id: 'battery', t: 0 };
        this.heroCrouch = 1;
        // le chemin jusqu'au pied de la capsule
        const pod = this.map.objects.find((o) => o.id === 'capsule07');
        const front: [number, number] = pod ? [pod.x, pod.y + 1] : [this.x, this.y];
        const path = this.x === front[0] && this.y === front[1] ? [] : this.pixelPath([this.x, this.y], front, true, 20) ?? [];
        this.endSeq = { stage: 'unplug', t: 0, path };
      },
    );
  }

  private endStep(to: [number, number], dur: number) {
    this.dir = to[0] > this.x ? 'right' : to[0] < this.x ? 'left' : to[1] > this.y ? 'down' : 'up';
    this.drag = { fx: this.x, fy: this.y, t: 0, dur };
    this.x = to[0];
    this.y = to[1];
    sfx.step();
  }

  private updateEnding(dt: number) {
    const e = this.endSeq!;
    e.t += dt;
    if (this.drag) {
      this.drag.t += dt / this.drag.dur;
      if (this.drag.t >= 1) this.drag = null;
    }
    if (e.stage !== 'unplug' && e.stage !== 'walk') this.podGlow = Math.min(1, this.podGlow + dt * 0.6);
    if (e.stage === 'unplug' && e.t > 1.4) {
      e.stage = 'walk';
      e.t = 0;
    }
    if (e.stage === 'walk' && !this.drag) {
      const next = e.path.shift();
      if (next) return this.endStep(next, 0.32);
      // devant la capsule : on y glisse la batterie
      e.stage = 'prime';
      e.t = 0;
      this.dir = 'up';
      this.heroCrouch = 1.2;
      sfx.door();
      ui.say(['Tu glisses la batterie dans le logement de l’amorce.', 'La capsule s’éclaire et ronronne.'], () => {
        // le héros entre dans la capsule
        const pod = this.map.objects.find((o) => o.id === 'capsule07');
        e.stage = 'enter';
        e.t = 0;
        if (pod) this.endStep([pod.x, pod.y], 1.1);
      });
      return;
    }
    if (e.stage === 'enter') {
      this.heroAlpha = Math.max(0, 1 - e.t / 1.1);
      if (e.t >= 1.1) {
        this.heroAlpha = 0;
        e.stage = 'glow';
        e.t = 0;
        sfx.success();
      }
    }
    if (e.stage === 'glow' && e.t > 1.8) {
      this.endSeq = null;
      ui.say(['Tu t’allonges dans la capsule 07. Pixel est couché à son pied.', ...FINALE], async () => {
        await ui.playFinale(dogAsleep(), () => { this.blackout = true; });
        this.locked = false;
        this.onFinished();
      });
    }
  }


  private onSignal() {
    if (this.flags.has('signalFound')) return;
    this.flags.add('signalFound');
    sfx.success();
    ui.say(
      [
        '… Là ! Sur 47,2, un signal se détache du bruit.',
        'Une suite de bips, toujours la même :\n–··   ··–   –––   ·–·',
        'Régulier, insistant. Il vient de très loin, de la planète d’Aurore.',
        'Ce n’est pas du silence… mais je n’y comprends rien. Le message est indéchiffrable.',
      ],
      () => this.addClue('mis7'),
    );
    this.save();
  }

  /** Près de l'endroit indiqué par le journal de Betti : sous le potager, à deux pas à droite du grand arbre. */
  private nearCabin() {
    const hatch = this.map.objects.find((o) => o.id === 'cabinHatch');
    return (
      !!hatch &&
      this.flags.has('readLeaDiary') &&
      !this.flags.has('knowsCabin') &&
      Math.max(Math.abs(this.x - hatch.x), Math.abs(this.y - hatch.y)) <= 1
    );
  }

  private dig() {
    this.heroCrouch = 0.9;
    if (this.pixel && !this.pixel.walk) {
      this.pixelMode = 'dig';
      this.pixelTimer = 1.4;
      // Pixel se tourne vers toi et gratte le sol à ses pieds
      this.pixel.dir = this.x >= this.pixel.x ? 'right' : 'left';
    }
    if (this.map.id === 'quartier' && !this.flags.has('memo2Found') && Math.max(Math.abs(this.x - 9), Math.abs(this.y - 9)) <= 1) {
      ui.say(['Tu creuses à côté de la boîte aux lettres…', 'Un petit trésor enterré : une carte mémoire, enveloppée dans un chiffon.'], () => {
        this.flags.add('memo2Found');
        this.api.item('memo2');
        this.save();
      });
      return;
    }
    if (this.nearCabin()) {
      ui.say(['Tu plantes la pelle dans la terre du potager…', 'Elle heurte du bois. Une trappe !'], () => {
        sfx.door();
        this.flags.add('knowsCabin');
        this.save();
      });
      return;
    }
    const ch = charAt(this.map, this.x, this.y);
    if (ch !== 'S') return ui.say(['Le sol est trop dur ici. Il faudrait du sable.']);
    const key = `dug:${this.map.id}:${this.x},${this.y}`;
    if (this.flags.has(key)) return ui.say(['J’ai déjà creusé ici.']);
    this.flags.add(key);
    sfx.page();
    const src = this.nearestSource();
    const found = src && src.d <= 1 && this.flags.has('sondeOn') && this.flags.has('knowsBattery');
    if (found) {
      ui.say(['Tu creuses… La pelle heurte quelque chose de dur.', 'Une batterie solaire, enveloppée dans une bâche : le prototype BS-1 !'], () => {
        this.flags.add('batteryFound');
        this.api.item('battery');
        this.flags.delete('sondeOn'); // sa mission est accomplie
        ui.toast('Sonde éteinte');
        this.save();
      });
    } else {
      ui.say(['Tu creuses… rien que du sable.', this.flags.has('sondeOn') ? 'La Sonde n’indique rien de précis ici.' : 'Creuser au hasard ne mènera nulle part.']);
      this.save();
    }
  }

  // ---------- Sonde Lumen ----------
  private nearestSource(): { d: number } | null {
    let best: number | null = null;
    for (const e of this.map.energy ?? []) {
      if (this.flags.has(e.goneWhen)) continue;
      const d = Math.max(Math.abs(e.x - this.x), Math.abs(e.y - this.y));
      if (best === null || d < best) best = d;
    }
    return best === null ? null : { d: best };
  }

  private updateDetector(dt: number) {
    const on = this.flags.has('sondeOn') && !this.blackout;
    let level = 0;
    if (on) {
      const src = this.nearestSource();
      if (src) level = src.d <= 1 ? 3 : src.d <= 4 ? 2 : src.d <= 10 ? 1 : 0;
      this.beepTimer -= dt;
      const every = [0, 1.4, 0.6, 0.22][level];
      if (level > 0 && this.beepTimer <= 0) {
        sfx.key();
        this.beepTimer = every;
      }
    }
    ui.setDetector(on, level);
  }

  // ---------- API offerte aux scripts de l'histoire ----------
  api: Api = {
    has: (f) => this.flags.has(f),
    set: (f) => {
      this.flags.add(f);
      this.refreshQuestions(false);
      this.save();
    },
    hasItem: (id) => this.items.has(id),
    item: (id) => {
      if (this.items.has(id)) return;
      this.items.add(id);
      ui.toast(`Objet obtenu : ${ITEMS[id]?.name ?? id}`);
      this.pop = { kind: 'item', id, t: 0 };
      sfx.item();
      document.getElementById('btn-bag')?.classList.add('fresh');
      this.save();
    },
    clue: (id) => this.addClue(id),
    say: (lines, then) => ui.say(lines, then),
    keypad: (title, cb) => {
      releaseAll();
      ui.openKeypad(title, cb);
    },
    sfx: (name) => sfx[name](),
    ui: (kind, then) => {
      releaseAll();
      if (kind === 'switches') ui.openSwitches(SWITCHES, RESTART_ORDER, () => then?.());
      else if (kind === 'pixelFlap' || kind === 'pixelVent' || kind === 'pixelPower' || kind === 'pixelCar') this.startCut(kind, then);
      else if (kind === 'archives')
        ui.openTerminal({
          folders: ARCHIVES,
          code: ARCHIVE_CODE,
          loggedIn: this.flags.has('archLogin'),
          unlocked: new Set(ARCHIVES.filter((f) => this.flags.has('archUnlock_' + f.id)).map((f) => f.id)),
          onEvent: (ev) => {
            this.flags.add(ev === 'login' ? 'archLogin' : ev === 'azura' ? 'archAzura' : ev.startsWith('unlock:') ? 'archUnlock_' + ev.slice(7) : 'arch_' + ev);
            this.save();
          },
          onClose: then,
        });
      else if (kind === 'orbit') ui.openViewer('Carte des orbites', ui.orbitChart(), then);
      else ui.openViewer('Grille de décodage', ui.codebookTable(), then);
    },
  };

  /** Appelé quand la scène finale est terminée (main.ts revient à l'écran titre). */
  onFinished: () => void = () => {};

  startMusic() {
    // musique principale par défaut ; une berceuse plus douce chez Betti
    playTheme(this.map.id === 'maisonLea' || this.map.id === 'cabane' ? 'home' : this.map.outdoor ? 'outdoor' : 'lab');
  }

  known(id: string) {
    return this.clues.has(id) || this.flags.has(id);
  }

  addClue(id: string) {
    if (this.clues.has(id)) return;
    this.clues.add(id);
    this.fresh.add(id);
    const c = CLUES.find((x) => x.id === id);
    ui.toast(`Journal mis à jour : ${c?.title ?? id}`);
    if (this.pop?.kind !== 'item') this.pop = { kind: 'clue', id, t: 0 };
    sfx.clue();
    document.getElementById('btn-journal')?.classList.add('fresh');
    this.refreshQuestions(false);
    this.save();
  }

  /** Ouvre ou résout les questions du journal selon ce qui est connu. */
  refreshQuestions(silent: boolean) {
    for (const q of QUESTIONS) {
      const open = q.opensWith.some((c) => this.clues.has(c));
      const solved = open && this.known(q.answeredBy);
      if (open && !this.openQ.has(q.id)) {
        this.openQ.add(q.id);
        if (!silent && !solved) {
          this.fresh.add(q.id);
          window.setTimeout(() => ui.toast(`Nouvelle question : ${q.ask}`), 1400);
        }
      }
      if (solved && !this.solvedQ.has(q.id)) {
        this.solvedQ.add(q.id);
        if (!silent) {
          this.fresh.add(q.id);
          window.setTimeout(() => ui.toast(`Question résolue : ${q.ask}`), 1400);
          document.getElementById('btn-journal')?.classList.add('fresh');
        }
      }
    }
  }

  openJournal() {
    ui.renderJournal(this.clues, this.fresh, this.openQ, this.solvedQ, (id) => this.flags.has(id) || this.items.has(id),
      ACHIEVEMENTS.map((a) => ({ title: a.title, text: a.text, done: this.flags.has(`ach_${a.id}`), progress: `${Math.min(a.goal, this.counters[a.counter] ?? 0)}/${a.goal}` })),
      (n) => this.replayMemory(n));
    ui.setJournal(true);
    releaseAll();
    // tout ce qui vient d'être affiché est désormais « lu »
    this.fresh.clear();
    document.getElementById('btn-journal')?.classList.remove('fresh');
    this.save();
  }

  openBag() {
    ui.renderBag([...this.items], (id) => this.useItem(id), this.flags.has('sondeOn'), !!this.pixel);
    ui.setBag(true);
    releaseAll();
    document.getElementById('btn-bag')?.classList.remove('fresh');
  }

  // ---------- rendu ----------
  private tileName(x: number, y: number): string {
    const m = this.map;
    const mark = m.marks?.find((k) => k.x === x && k.y === y);
    if (mark) return mark.sprite;
    const ch = charAt(m, x, y);
    const below = y + 1 >= m.height ? ch : charAt(m, x, y + 1);
    if (ch === '#' && m.skins) {
      const sk = m.skins.find((k) => x >= k.x && x < k.x + k.w && y >= k.y && y < k.y + k.h);
      if (sk) return `${sk.style}${below === '#' && y + 1 < sk.y + sk.h ? 'Top' : 'Front'}`;
    }
    switch (ch) {
      case 'H': return 'pad';
      case 'N': return m.solidBase ?? 'pad';
      case '.': return 'dust';
      case '"': return 'grass';
      case ',': return 'asphalt';
      case '-': return 'road';
      case '~':
        if (m.dryFlag && this.flags.has(m.dryFlag)) return 'mud';
        return Math.floor(this.time * 1.6 + (x + y) * 0.35) % 2 ? 'toxic1' : 'toxic0';
      case '*': return 'rubble';
      case '|': return 'fence';
      case 'T': return 'tree';
      case 'C': return 'car';
      case 'S': return this.flags.has(`dug:${this.map.id}:${x},${y}`) ? 'hole' : 'sand';
      case 'P': return 'panel';
      case 'v': return 'deadPlants';
      case '=': return 'labFloor';
      case '#': return below === '#' ? 'wallTop' : 'wallFront';
      case 'X': return below === 'X' ? 'labWallTop' : 'labWallFront';
      case 'Y': return below === 'Y' ? 'wallpaperTop' : 'wallpaperFront';
      case 'K': return below === 'K' ? 'plankTop' : 'plankFront';
      case 'W': return below === 'W' ? 'metroWallTop' : 'metroWallFront';
      case 'w': return 'woodFloor';
      case 'm': return 'platform';
      case '_': return 'platformEdge';
      case 'r': return 'rails';
      case 'k': return 'sky';
      case 'g': return 'grating';
      default: return 'dust';
    }
  }

  heroPixel(): [number, number] {
    if (this.drag) {
      const t = Math.min(1, this.drag.t);
      return [(this.drag.fx + (this.x - this.drag.fx) * t) * T, (this.drag.fy + (this.y - this.drag.fy) * t) * T];
    }
    if (!this.moving) return [this.x * T, this.y * T];
    const t = Math.min(1, this.moving.t);
    return [(this.moving.fx + (this.x - this.moving.fx) * t) * T, (this.moving.fy + (this.y - this.moving.fy) * t) * T];
  }

  private pixelPixel(): [number, number] {
    const p = this.pixel!;
    if (p.walk && p.walk.path.length) {
      const [ax, ay] = p.walk.from;
      const [bx, by] = p.walk.path[0];
      const t = Math.min(1, p.walk.t);
      return [(ax + (bx - ax) * t) * T, (ay + (by - ay) * t) * T];
    }
    if (!p.moving || !this.moving) return [p.x * T, p.y * T];
    const t = Math.min(1, this.moving.t);
    return [(p.moving.fx + (p.x - p.moving.fx) * t) * T, (p.moving.fy + (p.y - p.moving.fy) * t) * T];
  }

  render() {
    const c = this.ctx;
    c.imageSmoothingEnabled = false;
    c.fillStyle = '#05060c';
    c.fillRect(0, 0, view.w, view.h);
    if (this.blackout) return;

    const [hx, hy] = this.heroPixel();
    const mw = this.map.width * T;
    const mh = this.map.height * T;
    // caméra toujours centrée sur le héros, comme dans Pokémon (au-delà du bord : décor de ruines)
    const camX = hx + T / 2 - view.w / 2;
    const visH = view.h - view.padBottom; // on garde le héros au-dessus des commandes
    const camY = hy + T / 2 - visH / 2;
    const ox = Math.round(camX);
    const oy = Math.round(camY);

    const x0 = Math.floor(ox / T) - 1;
    const y0 = Math.floor(oy / T) - 1;
    const vis: [string, number, number][] = [];
    for (let y = y0; y <= y0 + view.h / T + 2; y++) {
      for (let x = x0; x <= x0 + view.w / T + 2; x++) {
        if (x < 0 || y < 0 || x >= this.map.width || y >= this.map.height) {
          const voidTile = this.map.voidTile ?? (this.map.outdoor ? 'rubble' : '');
          if (voidTile) c.drawImage(tile(voidTile, hash(x, y)), x * T - ox, y * T - oy);
          continue;
        }
        const obj = this.objAt(x, y);
        const sprite = obj ? this.objSprite(obj) : '';
        const name = sprite || this.tileName(x, y);
        const sh = obj ? this.shakeOf(obj) : 0;
        c.drawImage(tile(name, hash(x, y)), x * T - ox + sh, y * T - oy);
        vis.push([name, x, y]);
      }
    }
    this.renderShadows(vis, ox, oy);
    this.renderPrints(ox, oy);
    this.renderAmbient(vis, ox, oy);

    // grands décors, alignés sur le bas de leur emprise
    for (const d of this.map.decals ?? []) {
      const img =
        d.kind === 'shuttle' ? this.decalShuttle : d.kind === 'dish' ? this.decalDish : d.kind === 'radioTower' ? this.decalRadio
        : d.kind === 'train' ? this.decalTrain : d.kind === 'bigTree' ? this.decalBigTree : this.decalTower;
      const left = d.x * T - ox, top = (d.y + d.h) * T - img.height - oy;
      {
        // une ombre douce au pied des grands décors
        c.fillStyle = 'rgba(0,0,0,0.22)';
        c.beginPath();
        c.ellipse(left + img.width / 2 + 3, top + img.height - 2, img.width * 0.44, 4, 0, 0, Math.PI * 2);
        c.fill();
      }
      c.drawImage(img, left, top);
      this.animateDecal(d.kind, left, top, img.width, img.height);
    }

    // indicateur au-dessus de l'objet regardé
    if (!this.busy && !this.moving) {
      const [fx, fy] = this.facing();
      const obj = this.objAt(fx, fy);
      if (obj?.script) {
        const bob = Math.round(Math.sin(this.time * 6) * 1.5);
        const px = fx * T - ox + 6;
        const py = fy * T - oy - 7 + bob;
        c.fillStyle = '#14101c';
        c.fillRect(px - 1, py - 1, 6, 7);
        c.fillStyle = '#fff4d6';
        c.fillRect(px, py, 4, 5);
        c.fillStyle = '#14101c';
        c.fillRect(px + 1, py + 1, 2, 2);
        c.fillRect(px + 1, py + 4, 2, 1);
      }
    }

    let frame = 0;
    if (this.moving && this.moving.t < 0.75) frame = this.steps % 2 ? 1 : 2;
    else if (this.heroCrouch > 0) frame = 3;
    if (this.rescue || (this.wake && this.wake.stood <= 0)) frame = 5;
    if (this.endSeq && this.drag && this.endSeq.stage === 'walk') frame = Math.floor(this.time * 7) % 2 ? 1 : 2;
    else if (!this.moving && this.idle > 1.5 && Math.floor(this.time / 0.9) % 2) frame = 4;
    const suit = this.items.has('combinaison');
    const drawHero = () => {
      if (this.heroAlpha <= 0) return;
      c.globalAlpha = this.heroAlpha;
      c.drawImage(hero(this.dir, frame, suit), Math.round(hx - ox), Math.round(hy - oy) - (frame === 5 ? 0 : 3));
      c.globalAlpha = 1;
    };
    if (this.pixel) {
      const [px, py] = this.pixelPixel();
      const pdir = this.pixel.dir === 'left' ? 'left' : 'right';
      const look = this.pixelLook();
      // dans le noir, immobile, il tremble
      const shiver = look.pose === 'scared' && !this.pixel.walk && !this.moving ? Math.floor(this.time * 14) % 2 : 0;
      const carrying = this.fetch?.stage === 'back';
      const vis = this.pixelVisibility();
      const drawDog = () => {
        if (vis <= 0) return;
        let dx = Math.round(px - ox) + shiver, dy = Math.round(py - oy) - 1;
        if (vis < 1 && this.cut) {
          // il se faufile vers la chatière / le conduit
          dx += Math.round((this.cut.obj.x * T - px) * (1 - vis) * 0.5);
          dy += Math.round((this.cut.obj.y * T - py) * (1 - vis) * 0.5);
          c.globalAlpha = vis;
        }
        c.drawImage(dogSprite(pdir, look), dx, dy);
        c.globalAlpha = 1;
        // une carte pas encore lue dans le sac : la trappe de son flanc clignote
        if (!this.projecting && [1, 2, 3, 4, 5].some((n) => this.items.has(`memo${n}`)) && Math.floor(this.time * 2.5) % 2) {
          c.fillStyle = '#ffcf4a';
          c.fillRect(dx + (pdir === 'left' ? 9 : 6), dy + 9, 1, 1);
        }
        if (this.projecting > 0) {
          // le cône de lumière qui sort de son œil
          const ex = dx + (pdir === 'left' ? 4 : 12), ey = dy + 5;
          const dirx = pdir === 'left' ? -1 : 1;
          const a = Math.min(1, this.projecting / 0.4) * (0.35 + 0.1 * Math.sin(this.time * 30));
          c.fillStyle = `rgba(94,240,255,${a})`;
          c.beginPath();
          c.moveTo(ex, ey);
          c.lineTo(ex + dirx * 40, ey - 18);
          c.lineTo(ex + dirx * 40, ey + 14);
          c.closePath();
          c.fill();
          c.fillStyle = '#e8ffff';
          c.fillRect(ex - 1, ey - 1, 2, 2);
        }
        if (this.rescue?.stage === 'drag') {
          // l'écharpe tendue entre la gueule de Pixel et le héros
          const mx = pdir === 'left' ? dx + 1 : dx + 14;
          c.strokeStyle = '#c0423b';
          c.lineWidth = 1;
          c.beginPath();
          c.moveTo(mx + 0.5, dy + 7.5);
          c.lineTo(Math.round(hx - ox) + 8.5, Math.round(hy - oy) + 9.5);
          c.stroke();
        }
        if (carrying) {
          // l'écrou dans la gueule
          const mx = pdir === 'left' ? dx + 0 : dx + 14;
          c.fillStyle = '#1c1020';
          c.fillRect(mx - 1, dy + 6, 4, 3);
          c.fillStyle = '#c3c9d3';
          c.fillRect(mx, dy + 7, 2, 1);
        }
      };
      if (py <= hy) {
        drawDog();
        drawHero();
      } else {
        drawHero();
        drawDog();
      }
    } else drawHero();
    this.renderFx(ox, oy);
    this.renderZap(ox, oy);
    this.renderPop(hx - ox, hy - oy);

    this.renderAtmosphere();
    this.renderHeat();
    if (this.map.dark) {
      this.renderDarkness(hx - ox + T / 2, hy - oy + T / 2 - 2);
      // dans le noir, on devine Pixel à la lueur de son œil
      if (this.pixel && this.time % 3.7 >= 0.12) {
        const [px, py] = this.pixelPixel();
        const shiver = !this.pixel.walk && !this.moving ? Math.floor(this.time * 14) % 2 : 0;
        const ex = Math.round(px - ox) + shiver + (this.pixel.dir === 'left' ? 2 : 12);
        const ey = Math.round(py - oy) - 1 + 6;
        c.fillStyle = 'rgba(94,240,255,0.25)';
        c.fillRect(ex - 1, ey - 1, 4, 4);
        c.fillStyle = '#5ef0ff';
        c.fillRect(ex, ey, 2, 2);
      }
    }
  }

  /** Le noir complet, sauf un halo autour du héros : grand avec la lampe, minuscule sans. */
  private renderDarkness(cx: number, cy: number) {
    const c = this.ctx;
    const lamp = this.items.has('lampe');
    const flicker = lamp ? Math.sin(this.time * 9) * 1.5 + Math.sin(this.time * 23) * 0.8 : 0;
    const inner = lamp ? 26 + flicker : 6;
    const outer = lamp ? 64 + flicker : 16;
    const g = c.createRadialGradient(cx, cy, inner, cx, cy, outer);
    g.addColorStop(0, 'rgba(4,3,8,0)');
    g.addColorStop(0.7, 'rgba(4,3,8,0.85)');
    g.addColorStop(1, 'rgba(4,3,8,0.98)');
    c.fillStyle = g;
    c.fillRect(0, 0, view.w, view.h);
    if (lamp) {
      c.fillStyle = 'rgba(255,230,160,0.06)';
      c.beginPath();
      c.arc(cx, cy, inner, 0, Math.PI * 2);
      c.fill();
    }
  }

  private objSprite(o: MapObject): string {
    if (o.spriteWhen && this.flags.has(o.spriteWhen[0])) return o.spriteWhen[1];
    return o.sprite;
  }

  private newParticle(anywhere: boolean): Particle {
    return {
      x: anywhere ? Math.random() * view.w : -4,
      y: Math.random() * view.h,
      vx: 6 + Math.random() * 10,
      vy: 1 + Math.random() * 4,
      a: 0.15 + Math.random() * 0.35,
    };
  }

  private updateParticles(dt: number) {
    for (let i = 0; i < this.particles.length; i++) {
      const p = this.particles[i];
      const gust = 1 + 4 * this.heatK(); // la poussière s'emballe à l'approche d'une vague
      p.x += p.vx * dt * gust;
      p.y += p.vy * dt * gust + Math.sin(this.time * 2 + i) * 0.05;
      if (p.x > view.w + 4 || p.y > view.h + 4) this.particles[i] = this.newParticle(false);
    }
  }

  private renderAtmosphere() {
    const c = this.ctx;
    if (this.map.outdoor) {
      const g = c.createLinearGradient(0, 0, 0, view.h);
      g.addColorStop(0, 'rgba(255,110,40,0.22)');
      g.addColorStop(1, 'rgba(120,30,60,0.12)');
      c.fillStyle = g;
      c.fillRect(0, 0, view.w, view.h);
      for (const p of this.particles) {
        c.fillStyle = `rgba(255,214,160,${p.a})`;
        c.fillRect(Math.round(p.x), Math.round(p.y), 1, 1);
      }
    } else {
      const flicker = Math.sin(this.time * 23) > 0.96 ? 0.12 : 0;
      c.fillStyle = `rgba(20,40,80,${0.18 + flicker})`;
      c.fillRect(0, 0, view.w, view.h);
    }
    const v = c.createRadialGradient(view.w / 2, view.h / 2, view.h * 0.35, view.w / 2, view.h / 2, view.h * 0.75);
    v.addColorStop(0, 'rgba(0,0,0,0)');
    v.addColorStop(1, 'rgba(0,0,0,0.55)');
    c.fillStyle = v;
    c.fillRect(0, 0, view.w, view.h);
  }
}
