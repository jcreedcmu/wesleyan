import { createCanvas } from 'canvas';
import * as canvas from 'canvas';
import * as fs from 'fs';

type Ctx = canvas.CanvasRenderingContext2D;

async function getPng(c: canvas.Canvas): Promise<Buffer> {
  return new Promise((res, rej) => {
    const stream = c.createPNGStream();
    const bufs: Buffer[] = [];
    stream.on('data', d => bufs.push(d));
    stream.on('end', () => {
      res(Buffer.concat(bufs));
    });
  });
}

function perms(n: number): number[][] {
  if (n == 1) {
    return [[0]];
  }
  else {
    const ps = perms(n - 1);
    const rv = [];
    for (const p of ps) {
      for (let i = n - 1; i >= 0; i--) {
        //		for (let i = 0; i < n; i++) {
        const before = p.slice(0, i);
        const after = p.slice(i, p.length);
        rv.push(before.concat([n - 1], after));
      }
    }
    return rv;
  }
}

function totalPerms(n: number): number[][] {
  return perms(n - 1).map(p => {
    const q = [0].concat(p.map(x => x + 1));
    const r: number[] = [];
    for (let ix = 0; ix < q.length - 1; ix++) {
      r[q[ix]] = q[ix + 1];
    }
    r[q[q.length - 1]] = 0;
    return r;
  });
}

function range(n: number): number[] {
  return Array.from({ length: n }, (x, i) => i);
}

function apply(a: number[], p: number[], o: number) {
  return a.map((x, i) => {
    if (i - o >= 0 && i - o < p.length) {
      return a[o + p[i - o]];
    }
    else {
      return a[i];
    }
  });
}

function moveTo(d: Ctx, p: Point): void {
  d.moveTo(p.x, p.y);
}

function lineTo(d: Ctx, p: Point): void {
  d.lineTo(p.x, p.y);
}


const RADIUS = 2;
const GRID = 60;
const SPAN = 20;
const COLS = 16;
const ARROW_OFF = 3;
const ARROW = 1;
import { Point } from './types';
import { vplus, vscale, vminus, vnorm } from './util';

type Other = { selfInverse: boolean };

function renderp(d: Ctx, perm: number[], at: Point, other: Other) {
  const pts: Point[] = [];
  for (let i = 0; i < perm.length; i++) {
    const theta = 2 * Math.PI * i / perm.length;
    const rawpt = { x: Math.sin(theta), y: -Math.cos(theta) };
    pts.push(vplus(at, vscale(rawpt, SPAN)));
  }

  for (let i = 0; i < perm.length; i++) {

    if (perm[perm[i]] === i) {
      if (i < perm[i]) {
        d.beginPath();
        moveTo(d, pts[i]);
        lineTo(d, pts[perm[i]]);
        d.strokeStyle = "#77f";
        d.stroke();
      }
    }
    else {
      d.beginPath();
      moveTo(d, pts[i]);
      lineTo(d, pts[perm[i]]);
      d.strokeStyle = "black";
      d.stroke();
      d.beginPath();
      const diff = vminus(pts[i], pts[perm[i]]);
      d.save();
      d.translate(pts[perm[i]].x, pts[perm[i]].y);
      d.rotate(Math.atan2(diff.y, diff.x) + 6 * Math.PI / 4);
      d.beginPath();
      d.moveTo(-2 * ARROW, 6 * ARROW);
      d.lineTo(0, ARROW_OFF * ARROW);
      d.lineTo(2 * ARROW, 6 * ARROW);
      d.stroke();
      d.restore();
    }
  }
  let i = 0;
  for (const pt of pts) {
    d.beginPath();
    const spt = pt;
    d.arc(spt.x, spt.y, RADIUS, 0, 2 * Math.PI);
    d.fillStyle = 'gray';
    //    d.font = '4pt sans';
    //    d.fillText(i++ + '', spt.x, spt.y);
    d.fill();
  }
}

function render(d: Ctx) {
  let ix = 0;
  totalPerms(2 * K).forEach(p => {
    const r = range(3 * K);
    const lt = apply(apply(apply(r, p, 0), p, K), p, 0).join(',');
    const rt = apply(apply(apply(r, p, K), p, 0), p, K).join(',');
    const reid3 = lt == rt;
    const reid3txt = reid3 ? '3' : ' ';
    const selfInverse = apply(p, p, 0).join(',') == range(p.length).join(',');
    const selfInverseTxt = selfInverse ? ' ' : '2';

    const moved = p.map((x, i) => ((x == i ? 0 : 1) as number))
      .reduce((x, y) => x + y) + '';
    const info = reid3txt + selfInverseTxt + `${moved.padStart(10)}m`;

    if (reid3) {
      //	 console.log(info);
      const flip = [5, 6, 7, 8, 9, 0, 1, 2, 3, 4];
      // const flip = [4, 5, 6, 7, 0, 1, 2, 3];
      //    const rendered = p;
      //		const rendered = apply(flip, p, 0);
      const rendered = apply(flip, p, 0);
      renderp(d, rendered, vscale({ x: 1 + ix % COLS, y: 1 + Math.floor(ix / COLS) }, GRID), { selfInverse });
      ix++;
      console.log(info + '  ' + p.join(''));
    }
  });
}

const K = 5;
const WIDTH = 1050;
const HEIGHT = 1000;

async function go() {
  const c = canvas.createCanvas(WIDTH, HEIGHT);
  const d = c.getContext('2d');
  d.fillStyle = 'white';
  d.fillRect(0, 0, WIDTH, HEIGHT);
  render(d);
  fs.writeFileSync(`/tmp/a.png`, await getPng(c));
}

go();
