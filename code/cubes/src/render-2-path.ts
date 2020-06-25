import * as canvas from 'canvas';
import * as path from 'path';
import * as fs from 'fs';
import { createCanvas } from 'canvas';
import { Point, Ctx, vplus, vscale } from './util';
import { sprintf } from 'sprintf-js';


const SEG = 40;

const WIDTH = 600;
const HEIGHT = 600;

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

class Rel {
  constructor(public d: Ctx, public p: Point) {
    this.moveTo();
  }

  moveTo(): void {
    this.d.moveTo(this.p.x, this.p.y);
  }

  lineTo(): void {
    this.d.lineTo(this.p.x, this.p.y);
  }

  rlineTo(p: Point): void {
    this.add(p);
    this.lineTo();
  }

  add(p: Point): void {
    this.p = vplus(p, this.p);
  }
}

export async function renderPng(N: number): Promise<Buffer> {
  const RAD = N * SEG / Math.PI;
  const ORIGIN = { x: 300 - RAD, y: 300 };

  const c = createCanvas(WIDTH, HEIGHT);
  const d = c.getContext('2d');
  d.fillStyle = 'white';
  d.fillRect(0, 0, WIDTH, HEIGHT);


  const vs: Point[] = [];
  for (let i = 0; i < N; i++) {
    const theta = Math.PI * (i + 1 / 2) / N;
    vs.push(vscale({ x: Math.sin(theta), y: -Math.cos(theta) }, SEG));
  }

  for (let j = 0; j < N; j++) {
    d.beginPath();
    const rel = new Rel(d, ORIGIN);
    for (let i = j; i < N; i++) {
      rel.rlineTo(vs[i]);
    }
    d.stroke();
  }

  for (let j = 1; j < N; j++) {

    const relprev = new Rel(d, ORIGIN);
    const rel = new Rel(d, ORIGIN);
    relprev.add(vs[j - 1]);

    for (let i = j; i < N; i++) {
      relprev.add(vs[i]);
      rel.add(vs[i]);
      d.beginPath();
      relprev.moveTo();
      rel.lineTo();

      d.stroke();
    }
  }

  return getPng(c);
}

async function go(): Promise<void> {
  let frame = 0;
  for (let N = 3; N < 23; N++) {
    const png = await renderPng(N);
    fs.writeFileSync(`/tmp/anim/${sprintf("%03d", frame++)}.png`, png);
  }
  for (let N = 21; N > 3; N--) {
    const png = await renderPng(N);
    fs.writeFileSync(`/tmp/anim/${sprintf("%03d", frame++)}.png`, png);
  }
  // convert   -delay 20   -loop 0   /tmp/anim/*.png   /tmp/animation.gif
}

go().catch(console.error);
