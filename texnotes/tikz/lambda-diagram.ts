import * as fs from 'fs';

type Point = { x: number, y: number };

function lerp(a: number, b: number, t: number): number {
  return (1 - t) * a + t * b;
}

function ptToString(p: Point): string {
  return `(${p.x}, ${p.y})`;
}
class Context {
  buf: string = '';
  constructor() { }

  line(pts: Point[], options?: { [k: string]: string }) {
    const opts: string[] = [];
    opts.push('thick');
    if (options) {
      if (options.color)
        opts.push(options.color);
    }
    this.buf += `\\draw[${opts.join(',')}] ${pts.map(ptToString).join(' -- ')};\n`;
  }

  curve(pts: Point[], options?: { [k: string]: string }) {
    const opts: string[] = [];
    opts.push('thick');
    if (options) {
      if (options.color)
        opts.push(options.color);
    }
    const ps = pts.map(ptToString);
    for (let i = 0; ps.length - i >= 4; i += 4) {
      this.buf += `\\draw[${opts.join(',')}] ${ps[i]} .. controls ${ps[i + 1]} and ${ps[i + 2]} .. ${ps[i + 3]};\n`;
    }
  }

  cycle(pts: Point[]) {
    this.buf += `\\draw[thick] ${pts.map(ptToString).concat(['cycle']).join(' -- ')};\n`;
  }

  fillCircle(center: Point, radius: number, color?: string) {
    if (color == undefined) color = 'black';
    this.buf += `\\fill[${color}] ${ptToString(center)} circle (${radius}pt);\n`;
  }

  node(where: Point, options: { [k: string]: string }) {
    this.buf += `\\draw ${ptToString(where)} node[${options.color}] {${options.text}};\n`;
  }

  color(name: string, r: number, g: number, b: number) {
    this.buf += `\\definecolor{${name}}{rgb}{${r},${g},${b}}\n`;
  }

}

const d = new Context();

const TREE_LEN = 0.2;
const TREE_TENSE = 1.25;
const TREE_NUM = 6;

d.color('grn', 0, 0.7, 0.2);
d.color('blu', 0.4, 0.4, 0.9);

const treelines = Array.from(new Array(TREE_NUM), (x, i) => i)
  .map(i => lerp(-0.5, 0.5, (i + 1) / (TREE_NUM + 1)));

treelines.forEach((x, i) => {
  d.line([{ x, y: -1 }, { x, y: -1 - TREE_LEN }], i == 0 ? { color: 'grn' } : undefined);
});

d.curve([
  { x: treelines[0], y: -1 - TREE_LEN },
  { x: treelines[0], y: -1 - TREE_LEN - TREE_TENSE },
  { x: -2, y: -1 },
  { x: 0, y: 0 },
], { color: 'grn' });


d.line([{ x: 0, y: 0 }, { x: 0, y: 0.5 }], { color: 'blu' });
d.line([{ x: 0, y: 0 }, { x: 0, y: -0.5 }], { color: 'red' });
d.cycle([{ x: 0, y: -0.5 }, { x: 0.5, y: -1 }, { x: -0.5, y: -1 }]);
d.fillCircle({ x: 0, y: 0 }, 3);
d.node({ x: -1.3, y: -1 }, { color: 'grn', text: '$1$' });
d.node({ x: 0.3, y: -0.25 }, { color: 'red', text: '$0$' });
d.node({ x: 0.3, y: 0.25 }, { color: 'blu', text: '$2$' });


fs.writeFileSync('./lambda-diagram.tex', d.buf, 'utf8');


//// Convenience elisp for editing this file and getting results
//// interactively: (requires tsc --watch running in the background)
//
// (setenv "PATH" (concat (getenv "PATH") ":/Users/jreed/.nvm/versions/node/v9.6.1/bin"))

// (defun jcreed-tmp ()
//   (interactive)
//   (shell-command "node lambda-diagram.js")
//   (set-buffer jcreed-tex-main-buffer)
//   (tex-file))

// (define-key tide-mode-map "\C-c\C-f" 'jcreed-tmp)
