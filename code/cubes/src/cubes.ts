function times<T>(n: number, f: (x: T) => T, x: T): T {
  if (n <= 0)
    return x;
  else
    return times(n - 1, f, f(x));
}

type Dc = 'dom' | 'cod';

// cube boundary: returns domain or codomain of *^n
function cbd(n: number, dc: Dc): string[] {
  const rv: string[] = [];
  for (let i = 0; i < n; i++) {
    let s = "";
    for (let j = 0; j < i; j++) {
      s += "*";
    }
    s += (i + (dc == 'cod' ? 1 : 0)) % 2 ? "1" : "0";
    for (let j = 0; j < n - i - 1; j++) {
      s += "*";
    }
    rv.push(s);
  }
  return rv;
}

// cell boundary: returns domain or codomain of s
function bd(s: string, dc: Dc): string[] {
  const stars = (s.match(/\*/g) || []).length;
  const cbds = cbd(stars, dc);
  function expand(tdata: string): string {
    let rv = "";
    let tix = 0;
    s.split('').forEach((c, i) => {
      if (c == '*') {
        rv += tdata[tix];
        tix++;
      }
      else {
        rv += c;
      }
    });
    return rv;
  }
  return cbds.map(expand);
}

// element of the ring Z[{0,1,*}^n].
// represented as mapping strings in {0,1,*}^n to their coefficient.
// Example: {'*1': 1, '0*': -1}
type Ring = { [s: string]: number };

// signed boundary, as ring element
function sbd(s: string): Ring {
  const rv: Ring = {};
  bd(s, 'dom').forEach(x => rv[x] = -1);
  bd(s, 'cod').forEach(x => rv[x] = 1);
  return rv;
}

// add m * r into s
function addTo(m: number, r: Ring, s: Ring): void {
  for (const k of Object.keys(r)) {
    if (!s[k]) s[k] = 0;
    s[k] += m * r[k];
  }
}

// return signed boundary of ring element r, as a ring element
export function sbdr(r: Ring): Ring {
  const rv: Ring = {};
  for (const k of Object.keys(r)) {
    addTo(r[k], sbd(k), rv);
  }
  for (const k of Object.keys(rv)) {
    if (rv[k] == 0)
      delete rv[k];
  }
  return rv;
}

//console.log(sbdr({ '*0': 1, '0*': -1 }));

type Bound = { cod: string[], dom: string[] };

function fbd(s: string): Bound {
  return { cod: bd(s, 'cod'), dom: bd(s, 'dom') };
}

function mbd(b: string[]): Bound {
  const rv: { [k: string]: number } = {};
  function accum(k: string, v: number) {
    if (!rv[k]) rv[k] = 0;
    rv[k] += v;
  }
  b.forEach(s => {
    const { dom, cod } = fbd(s);
    dom.forEach(de => { accum(de, -1); });
    cod.forEach(de => { accum(de, 1); });
  });
  const ks = Object.keys(rv);
  const e = ks.map(k => ([k, rv[k]] as [string, number]));
  const dom = e.filter(x => x[1] == -1).map(x => x[0]);
  dom.sort();
  const cod = e.filter(x => x[1] == 1).map(x => x[0]);
  cod.sort();
  return { dom, cod };
}

function dmbd(b: Bound): Bound {
  return mbd(b.dom);
}

function go() {
  const n = 6;
  const k = 2;
  // What I expect this to output is
  // dom and cod both being a representation of n choose k
  // with non-* bits at the 'chosen' positions, with bit values starting at 0
  // with dom, and 1 with cod, and flipping for every *.
  const s = times(n, (a => a + '*'), '');
  console.log(times(k - 1, dmbd, fbd(s)));
}
