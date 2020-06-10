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

// add m * r into s, mutates s
function addTo(m: number, r: Ring, s: Ring): Ring {
  for (const k of Object.keys(r)) {
    if (!s[k]) s[k] = 0;
    s[k] += m * r[k];
  }
  clear(s);
  return s;
}

export function add(r: Ring, s: Ring): Ring {
  return addTo(1, r, addTo(1, s, zero()));
}

export function scale(k: number, r: Ring): Ring {
  return addTo(k, r, zero());
}

export function zero(): Ring {
  return {};
}

export function sing(x: string): Ring {
  return { [x]: 1 };
}

export function sub(r: Ring, s: Ring): Ring {
  return add(r, scale(-1, s));
}

// remove zero entries from r
function clear(r: Ring): Ring {
  for (const k of Object.keys(r)) {
    if (r[k] == 0)
      delete r[k];
  }
  return r;
}

// special case of kleisli lift (A -> Z[B]) -> Z[A] -> Z[B]
// where A = B = {0,1,2}^*
function lift(f: (s: string) => Ring): (r: Ring) => Ring {
  return (r: Ring) => {
    const rv: Ring = {};
    for (const k of Object.keys(r)) {
      addTo(r[k], f(k), rv);
    }
    clear(rv);
    return rv;
  }
}

// signed boundary, as ring element
export function bnd(s: string): Ring {
  const rv: Ring = {};
  bd(s, 'dom').forEach(x => rv[x] = -1);
  bd(s, 'cod').forEach(x => rv[x] = 1);
  return rv;
}

// return signed boundary of ring element r, as a ring element
export const bndr = lift(bnd);

// star-insertion function on s
// nondeterministically insert a star somewhere in s,
// flipping all bits to the right of it
export function ins(s: string): Ring {
  const rv: Ring = {};
  for (let i = 0; i <= s.length; i++) {
    const ns =
      s.substring(0, i) +
      '*' +
      s.substring(i, s.length).replace(/[01]/g, x => x === '0' ? '1' : '0');
    if (!rv[ns]) rv[ns] = 0;
    rv[ns] += 1;
  }
  return rv;
}

// return star-insertion of ring element r, as a ring element
export const insr = lift(ins);

// for sorting purposes, consider * later than 0 and 1
function munge(s: string): string {
  return s.replace(/\*/g, '2');
}

export function stringify(r: Ring): string {
  const ks = Object.keys(r).sort((a, b) => r[b] - r[a] || (munge(a)).localeCompare(munge(b)));
  if (ks.length == 0) return '[0]';
  const k0 = ks.shift()!;
  const c0 = r[k0];
  const pre0 = c0 === 1 ? '' : c0 === -1 ? '- ' : (c0 + ' ');
  function sify(k: string): string {
    const c = r[k];
    const pre = c === 1 ? ' + ' : c === -1 ? ' - ' : c < 0 ? ` - ${-c} ` : ` + ${c} `;
    return `${pre}(${k})`;
  }
  return `${pre0}(${k0})` + ks.map(sify).join('');
}

const x = sing('10111');
// console.log(stringify(sbdr(sinr(x))));
// console.log('minus');
// console.log(stringify(sinr(sbdr(x))));
// console.log('equals');
console.log(stringify(sub(bndr(insr(insr(x))), scale(2, insr(bndr(insr(x)))))));
//console.log(stringify(sbdr(sinr(x))));
