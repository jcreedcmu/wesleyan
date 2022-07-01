import assert from 'assert';
import { Exp, G } from './basics';
import { choose, comps, epretty, factorial, glie, lierule, nestedLie, plusa, proda, sep, sub } from './lib';

const G0 = G(0);
const G1 = G(1);
const G2 = G(2);
const G3 = G(3);
const G4 = G(4);

type ZeroInfo = { mu: number[], lam1: number[], lam2: number[], n1: number, n2: number, s: number, b: number };
// return all ways of doing λ₁ [μ, b] λ₂ where
// Σλ₁ = n₁
// Σλ₂ = n₂
// Σμ = s
// |μ| ≥ 2
// μ₂ = m
// μ₁ ≠ μ₂
function part3aux(q: Quad, m: number): ZeroInfo[] {
  const { s, b, n1, n2 } = q;
  const rv: ZeroInfo[] = [];
  comps(s).filter(mu => mu.length >= 2 && mu[1] == m && mu[0] != mu[1]).forEach(mu => {
    comps(n1).forEach(lam1 => {
      comps(n2).forEach(lam2 => {
        rv.push({ mu, lam1, lam2, b, n1, n2, s });
      });
    });
  });
  return rv;
}

type Quad = { s: number, b: number, n1: number, n2: number };
// return all quadruples [s, b, n1, n2] where s + b + n1 + n2 = n and s ≥ 3 and b ≥ 1
function part3(n: number): Quad[] {
  let rv: Quad[] = [];
  for (let s = 3; s <= n - 1; s++) {
    for (let b = 1; b <= n - s; b++) {
      for (let n1 = 0; n1 <= n - s - b; n1++) {
        rv = [...rv, { s, b, n1, n2: n - s - b - n1 }];
      }
    }
  }
  return rv;
}

export function positiveMotion(n: number, m: number): Exp {
  const parts = part3(n + 1).flatMap(q => part3aux(q, m));
  return plusa(...parts.map(({ mu, lam1, lam2, b, n1, n2, s }) => {
    let coeff = mu[1] * choose(lam1.length + mu.length, mu.length) * factorial(n1 + n2 + s + b - 1)
      / factorial(lam1.length + lam2.length + mu.length + 1);
    // const debug = `${coeff} ${lam1.join('')}[${mu.join('')},${b}]${lam2.join('')}`;
    // console.log(debug);

    return sep(coeff, proda(...lam1.map(x => G(x)), lierule(nestedLie(mu), G(b)), ...lam2.map(x => G(x))));
  }));
}

assert.equal(0, epretty(sub(positiveMotion(5, 2), plusa(
  // [32]
  sep(40, lierule(nestedLie([3, 2]), G1)),
  // [12]
  sep(40, lierule(nestedLie([1, 2]), G3)),
  sep(10, proda(lierule(nestedLie([1, 2]), G2), G1)),
  sep(10, proda(lierule(nestedLie([1, 2]), G1), G2)),
  sep(30, proda(G1, lierule(nestedLie([1, 2]), G2))),
  sep(30, proda(G2, lierule(nestedLie([1, 2]), G1))),
  sep(2, proda(lierule(nestedLie([1, 2]), G1), G1, G1)),
  sep(6, proda(G1, lierule(nestedLie([1, 2]), G1), G1)),
  sep(12, proda(G1, G1, lierule(nestedLie([1, 2]), G1))),
  // [122]
  sep(10, proda(lierule(nestedLie([1, 2, 2]), G1))),
  // [121]
  sep(10, proda(lierule(nestedLie([1, 2, 1]), G2))),
  sep(2, proda(lierule(nestedLie([1, 2, 1]), G1), G1)),
  sep(8, proda(G1, lierule(nestedLie([1, 2, 1]), G1))),
  // [1211]
  sep(2, proda(lierule(nestedLie([1, 2, 1, 1]), G1))),
))));
