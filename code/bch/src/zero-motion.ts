import assert from 'assert';
import { Exp, G } from './basics';
import { choose, comps, epretty, factorial, glie, lierule, nestedLie, plusa, proda, sep, sub } from './lib';

const G0 = G(0);
const G1 = G(1);
const G2 = G(2);
const G3 = G(3);
const G4 = G(4);

type ZeroInfo = { mu: number[], lam1: number[], lam2: number[], n1: number, n2: number, s: number, b: number };
// return all ways of doing λ₁ [μ, b] λ₂ where Σλ₁ = n₁, Σλ₂ = n₂, and Σμ = s
function part3aux(s: number, b: number, n1: number, n2: number): ZeroInfo[] {
  const rv: ZeroInfo[] = [];
  comps(s).forEach(mu => {
    comps(n1).forEach(lam1 => {
      comps(n2).forEach(lam2 => {
        rv.push({ mu, lam1, lam2, b, n1, n2, s });
      });
    });
  });
  return rv;
}

function part3(n: number): ZeroInfo[] {
  let rv: ZeroInfo[] = [];
  for (let i = 1; i <= n - 1; i++) {
    for (let j = 1; j <= n - i; j++) {
      for (let k = 0; k <= n - i - j; k++) {
        rv = [...rv, ...part3aux(i, j, k, n - i - j - k)];
      }
    }
  }
  return rv;
}

export function zeroMotion(n: number): Exp {
  return plusa(...part3(n).map(({ mu, lam1, lam2, b, n1, n2, s }) => {
    let coeff = choose(lam1.length + mu.length, mu.length) * factorial(n1 + n2 + s + b)
      / factorial(lam1.length + lam2.length + mu.length + 1);
    // const debug = `${coeff} ${lam1.join('')}[0${mu.join('')},${b}]${lam2.join('')}`;
    // console.log(debug);
    // if (debug != '1 [011,1]') coeff = 0;
    return sep(coeff, proda(...lam1.map(x => G(x)), lierule(nestedLie([0, ...mu]), G(b)), ...lam2.map(x => G(x))));
  }));
}


assert.equal('0', epretty(sub(zeroMotion(3),
  plusa(
    sep(3, lierule(glie(0, 1), G2)),
    sep(1, proda(lierule(glie(0, 1), G1), G1)),
    sep(2, proda(G1, lierule(glie(0, 1), G1))),
    sep(3, lierule(glie(0, 2), G1)),
    sep(1, lierule(nestedLie([0, 1, 1]), G1)),
  ))));

assert.equal('0', epretty(sub(zeroMotion(4),
  plusa(
    // [01]
    sep(12, lierule(glie(0, 1), G3)),
    sep(4, proda(lierule(glie(0, 1), G1), G2)),
    sep(4, proda(lierule(glie(0, 1), G2), G1)),
    sep(8, proda(G2, lierule(glie(0, 1), G1))),
    sep(8, proda(G1, lierule(glie(0, 1), G2))),
    sep(1, proda(lierule(glie(0, 1), G1), G1, G1)),
    sep(2, proda(G1, lierule(glie(0, 1), G1), G1)),
    sep(3, proda(G1, G1, lierule(glie(0, 1), G1))),
    // [02]
    sep(12, lierule(glie(0, 2), G2)),
    sep(4, proda(lierule(glie(0, 2), G1), G1)),
    sep(8, proda(G1, lierule(glie(0, 2), G1))),
    // [03]
    sep(12, lierule(glie(0, 3), G1)),
    // [021]
    sep(4, lierule(nestedLie([0, 2, 1]), G1)),
    // [012]
    sep(4, lierule(nestedLie([0, 1, 2]), G1)),
    // [011]
    sep(4, lierule(nestedLie([0, 1, 1]), G2)),
    sep(1, proda(lierule(nestedLie([0, 1, 1]), G1), G1)),
    sep(3, proda(G1, lierule(nestedLie([0, 1, 1]), G1))),
    // [0111]
    sep(1, proda(lierule(nestedLie([0, 1, 1, 1]), G1))),
  ))));
