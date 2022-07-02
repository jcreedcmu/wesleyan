import { Exp, G } from './basics';
import { choose, comps, factorial, nestedLie, plus, plusa, prod, proda, sep, spretty } from './lib';

type CompPair = { lam1: number[], lam2: number[] };

function part(n: number): CompPair[] {
  let rv: CompPair[] = [];
  for (let n1 = 0; n1 <= n - 1; n1++) {
    const n2 = n - n1;
    comps(n1).forEach(lam1 => {
      comps(n2).forEach(lam2 => {
        rv.push({ lam1, lam2 });
      });
    });
  }
  return rv;
}

function Gp(c: number[]): Exp[] {
  return c.map(x => G(x));
}

export function postZeroState(n: number): Exp {
  const positives = plusa(...comps(n).map(c =>
    sep(factorial(n) / factorial(c.length),
      proda(...[...c, 1].map(x => G(x))))
  ));
  const zeroes = plusa(...part(n).map(({ lam1, lam2 }) => {
    const coeff =
      factorial(n)
      / factorial(lam1.length) / factorial(lam2.length);
    return sep(coeff,
      proda(...Gp(lam1), nestedLie([0, ...lam2])));
  }
  ));
  return plus(zeroes, positives);
}
