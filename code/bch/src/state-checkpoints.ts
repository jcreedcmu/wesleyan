import * as assert from 'assert';
import { Exp, G } from './basics';
import { choose, comps, factorial, lie, nestedLie, plus, plusa, prod, proda, sep, spretty, sub } from './lib';

// -------------------------------------------------------------------------
// 1. Basic helper functions
// -------------------------------------------------------------------------

type CompPair = { lam1: number[], lam2: number[] };

function Gp(c: number[]): Exp[] {
  return c.map(x => G(x));
}

//// dunno if I'm going to need this
// function sum(a: number, b: number, f: (i: number) => number): number {
//   let rv = 0;
//   for (let i = a; i <= b; i++) {
//     rv += f(i);
//   }
//   return rv;
// }

function esum(a: number, b: number, f: (i: number) => Exp): Exp {
  let rv = sep(0, G(0));
  for (let i = a; i <= b; i++) {
    rv = plus(rv, f(i));
  }
  return rv;
}

// This captures all the expressions that have freshly synthesized 1's
// in the n→n+1 proof.
function synth1(n: number) {
  return plusa(...comps(n).map(c =>
    sep(factorial(n) / factorial(c.length),
      proda(...[...c, 1].map(x => G(x))))
  ));
}

function cartprod<T, U>(ts: T[], us: U[]): [T, U][] {
  let rv: [T, U][] = [];
  ts.forEach(t => {
    us.forEach(u => {
      rv.push([t, u]);
    });
  });
  return rv;
}

// returns G_{1⋯1} with n 1's
function fullySplit(n: number) {
  let rv = G(1);
  for (let i = 0; i < n - 1; i++) {
    rv = prod(rv, G(1));
  }
  return rv;
}

assert.equal('G_{11111}', spretty(fullySplit(5)));

// -------------------------------------------------------------------------
// 2. Major chunks of proof state
// -------------------------------------------------------------------------

// This captures all the zero-swap expressions in the n→n+1 proof,
// which are going to be used for m-synthesis. For example:
// - G_{23[022]} has n=(2+3)+(2+2)=9, and m=(2+2)+1=5.
// - G_{4[01]} has n=(4)+(1)=5, and m=(1)+1=2.
function zeroSwaps(n: number, m: number) {
  return plusa(
    ...cartprod(comps(n - m + 1), comps(m - 1)).map(([lam1, lam2]) => {
      const coeff =
        factorial(n)
        / factorial(lam1.length) / factorial(lam2.length);
      return sep(coeff,
        proda(...Gp(lam1), nestedLie([0, ...lam2])));
    }
    ));
}

assert.ok(spretty(zeroSwaps(9, 5)).includes('90720G_{23[[0,2],2]}'));
assert.ok(spretty(zeroSwaps(5, 2)).includes('120G_{4[0,1]}'));

// Returns all the fully stable no-swap expressions that arise from rebalancing 1
function balanced1(n: number): Exp {
  return esum(0, n, n1 => {
    const n2 = n - n1;
    return plusa(
      ...cartprod(comps(n1), comps(n2))
        .filter(([lam1, lam2]) => lam1.length + lam2.length != n)
        .map(([lam1, lam2]) => {
          return sep(
            factorial(n) / factorial(lam1.length + lam2.length + 1),
            proda(...Gp(lam1), G(1), ...Gp(lam2))
          );
        })
    );
  });
}

// Returns all the pairwise swaps that arise from rebalancing 1
function swaps1(n: number): Exp {
  return esum(2, n, b => {
    return esum(0, n - b, n1 => {
      const n2 = n - b - n1;
      return plusa(
        ...cartprod(comps(n1), comps(n2))
          .map(([lam1, lam2]) => {
            return sep(
              (lam1.length + 1) *
              factorial(n) / factorial(lam1.length + lam2.length + 2),
              proda(...Gp(lam1), lie(G(b), G(1)), ...Gp(lam2))
            );
          })
      );
    });
  });
}

// Returns all the right-aligned swaps that arise from rebalancing 1, which
// are used for m-synthesis
function rightSwaps1(n: number, m: number): Exp {
  let n1 = n + 1 - m;
  // the structure of the swap is going to be
  // λ₁ [b, 1, λ₂]
  // where Σλ₁ = n₁, Σλ₂ = n₂

  // n₁ + m = n ∴ n₁ = n - m
  // b + 1 + n₂ = m ∴

  // b is at least 2, and at most whatever would cause
  // n₂ to be zero, in which case b = m - 1.
  const rv = esum(2, m - 1, b => {
    const n2 = m - b - 1;
    return plusa(
      ...cartprod(comps(n1), comps(n2))
        .map(([lam1, lam2]) => {
          return sep(
            factorial(n) / (factorial(lam1.length) * factorial(lam2.length + 2)),
            // (lam1.length + 1) *
            // factorial(n) / factorial(lam1.length + lam2.length + 2),
            proda(...Gp(lam1), nestedLie([b, 1, ...lam2]))
          );
        })
    );
  });
  return rv;
}

// -------------------------------------------------------------------------
// 3. Functions that return full states
// -------------------------------------------------------------------------

export function postZeroState(n: number): Exp {
  return plusa(
    synth1(n),
    esum(2, n + 1, m => zeroSwaps(n, m)),
  );
}

export function postRebalance1State(n: number): Exp {
  return plusa(
    balanced1(n),
    swaps1(n),
    fullySplit(n + 1),
    esum(2, n + 1, m => zeroSwaps(n, m)),
  );
}

export function postMotion1State(n: number): Exp {
  return plusa(
    esum(3, n + 1, m => rightSwaps1(n, m)),
    balanced1(n),
    fullySplit(n + 1),
    esum(2, n + 1, m => zeroSwaps(n, m)),
  );
}
