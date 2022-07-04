import * as assert from 'assert';
import { Exp, G } from './basics';
import { choose, comps, factorial, lie, nestedLie, plus, plusa, prod, proda, sep, spretty, sub, target } from './lib';

// -------------------------------------------------------------------------
// 1. Basic helper functions
// -------------------------------------------------------------------------

type CompPair = { lam1: number[], lam2: number[] };

export function Gp(c: number[]): Exp[] {
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

export function csum(n: number, f: (c: number[]) => Exp): Exp {
  let rv = G(0, 0);
  comps(n).forEach(c => {
    rv = plus(rv, f(c));
  });
  return rv;
}

export function esum(a: number, b: number, f: (i: number) => Exp): Exp {
  let rv = sep(0, G(0));
  for (let i = a; i <= b; i++) {
    rv = plus(rv, f(i));
  }
  return rv;
}

// This captures all the expressions that have freshly synthesized G_s's
// in the n→n+1 proof.
export function synths(n: number, s: number) {
  return plusa(...comps(n + 1 - s).map(c =>
    sep(s * factorial(n) / factorial(c.length),
      proda(...[...c, s].map(x => G(x))))
  ));
}

export function cartprod<T, U>(ts: T[], us: U[]): [T, U][] {
  let rv: [T, U][] = [];
  ts.forEach(t => {
    us.forEach(u => {
      rv.push([t, u]);
    });
  });
  return rv;
}

// returns G_{1⋯1} with n 1's
export function fullySplit(n: number) {
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
export function zeroSwaps(n: number, m: number) {
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

// Returns all the fully stable no-swap expressions that arise from rebalancing s
// they look like
// λ₁ s λ₂
// so n₁ = Σλ₁ is going to range from 0 to n+1-s
// and n₂ = n + 1 - s - n₁
export function balanceds(n: number, s: number): Exp {
  return esum(0, n + 1 - s, n1 => {
    const n2 = n + 1 - s - n1;
    return plusa(
      ...cartprod(comps(n1), comps(n2))
        .filter(([lam1, lam2]) => lam1.length + lam2.length != n)
        .map(([lam1, lam2]) => {
          return sep(
            s *
            factorial(n) / factorial(lam1.length + lam2.length + 1),
            proda(...Gp(lam1), G(s), ...Gp(lam2))
          );
        })
    );
  });
}

// Returns all the pairwise swaps that arise from rebalancing s
// they look like
// λ₁[b,s]λ₂
// where b ranges from 1 to (n+1)-s, but not equalling s, because
// we have a total of (n+1)-s-b to spread around λ₁ and λ₂
export function swapss(n: number, s: number): Exp {
  return esum(1, (n + 1) - s, b => {
    if (b == s)
      return G(0, 0);
    else
      return esum(0, (n + 1) - s - b, n1 => {
        const n2 = (n + 1) - s - b - n1;
        return plusa(
          ...cartprod(comps(n1), comps(n2))
            .map(([lam1, lam2]) => {
              return sep(
                s *
                (lam1.length + 1) *
                factorial(n) / factorial(lam1.length + lam2.length + 2),
                proda(...Gp(lam1), lie(G(b), G(s)), ...Gp(lam2))
              );
            })
        );
      });
  });
}

// Returns all the right-aligned swaps that arise from rebalancing s, which
// are used for m-synthesis
export function rightSwapss(n: number, m: number, s: number): Exp {
  // the structure of the swap is going to be
  // λ₁ [b, s, λ₂]
  // where Σλ₁ = n₁, Σλ₂ = n₂

  // n₁ + m = n ∴ n₁ = n - m
  // b + s + n₂ = m

  // b is at least 1, and not equal to s, and at most whatever would cause
  // n₂ to be zero, in which case b = m - s.
  let n1 = n + 1 - m;

  const rv = esum(1, m - s, b => {
    if (b == s)
      return G(0, 0);

    const n2 = m - b - s;
    return plusa(
      ...cartprod(comps(n1), comps(n2))
        .map(([lam1, lam2]) => {
          return sep(
            s *
            factorial(n) / (factorial(lam1.length) * factorial(lam2.length + 2)),
            proda(...Gp(lam1), nestedLie([b, s, ...lam2]))
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
    synths(n, 1),
    esum(2, n + 1, m => zeroSwaps(n, m)),
  );
}

export function postSynthState(n: number, s: number): Exp {
  return plusa(
    esum(1, s - 1, i => balanceds(n, i)),
    synths(n, s),
    esum(1, s - 1, i =>
      esum(s + 1, n + 1, m => rightSwapss(n, m, i))),
    esum(s + 1, n + 1, m => zeroSwaps(n, m)),
    fullySplit(n + 1),
  );
}

export function postRebalanceState(n: number, s: number): Exp {
  return plusa(
    esum(1, s, i => balanceds(n, i)),
    swapss(n, s),
    esum(1, s - 1, i =>
      esum(s + 1, n + 1, m => rightSwapss(n, m, i))),
    esum(s + 1, n + 1, m => zeroSwaps(n, m)),
    fullySplit(n + 1),
  );
}

export function postMotionState(n: number, s: number): Exp {
  return plusa(
    esum(1, s, i => balanceds(n, i)),
    esum(1, s, i =>
      esum(s + 1, n + 1, m => rightSwapss(n, m, i))),
    esum(s + 1, n + 1, m => zeroSwaps(n, m)),
    fullySplit(n + 1),
  );
}

export function finalState(n: number): Exp {
  return target(n + 1);
}
