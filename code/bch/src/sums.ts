import { Exp, G } from './basics';
import { comps, plus, sep } from './lib';

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
  let rv = G(0, 0);
  for (let i = a; i <= b; i++) {
    rv = plus(rv, f(i));
  }
  return rv;
}

// "generic splitting sum".
// return the iterated `combine` of f(λ1, λ2) for all possible ways that λ can be
// constructed as an interleaving of λ1, λ2
function gssum<T>(λ: number[], f: (λ1: number[], λ2: number[]) => T, combine: (a: T, b: T) => T): T {
  let rv = G(0, 0);
  if (λ.length == 0) {
    return f([], []);
  }
  else {
    return combine(
      gssum(λ.slice(1), (λ1, λ2) => f([λ[0], ...λ1], λ2), combine),
      gssum(λ.slice(1), (λ1, λ2) => f(λ1, [λ[0], ...λ2]), combine)
    );
  }
}

import * as assert from 'assert';
assert.deepEqual(
  gssum([5, 6, 7], (λ1, λ2) => ([{ first: λ1, second: λ2 }]), (a, b) => [...a, ...b]),
  [
    { first: [5, 6, 7], second: [] },
    { first: [5, 6], second: [7] },
    { first: [5, 7], second: [6] },
    { first: [5], second: [6, 7] },
    { first: [6, 7], second: [5] },
    { first: [6], second: [5, 7] },
    { first: [7], second: [5, 6] },
    { first: [], second: [5, 6, 7] }
  ]
);

// "splitting sum" specialized to Exp
// return the sum of f(λ1, λ2) for all possible ways that λ can be
// constructed as an interleaving of λ1, λ2
function ssum<T>(λ: number[], f: (λ1: number[], λ2: number[]) => Exp): Exp {
  return gssum(λ, f, plus);
}
