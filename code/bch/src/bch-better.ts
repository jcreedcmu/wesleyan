import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm } from './basics';
import assert from 'assert';

// assumes a.length == b.length
function lexo(a: number[], b: number[]) {
  for (let i = 0; i < a.length; i++) {
    const d = a[i] - b[i];
    if (d) return d;
  }
  return 0;
}

// list of all compositions (i.e. ordered partitions) of length n
function comps(n: number): number[][] {
  if (n <= 0) return [[]];
  let rv: number[][] = [];
  for (let i = 1; i <= n; i++) {
    rv = [...rv, ...comps(n - i).map(c => [...c, i])];
  }
  return rv
    .map(val => ({ val, sortBy: [...val].sort((a, b) => b - a) }))
    .sort((a, b) => a.val.length - b.val.length || lexo(b.sortBy, a.sortBy))
    .map(x => x.val);
}

assert.deepEqual(comps(4), [
  [4],
  [3, 1],
  [1, 3],
  [2, 2],
  [2, 1, 1],
  [1, 2, 1],
  [1, 1, 2],
  [1, 1, 1, 1]
]);

// factorial
function factorial(n: number): number {
  if (n <= 1) return 1;
  return n * factorial(n - 1);
}

assert.equal(factorial(10), 3628800);

// binomial coefficients
function choose(n: number, k: number): number {
  return factorial(n) / factorial(k) / factorial(n - k);
}

assert.equal(choose(10, 3), 120);

// pretty-print an expression
function epretty(e: Exp): string {
  if (Object.keys(e).every(k => e[k] == 0)) {
    return '0';
  }
  let rv: string[] = [];
  for (const t of Object.keys(e)) {
    if (e[t] != 0) {
      let coeff = e[t] == -1 ? '-' : e[t] == 1 ? '' : e[t];
      const sub = t.replace(/,/g, '');
      rv.push(`${coeff}G_{${sub}}`);
    }
  }
  return rv.join(" + ").replace(/\+ -/g, '- ');
}

// sum of two expressions
function plus(t1: Exp, t2: Exp): Exp {
  const rv: Exp = {};
  for (const e of Object.keys(t1)) {
    rv[e] = (rv[e] ?? 0) + t1[e];
  }
  for (const e of Object.keys(t2)) {
    rv[e] = (rv[e] ?? 0) + t2[e];
  }
  return rv;
}

function plusa(...args: Exp[]): Exp {
  return args.reduce(plus);
}

assert.equal(
  epretty(plusa(
    mkexp([1, 2], 3),
    mkexp([2, 1], -1),
    mkexp([5], 10),
    mkexp([5], -2),
    mkexp([6], -3))),
  '8G_{5} - 3G_{6} + 3G_{12} - G_{21}'
);

// scalar-expression product
function sep(s: number, e: Exp): Exp {
  const rv: Exp = {};
  for (const t of Object.keys(e)) {
    rv[t] = s * e[t];
  }
  return rv;
}

// tree-expression product
function tep(tr: Tree, e: Exp): Exp {
  const rv: Exp = {};
  for (const etm of Object.keys(e)) {
    rv[termOfTree([...tr, ...treeOfTerm(etm)])] = e[etm];
  }
  return rv;
}

// product of two expressions
function prod(e1: Exp, e2: Exp): Exp {
  let rv: Exp = {};
  for (const t of Object.keys(e1)) {
    rv = plus(tep(treeOfTerm(t), sep(e1[t], e2)), rv);
  }
  return rv;
}

const e1 = [1, 2]
assert.equal(
  epretty(prod(plusa(mkexp([1, 2], 3), mkexp([2, 1], -1)), plusa(mkexp([5], 10), mkexp([0], -2)))),
  '2G_{210} - 10G_{215} - 6G_{120} + 30G_{125}'
);

// compute the "target rhs", which corresponds to
// n! times the q^n coefficient of e^{qG₁ + q²G₂ + q³G₃ + ⋯ }
// which turns out to be the sum over all compositions λ₁, …, λₖ of n into k parts of
// (n!/k!) G_{λ₁}⋯G_{λₖ}
function target(n: number): Exp {
  return comps(n).map(c => (mkexp(c, factorial(n) / factorial(c.length)))).reduce(plus);
}

assert.equal(epretty(target(4)), '24G_{4} + 12G_{31} + 12G_{13} + 12G_{22} + 4G_{211} + 4G_{121} + 4G_{112} + G_{1111}');


function Z(e: Exp): Exp {
  const rv: Exp[] = [];
  for (const tm of Object.keys(e)) {
    const coef = e[tm];
    const tr = treeOfTerm(tm);
    for (let i = 0; i < tr.length; i++) {
      const deriv: Exp = mkexp([...tr.slice(0, i), [0, tr[i]], ...tr.slice(i + 1)], coef);
      rv.push(deriv);
    }
    rv.push(mkexp([...tr, 1], coef));
  }
  return rv.reduce(plus);
}

console.log(epretty(Z(target(3))));
