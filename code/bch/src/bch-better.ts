import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm, G, Item } from './basics';
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
      const sub = t.replace(/;/g, '');
      rv.push(`${coeff}G_{${sub}}`);
    }
  }
  return rv.join(" + ").replace(/\+ -/g, '- ');
}

// pretty-print an expression, sorted
function spretty(e: Exp): string {
  if (Object.keys(e).every(k => e[k] == 0)) {
    return '0';
  }
  function sortBy(a: string, b: string): number {
    return a.length - b.length || a.split('').sort().join('').localeCompare(b.split('').sort().join('')) || b.localeCompare(a);
  }
  let rv: string[] = [];
  for (const t of Object.keys(e).sort(sortBy)) {
    if (e[t] != 0) {
      let coeff = e[t] == -1 ? '-' : e[t] == 1 ? '' : e[t];
      const sub = t.replace(/;/g, '');
      rv.push(`${coeff}G_{${sub}}`);
    }
  }
  return rv.join(" +\n ").replace(/\+\n -/g, '\n - ');
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

// difference of two expressions
function sub(t1: Exp, t2: Exp): Exp {
  return plus(t1, sep(-1, t2));
}

type TreeCombiner = (tr1: Tree, tr2: Tree) => Tree;

function defaultTreeCombiner(tr1: Tree, tr2: Tree): Tree {
  return [...tr1, ...tr2];
}

function lieTreeCombiner(tr1: Tree, tr2: Tree): Tree {
  return [[tr1, tr2]];
}

// tree-expression product, f to combine trees
function tep(tr: Tree, e: Exp, f: TreeCombiner): Exp {
  const rv: Exp = {};
  for (const etm of Object.keys(e)) {
    rv[termOfTree(f(tr, treeOfTerm(etm)))] = e[etm];
  }
  return rv;
}

// product of two expressions
function prod(e1: Exp, e2: Exp, f: TreeCombiner = defaultTreeCombiner): Exp {
  let rv: Exp = {};
  for (const t of Object.keys(e1)) {
    rv = plus(tep(treeOfTerm(t), sep(e1[t], e2), f), rv);
  }
  return rv;
}

function proda(...args: Exp[]): Exp {
  return args.reduce((x, y) => prod(x, y));
}

function lie(e1: Exp, e2: Exp): Exp {
  return prod(e1, e2, lieTreeCombiner);
}

function glie(n1: number, n2: number): Exp {
  return prod(G(n1), G(n2), lieTreeCombiner);
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
      const deriv: Exp = mkexp([...tr.slice(0, i), [[0], [tr[i]]], ...tr.slice(i + 1)], coef);
      rv.push(deriv);
    }
    rv.push(mkexp([...tr, 1], coef));
  }
  return rv.reduce(plus);
}

assert.equal(epretty(Z(target(3))), '6G_{[0,3]} + 6G_{31} + 3G_{[0,2]1} + 3G_{2[0,1]} + 3G_{211} + 3G_{[0,1]2} + 3G_{1[0,2]} + 3G_{121} + G_{[0,1]11} + G_{1[0,1]1} + G_{11[0,1]} + G_{1111}');

function lierule(a: Exp, b: Exp): Exp {
  return sub(lie(a, b), sub(prod(a, b), prod(b, a)));
}

const rule2: Exp = sub(mkexp([2], 2), lie(G(0), G(1)));
const rule3: Exp = sub(mkexp([3], 6), plusa(
  sep(2, lie(G(0), G(2))),
  sep(1, lie(G(2), G(1))),
));
const rule4: Exp = sub(mkexp([4], 24), plusa(
  lie(glie(0, 2), G(1)),
  sep(6, glie(0, 3)),
));

const rule5: Exp = sub(mkexp([5], 120), plusa(
  sep(24, glie(0, 4)),
  sep(12, glie(4, 1)),
  sep(2, lie(glie(1, 3), G(1))),
  sep(2, lie(G(2), glie(2, 1))),
));

console.log('rule2:', epretty(rule2));
console.log('rule3:', epretty(rule3));
console.log('rule4:', epretty(rule4));
console.log('rule5:', epretty(rule5));
console.log('---');
//proof of 1->2
assert.equal(
  epretty(target(2)),
  epretty(plus(Z(target(1)), rule2))
);
// proof of 2->3
assert.equal(
  spretty(plusa(
    Z(target(2)),
    prod(rule2, G(1)),
    prod(G(1), rule2),
    lierule(G(2), G(1)),
    rule3
  )),
  spretty(target(3))
);
// proof of 3->4
assert.equal('0', epretty(plusa(
  Z(target(3)),
  proda(rule2, G(1), G(1)),
  proda(G(1), rule2, G(1)),
  proda(G(1), G(1), rule2),
  prod(lierule(G(2), G(1)), G(1)),
  sep(3, proda(G(2), rule2)),
  sep(3, proda(rule2, G(2))),
  sep(2, prod(G(1), lierule(G(2), G(1)))),
  sep(1, prod(rule3, G(1))),
  sep(2, prod(G(1), rule3)),
  lierule(lie(G(0), G(2)), G(1)),
  rule4,
  sep(-1, target(4))
)));

function pseudoZ(e: Exp, e2: Exp, cond: (x: Item) => boolean): Exp {
  const rv: Exp[] = [];
  for (const tm of Object.keys(e)) {
    const coef = e[tm];
    const tr = treeOfTerm(tm);
    for (let i = 0; i < tr.length; i++) {
      const deriv: Exp = sep(coef, proda(
        mkexp([...tr.slice(0, i)]),
        e2,
        mkexp([...tr.slice(i + 1)])
      ));
      if (cond(tr[i]))
        rv.push(deriv);
    }
  }
  return rv.reduce(plus);
}


const L21 = lierule(G(2), G(1));
console.log(spretty(plusa(
  Z(target(4)),
  // synthesize all 2's
  pseudoZ(target(4), rule2, x => x == 1),

  // guess the 4's
  prod(rule4, G(1)),
  sep(3, prod(G(1), rule4)),
  // sort out (41)
  sep(12, lierule(G(1), G(4))),
  // sort out the 1,[0,3]
  sep(6, lierule(glie(0, 3), G(1))),

  // sort out some misc 0,2,1 stuff???
  lierule(lie(glie(0, 2), G(1)), G(1)),
  sep(2, prod(lierule(glie(0, 2), G(1)), G(1))),
  sep(2, prod(G(1), lierule(glie(0, 2), G(1)))),
  // // clean up 221
  sep(8, prod(G(2), lierule(G(2), G(1)))),
  sep(4, prod(lierule(G(2), G(1)), G(2))),
  // // clean up 2111
  sep(3, proda(G(1), G(1), lierule(G(2), G(1)))),
  sep(2, proda(G(1), lierule(G(2), G(1)), G(1))),
  sep(1, proda(lierule(G(2), G(1)), G(1), G(1))),

  // get rid of some [0,2]s
  sep(6, proda(G(2), rule3)),
  sep(6, proda(rule3, G(2))),

  // this gets rid of some [0,2]s
  sep(3, proda(G(1), G(1), rule3)),
  sep(2, proda(G(1), rule3, G(1))),
  sep(1, proda(rule3, G(1), G(1))),


  // // this gets rid of all [0,2]s remaining.
  sep(2, lierule(G(2), glie(2, 1))),


  // // This clears up the G_{(311)}
  sep(2, prod(lierule(G(1), G(3)), G(1))),
  sep(2, prod(G(1), lierule(G(3), G(1)))),


  // // synthesize some 4's
  // sep(2, proda(G(1), rule4)),
  // sep(2, proda(rule4, G(1))),



  // // swizzle [1,[3,1]] business
  sep(2, lierule(glie(1, 3), G(1))),
  sep(-2, prod(G(1), lierule(G(1), G(3)))),
  sep(-2, prod(G(1), lierule(G(3), G(1)))),


  sep(-1, target(5)),
)));
