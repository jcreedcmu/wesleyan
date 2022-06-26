import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm, G, Item } from './basics';
import assert from 'assert';
import { epretty, lie, plusa, spretty, sub, sep, glie, target, plus, prod, proda, lierule, Z } from './lib';

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
const L31 = lierule(G(3), G(1));
const L13 = lierule(G(1), G(3));
function alternate34() {
  console.log(spretty(plusa(
    Z(target(3)),
    // synthesize all 2's
    pseudoZ(target(3), rule2, x => x == 1),


    sep(2, prod(rule3, G(1))),
    sep(1, prod(G(1), rule3)),

    sep(6, lierule(G(3), G(1))),

    sep(1, lierule(G(1), glie(0, 2))),
    sep(1, prod(G(1), lierule(G(2), G(1)))),
    sep(2, prod(lierule(G(2), G(1)), G(1))),
    sep(-1, target(4)),

    // clean up 211
    sep(1, prod(lierule(G(1), G(2)), G(1))),
    sep(1, prod(G(1), lierule(G(2), G(1)))),

    // swizzle [1,[2,1]]
    sep(1, lierule(glie(1, 2), G(1))),
    sep(-1, prod(G(1), lierule(G(1), G(2)))),
    sep(-1, prod(G(1), lierule(G(2), G(1)))),

  )));
}

function alternate45() {
  console.log(spretty(plusa(
    Z(target(4)),
    // synthesize all 2's
    pseudoZ(target(4), rule2, x => x == 1),
    // synthesize all 3's
    sep(6, proda(G(2), rule3)),
    sep(6, proda(rule3, G(2))),
    sep(3, proda(G(1), G(1), rule3)),
    sep(2, proda(G(1), rule3, G(1))),
    sep(1, proda(rule3, G(1), G(1))),
    // synthesize all 4's
    prod(rule4, G(1)),
    sep(3, prod(G(1), rule4)),

    // remainder is cleanup

    // clean up 41
    sep(12, lierule(G(1), G(4))),

    // clean up 311
    sep(2, prod(lierule(G(1), G(3)), G(1))),
    sep(2, prod(G(1), lierule(G(3), G(1)))),

    // clean up 221
    sep(8, prod(G(2), lierule(G(2), G(1)))),
    sep(4, prod(lierule(G(2), G(1)), G(2))),

    // clean up 2111
    sep(3, proda(G(1), G(1), lierule(G(2), G(1)))),
    sep(2, proda(G(1), lierule(G(2), G(1)), G(1))),
    sep(1, proda(lierule(G(2), G(1)), G(1), G(1))),

    // clean up 1[0,3]
    sep(6, lierule(glie(0, 3), G(1))),

    // clean up [[0,2]11
    sep(2, prod(lierule(glie(0, 2), G(1)), G(1))),
    sep(2, prod(G(1), lierule(glie(0, 2), G(1)))),

    // clean up 1[[0,2],1]
    lierule(lie(glie(0, 2), G(1)), G(1)),

    // clean up 2[2,1]
    sep(2, lierule(G(2), glie(2, 1))),

    // swizzle [1,[3,1]]
    sep(2, lierule(glie(1, 3), G(1))),
    sep(-2, prod(G(1), lierule(G(1), G(3)))),
    sep(-2, prod(G(1), lierule(G(3), G(1)))),

    sep(-1, target(5)),
  )));
}

alternate34();
