import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm, G, Item } from './basics';
import assert from 'assert';
import { epretty, lie, plusa, spretty, sub, sep, glie, target, plus, prod, proda, lierule, Z, extract } from './lib';

// This is me trying to realize the "only synthesize on the rightmost
// side of expressions" approach described in the latex document

const G0 = G(0);
const G1 = G(1);
const G2 = G(2);
const G3 = G(3);
const G4 = G(4);
const L01 = lie(G0, G1);
const L011 = lie(L01, G1);
const L02 = lie(G0, G2);
const L12 = lie(G1, G2);
const R011 = lierule(L01, G1);
const R12 = lierule(G1, G2);

function tick(x: Exp) { return lie(G0, x); }

const rule: Exp[] = [];

rule[2] = sub(sep(2, G2), lie(G0, G1));
rule[3] = sub(sep(6, G3), plusa(
  sep(2, lie(G0, G2)),
  lie(lie(G0, G1), G1),
  lie(G1, G2)
));
rule[4] = sub(sep(24, G4), plusa(
  sep(6, lie(G0, G3)),
  sep(3, lie(lie(G0, G1), G2)),
  lie(lie(lie(G0, G1), G1), G1),
  lie(lie(G1, G2), G1),
  sep(3, lie(lie(G0, G2), G1)),
  sep(6, lie(G1, G3))
));

const proof23 = plusa(
  // move [0,1]
  lierule(glie(0, 1), G1),
  // synthesize G2
  sep(2, prod(G1, rule[2])),
  // rebalance (21)
  lierule(G1, G2),
);

const proof34 = plusa(
  // move [01]
  sep(2, proda(G1, R011)),
  sep(1, proda(R011, G1)),
  sep(3, lierule(L01, G2)),
  // synthesize G2
  sep(6, proda(G2, rule[2])),
  sep(3, proda(G1, G1, rule[2])),
  // rebalance (211)
  sep(2, proda(G1, R12)),
  sep(1, proda(R12, G1)),
  // move [011]
  lierule(L011, G1),
  // move [12]
  lierule(L12, G1),
  // move [02]
  sep(3, lierule(L02, G1)),
  // synthesize G3
  sep(3, proda(G1, rule[3])),
  // rebalance (31)
  sep(6, lierule(G1, G3)),
);

for (let i = 2; i < 4; i++) {
  console.log(`rule ${i}: ${epretty(rule[i])}`);
}
console.log('---\nhave:\n', spretty(plusa(
  Z(target(3)),
  proof34,
  sep(-1, target(4))
)));
console.log(extract(proof34, 3));
