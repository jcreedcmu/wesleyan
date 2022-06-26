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
function tick(x: Exp) { return lie(G0, x); }

const rule: Exp[] = [];

rule[2] = sub(sep(2, G2), tick(G1));
rule[3] = sub(sep(6, G2), plusa(
  sep(2, lie(G0, G2)),
  lie(lie(G0, G1), G1),
  lie(G1, G2)
));

const proof23 = plusa(
  // move [0,1]
  lierule(glie(0, 1), G1),
  // synthesize G2
  sep(2, prod(G1, rule[2])),
  // rebalance (21)
  lierule(G1, G2),
);

console.log('have:\n', spretty(plusa(
  Z(target(2)),
  proof23,
  sep(-1, target(3))
)));
// console.log(extract(proof23, 2));
