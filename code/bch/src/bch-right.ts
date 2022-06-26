import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm, G, Item } from './basics';
import assert from 'assert';
import { epretty, lie, plusa, spretty, sub, sep, glie, target, plus, prod, proda, lierule, Z } from './lib';

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

console.log('have:\n', spretty(plusa(
  Z(target(2))
)));
