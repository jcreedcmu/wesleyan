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
const G5 = G(5);
const G6 = G(6);
const L01 = lie(G0, G1);
const L02 = lie(G0, G2);
const L04 = lie(G0, G4);
const L12 = lie(G1, G2);
const L011 = lie(L01, G1);
const L012 = lie(L01, G2);
const L021 = lie(L02, G1);
const L0111 = lie(L011, G1);
const L121 = lie(L12, G1);
const L03 = lie(G0, G3);
const L13 = lie(G1, G3);
const R011 = lierule(L01, G1);
const R12 = lierule(G1, G2);
const R13 = lierule(G1, G3);
const R013 = lierule(L01, G3);
const R012 = lierule(L01, G2);

function tick(x: Exp) { return lie(G0, x); }

const rule: Exp[] = [];
const proof: Exp[] = [];

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
rule[5] = sub(sep(120, G5), plusa(
  sep(24, lie(G0, G4)),
  sep(12, lie(lie(G0, G1), G3)),
  sep(4, lie(lie(lie(G0, G1), G1), G2)),
  sep(4, lie(lie(G1, G2), G2)),
  sep(12, lie(lie(G0, G2), G2)),
  sep(12, lie(G2, G3)),
  sep(12, lie(lie(G0, G3), G1)),
  sep(4, lie(lie(lie(G0, G1), G2), G1)),
  sep(4, lie(lie(lie(G0, G2), G1), G1)),
  lie(lie(lie(lie(G0, G1), G1), G1), G1),
  lie(lie(lie(G1, G2), G1), G1),
  sep(8, lie(lie(G1, G3), G1)),
  sep(36, lie(G1, G4))
));
rule[6] = sub(sep(720, G6), plusa(
  sep(120, lie(G0, G5)),
  sep(60, lie(lie(G0, G1), G4)),
  sep(20, lie(lie(lie(G0, G1), G1), G3)),
  sep(60, lie(lie(G0, G2), G3)),
  sep(60, lie(lie(G0, G3), G2)),
  sep(20, lie(lie(lie(G0, G1), G2), G2)),
  sep(5, lie(lie(lie(lie(G0, G1), G1), G1), G2)),
  sep(5, lie(lie(lie(G1, G2), G1), G2)),
  sep(20, lie(lie(lie(G0, G2), G1), G2)),
  sep(60, lie(lie(G1, G3), G2)),
  sep(120, lie(G2, G4)),
  sep(60, lie(lie(G0, G4), G1)),
  sep(20, lie(lie(lie(G0, G1), G3), G1)),
  sep(5, lie(lie(lie(lie(G0, G1), G1), G2), G1)),
  sep(5, lie(lie(lie(G1, G2), G2), G1)),
  sep(20, lie(lie(lie(G0, G2), G2), G1)),
  sep(20, lie(lie(lie(G0, G3), G1), G1)),
  sep(5, lie(lie(lie(lie(G0, G1), G2), G1), G1)),
  sep(5, lie(lie(lie(lie(G0, G2), G1), G1), G1)),
  lie(lie(lie(lie(lie(G0, G1), G1), G1), G1), G1),
  lie(lie(lie(lie(G1, G2), G1), G1), G1),
  sep(10, lie(lie(lie(G1, G3), G1), G1)),
  sep(60, lie(lie(G1, G4), G1)),
  sep(240, lie(G1, G5))
));

proof[2] = plusa(
  // move [0,1]
  lierule(glie(0, 1), G1),
  // synthesize G2
  sep(2, prod(G1, rule[2])),
  // rebalance (21)
  lierule(G1, G2),
);

proof[3] = plusa(
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

proof[4] = plusa(
  // move [01]
  sep(12, R013),
  sep(8, prod(G2, R011)),
  sep(8, prod(G1, R012)),
  sep(4, prod(R011, G2)),
  sep(4, prod(R012, G1)),
  sep(1, proda(R011, G1, G1)),
  sep(2, proda(G1, R011, G1)),
  sep(3, proda(G1, G1, R011)),
  // synthesize G2
  sep(24, proda(G3, rule[2])),
  sep(12, proda(G1, G2, rule[2])),
  sep(12, proda(G2, G1, rule[2])),
  sep(4, proda(G1, G1, G1, rule[2])),

  // rebalance (221)
  sep(8, proda(G2, R12)),
  sep(4, proda(R12, G2)),
  // rebalance (2111)
  sep(3, proda(G1, G1, R12)),
  sep(2, proda(G1, R12, G1)),
  sep(1, proda(R12, G1, G1)),

  // prepare to synthesize G3...
  // move [011]
  sep(1, proda(lierule(L011, G1), G1)),
  sep(3, proda(G1, lierule(L011, G1))),
  sep(4, lierule(L011, G2)),
  // move [12]
  sep(1, proda(lierule(L12, G1), G1)),
  sep(3, proda(G1, lierule(L12, G1))),
  sep(4, lierule(L12, G2)),
  // move [02]
  sep(4, proda(lierule(L02, G1), G1)),
  sep(8, proda(G1, lierule(L02, G1))),
  sep(12, lierule(L02, G2)),
  // synthesize G3
  sep(6, proda(G1, G1, rule[3])),
  sep(12, proda(G2, rule[3])),

  // rebalance (32)
  sep(12, lierule(G2, G3)),
  // rebalance (311)
  sep(16, proda(G1, R13)),
  sep(8, proda(R13, G1)),

  // prepare to synthesize G4...
  // move [03]
  sep(12, lierule(L03, G1)),
  // move [012]
  sep(4, lierule(L012, G1)),
  // move [021]
  sep(4, lierule(L021, G1)),
  // move [0111]
  sep(1, lierule(L0111, G1)),
  // move [121]
  sep(1, lierule(L121, G1)),
  // move [13]
  sep(8, lierule(L13, G1)),
  // synthesize G4
  sep(4, proda(G1, rule[4])),
  // rebalance (41)
  sep(36, lierule(G1, G4)),
);

// can be anywhere [-5, 5] and I see to get a valid solution.
// ultimately I get
// (5 + knob) G_{[1221]}
// (5 - knob) G_{[1212]}
// in rule[6], so I assume these are "numerically" equal Lie expressions?
// Setting it to zero seems to make the most natural symmetric sense for now.
const knob = 0;

proof[5] = plusa(
  // move [01]
  sep(60, lierule(L01, G4)),

  sep(20, prod(lierule(L01, G3), G1)),
  sep(20, prod(lierule(L01, G1), G3)),
  sep(40, prod(G1, lierule(L01, G3))),
  sep(40, prod(G3, lierule(L01, G1))),

  sep(20, prod(lierule(L01, G2), G2)),
  sep(40, prod(G2, lierule(L01, G2))),

  sep(5, proda(lierule(L01, G2), G1, G1)),
  sep(5, proda(lierule(L01, G1), G2, G1)),
  sep(5, proda(lierule(L01, G1), G1, G2)),

  sep(10, proda(G1, lierule(L01, G2), G1)),
  sep(10, proda(G2, lierule(L01, G1), G1)),
  sep(10, proda(G1, lierule(L01, G1), G2)),

  sep(15, proda(G1, G1, lierule(L01, G2))),
  sep(15, proda(G2, G1, lierule(L01, G1))),
  sep(15, proda(G1, G2, lierule(L01, G1))),

  sep(1, proda(lierule(L01, G1), G1, G1, G1)),
  sep(2, proda(G1, lierule(L01, G1), G1, G1)),
  sep(3, proda(G1, G1, lierule(L01, G1), G1)),
  sep(4, proda(G1, G1, G1, lierule(L01, G1))),

  // synthesize G2
  sep(120, proda(G4, rule[2])),
  sep(60, proda(G1, G3, rule[2])),
  sep(60, proda(G3, G1, rule[2])),
  sep(60, proda(G2, G2, rule[2])),
  sep(20, proda(G2, G1, G1, rule[2])),
  sep(20, proda(G1, G2, G1, rule[2])),
  sep(20, proda(G1, G1, G2, rule[2])),
  sep(5, proda(G1, G1, G1, G1, rule[2])),

  // rebalance (2211)
  sep(10, proda(G1, R12, G2)),
  sep(5 - knob, proda(R12, G1, G2)),
  sep(15 + knob, proda(G1, G2, R12)),

  sep(15 - knob, proda(G2, G1, R12)),
  sep(5 + knob, proda(R12, G2, G1)),
  sep(10, proda(G2, R12, G1)),

  // rebalance (21111)
  sep(4, proda(G1, G1, G1, lierule(G1, G2))),
  sep(3, proda(G1, G1, lierule(G1, G2), G1)),
  sep(2, proda(G1, lierule(G1, G2), G1, G1)),
  sep(1, proda(lierule(G1, G2), G1, G1, G1)),

  // prepare to synthesize G3...
  // move [011]
  sep(20, lierule(L011, G3)),
  sep(5, proda(lierule(L011, G2), G1)),
  sep(5, proda(lierule(L011, G1), G2)),
  sep(15, proda(G1, lierule(L011, G2))),
  sep(15, proda(G2, lierule(L011, G1))),
  sep(1, proda(lierule(L011, G1), G1, G1)),
  sep(3, proda(G1, lierule(L011, G1), G1)),
  sep(6, proda(G1, G1, lierule(L011, G1))),

  // move [12]
  sep(5 - knob, proda(lierule(L12, G1), G2)),
  sep(15 - knob, proda(G1, lierule(L12, G2))),
  sep(5 + knob, proda(lierule(L12, G2), G1)),
  sep(15 + knob, proda(G2, lierule(L12, G1))),
  sep(1, proda(lierule(L12, G1), G1, G1)),
  sep(3, proda(G1, lierule(L12, G1), G1)),
  sep(6, proda(G1, G1, lierule(L12, G1))),

  // move [02]
  sep(60, lierule(L02, G3)),
  sep(20, proda(lierule(L02, G2), G1)),
  sep(20, proda(lierule(L02, G1), G2)),
  sep(40, proda(G1, lierule(L02, G2))),
  sep(40, proda(G2, lierule(L02, G1))),
  sep(5, proda(lierule(L02, G1), G1, G1)),
  sep(10, proda(G1, lierule(L02, G1), G1)),
  sep(15, proda(G1, G1, lierule(L02, G1))),

  // synthesize some G3, but not the one that results in 33 yet
  sep(30, proda(G2, G1, rule[3])),
  sep(30, proda(G1, G2, rule[3])),
  sep(10, proda(G1, G1, G1, rule[3])),

  // there would be a degree of freedom in rebalancing (321), but
  // I need 60 G_{3[12]} to work out correctly for G33 synthesis.
  // this forces my hand to go the "long way around" the hexagon.
  sep(60, prod(G3, lierule(G1, G2))),
  sep(60, prod(lierule(G1, G3), G2)),
  sep(60, prod(G1, lierule(G2, G3))),
  sep(60, prod(G2, lierule(G1, G3))),

  //// this is the other extremal solution (in principle there's an
  //// interpolating knob between the two) but it doesn't generate the
  //// required G_{3[12]}.
  //
  // sep(60, prod(G2, lierule(G1, G3))),
  // sep(60, prod(G2, lierule(G1, G3))),
  // sep(60, prod(lierule(G2, G3), G1)),
  // sep(60, prod(lierule(G1, G2), G3)),

  // now synthesize G33
  sep(60, proda(G3, rule[3])),

  // rebalance (311)
  sep(10, proda(lierule(G1, G3), G1, G1)),
  sep(20, proda(G1, lierule(G1, G3), G1)),
  sep(30, proda(G1, G1, lierule(G1, G3))),

  // now do some moves in preparation for G4 synthesis

  // move [0,3]: yields 120, 60
  sep(60, lierule(L03, G2)),
  sep(20, proda(lierule(L03, G1), G1)),
  sep(40, proda(G1, lierule(L03, G1))),

  // move [[0,1],2]: yields 60, 30
  sep(20, lierule(L012, G2)),
  sep(5, proda(lierule(L012, G1), G1)),
  sep(15, proda(G1, lierule(L012, G1))),

  // move [[[0,1],1],1]: yields 20, 10
  sep(5, lierule(L0111, G2)),
  sep(1, proda(lierule(L0111, G1), G1)),
  sep(4, proda(G1, lierule(L0111, G1))),

  // move [[1,2],1]: yields 20, 10
  sep(5 - knob, lierule(L121, G2)),
  sep(1, proda(lierule(L121, G1), G1)),
  sep(4, proda(G1, lierule(L121, G1))),

  // move [[0,2],1]: yields 60, 30
  sep(20, lierule(L021, G2)),
  sep(5, proda(lierule(L021, G1), G1)),
  sep(15, proda(G1, lierule(L021, G1))),

  // move [1,3]: yields 120, 60
  sep(60, lierule(L13, G2)),
  sep(10, proda(lierule(L13, G1), G1)),
  sep(30, proda(G1, lierule(L13, G1))),

  // synthesize G4
  sep(20, prod(G2, rule[4])),
  sep(10, proda(G1, G1, rule[4])),

  // rebalance (411)
  sep(60, prod(lierule(G1, G4), G1)),
  sep(120, prod(G1, lierule(G1, G4))),

  // rebalance (42)
  sep(120, lierule(G2, G4)),

  // now do some moves in preparation for G5 synthesis
  //  24G_{[0,4]}
  sep(60, lierule(lie(G0, G4), G1)),
  //  12G_{[[0,1],3]}
  sep(20, lierule(lie(lie(G0, G1), G3), G1)),
  //  4G_{[[[0,1],1],2]}
  sep(5, lierule(lie(lie(lie(G0, G1), G1), G2), G1)),
  //  4G_{[[1,2],2]}
  sep(5 + knob, lierule(lie(L12, G2), G1)),
  //  12G_{[[0,2],2]}
  sep(20, lierule(lie(L02, G2), G1)),
  //  12G_{[2,3]}
  // We already miraculously have the right amount here already with
  // no shifting? that's pretty weird.
  //  12G_{[[0,3],1]}
  sep(20, lierule(lie(L03, G1), G1)),
  //  4G_{[[[0,1],2],1]}
  sep(5, lierule(lie(lie(L01, G2), G1), G1)),
  //  4G_{[[[0,2],1],1]}
  sep(5, lierule(lie(lie(L02, G1), G1), G1)),
  //  G_{[[[[0,1],1],1],1]}
  sep(1, lierule(lie(lie(lie(L01, G1), G1), G1), G1)),
  //  G_{[[[1,2],1],1]}
  sep(1, lierule(lie(lie(L12, G1), G1), G1)),
  //  8G_{[[1,3],1]}
  sep(10, lierule(lie(L13, G1), G1)),
  //  36G_{[1,4]}
  sep(60, lierule(lie(G1, G4), G1)),

  // synthesize G5
  sep(5, prod(G1, rule[5])),

  // rebalance (51)
  sep(240, lierule(G1, G5)),
)

const N = 5;

for (let i = 2; i < N + 1; i++) {
  console.log(`rule ${i}: ${spretty(sep(-1, rule[i]))}`);
}
console.log('---\nhave:', spretty(plusa(
  Z(target(N)),
  proof[N],
  sep(-1, target(N + 1))
)));
//console.log(extract(proof[N], N));
