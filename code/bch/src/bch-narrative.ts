import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm, G, Item } from './basics';
import assert from 'assert';
import { epretty, lie, plusa, spretty, sub, sep, glie, target, plus, prod, proda, lierule, Z, extract, comps, factorial, choose, nestedLie, rule } from './lib';
import { zeroMotion } from './zero-motion';
import { rebalance } from './rebalance';

// This is me trying to deliberately collect some coefficients from medium-sized examples.

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

type Phase = [string, ...Exp[]];
type Story = { size: number, phases: Phase[] };

function tellStory(story: Story) {
  const N = story.size;
  let state = Z(target(N));
  console.log(spretty(state));
  story.phases.forEach(phase => {
    const [text, ...steps] = phase;
    console.log('----', text, '----');
    state = plus(state, plusa(...steps));
    console.log(spretty(state));
  });
  if ('0' == epretty(sub(state, target(N + 1)))) console.log('---- done! ----');
}

function synthAll(n: number, m: number): Exp {
  const r = rule(m);
  return plusa(...comps(n + 1 - m).map(c => {
    const coeff = factorial(n) / (factorial(m - 1) * factorial(c.length));
    return sep(coeff, proda(...c.map(x => G(x)), r));
  }));
}

const proof2: Story = {
  size: 2,
  phases: [
    ["move [0,1]",
      lierule(glie(0, 1), G1)],
    ["synthesize G2",
      sep(2, prod(G1, rule(2)))],
    ["rebalance (21)",
      lierule(G2, G1),
      sep(2, lierule(G1, G2))],
    ["synthesize G3",
      rule(3)]
  ]
};

const proof3: Story = {
  size: 3,
  phases: [
    ["move [0,-]", zeroMotion(3)],
    ["rebalance ...1", rebalance(3, 1)],
    ["move [-,1]",
      // [21]
      sep(1, lierule(nestedLie([2, 1]), G1)),
    ],
    ["synthesize G2", synthAll(3, 2)],
    ["rebalance ...2", rebalance(3, 2)],
    ["move [-,2]",
      // [12]
      sep(2, lierule(nestedLie([1, 2]), G1)),
    ],
    ["synthesize G3", synthAll(3, 3)],
    ["rebalance ...3", rebalance(3, 3)],
    ["synthesize G4", synthAll(3, 4)],
  ]
};

const proof4: Story = {
  size: 4,
  phases: [
    ["move [0,-]",
      zeroMotion(4),
    ],
  ]
};

tellStory(proof3);
