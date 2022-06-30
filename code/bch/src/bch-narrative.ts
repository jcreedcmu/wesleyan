import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm, G, Item } from './basics';
import assert from 'assert';
import { epretty, lie, plusa, spretty, sub, sep, glie, target, plus, prod, proda, lierule, Z, extract, comps, factorial } from './lib';

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

function nestedLie(x: number[]): Exp {
  if (x.length < 1) throw new Error(`Two few elements in ${x}`);
  if (x.length == 1)
    return G(x[0]);
  else
    return x.slice(1).reduce<Exp>((x: Exp, y: number) => lie(x, G(y)), G(x[0]));
}
assert.equal(epretty(sub(nestedLie([4]), G4)), '0');
assert.equal(epretty(sub(nestedLie([4, 5, 3, 1]), lie(lie(lie(G4, G5), G3), G1))), '0');

function rule(n: number) {
  if (n == 2) {
    return sub(sep(2, G(2)), lie(G0, G1));
  }

  const fnmo = factorial(n - 1);
  const nonzeroTerms: Exp = plusa(
    ...comps(n).filter(c => c.length > 1).filter(c => c[0] != c[1]).map(c =>
      sep(fnmo * c[1] / factorial(c.length), nestedLie(c))
    )
  );
  const zeroTerms = plusa(...comps(n - 1).map(c =>
    sep(fnmo / factorial(c.length), nestedLie([0, ...c]))
  ));
  return sub(sep(factorial(n), G(n)), plus(zeroTerms, nonzeroTerms));
}

type Phase = [string, ...Exp[]];
type Story = { size: number, phases: Phase[] };

function tellStory(story: Story) {
  const N = story.size;
  let state = Z(target(N));
  console.log(spretty(state));
  story.phases.forEach(phase => {
    const [text, ...steps] = phase;
    console.log('----', text, '---');
    state = plus(state, plusa(...steps));
    console.log(spretty(state));
  });
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

function rebalance(n: number, lam: number[]) {
  const prefix = lam.slice(0, lam.length - 1);
  const tail = lam[lam.length - 1];

  return sep(n / lam.length, plusa(
    ...lam.slice(1).map((x, i) => sep((i + 1), proda(
      ...prefix.slice(0, i).map(x => G(x)),
      lierule(G(prefix[i]), G(tail)),
      ...prefix.slice(i + 1).map(x => G(x))
    )))));
}

assert.equal(spretty(rebalance(5, [8, 9, 7, 2, 4])),
  `G_{89742} +
 -4G_{89724} +
 G_{89472} +
 G_{84972} +
 G_{48972} +
 4G_{897[2,4]} +
 3G_{89[7,4]2} +
 2G_{8[9,4]72} +
 G_{[8,4]972}`
);

// const proof3: Story = {
//   size: 3,
//   phases: [
//     ["move [0,-]",
//       // [01]
//       sep(3, lierule(glie(0, 1), G2)),
//       sep(1, proda(lierule(glie(0, 1), G1), G1)),
//       sep(2, proda(G1, lierule(glie(0, 1), G1))),
//       // [02]
//       sep(3, lierule(glie(0, 2), G1)),
//       // [011]
//       sep(1, lierule(nestedLie([0, 1, 1]), G1)),
//     ],
//     ["rebalance ...1",
//       rebalance(6, [3, 1]),
//       rebalance(3, [2, 1, 1]),
//       rebalance(3, [1, 2, 1]),
//     ],
//     ["synthesize G2",
//       sep(6, prod(G2, rule(2))),
//       sep(3, proda(G1, G1, rule(2)))
//     ],
//     // ["synthesize G3",
//     //   rule(3)]
//   ]
// };

// tellStory(proof3);
