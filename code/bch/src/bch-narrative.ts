import { Exp, mkexp, Term, termOfTree, Tree, treeOfTerm, G, Item } from './basics';
import assert from 'assert';
import { epretty, lie, plusa, spretty, sub, sep, glie, target, plus, prod, proda, lierule, Z, extract, comps, factorial, choose, nestedLie, rule } from './lib';
import { zeroMotion } from './zero-motion';
import { rebalance } from './rebalance';
import { positiveMotion } from './positive-motion';
import { Opts, Story, synthAll, tellStory } from './synth-and-story';

const G0 = G(0);
const G1 = G(1);
const G2 = G(2);

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

// empirically works for n = {3,4,5,6,7,8,9}
function tellStoryN(n: number, opts: Opts) {
  const proof: Story = {
    size: n,
    phases: []
  };
  proof.phases.push([`move [0,-]`, zeroMotion(n)]);
  for (let i = 1; i <= n + 1; i++) {
    if (i >= 2)
      proof.phases.push([`synthesize G${i}`, synthAll(n, i)]);
    if (i <= n)
      proof.phases.push([`rebalance ...${i}`, rebalance(n, i)]);
    if (i <= n - 1)
      proof.phases.push([`move [-,${i}]`, positiveMotion(n, i)]);
  }
  tellStory(proof, opts);
}

for (let i = 3; i < 10; i++) {
  tellStoryN(i, {
    reqPos: true,
    reqDone: true,
    verbose: true
  });
}
