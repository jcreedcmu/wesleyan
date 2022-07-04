import * as assert from 'assert';
import { Exp } from './basics';
import { spretty, sub } from './lib';
import { positiveMotion } from './positive-motion';
import { rebalance } from './rebalance';
import { finalState, postMotionState, postRebalanceState, postSynthState, postZeroState } from './state-checkpoints';
import { Phase, Story, synthAll, tellStory } from './synth-and-story';
import { zeroMotion } from './zero-motion';

const N = 6;

function makeStep(msg: string, trans: Exp, have: Exp): Phase[] {
  return [
    [msg, trans],
    { t: 'check', f: state => assert.equal('0', spretty(sub(state, have))) }
  ];
}

const phases = [
  ...makeStep("move [0,-]", zeroMotion(N), postZeroState(N)),
  ...makeStep("rebalance ...1", rebalance(N, 1), postRebalanceState(N, 1)),
  ...makeStep("move [-,1]", positiveMotion(N, 1), postMotionState(N, 1)),
];
for (let s = 2; s <= N - 1; s++) {
  phases.push(
    ...makeStep(`synthesize G${s}`, synthAll(N, s), postSynthState(N, s)),
    ...makeStep(`rebalance ...${s}`, rebalance(N, s), postRebalanceState(N, s)),
    ...makeStep(`move [-,${s}]`, positiveMotion(N, s), postMotionState(N, s)),
  );
}
phases.push(
  ...makeStep(`synthesize G${N}`, synthAll(N, N), postSynthState(N, N)),
  ...makeStep(`rebalance ...${N}`, rebalance(N, N), postRebalanceState(N, N)),
  ...makeStep(`final synthesis of G${N + 1}`, synthAll(N, N + 1), finalState(N)),
);

tellStory(
  {
    size: N,
    phases
  },
  {
    verbose: false,
    reqDone: false,
    reqPos: true
  }
);
