import * as assert from 'assert';
import { Exp } from './basics';
import { spretty, sub } from './lib';
import { positiveMotion } from './positive-motion';
import { rebalance } from './rebalance';
import { finalState, postMotion1State, postMotionState, postRebalanceState, postSynthState, postZeroState } from './state-checkpoints';
import { Phase, Story, synthAll, tellStory } from './synth-and-story';
import { zeroMotion } from './zero-motion';

const N = 5;

function makeStep(msg: string, trans: Exp, have: Exp): Phase[] {
  return [[msg, trans], { t: 'check', f: state => assert.equal('0', spretty(sub(state, have))) }];
}

function tryStep(msg: string, trans: Exp, have: Exp): Phase[] {
  return [[msg, trans], {
    t: 'check', f: state => {
      const need = state;
      console.log('*** have ***');
      console.log(spretty(have));
      console.log('*** need ***');
      console.log(spretty(need));
      if ('0' == spretty(sub(state, have))) {
        console.log('*** success! ***');
      }
      else {
        console.log('*** not yet! ***');
        console.log(spretty(sub(state, have)));
      }
    }
  }]
}

const proofN: Story = {
  size: N,
  phases: [
    ...makeStep("move [0,-]", zeroMotion(N), postZeroState(N)),
    ...makeStep("rebalance ...1", rebalance(N, 1), postRebalanceState(N, 1)),
    ...makeStep("move [-,1]", positiveMotion(N, 1), postMotionState(N, 1)),

    ...makeStep("synthesize G2", synthAll(N, 2), postSynthState(N, 2)),
    ...makeStep("rebalance ...2", rebalance(N, 2), postRebalanceState(N, 2)),
    ...makeStep("move [-,2]", positiveMotion(N, 2), postMotionState(N, 2)),

    ...makeStep("synthesize G3", synthAll(N, 3), postSynthState(N, 3)),
    ...makeStep("rebalance ...3", rebalance(N, 3), postRebalanceState(N, 3)),
    ...makeStep("move [-,3]", positiveMotion(N, 3), postMotionState(N, 3)),

    ...makeStep("synthesize G4", synthAll(N, 4), postSynthState(N, 4)),
    ...makeStep("rebalance ...4", rebalance(N, 4), postRebalanceState(N, 4)),
    ...makeStep("move [-,4]", positiveMotion(N, 4), postMotionState(N, 4)),

    ...makeStep("synthesize G5", synthAll(N, 5), postSynthState(N, 5)),
    ...makeStep("rebalance ...5", rebalance(N, 5), postRebalanceState(N, 5)),

    ...tryStep("final synthesis", synthAll(N, 6), finalState(N)),
  ]
};

tellStory(proofN, { verbose: false, reqDone: false, reqPos: true });
