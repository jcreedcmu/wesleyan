import * as assert from 'assert';
import { Exp } from './basics';
import { spretty, sub } from './lib';
import { positiveMotion } from './positive-motion';
import { rebalance } from './rebalance';
import { postMotion1State, postMotion2State, postRebalance1State, postRebalance2State, postSynth2State, postZeroState } from './state-checkpoints';
import { Phase, Story, synthAll, tellStory } from './synth-and-story';
import { zeroMotion } from './zero-motion';

const N = 6;


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
    ...makeStep("rebalance ...1", rebalance(N, 1), postRebalance1State(N)),
    ...makeStep("move [-,1]", positiveMotion(N, 1), postMotion1State(N)),
    ...makeStep("synthesize G2", synthAll(N, 2), postSynth2State(N)),
    ...makeStep("rebalance ...2", rebalance(N, 2), postRebalance2State(N)),
    ...tryStep("move [-,2]", positiveMotion(N, 2), postMotion2State(N)),

    // ["move [-,2]", positiveMotion(N, 2)],
    // ["synthesize G3", synthAll(N, 3)],
    // ["rebalance ...3", rebalance(N, 3)],
    // ["move [-,3]", positiveMotion(N, 3)],
    // ["synthesize G4", synthAll(N, 4)],
    // ["rebalance ...4", rebalance(N, 4)],
    // ["move [-,4]", positiveMotion(N, 4)],
    // ["synthesize G5", synthAll(N, 5)],
    // ["rebalance ...5", rebalance(N, 5)],
    // ["synthesize G6", synthAll(N, 6)],
  ]
};

tellStory(proofN, { verbose: false, reqDone: false, reqPos: true });
