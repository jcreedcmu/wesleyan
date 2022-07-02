import * as assert from 'assert';
import { spretty, sub } from './lib';
import { positiveMotion } from './positive-motion';
import { rebalance } from './rebalance';
import { postZeroState } from './state-checkpoints';
import { Story, synthAll, tellStory } from './synth-and-story';
import { zeroMotion } from './zero-motion';

const proof5: Story = {
  size: 5,
  phases: [
    ["move [0,-]", zeroMotion(5)],
    {
      t: 'check', f: state => {
        assert.equal('0', spretty(sub(state, postZeroState(5))));
      }
    },
    ["rebalance ...1", rebalance(5, 1)],
    ["move [-,1]", positiveMotion(5, 1)],
    ["synthesize G2", synthAll(5, 2)],
    ["rebalance ...2", rebalance(5, 2)],
    ["move [-,2]", positiveMotion(5, 2)],
    ["synthesize G3", synthAll(5, 3)],
    ["rebalance ...3", rebalance(5, 3)],
    ["move [-,3]", positiveMotion(5, 3)],
    ["synthesize G4", synthAll(5, 4)],
    ["rebalance ...4", rebalance(5, 4)],
    ["move [-,4]", positiveMotion(5, 4)],
    ["synthesize G5", synthAll(5, 5)],
    ["rebalance ...5", rebalance(5, 5)],
    ["synthesize G6", synthAll(5, 6)],
  ]
};

tellStory(proof5, { verbose: false, reqDone: false, reqPos: true });
