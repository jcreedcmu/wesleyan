import * as assert from 'assert';
import { Exp, G } from './basics';
import { factorial, lie, plus, proda, sep, spretty, sub } from './lib';
import { positiveMotion } from './positive-motion';
import { rebalance } from './rebalance';
import { Gp, finalState, postMotionState, postRebalanceState, postSynthState, postZeroState, zeroSwaps, csum, esum } from './state-checkpoints';
import { Phase, Story, synthAll, tellStory } from './synth-and-story';
import { zeroMotion } from './zero-motion';


function Δ(comp: number[]): Exp {
  let rv = G(0, 0);
  for (let i = 0; i < comp.length; i++) {
    rv = plus(rv, proda(
      ...Gp(comp.slice(0, i)),
      lie(G(0), G(comp[i])),
      ...Gp(comp.slice(i + 1))));
  }
  return rv;
}

assert.equal(spretty(Δ([3, 4, 5])),
  `G_{34[0,5]} +
 G_{3[0,4]5} +
 G_{[0,3]45}`);

function zeroMovementLemma(N: number) {
  const left = plus(
    zeroMotion(N),
    csum(N, λ => sep(factorial(N) / factorial(λ.length), Δ(λ)))
  );
  const right = esum(2, N + 1, m => zeroSwaps(N, m));
  assert.equal('0', spretty(sub(left, right)));
}

zeroMovementLemma(5);
