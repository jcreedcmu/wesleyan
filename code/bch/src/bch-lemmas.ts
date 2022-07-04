import * as assert from 'assert';
import { Exp, G } from './basics';
import { comps, factorial, lie, plus, plusa, proda, sep, spretty, sub } from './lib';
import { positiveMotion } from './positive-motion';
import { rebalance } from './rebalance';
import { Gp, finalState, postMotionState, postRebalanceState, postSynthState, postZeroState, zeroSwaps, cartprod } from './state-checkpoints';
import { csum, esum } from './sums';
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


function go(N: number) {
  const start = csum(N, λ => sep(factorial(N) / factorial(λ.length), Δ(λ)));
  const e = esum(1, N, p =>
    esum(0, N - p, n1 => {
      let n2 = N - p - n1;
      return csum(n1, λ1 => csum(n2, λ2 => {
        return sep(
          factorial(N) / factorial(λ1.length + 1 + λ2.length),
          proda(...Gp(λ1), lie(G(0), G(p)), ...Gp(λ2))
        );
      }));
    }));
  console.log(spretty(sub(e, start)));
}
go(5);
