import * as assert from 'assert';
import { Exp, G } from './basics';
import { comps, factorial, lie, nestedLie, plus, plusa, proda, sep, spretty, sub } from './lib';
import { positiveMotion } from './positive-motion';
import { rebalance } from './rebalance';
import { Gp, finalState, postMotionState, postRebalanceState, postSynthState, postZeroState, zeroSwaps, cartprod } from './state-checkpoints';
import { csum, esum, ssum } from './sums';
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

function primZeroSwaps(N: number): Exp {
  return csum(N, λ => sep(factorial(N) / factorial(λ.length), Δ(λ)));
}

function sumZeroSwaps(N: number): Exp {
  return esum(2, N + 1, m => zeroSwaps(N, m));
}

function zeroMovementLemma(N: number) {
  const left = plus(
    zeroMotion(N),
    primZeroSwaps(N)
  );
  const right = sumZeroSwaps(N);
  assert.equal('0', spretty(sub(left, right)));
}



function zeroMovementLemmaEqn1(N: number) {
  const goal = primZeroSwaps(N);
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
  assert.equal(0, spretty(sub(e, goal)));
}

function zeroMovementLemmaEqn2(N: number) {
  const goal = sumZeroSwaps(N);
  const e = esum(1, N, p =>
    esum(0, N - p, n1 => {
      let n2 = N - p - n1;
      return csum(n1, λ1 => csum(n2, λ2 => {
        const inner = ssum(λ2, (λ2a, λ2b) => proda(...Gp(λ2a), nestedLie([0, p, ...λ2b])));
        return sep(
          factorial(N) / factorial(λ1.length + 1 + λ2.length),
          proda(...Gp(λ1), inner)
        );
      }));
    }));
  assert.equal(0, spretty(sub(e, goal)));
}


function zeroMovementLemmaEqn3(N: number) {
  const goal = sumZeroSwaps(N);
  const e = esum(1, N, p =>
    esum(0, N - p, n1 =>
      esum(0, N - p - n1, n2 => {
        let n3 = N - p - n1 - n2;
        return csum(n1, λ1 => csum(n2, λ2 => csum(n3, λ3 =>
          sep(
            (factorial(N) / factorial(λ1.length + 1 + λ2.length + λ3.length)) *
            (factorial(λ2.length + λ3.length) / (factorial(λ2.length) * factorial(λ3.length))),
            proda(...Gp(λ1), ...Gp(λ2), nestedLie([0, p, ...λ3]))
          )
        )));
      })
    )
  );
  assert.equal(0, spretty(sub(e, goal)));
}

// run some tests
{
  const N = 5;
  zeroMovementLemma(N);
  zeroMovementLemmaEqn1(N);
  zeroMovementLemmaEqn2(N);
  zeroMovementLemmaEqn3(N);
}
