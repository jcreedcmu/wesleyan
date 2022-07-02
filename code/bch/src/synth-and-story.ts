import assert from 'assert';
import { Exp, G } from './basics';
import { comps, epretty, factorial, plus, plusa, proda, rule, sep, spretty, sub, target, Z } from './lib';
import { zeroMotion } from './zero-motion';

export type Phase = [string, ...Exp[]] | { t: 'check', f: (e: Exp) => void };
export type Story = { size: number, phases: Phase[] };
export type Opts = { reqPos?: boolean, verbose?: boolean, reqDone?: boolean };
export function tellStory(story: Story, opts: Opts = {}) {
  const { reqPos, reqDone, verbose } = opts;
  const N = story.size;
  let state = Z(target(N));
  if (verbose)
    console.log(spretty(state));
  story.phases.forEach(phase => {
    if ('t' in phase) {
      phase.f(state);
    }
    else {
      const [text, ...steps] = phase;
      console.log('----', text, '----');
      state = plus(state, plusa(...steps));
      if (verbose)
        console.log(spretty(state));
      if (reqPos)
        assert(Object.values(state).every(x => x >= 0));
    }
  });
  if ('0' == epretty(sub(state, target(N + 1))))
    console.log('---- achieved success! ----');
  else {
    if (reqDone) {
      throw new Error(`not done yet!`);
    }
  }
}

export function synthAll(n: number, m: number): Exp {
  if (m == 1) {
    return zeroMotion(n);
  }
  const r = rule(m);
  return plusa(...comps(n + 1 - m).map(c => {
    const coeff = factorial(n) / (factorial(m - 1) * factorial(c.length));
    return sep(coeff, proda(...c.map(x => G(x)), r));
  }));
}
