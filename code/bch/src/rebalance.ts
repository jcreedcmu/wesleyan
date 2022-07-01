import assert from 'assert';
import { Exp, G } from './basics';
import { comps, epretty, factorial, lierule, plusa, proda, sep, spretty, sub } from './lib';

function rebalanceOne(n: number, lam: number[]) {
  const prefix = lam.slice(0, lam.length - 1);
  const tail = lam[lam.length - 1];

  const terms = [...lam.slice(1)
    .map((x, i) => i)
    .filter(i => prefix[i] != tail)
    .map(i => sep((i + 1), proda(
      ...prefix.slice(0, i).map(x => G(x)),
      lierule(G(prefix[i]), G(tail)),
      ...prefix.slice(i + 1).map(x => G(x)))))];

  if (terms.length == 0)
    return sep(0, G(0));
  else
    return sep(n / lam.length, plusa(...terms));
}

assert.equal(spretty(rebalanceOne(5, [8, 9, 7, 2, 4])),
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

export function rebalance(n: number, tail: number): Exp {
  const headSum = n + 1 - tail;
  const cs = comps(headSum);
  return plusa(...cs.filter(c => !(c.length == headSum && tail == 1)).map(c => {
    const coeff = tail * factorial(headSum + tail - 1) / factorial(c.length);
    // console.log(coeff, [...c, tail]);
    return rebalanceOne(coeff, [...c, tail]);
  }));
}

assert.equal('0', epretty(sub(rebalance(3, 1), plusa(
  rebalanceOne(6, [3, 1]),
  rebalanceOne(3, [2, 1, 1]),
  rebalanceOne(3, [1, 2, 1]),
))));
