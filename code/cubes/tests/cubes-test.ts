import * as cubes from '../src/cubes';
import { sub, bndr, insr, stringify, scale, sing } from '../src/cubes';
import { expect } from 'chai';
import 'mocha';

describe('Cube', () => {

  it('should be able to compute boundaries', () => {
    const result = cubes.bndr({ '0*': 1, '*0': -1 });
    expect(result).to.eql({ '10': -1, '01': 1 });
  });

  it('should be able to compute star insertions', () => {
    const result = cubes.ins('*11110');
    expect(result).to.eql({
      "**00001": 2,
      "*1*0001": 1,
      "*11*001": 1,
      "*111*01": 1,
      "*1111*1": 1,
      "*11110*": 1
    });
  });

  it('should satisfy a 2-version of the conjecture', () => {
    for (const x of ['10111', '000', '', '0111']) {
      const y = sing(x);
      const result = sub(bndr(insr(insr(y))),
        scale(2, insr(bndr(insr(y)))));
      expect(result).to.eql({});
    }
  });

  it('should satisfy a 3-version of the conjecture', () => {
    for (const x of ['10111', '000', '', '0111']) {
      const y = sing(x);
      const result = sub(bndr(insr(insr(insr(y)))),
        scale(3, insr(insr(bndr(insr(y))))));
      expect(result).to.eql({});
    }
  });

  it('should satisfy a 4-version of the conjecture', () => {
    for (const x of ['10111', '000', '', '0111']) {
      const y = sing(x);
      const result = sub(bndr(insr(insr(insr(insr(y))))),
        scale(4, insr(insr(insr(bndr(insr(y)))))));
      expect(result).to.eql({});
    }
  });

});
