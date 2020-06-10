import * as cubes from '../src/cubes';
import { expect } from 'chai';
import 'mocha';

describe('Cube', () => {

  it('should be able to compute boundaries', () => {
    const result = cubes.sbdr({ '0*': 1, '*0': -1 });
    expect(result).to.eql({ '10': -1, '01': 1 });
  });

  it('should be able to compute star insertions', () => {
    const result = cubes.sins('*11110');
    expect(result).to.eql({
      "**00001": 2,
      "*1*0001": 1,
      "*11*001": 1,
      "*111*01": 1,
      "*1111*1": 1,
      "*11110*": 1
    });
  });

});
