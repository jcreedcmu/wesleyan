import * as cubes from '../src/cubes';
import { expect } from 'chai';
import 'mocha';

describe('Cube computations', () => {

  it('should work', () => {
    const result = cubes.sbdr({ '0*': 1, '*0': -1 });
    expect(result).to.eql({ '10': -1, '01': 1 });
  });

});
