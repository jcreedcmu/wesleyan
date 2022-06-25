import assert from 'assert';

// values are coefficients
type Exp = Record<Term, number>;
type Term = string // e.g. '1,2,[3,4]'

function plus(t1: Exp, t2: Exp): Exp {
  const rv: Exp = {};
  for (const e of Object.keys(t1)) {
    rv[e] = (rv[e] ?? 0) + t1[e];
  }
  for (const e of Object.keys(t2)) {
    rv[e] = (rv[e] ?? 0) + t2[e];
  }
  return rv;
}

// scalar-expression product
function sep(s: number, e: Exp): Exp {
  const rv: Exp = {};
  for (const t of Object.keys(e)) {
    rv[t] = s * e[t];
  }
  return rv;
}

// term-expression product
function tep(t: Term, e: Exp): Exp {
  const rv: Exp = {};
  for (const tt of Object.keys(e)) {
    rv[`${t},${tt}`] = e[tt];
  }
  return rv;
}

function prod(e1: Exp, e2: Exp): Exp {
  let rv: Exp = {};
  for (const t of Object.keys(e1)) {
    rv = plus(tep(t, sep(e1[t], e2)), rv);
  }
  return rv;
}

function epretty(e: Exp): string {
  let rv: string[] = [];
  for (const t of Object.keys(e)) {
    if (e[t] != 0) {
      let coeff = e[t] == -1 ? '-' : e[t] == 1 ? '' : e[t];
      const sub = t.replace(/,/g, '');
      rv.push(`${coeff}G_{${sub}}`);
    }
  }
  return rv.join(" + ").replace(/\+ -/g, '- ');
}

assert.equal(epretty(plus({ '1,2': 3, '2,1': -1 }, { '5': 10, '0': -2, '6': -3 })), '-2G_{0} + 10G_{5} - 3G_{6} + 3G_{12} - G_{21}');
assert.equal(epretty(prod({ '1,2': 3, '2,1': -1 }, { '5': 10, '0': -2 })), '2G_{210} - 10G_{215} - 6G_{120} + 30G_{125}');
