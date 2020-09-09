function monomials(vars, deg) {
  if (vars == 1) {
	 return [[deg]];
  }
  if (deg == 0) {
	 return [ Array.from(Array(vars)).map(x => 0)]
  }
  let rv = [];
  for (let i = 0; i <= deg; i++) {
	 rv.push.apply(rv,  monomials(vars - 1, deg - i).map(a => [i].concat(a)));
  }
  return rv;
}

// returns s, a dash-delimited sequence of numbers, in a canonical orientation.
// (this uses alphabetical sort; might be more principled to use lex sort on lists)
function orient(s) {
  return [s, s.split('-').reverse().join('-')].sort()[1];
}
function shape_of_mon(mon) {
  let s = mon.map(x => `[${x}]`).join('-');
  s=s.replace(/\[0\]/g, ' ').replace(/( -)/g, ' ')
	 .replace(/- /g, ' ')
	 .replace(/^ +/, '').replace(/ +$/, '')
	 .replace(/\[|\]/g, '')
	 .split(/ +/).map(orient).sort().reverse()
	 .join(' ');
  return s;
}

function mons_by_shape(vars, deg) {
  const rv = {};
  for(const mon of monomials(vars, deg)) {
	 const k = shape_of_mon(mon);
	 if (!rv[k]) rv[k] = [];
	 rv[k].push(mon);
  }
  return rv;
}

for (let i = 1; i < 10; i++) {
  let s = '';
  for (let j = 1; j < 10; j++) {
	 s += ' ' + Object.keys(mons_by_shape(i, j)).length;
  }
  console.log(s);
}
// produces:
// 1 1 1 1 1 1 1 1 1
// 1 2 2 3 3 4 4 5 5
// 1 3 4 7 9 13 16 21 25 // A004652?
// 1 3 5 10 15 25 35 52 69
// 1 3 6 13 22 41 65 106 158
// 1 3 6 14 26 53 93 167 274
// 1 3 6 15 29 63 119 231 411
// 1 3 6 15 30 68 135 278 530
// 1 3 6 15 31 71 146 313 627
