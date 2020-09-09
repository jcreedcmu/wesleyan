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

function _accum(vars, deg, rv) {
  for (const mon of monomials(vars, deg)) {
	 const k = shape_of_mon(mon);
	 if (!rv[k]) rv[k] = [];
	 rv[k].unshift(mon);
  }
}

function mons_by_shape(vars, bdeg) {
  const rv = {};
  for (let deg = 1; deg <= bdeg; deg++) {
	 _accum(vars, deg, rv);
  }
  return rv;
}

function sage_of_mon(mon, vars) {
  const parts = vars.map((x, i) => [i, x]).filter(([i, x]) => mon[i] != 0);
  return parts.map(([i,x]) => {
	 if (mon[i] == 1)
		return x
	 else
		return `${x}^${mon[i]}`
  }).join('*');
}



function sage_of_poly({v, deg}, poly) {
  const vars = v.split(' ');
  const cache = mons_by_shape(vars.length, deg);

  function sage_of_shape(shape) {
	 if (shape == '') return '1';
	 const cached = cache[shape];
	 if (!cached) {
		throw `Can't find ${shape}`
	 }
	 return cached.map(mon => sage_of_mon(mon, vars)).join(' + ');
  }

  return  '(' + poly.split('\n').filter(x => x).map(x => {
	 const m = x.match(/(.*) \((?:(.*)\/)?(.*)\)/);
	 const v = m[2] ? (m[2] == 1 ? 'x * ' : `x^${m[2]} * `) : '';
	 return `${m[1]} * ${v}(${sage_of_shape(m[3])})`;
  }).join(' +\n ') + ')';
}

console.log('poly41 == ' + sage_of_poly({v: 'a b c d', deg: 4}, `
1 (4/)
2 (3/1)
3 (2/1-1)
4 (2/1 1)
-2 (1/3)
2 (1/2 1)
4 (1/1-1 1)
4 (1/1-1-1)
-1 (4)
-1 (3-1)
1 (2 1-1)
1 (2-1-1)
3 (1-1-1-1)
2 (2 2)
`));

console.log('poly32 == ' + sage_of_poly({v: 'a b c d', deg: 5}, `
-2 (1/2-1-1)
1 (5/)
1 (5)
1 (4/1)
1 (1/4)
1 (4 1)
-2 (3 2)
-2 (3/2)
-2 (2/3)
2 (3 1-1)
2 (3/1-1)
-2 (2/2 1)
-2 (1/2 2)
2 (2/1-1 1)
2 (1/2 1-1)
-2 (3-1 1)
-2 (1/3-1)
3 (2-2 1)
3 (1/2-2)
2 (1/1-2-1)
2 (1/1-1-1-1)
-1 (4-1)
1 (3-2)
-1 (2-2-1)
2 (2-1-2)
2 (1-3-1)
-2 (2-1-1-1)
2 (1-2-1-1)
`));
