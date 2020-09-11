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

function weight_of_shape(shape) {
  if (shape === undefined || shape === '') return 0;
  return shape.split(/ |-/).map(x => parseInt(x)).reduce((x,y)=>x+y);
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

  return  '(' + poly.match(/(\S*\[.*?\])/g).map(x => {
	 const m = x.match(/(.*)\[(.*)\]/);
	 const [coef, shape] = [m[1],m[2]];
	 const sdeg = deg - weight_of_shape(shape);
	 const v = sdeg == 0 ? '' : (sdeg == 1 ? 'x * ' : `x^${sdeg} * `);
	 let rcoef = coef;
	 if (rcoef === '') rcoef = 1;
	 if (rcoef === '-') rcoef = -1;
	 return `${rcoef} * ${v}(${sage_of_shape(shape)})`;
  }).join(' +\n ') + ')';
}

let id = 100;

function nb_of_poly(name, opt, poly) {
  return `{{{id=${id++}|\n${name} = ${sage_of_poly(opt,poly)}\n///\n}}}\n`
}

console.log(nb_of_poly('poly21', {v: 'a b', deg: 2},   '[] -[2] [1-1]'));
console.log(nb_of_poly('poly22', {v: 'a b c', deg: 2}, '[] -[2] [1-1] -2[1 1]'));

console.log(nb_of_poly('poly31', {v: 'a b c', deg: 3}, `
[]
-[3]
[1]
-[2]
[2 1]
2[1 1]
[1-1]
`));

console.log(nb_of_poly('poly41', {v: 'a b c d', deg: 4}, `
[]
2[1]
3[1-1]
4[1 1]
-2[3]
2[2 1]
4[1-1 1]
4[1-1-1]
-[4]
-[3-1]
[2 1-1]
[2-1-1]
3[1-1-1-1]
2[2 2]
`));

console.log(nb_of_poly('poly32', {v: 'a b c d', deg: 5}, `
[]
[5]
[4]
[4 1]
[3-2]
[1]
-[2-2-1]
-[4-1]
-2[2 1]
-2[2 2]
-2[2-1-1-1]
-2[2-1-1]
-2[2]
-2[3 2]
-2[3-1 1]
-2[3-1]
-2[3]
2[1-1 1]
2[1-1-1-1]
2[1-1]
2[1-2-1-1]
2[1-2-1]
2[1-3-1]
2[2 1-1]
2[2-1-2]
2[3 1-1]
3[2-2 1]
3[2-2]
`));

console.log(nb_of_poly('poly311', {v: 'a b c d', deg: 6}, `
[]
[4 2]
-4[4 1-1]
-4[3 3]
-4[3 1]
-4[2-1-1-2]
-3[2]
-3[2-2 2]
-2[4-1 1]
-2[3-3]
-2[2-2-1-1]
-2[1-3-1-1]
-2[1-2-2-1]
-2[1-2-1]
-2[1-1-1-1]
-[6]
2[1 1]
2[2 2]
2[2-1-2-1]
2[2-3-1]
2[3-1-1-1]
2[3-2 1]
2[5 1]
3[2-2]
3[4]
4[2 1-1]
4[3-1 2]
`));
