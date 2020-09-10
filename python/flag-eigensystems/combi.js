// trying to enumerate all shapes of a given weight

function compos(n) {
  if (n == 0) return [[]];
  if (n == 1) return [[1]];
  const rv = [];
  for (let i = 1; i <= n; i++) {
	 rv.push.apply(rv, compos(n-i).map(tl => [i].concat(tl)));
  }
  return rv;
}

function orient(s) {
  // return s.split('-').sort().join('-'); // this gives A001970
  return [s, s.split('-').reverse().join('-')].sort()[1];
}

function normalize(shape) {
  return (
	 shape
		.split(/ +/).map(orient).sort().reverse()
		.join(' '));
}

function all_joins(xs) {
  if (xs.length == 1) { return [xs[0]+''] }
  const sp = all_joins(xs.slice(1)).map(s => xs[0] + ' ' + s);
  const dsh = all_joins(xs.slice(1)).map(s => xs[0] + '-' + s);
  return sp.concat(dsh);
}


for (let ix = 1; ix < 9; ix++) {
  const s = {};
  compos(ix).map(all_joins).flat(1).forEach(shape => {
	 s[normalize(shape)] = 1;
  });

  console.log(Object.keys(s));
  console.log(Object.keys(s).length);
}
