function perms(n) {
  if (n == 1) {
	 return [[0]];
  }
  else {
	 const ps = perms(n-1);
	 const rv = [];
	 for (const p of ps) {
		for (let i = n-1; i >= 0; i--) {
//		for (let i = 0; i < n; i++) {
		  const before = p.slice(0, i);
		  const after = p.slice(i, p.length);
		  rv.push(before.concat([n-1], after));
		}
	 }
	 return rv;
  }
}

function range(n) { return Array.from({length: n}, (x, i) => i); }

function apply(a, p, o) {
  return a.map((x, i) => {
	 if (i - o >= 0 && i - o < p.length) {
		return a[o + p[i - o]];
	 }
	 else {
		return a[i];
	 }
  });
}

const K = 4;

perms(2 * K).forEach(p => {
  const r = range(3 * K);
  const lt = apply(apply(apply(r, p, 0), p, K), p, 0).join(',');
  const rt = apply(apply(apply(r, p, K), p, 0), p, K).join(',');
  const reid3 = lt == rt;
  const reid3txt = reid3 ? '3' : ' ';
  const selfInverse = apply(p, p, 0).join(',') == range(p.length).join(',');
  const selfInverseTxt = selfInverse ? ' ' : '2';

  const moved = p.map((x,i) => (x == i ? 0 : 1)).reduce((x,y)=>x+y) + '';
  const info =  reid3txt + selfInverseTxt + `${moved.padStart(10)}m` ;

  if (reid3) {
//	 console.log(info);
	 console.log(info + '  ' + p.join(''));
  }
});
