function comps(n) {
  if (n <= 0) return [[]];
  let rv = [];
  for (let i = 1; i <= n; i++) {
    rv = [...rv, ...comps(n-i).map(c => [...c, i])];
  }
  return rv;
}

function perms(comp, sgn) {
  if (comp.length == 1) {
    return sgn == 1 ? [comp] : [];
  }
  const prefix = comp.slice(0, comp.length - 1);
  const last = comp[comp.length - 1];
  return [
    ...perms(prefix, -sgn).map(perm => [last, ...perm]),
    ...perms(prefix, sgn).map(perm => [...perm, last]),
  ];
}

function factorial(n) {
  if (n <= 1) return 1;
  return n * factorial(n-1);
}

function choose(n, k) {
  return factorial(n) / factorial(k) / factorial(n-k);
}

function recordOfTerms(terms) {
  const rv = {};
  terms.forEach(term => {
    const {coeff, perm} = term;
    const k = perm.join(''); // not valid if numbers > 9!
    rv[k] = (rv[k] ?? 0) + coeff;
  });
  return rv;
}

function pretty(rec) {
  return Object.entries(rec).map(([k,v]) => {
    return `${v} G_{${k}}`;
  }).join(' + ');
}

function getRecs(n) {
  const cs = comps(n+1);
  let posTerms = [];
  let negTerms = [];
  for (let k = 2; k <= n; k++) {
    const csk = cs.filter(c => c.length == k); // compositions of k parts, adding to n+1
    const nk = factorial(n) / factorial(k);
    function getTerms(c, sgn) {
      const rv = [];
      for (let i = 0; i < k; i++) {
        if (i % 2 == sgn) rv.push({perm: c, coeff: nk * choose(k-1, i) * c[i]});
      }
      return rv;
    }
    posTerms = [...posTerms, ...csk.flatMap(c => getTerms(c, 0))];
    negTerms = [...negTerms, ...csk.flatMap(c => getTerms(c, 1))];

  }
  const posrec = recordOfTerms(posTerms);
  const negrec = recordOfTerms(negTerms);
  return {posrec, negrec};
}

function go(m) {
  const n = m - 1;
  const {posrec, negrec} = getRecs(n);
  console.log(`${factorial(n+1)}G_{${n+1}} + ${pretty(posrec)} = L_{${n}} + ${pretty(negrec)}`.replace(/\+/g, '+\n'));
}

go(4);
