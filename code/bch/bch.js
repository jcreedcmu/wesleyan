function comps(n) {
  if (n <= 0) return [[]];
  let rv = [];
  for (let i = 1; i <= n; i++) {
    rv = [...rv, ...comps(n-i).map(c => [...c, i])];
  }
  return rv;
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
    const {coeff, prod} = term;
    const k = prod.map(n => 'G' + n).join('*');
    rv[k] = (rv[k] ?? 0) + coeff;
  });
  return rv;
}

function pretty(rec) {
  return Object.entries(rec).map(([k,v]) => {
    return `${v} ${k}`;
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
        if (i % 2 == sgn) rv.push({prod: c, coeff: nk * choose(k-1, i) * c[i]});
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

function recurrenceG(m) {
  const n = m - 1;
  const {posrec, negrec} = getRecs(n);
  return `${factorial(n+1)}G${n+1} + ${pretty(posrec)} = L${n} + ${pretty(negrec)}`;
}

function filterZeros(rec) {
  return Object.fromEntries(Object.entries(rec).filter(([k,v]) => v != 0));
}

function addRecs(r1, r2) {
  const rv = {};
  for (const k of Object.keys(r1)) {
    rv[k] = (rv[k] ?? 0) + r1[k];
  }
  for (const k of Object.keys(r2)) {
    rv[k] = (rv[k] ?? 0) + r2[k];
  }
  return filterZeros(rv);
}

function subRecs(r1, r2) {
  const rv = {};
  for (const k of Object.keys(r1)) {
    rv[k] = (rv[k] ?? 0) + r1[k];
  }
  for (const k of Object.keys(r2)) {
    rv[k] = (rv[k] ?? 0) - r2[k];
  }
  return rv;
}

function ruleG(m) {
  if (m == 1) return {src: {'G1': 1}, dst:{ 'A' : 1, 'B': 1}};
  const n = m - 1;
  const {posrec, negrec} = getRecs(n);
  posrec[`G${m}`] = factorial(m);
  negrec[`L${n}`] = 1;
  return  {src:  posrec, dst: negrec};
}

// f : string → string
function srec(f, rec, nn=1) {
  const rv = {};
  for (const k of Object.keys(rec)) {
    rv[f(k)] = rec[k]*nn;
  }
  return rv;
}


function ruleprod(rr1, rr2) {
  return {src: recprod(rr1.src, rr2.src),
          dst: recprod(rr1.dst, rr2.dst)};
}

function rulesprod(f, r, nn=1) {
  return {src: srec(f, r.src, nn),
          dst: srec(f, r.dst, nn)};
}

function recprod(r1, r2) {
  const rv = {};
  for (const k1 of Object.keys(r1)) {
    for (const k2 of Object.keys(r2)) {
      rv[`${k1}*${k2}`] = r1[k1] * r2[k2];
    }
  }
  return rv;
}

function net(rule) {
  return subRecs(rule.dst, rule.src);
}

function initialState(n) {
  const cs = comps(n);
  const terms = cs.map(c => ({coeff: factorial(n) / factorial(c.length), prod: c}));
  return recordOfTerms(terms);
}

function ruleL(n) {
  const prev = n == 1 ? 'A' : `L${n-1}`;
  return {src: {[`L${n}`]: 1, [`B*${prev}`]: 1}, dst: {[`${prev}*B`]: 1 }};
}

// Proof of n=3 case
// console.log(recurrenceG(3));
// let state = initialState(3);
// state = addRecs(state, net(ruleG(3)) );
// state = addRecs(state, net(rulesprod( x => `G1*${x}`, ruleG(2)) ));
// state = addRecs(state, net(rulesprod( x => `G1*${x}`, ruleG(2)) ));
// state = addRecs(state, net(rulesprod( x => `${x}*G1`, ruleG(2)) ));
// state = addRecs(state, net(rulesprod( x => `${x}*L1`, ruleG(1)) ));
// state = addRecs(state, net(rulesprod( x => `${x}*L1`, ruleG(1)) ));
// state = addRecs(state, net(rulesprod( x => `L1*${x}`, ruleG(1)) ));
// state = addRecs(state, net(ruleL(2) ));
// state = addRecs(state, net(rulesprod( x => `A*${x}`, ruleL(1)) ));
// state = addRecs(state, net(rulesprod( x => `${x}*A`, ruleL(1)) ));
// state = addRecs(state, net(rulesprod( x => `${x}*B`, ruleL(1)) ));
// state = addRecs(state, net(rulesprod( x => `A*${x}`, ruleL(1)) ));
// state = addRecs(state, net(rulesprod( x => `B*${x}`, ruleL(1)) ));
// state = addRecs(state, net(rulesprod( x => `${x}*B`, ruleL(1)) ));
// state = addRecs(state, net(ruleprod(ruleG(1), ruleprod(ruleG(1), ruleG(1)))) );
// console.log(state);
console.log(recurrenceG(4));
let state = initialState(4);
const steps = [
  // G4
  ruleG(4),
  // G3
  rulesprod( x => `G1*${x}`, ruleG(3), 3),
  rulesprod( x => `${x}*G1`, ruleG(3)),
  // G2
  rulesprod( x => x, ruleprod( ruleG(2), ruleG(2)), 3),
  rulesprod( x => `${x}*G1*G1`, ruleG(2), 1),
  rulesprod( x => `G1*${x}*G1`, ruleG(2), 2),
  rulesprod( x => `G1*G1*${x}`, ruleG(2), 3),
  // G1
  ruleprod(ruleprod(ruleG(1), ruleG(1)), ruleprod(ruleG(1), ruleG(1))),
  rulesprod( x => `L1*${x}`, ruleprod(ruleG(1), ruleG(1)) ),
  ruleprod(ruleG(1), rulesprod( x => `L1*${x}`, ruleG(1), 2 )),
  rulesprod( x => `${x}*L1`, ruleprod(ruleG(1), ruleG(1)), 3 ),
  rulesprod( x => `${x}*L2`, ruleG(1), 3),
  rulesprod( x => `L2*${x}`, ruleG(1), 1),
  // L3
  ruleL(3),
  // L2
  rulesprod( x => `${x}*A`, ruleL(2)),
  rulesprod( x => `${x}*B`, ruleL(2), 2),
  rulesprod( x => `A*${x}`, ruleL(2), 3),
  rulesprod( x => `B*${x}`, ruleL(2), 2),
  // L1
  rulesprod(x=>x, ruleprod(ruleL(1), ruleL(1)), 3),
  // Everything past this point is a little suspect; we head into the negatives.
  rulesprod( x =>   `${x}*A*A`, ruleL(1), 1),
  rulesprod( x =>   `${x}*A*B`, ruleL(1), 1),
  rulesprod( x =>   `${x}*B*B`, ruleL(1), 1),
  rulesprod( x =>   `A*${x}*A`, ruleL(1), 2),
  rulesprod( x =>   `A*${x}*B`, ruleL(1), 3),
  rulesprod( x =>   `B*${x}*A`, ruleL(1), 1),
  rulesprod( x =>   `A*A*${x}`, ruleL(1), 3),
  rulesprod( x =>   `B*B*${x}`, ruleL(1), 1),
  rulesprod( x =>   `B*${x}*B`, ruleL(1), 2),
  rulesprod( x =>   `${x}*B*B`, ruleL(1), 2),
  rulesprod( x =>   `A*${x}*B`, ruleL(1), 2),
  rulesprod( x =>   `${x}*B*A`, ruleL(1), -1),
]
for (const step of steps) {
  state = addRecs(state, net(step) );
}

console.log(state);
