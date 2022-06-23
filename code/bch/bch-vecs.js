const assert = require('assert');

function vz(len) {
  const ent = [];
  for (let i = 0; i < (1 << len); i++) {
    ent[i] = 0;
  }
  return {len, ent};
}

function vplus(a, b) {
  assert(a.len == b.len);
  const len = a.len;
  const ent = [];
  for (let i = 0; i < (1 << len); i++) {
    ent[i] = a.ent[i] + b.ent[i];
  }
  return {len, ent};
}

function vplusl(as) {
  return as.reduce(vplus);
}

function vs(a, s) {
  const len = a.len;
  const ent = [];
  for (let i = 0; i < (1 << len); i++) {
    ent[i] = a.ent[i] * s;
  }
  return {len, ent};
}

function vsub(a, b) {
  return vplus(a, vs(b, -1));
}

function vprod(a, b) {
  const len = a.len + b.len;
  const ent = [];
  for (let i = 0; i < (1 << a.len); i++) {
    for (let j = 0; j < (1 << b.len); j++) {
      ent[(i << b.len) + j] = a.ent[i] * b.ent[j];
    }
  }
  return {len, ent};
}

function vprodl(as) {
  return as.reduce(vprod);
}

function lie(a, b) {
  return vsub(vprod(a, b), vprod(b, a));
}

const A = {len: 1, ent: [1,0]};
const B = {len: 1, ent: [0,1]};

function Z(x) {
  return vplus(vprod(A, x), vprod(x, B));
}

function equal(x, y) {
  const ent = vsub(x, y).ent;
  return ent.every(e => e < 1e-10);
}

function lhs(n) { // (A ⊕ B)^n
  if (n == 1) return G1;
  return Z(lhs(n-1));
}

const G0 = A;
const G1 = vplus(A, B);
const G2 = vs(lie(G0, G1), 1/2);
const G3 = vs(vplus( lie(A,lie(A, B)), lie(B, lie(B, A))), 1/12);
const G3a = vs(vplus(lie(G2, G1), vs(lie(G0, G2), 2)), 1/6);

assert(equal(G3, G3a));

const G4 = vs( lie(B, lie(A, lie(A, B))), -1/24);
const G4a = vs(vplusl([
  vs(lie(G0,G3), 6),
  vs(lie(lie(G0,G2),G1), 1),
]), 1/24);
assert(equal(G4, G4a));


const G5 = vplusl([
  vs(lie(B, lie(B, lie(B, lie(B, A)))), -1/720),
  vs(lie(A, lie(A, lie(A, lie(A, B)))), -1/720),
  vs(lie(A, lie(B, lie(B, lie(B, A)))), +1/360),
  vs(lie(B, lie(A, lie(A, lie(A, B)))), +1/360),
  vs(lie(A, lie(B, lie(A, lie(B, A)))), +1/120),
  vs(lie(B, lie(A, lie(B, lie(A, B)))), +1/120),
]);

const S = [undefined,
           G1, // n=1
           vplusl([vs(G2, 2), vprodl([G1, G1])]), // n=2
           vplusl([
             vs(G3, 6),
             vs(vprod(G2,G1), 3),
             vs(vprod(G1,G2), 3),
             vprodl([G1, G1, G1]),
           ]), // n=3
           vplusl([
             vs(G4, 24),
             vs(vprod(G3,G1), 12),
             vs(vprod(G1,G3), 12),
             vs(vprod(G2,G2), 12),
             vs(vprodl([G2, G1, G1]), 4),
             vs(vprodl([G1, G2, G1]), 4),
             vs(vprodl([G1, G1, G2]), 4),
             vprodl([G1, G1, G1, G1]),
           ]), // n=4
           vplusl([
             vs(G5, 120),
             vs(vprod(G4,G1), 60),
             vs(vprod(G1,G4), 60),
             vs(vprod(G2,G3), 60),
             vs(vprod(G3,G2), 60),
             vs(vprodl([G3, G1, G1]), 20),
             vs(vprodl([G1, G3, G1]), 20),
             vs(vprodl([G1, G1, G3]), 20),
             vs(vprodl([G2, G2, G1]), 20),
             vs(vprodl([G2, G1, G2]), 20),
             vs(vprodl([G1, G2, G2]), 20),
             vs(vprodl([G1, G1, G1, G2]), 5),
             vs(vprodl([G1, G1, G2, G1]), 5),
             vs(vprodl([G1, G2, G1, G1]), 5),
             vs(vprodl([G2, G1, G1, G1]), 5),
             vprodl([G1, G1, G1, G1, G1]),
           ]), // n=5
      ];
assert(equal(lhs(2), S[2]));
assert(equal(lhs(3), S[3]));
assert(equal(lhs(4), S[4]));
assert(equal(lhs(5), S[5]));


// t = 10
const ll = vplusl([
  vs(lie(G0,G4), 24),
  vs(lie(G4,G1), 12),
  vs(vprod(G4,G1), 60),
  vs(vprod(G1,G4), 60),

  vs(vprod(G3,G2), 24),
  vs(vprodl([G3,G1,G1]), 12),
  vs(vprod(G2,G3), 24),

  vs(vprodl([G1,G3,G1]), 12),

  vs(vprodl([lie(G0,G2), G2]), 12),
  vs(vprodl([G2, lie(G0,G2)]), 12),

  vs(vprodl([lie(G0,G2), G1, G1]), 2),
  vs(vprodl([G1, lie(G0,G2), G1]), 4),
  vs(vprodl([G1, G1, lie(G0,G2)]), 6),

  vs(vprodl([G2,lie(G2,G1)]), 8),
  vs(vprodl([lie(G2,G1),G2]), 4),

  vs(vprodl([lie(G2, G1), G1, G1]),1),
  vs(vprodl([G1, lie(G2, G1), G1]),2),
  vs(vprodl([G1, G1, lie(G2, G1)]),3),

  vs(vprodl([G2, G1, G1, G1]),5),
  vs(vprodl([G1, G2, G1, G1]),5),
  vs(vprodl([G1, G1, G2, G1]),5),
  vs(vprodl([G1, G1, G1, G2]),5),

  vs(vprodl([G2,G2,G1]), 20),
  vs(vprodl([G2,G1,G2]), 20),
  vs(vprodl([G1,G2,G2]), 20),

  vprodl([G1, G1, G1, G1, G1]),
]);

const rr = S[5];


assert(equal(ll, rr));
