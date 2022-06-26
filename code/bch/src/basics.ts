// values are coefficients
export type Exp = Record<Term, number>;
export type Term = string // e.g. '1,2,[3,4]'
export type Item = number | [Tree, Tree]; // a pair meanse a lie product
export type Tree = Item[]; // the list structure here implies ordinary product

const _cache: Record<Term, Tree> = {};

function termOfItem(it: Item): Term {
  if (typeof it == 'number')
    return it + '';
  else
    return '[' + termOfTree(it[0]) + ',' + termOfTree(it[1]) + ']';
}

function _termOfTree(t: Tree): Term {
  return t.map(termOfItem).join(';');
}

export function termOfTree(t: Tree): Term {
  const tm = _termOfTree(t);
  _cache[tm] = t;
  return tm;
}

export function treeOfTerm(tm: Term): Tree {
  if (!(tm in _cache)) {
    throw new Error(`haven't cached ${tm}`);
  }
  return _cache[tm];
}

export function mkexp(tr: Tree, coeff: number = 1): Exp {
  return { [termOfTree(tr)]: coeff };
}

export function G(n: number, coeff: number = 1): Exp {
  return mkexp([n], coeff);
}
