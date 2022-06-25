// values are coefficients
export type Exp = Record<Term, number>;
export type Term = string // e.g. '1,2,[3,4]'
export type Item = number | [Item, Item];
export type Tree = Item[];

const _cache: Record<Term, Tree> = {};

function termOfItem(it: Item): Term {
  if (typeof it == 'number')
    return it + '';
  else
    return '[' + termOfItem(it[0]) + ',' + termOfItem(it[1]) + ']';
}

function _termOfTree(t: Tree): Term {
  return t.map(termOfItem).join(',');
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
