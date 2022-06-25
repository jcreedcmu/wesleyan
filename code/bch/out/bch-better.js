"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const basics_1 = require("./basics");
const assert_1 = __importDefault(require("assert"));
// assumes a.length == b.length
function lexo(a, b) {
    for (let i = 0; i < a.length; i++) {
        const d = a[i] - b[i];
        if (d)
            return d;
    }
    return 0;
}
// list of all compositions (i.e. ordered partitions) of length n
function comps(n) {
    if (n <= 0)
        return [[]];
    let rv = [];
    for (let i = 1; i <= n; i++) {
        rv = [...rv, ...comps(n - i).map(c => [...c, i])];
    }
    return rv
        .map(val => ({ val, sortBy: [...val].sort((a, b) => b - a) }))
        .sort((a, b) => a.val.length - b.val.length || lexo(b.sortBy, a.sortBy))
        .map(x => x.val);
}
assert_1.default.deepEqual(comps(4), [
    [4],
    [3, 1],
    [1, 3],
    [2, 2],
    [2, 1, 1],
    [1, 2, 1],
    [1, 1, 2],
    [1, 1, 1, 1]
]);
// factorial
function factorial(n) {
    if (n <= 1)
        return 1;
    return n * factorial(n - 1);
}
assert_1.default.equal(factorial(10), 3628800);
// binomial coefficients
function choose(n, k) {
    return factorial(n) / factorial(k) / factorial(n - k);
}
assert_1.default.equal(choose(10, 3), 120);
// pretty-print an expression
function epretty(e) {
    if (Object.keys(e).every(k => e[k] == 0)) {
        return '0';
    }
    let rv = [];
    for (const t of Object.keys(e)) {
        if (e[t] != 0) {
            let coeff = e[t] == -1 ? '-' : e[t] == 1 ? '' : e[t];
            const sub = t.replace(/,/g, '');
            rv.push(`${coeff}G_{${sub}}`);
        }
    }
    return rv.join(" + ").replace(/\+ -/g, '- ');
}
// sum of two expressions
function plus(t1, t2) {
    var _a, _b;
    const rv = {};
    for (const e of Object.keys(t1)) {
        rv[e] = ((_a = rv[e]) !== null && _a !== void 0 ? _a : 0) + t1[e];
    }
    for (const e of Object.keys(t2)) {
        rv[e] = ((_b = rv[e]) !== null && _b !== void 0 ? _b : 0) + t2[e];
    }
    return rv;
}
function plusa(...args) {
    return args.reduce(plus);
}
assert_1.default.equal(epretty(plusa((0, basics_1.mkexp)([1, 2], 3), (0, basics_1.mkexp)([2, 1], -1), (0, basics_1.mkexp)([5], 10), (0, basics_1.mkexp)([5], -2), (0, basics_1.mkexp)([6], -3))), '8G_{5} - 3G_{6} + 3G_{12} - G_{21}');
// scalar-expression product
function sep(s, e) {
    const rv = {};
    for (const t of Object.keys(e)) {
        rv[t] = s * e[t];
    }
    return rv;
}
// tree-expression product
function tep(tr, e) {
    const rv = {};
    for (const etm of Object.keys(e)) {
        rv[(0, basics_1.termOfTree)([...tr, ...(0, basics_1.treeOfTerm)(etm)])] = e[etm];
    }
    return rv;
}
// product of two expressions
function prod(e1, e2) {
    let rv = {};
    for (const t of Object.keys(e1)) {
        rv = plus(tep((0, basics_1.treeOfTerm)(t), sep(e1[t], e2)), rv);
    }
    return rv;
}
const e1 = [1, 2];
assert_1.default.equal(epretty(prod(plusa((0, basics_1.mkexp)([1, 2], 3), (0, basics_1.mkexp)([2, 1], -1)), plusa((0, basics_1.mkexp)([5], 10), (0, basics_1.mkexp)([0], -2)))), '2G_{210} - 10G_{215} - 6G_{120} + 30G_{125}');
// compute the "target rhs", which corresponds to
// n! times the q^n coefficient of e^{qG₁ + q²G₂ + q³G₃ + ⋯ }
// which turns out to be the sum over all compositions λ₁, …, λₖ of n into k parts of
// (n!/k!) G_{λ₁}⋯G_{λₖ}
function target(n) {
    return comps(n).map(c => ({ [c.join(',')]: factorial(n) / factorial(c.length) })).reduce(plus);
}
assert_1.default.equal(epretty(target(4)), '24G_{4} + 12G_{31} + 12G_{13} + 12G_{22} + 4G_{211} + 4G_{121} + 4G_{112} + G_{1111}');
