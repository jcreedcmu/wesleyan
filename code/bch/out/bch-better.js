"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const assert_1 = __importDefault(require("assert"));
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
// scalar-expression product
function sep(s, e) {
    const rv = {};
    for (const t of Object.keys(e)) {
        rv[t] = s * e[t];
    }
    return rv;
}
// term-expression product
function tep(t, e) {
    const rv = {};
    for (const tt of Object.keys(e)) {
        rv[`${t},${tt}`] = e[tt];
    }
    return rv;
}
function prod(e1, e2) {
    let rv = {};
    for (const t of Object.keys(e1)) {
        rv = plus(tep(t, sep(e1[t], e2)), rv);
    }
    return rv;
}
function epretty(e) {
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
assert_1.default.equal(epretty(plus({ '1,2': 3, '2,1': -1 }, { '5': 10, '0': -2, '6': -3 })), '-2G_{0} + 10G_{5} - 3G_{6} + 3G_{12} - G_{21}');
assert_1.default.equal(epretty(prod({ '1,2': 3, '2,1': -1 }, { '5': 10, '0': -2 })), '2G_{210} - 10G_{215} - 6G_{120} + 30G_{125}');
