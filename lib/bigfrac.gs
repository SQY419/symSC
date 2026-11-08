# Normalize a product containing big integer numerator/denominator factors.
# A fraction is represented as Big(n) * Pow(Big(d), -1), not as a separate
# rational node type.

list bnf_stk;
list bnf_facs;
var bnf_n = "1";
var bnf_d = "1";
var bnf_ok = false;

proc bnf_reduce n, d {
    local nn = bi_norm($n);
    local dd = bi_norm($d);
    if dd == "0" { set_err "除数为零"; } else {
        if dd[1] == "-" { bi_neg_str nn; nn = bi_neg_str; dd = substr(dd, 2, length(dd)); }
        bi_gcd_str nn, dd;
        local g = bi_gcd_str;
        if g != "1" and g != "0" {
            bi_div_str nn, g; nn = bi_div_str;
            bi_div_str dd, g; dd = bi_div_str;
        }
        if nn == "0" { dd = "1"; }
        bnf_n = nn;
        bnf_d = dd;
    }
}

proc normalize_big_fraction root {
    normalize_big_fraction = 0;
    if nd_kind[$root] != K.Mul { normalize_big_fraction = 0; }
    else {
        delete bnf_stk; delete bnf_facs;
        local sp = 0;
        sp++; add $root to bnf_stk;
        until sp == 0 {
            local x = bnf_stk[sp];
            sp--;
            if nd_kind[x] == K.Mul {
                sp++;
                if sp > length(bnf_stk) { add nd_b[x] to bnf_stk; } else { bnf_stk[sp] = nd_b[x]; }
                sp++;
                if sp > length(bnf_stk) { add nd_a[x] to bnf_stk; } else { bnf_stk[sp] = nd_a[x]; }
            } else { add x to bnf_facs; }
        }
        bnf_n = "1";
        bnf_d = "1";
        bnf_ok = true;
        local i = 1;
        until i > length(bnf_facs) or bnf_ok == false {
            local f = bnf_facs[i];
            if nd_kind[f] == K.Big {
                bi_mul_str bnf_n, nd_txt[f]; bnf_n = bi_mul_str;
            } elif nd_kind[f] == K.Num {
                bi_mul_str bnf_n, ("" & nd_num[f]); bnf_n = bi_mul_str;
                bi_mul_str bnf_d, ("" & nd_den[f]); bnf_d = bi_mul_str;
            } elif nd_kind[f] == K.Pow and nd_kind[nd_a[f]] == K.Big {
                local e = nd_num[f];
                if e < 0 {
                    bi_pow_str nd_txt[nd_a[f]], 0 - e; local p = bi_pow_str;
                    bi_mul_str bnf_d, p; bnf_d = bi_mul_str;
                } elif e > 0 {
                    bi_pow_str nd_txt[nd_a[f]], e; local p = bi_pow_str;
                    bi_mul_str bnf_n, p; bnf_n = bi_mul_str;
                }
            } else {
                bnf_ok = false;
            }
            i++;
        }
        if bnf_ok == false {
            normalize_big_fraction = 0;
        } else {
            bnf_reduce bnf_n, bnf_d;
            if bnf_d == "1" {
                mk_big bnf_n;
                normalize_big_fraction = mk_big;
            } else {
                mk_big bnf_n; local nn = mk_big;
                mk_big bnf_d; local dd = mk_big;
                mk_pow dd, -1; local inv = mk_pow;
                mk_mul nn, inv;
                normalize_big_fraction = mk_mul;
            }
        }
    }
}

# Recognize and numerically evaluate a normalized fraction tree:
#   Big(num) * Pow(Big(den), -1)   (plus optional numeric constants)
func is_bigfrac(root) {
    if $root == 0 or nd_kind[$root] != K.Mul { return false; }
    delete bnf_stk;
    local sp = 0;
    sp++; add $root to bnf_stk;
    local has_den = false;
    local ok = true;
    until sp == 0 {
        local x = bnf_stk[sp];
        sp--;
        if nd_kind[x] == K.Mul {
            sp++;
            if sp > length(bnf_stk) { add nd_b[x] to bnf_stk; } else { bnf_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(bnf_stk) { add nd_a[x] to bnf_stk; } else { bnf_stk[sp] = nd_a[x]; }
        } elif nd_kind[x] == K.Big {
            # numerator integer
        } elif nd_kind[x] == K.Num {
            # numeric coefficient
        } elif nd_kind[x] == K.Pow and nd_kind[nd_a[x]] == K.Big and nd_num[x] < 0 {
            has_den = true;
        } else {
            ok = false;
            sp = 0;
        }
    }
    return ok and has_den;
}

proc bigfrac_double root {
    local n = 1;
    local d = 1;
    delete bnf_stk;
    local sp = 0;
    sp++; add $root to bnf_stk;
    until sp == 0 {
        local x = bnf_stk[sp];
        sp--;
        if nd_kind[x] == K.Mul {
            sp++;
            if sp > length(bnf_stk) { add nd_b[x] to bnf_stk; } else { bnf_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(bnf_stk) { add nd_a[x] to bnf_stk; } else { bnf_stk[sp] = nd_a[x]; }
        } elif nd_kind[x] == K.Big {
            n = n * (nd_txt[x] + 0);
        } elif nd_kind[x] == K.Num {
            n = n * (nd_num[x] / nd_den[x]);
        } elif nd_kind[x] == K.Pow and nd_kind[nd_a[x]] == K.Big and nd_num[x] < 0 {
            local e = 0 - nd_num[x];
            local bv = nd_txt[nd_a[x]] + 0;
            local p = 1;
            local k = 0;
            until k >= e { p = p * bv; k++; }
            d = d * p;
        }
    }
    if d == 0 { bigfrac_double = 0; } else { bigfrac_double = n / d; }
}

proc bigfrac_text root {
    bigfrac_text = "";
    if nd_kind[$root] != K.Mul { bigfrac_text = ""; }
    else {
        delete bnf_stk;
        local sp = 0;
        sp++; add $root to bnf_stk;
        local nn = "1";
        local dd = "1";
        until sp == 0 {
            local x = bnf_stk[sp];
            sp--;
            if nd_kind[x] == K.Mul {
                sp++;
                if sp > length(bnf_stk) { add nd_b[x] to bnf_stk; } else { bnf_stk[sp] = nd_b[x]; }
                sp++;
                if sp > length(bnf_stk) { add nd_a[x] to bnf_stk; } else { bnf_stk[sp] = nd_a[x]; }
            } elif nd_kind[x] == K.Big {
                bi_mul_str nn, nd_txt[x]; nn = bi_mul_str;
            } elif nd_kind[x] == K.Num {
                bi_mul_str nn, ("" & nd_num[x]); nn = bi_mul_str;
                bi_mul_str dd, ("" & nd_den[x]); dd = bi_mul_str;
            } elif nd_kind[x] == K.Pow and nd_kind[nd_a[x]] == K.Big and nd_num[x] < 0 {
                bi_pow_str nd_txt[nd_a[x]], 0 - nd_num[x];
                bi_mul_str dd, bi_pow_str; dd = bi_mul_str;
            } else {
                bigfrac_text = "";
                sp = 0;
            }
        }
        bi_gcd_str nn, dd;
        local g = bi_gcd_str;
        if g != "1" and g != "0" {
            bi_div_str nn, g; nn = bi_div_str;
            bi_div_str dd, g; dd = bi_div_str;
        }
        if dd == "1" { bigfrac_text = nn; }
        else { bigfrac_text = nn & "/" & dd; }
    }
}
