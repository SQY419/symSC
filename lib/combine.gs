# Combine factors with equal bases, including general (rational) powers.
# This turns a^(1/3)*b^2/(a*b^(2/3)) into b^(4/3)/a^(2/3).

list cp_node;
list cp_exp;
list cp_base;
list cp_pexp;
var cp_sp = 0;

proc cp_push node, exp {
    cp_sp++;
    if cp_sp > length(cp_node) {
        add $node to cp_node;
        add $exp to cp_exp;
    } else {
        cp_node[cp_sp] = $node;
        cp_exp[cp_sp] = $exp;
    }
}

proc cp_add base, ex {
    local i = 1;
    until i > length(cp_base) or nd_sig[cp_base[i]] == nd_sig[$base] {
        i++;
    }
    if i <= length(cp_base) {
        mk_add cp_pexp[i], $ex;
        cp_pexp[i] = mk_add;
    } else {
        add $base to cp_base;
        add $ex to cp_pexp;
    }
}

proc combine_powers root {
    combine_powers = $root;
    if $root == 0 or err != "" {
        combine_powers = 0;
    } else {
        delete cp_base;
        delete cp_pexp;
        delete cp_node;
        delete cp_exp;
        cp_sp = 0;
        mk_num 1, 1;
        cp_push $root, mk_num;
        until cp_sp == 0 or err != "" {
            local n = cp_node[cp_sp];
            local ex = cp_exp[cp_sp];
            cp_sp--;
            local k = nd_kind[n];
            if k == K.Mul {
                cp_push nd_b[n], ex;
                cp_push nd_a[n], ex;
            } elif k == K.Pow {
                local b = nd_a[n];
                mk_num nd_num[n], 1;
                local en = mk_num;
                mk_mul ex, en;
                local ne = mk_mul;
                if nd_kind[b] == K.Mul {
                    cp_push b, ne;
                } elif nd_kind[b] == K.PowE {
                    mk_mul ne, nd_b[b];
                    local ne2 = mk_mul;
                    cp_add nd_a[b], ne2;
                } else {
                    cp_add b, ne;
                }
            } elif k == K.PowE {
                local b = nd_a[n];
                local e = nd_b[n];
                mk_mul ex, e;
                local ne = mk_mul;
                if nd_kind[b] == K.Mul {
                    cp_push b, ne;
                } else {
                    cp_add b, ne;
                }
            } else {
                cp_add n, ex;
            }
        }
        if err != "" {
            combine_powers = 0;
        } else {
            local out = 0;
            local i = 1;
            until i > length(cp_base) or err != "" {
                local ex = cp_pexp[i];
                if is_zero(ex) {
                    i++;
                } else {
                    local f = cp_base[i];
                    if is_one(ex) {
                        f = cp_base[i];
                    } else {
                        mk_pow_expr cp_base[i], ex;
                        f = mk_pow_expr;
                    }
                    if out == 0 {
                        out = f;
                    } else {
                        mk_mul out, f;
                        out = mk_mul;
                    }
                    i++;
                }
            }
            if err != "" {
                combine_powers = 0;
            } elif out == 0 {
                mk_num 1, 1;
                combine_powers = mk_num;
            } else {
                combine_powers = out;
            }
        }
    }
}
