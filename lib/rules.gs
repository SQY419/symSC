# Structural rule engine for simplification.
# Rule table:
#   1. Pow(Sqrt(?u), n) : n even -> ?u^(n/2)
#   2. Pow(Sqrt(?u), n) : n odd, n > 1 -> ?u^((n-1)/2) * Sqrt(?u)
#   3. Sqrt(Pow(?u, 2)) -> Abs(?u)
#   4. Ln(Exp(?u)) -> ?u
#   5. Exp(Ln(?u)) -> ?u
#   6. Abs(Abs(?u)) -> Abs(?u)
# Rule 1/2 are applied only for integer n; negative odd n is left alone
# to avoid a rewrite loop on 1/sqrt(u).

var rs_changed = false;

list rs_val;
list rs_stk_node;
list rs_stk_state;
var rs_sp = 0;

proc rs_push id, state {
    rs_sp++;
    if rs_sp > length(rs_stk_node) {
        add $id to rs_stk_node;
        add $state to rs_stk_state;
    } else {
        rs_stk_node[rs_sp] = $id;
        rs_stk_state[rs_sp] = $state;
    }
}

proc rule_sqrt_power node {
    if $node == 0 or nd_kind[$node] != K.Pow or nd_kind[nd_a[$node]] != K.Sqrt {
        rule_sqrt_power = 0;
    } else {
        local base = nd_a[$node];
        local u = nd_a[base];
        local e = nd_num[$node];
        if e == 0 or e == 1 {
            rule_sqrt_power = 0;
        } elif e % 2 == 0 {
            mk_pow u, e / 2;
            rule_sqrt_power = mk_pow;
        } elif e > 1 {
            mk_pow u, (e - 1) / 2;
            local p = mk_pow;
            mk_mul p, base;
            rule_sqrt_power = mk_mul;
        } else {
            rule_sqrt_power = 0;
        }
    }
}

proc rule_sqrt_square node {
    if $node == 0 or nd_kind[$node] != K.Sqrt {
        rule_sqrt_square = 0;
    } else {
        local ch = nd_a[$node];
        if nd_kind[ch] == K.Pow and nd_num[ch] == 2 {
            mk_func K.Abs, nd_a[ch];
            rule_sqrt_square = mk_func;
        } else {
            rule_sqrt_square = 0;
        }
    }
}


proc rule_sqrt_neg_square node {
    if $node == 0 or nd_kind[$node] != K.Sqrt {
        rule_sqrt_neg_square = 0;
    } else {
        local ch = nd_a[$node];
        if nd_kind[ch] == K.Pow and nd_num[ch] == -2 and nd_den[ch] == 1 {
            mk_func K.Abs, nd_a[ch];
            local a = mk_func;
            mk_pow a, -1;
            rule_sqrt_neg_square = mk_pow;
        } else {
            rule_sqrt_neg_square = 0;
        }
    }
}

proc rule_sqrt_product_square node {
    if $node == 0 or nd_kind[$node] != K.Sqrt {
        rule_sqrt_product_square = 0;
    } else {
        local ch = nd_a[$node];
        if nd_kind[ch] != K.Mul {
            rule_sqrt_product_square = 0;
        } else {
            local a = nd_a[ch];
            local b = nd_b[ch];
            local c = 0;
            local u = 0;
            if nd_kind[a] == K.Num and nd_kind[b] == K.Pow and nd_num[b] == 2 and nd_den[b] == 1 {
                c = a;
                u = nd_a[b];
            } elif nd_kind[b] == K.Num and nd_kind[a] == K.Pow and nd_num[a] == 2 and nd_den[a] == 1 {
                c = b;
                u = nd_a[a];
            }
            if c == 0 or nd_num[c] < 0 {
                rule_sqrt_product_square = 0;
            } else {
                mk_func K.Sqrt, c;
                local coef = mk_func;
                mk_func K.Abs, u;
                local ab = mk_func;
                mk_mul coef, ab;
                rule_sqrt_product_square = mk_mul;
            }
        }
    }
}

proc rule_ln_exp node {
    if $node != 0 and nd_kind[$node] == K.Ln and nd_kind[nd_a[$node]] == K.Exp {
        rule_ln_exp = nd_a[nd_a[$node]];
    } else {
        rule_ln_exp = 0;
    }
}

proc rule_exp_ln node {
    if $node != 0 and nd_kind[$node] == K.Exp and nd_kind[nd_a[$node]] == K.Ln {
        rule_exp_ln = nd_a[nd_a[$node]];
    } else {
        rule_exp_ln = 0;
    }
}

proc rule_abs_abs node {
    if $node != 0 and nd_kind[$node] == K.Abs and nd_kind[nd_a[$node]] == K.Abs {
        rule_abs_abs = nd_a[$node];
    } else {
        rule_abs_abs = 0;
    }
}

proc rules_try rid, node {
    local r = 0;
    if $rid == 1 {
        rule_sqrt_power $node;
        r = rule_sqrt_power;
    } elif $rid == 2 {
        rule_sqrt_square $node;
        r = rule_sqrt_square;
    } elif $rid == 3 {
        rule_ln_exp $node;
        r = rule_ln_exp;
    } elif $rid == 4 {
        rule_exp_ln $node;
        r = rule_exp_ln;
    } elif $rid == 5 {
        rule_abs_abs $node;
        r = rule_abs_abs;
    } elif $rid == 6 {
        rule_sqrt_neg_square $node;
        r = rule_sqrt_neg_square;
    } elif $rid == 7 {
        rule_sqrt_product_square $node;
        r = rule_sqrt_product_square;
    }
    rules_try = r;
}

proc rules_apply node {
    local r = 0;
    local rid = 1;
    until rid > 7 or r != 0 or err != "" {
        rules_try rid, $node;
        r = rules_try;
        rid++;
    }
    rules_apply = r;
}

proc rules_pass root {
    if $root == 0 or err != "" {
        rules_pass = 0;
    } else {
        delete rs_val;
        local i = 1;
        until i > node_count {
            add 0 to rs_val;
            i++;
        }
        delete rs_stk_node;
        delete rs_stk_state;
        rs_sp = 0;
        rs_push $root, 0;
        until rs_sp == 0 or err != "" {
            local n = rs_stk_node[rs_sp];
            local st = rs_stk_state[rs_sp];
            rs_sp--;
            if st == 0 {
                rs_push n, 1;
                if nd_kind[n] == K.Add or nd_kind[n] == K.Mul or nd_kind[n] == K.PowE {
                    rs_push nd_b[n], 0;
                    rs_push nd_a[n], 0;
                } elif nd_kind[n] == K.Pow {
                    rs_push nd_a[n], 0;
                } elif nd_kind[n] >= K.Sin and nd_kind[n] <= K.Atan {
                    rs_push nd_a[n], 0;
                } elif nd_kind[n] == K.Unknown {
                    rs_push nd_a[n], 0;
                }
            } else {
                local k = nd_kind[n];
                local r = n;
                if k == K.Add {
                    mk_add rs_val[nd_a[n]], rs_val[nd_b[n]];
                    r = mk_add;
                } elif k == K.Mul {
                    mk_mul rs_val[nd_a[n]], rs_val[nd_b[n]];
                    r = mk_mul;
                } elif k == K.Pow {
                    mk_pow rs_val[nd_a[n]], nd_num[n];
                    r = mk_pow;
                } elif k == K.PowE {
                    mk_pow_expr rs_val[nd_a[n]], rs_val[nd_b[n]];
                    r = mk_pow_expr;
                } elif k == K.Num or k == K.Var or k == K.Pi or k == K.E or k == K.Float or k == K.UN or k == K.Inf or k == K.Big or k == K.Vec or k == K.List or k == K.BigFloat {
                    r = n;
                } elif k == K.Unknown {
                    mk_genfunc nd_txt[n], rs_val[nd_a[n]];
                    r = mk_genfunc;
                } else {
                    mk_func k, rs_val[nd_a[n]];
                    r = mk_func;
                }
                if err == "" and r != 0 {
                    rules_apply r;
                    local rep = rules_apply;
                    if rep != 0 and nd_sig[rep] != nd_sig[r] {
                        r = rep;
                        rs_changed = true;
                    }
                }
                if err == "" and r != 0 {
                    rs_val[n] = r;
                }
            }
        }
        if err != "" {
            rules_pass = 0;
        } else {
            rules_pass = rs_val[$root];
        }
    }
}

proc rules_simplify root {
    local cur = $root;
    local rounds = 0;
    local did = true;
    until did == false or rounds >= 8 or err != "" {
        rs_changed = false;
        rules_pass cur;
        local next = rules_pass;
        did = rs_changed;
        cur = next;
        rounds++;
    }
    if err == "" {
        trig_simplify cur;
        if err == "" { cur = trig_simplify; }
    }
    if err != "" {
        rules_simplify = 0;
    } else {
        rules_simplify = cur;
    }
}
