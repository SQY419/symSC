list ex_done;
list ex_val;
list ex_stk_node;
list ex_stk_state;
var ex_sp = 0;

list ex_ta;
list ex_tb;
list ex_stk2;
var ex_sp2 = 0;

list ex_pow_terms;
list ex_pow_stk;
var ex_pow_sp = 0;
var ex_bin_ok = false;

proc ex_push id, state {
    ex_sp++;
    if ex_sp > length(ex_stk_node) {
        add $id to ex_stk_node;
        add $state to ex_stk_state;
    } else {
        ex_stk_node[ex_sp] = $id;
        ex_stk_state[ex_sp] = $state;
    }
}

proc ex_push2 id {
    ex_sp2++;
    if ex_sp2 > length(ex_stk2) {
        add $id to ex_stk2;
    } else {
        ex_stk2[ex_sp2] = $id;
    }
}

proc collect_a root {
    delete ex_ta;
    delete ex_stk2;
    ex_sp2 = 0;
    ex_push2 $root;
    until ex_sp2 == 0 {
        local x = ex_stk2[ex_sp2];
        ex_sp2--;
        if nd_kind[x] == K.Add {
            ex_push2 nd_b[x];
            ex_push2 nd_a[x];
        } else {
            add x to ex_ta;
        }
    }
}

proc collect_b root {
    delete ex_tb;
    delete ex_stk2;
    ex_sp2 = 0;
    ex_push2 $root;
    until ex_sp2 == 0 {
        local x = ex_stk2[ex_sp2];
        ex_sp2--;
        if nd_kind[x] == K.Add {
            ex_push2 nd_b[x];
            ex_push2 nd_a[x];
        } else {
            add x to ex_tb;
        }
    }
}

proc expand_mul a, b {
    if $a == 0 or $b == 0 or err != "" {
        expand_mul = 0;
    } else {
        delete ex_ta;
        delete ex_tb;
        if nd_kind[$a] == K.Add {
            collect_a $a;
        } else {
            add $a to ex_ta;
        }
        if nd_kind[$b] == K.Add {
            collect_b $b;
        } else {
            add $b to ex_tb;
        }
        local na = length(ex_ta);
        local nb = length(ex_tb);
        if na * nb > MAX_TERMS {
            set_err "展开项过多";
            expand_mul = 0;
        } else {
            local acc = 0;
            local i = 1;
            until i > na or err != "" {
                local j = 1;
                until j > nb or err != "" {
                    mk_mul ex_ta[i], ex_tb[j];
                    local p = mk_mul;
                    if acc == 0 {
                        acc = p;
                    } else {
                        mk_add acc, p;
                        acc = mk_add;
                    }
                    j++;
                }
                i++;
            }
            expand_mul = acc;
        }
    }
}

proc ex_pow_push id {
    ex_pow_sp++;
    if ex_pow_sp > length(ex_pow_stk) {
        add $id to ex_pow_stk;
    } else {
        ex_pow_stk[ex_pow_sp] = $id;
    }
}

proc collect_pow_terms root {
    delete ex_pow_terms;
    delete ex_pow_stk;
    ex_pow_sp = 0;
    ex_pow_push $root;
    until ex_pow_sp == 0 {
        local x = ex_pow_stk[ex_pow_sp];
        ex_pow_sp--;
        if nd_kind[x] == K.Add {
            ex_pow_push nd_b[x];
            ex_pow_push nd_a[x];
        } else {
            add x to ex_pow_terms;
        }
    }
}

proc expand_binomial a, b, n {
    ex_bin_ok = false;
    if $n < 0 or $n > MAX_EXP or $n + 1 > MAX_TERMS {
        expand_binomial = 0;
    } else {
        local sum = 0;
        local c = 1;
        local k = 0;
        local ok = true;
        until k > $n or ok == false or err != "" {
            mk_pow $a, $n - k;
            local pa = mk_pow;
            mk_pow $b, k;
            local pb = mk_pow;
            mk_mul pa, pb;
            local term = mk_mul;
            if c != 1 {
                mk_num c, 1;
                local cn = mk_num;
                mk_mul cn, term;
                term = mk_mul;
            }
            if sum == 0 {
                sum = term;
            } else {
                mk_add sum, term;
                sum = mk_add;
            }
            if k < $n {
                local num = c * ($n - k);
                local den = k + 1;
                if abs(num) > MAX_SAFE {
                    ok = false;
                } else {
                    local nextc = num / den;
                    if nextc != round(nextc) or abs(nextc) > MAX_SAFE {
                        ok = false;
                    } else {
                        c = round(nextc);
                    }
                }
            }
            k++;
        }
        if ok and err == "" {
            ex_bin_ok = true;
            expand_binomial = sum;
        } else {
            expand_binomial = 0;
        }
    }
}

proc expand_pow base, e {
    if $base == 0 or err != "" {
        expand_pow = 0;
    } elif $e <= 0 {
        mk_pow $base, $e;
        expand_pow = mk_pow;
    } elif nd_kind[$base] != K.Add {
        mk_pow $base, $e;
        expand_pow = mk_pow;
    } else {
        collect_pow_terms $base;
        local bin = 0;
        if length(ex_pow_terms) == 2 and $e > 1 {
            expand_binomial ex_pow_terms[1], ex_pow_terms[2], $e;
            if ex_bin_ok {
                bin = expand_binomial;
            }
        }
        if bin != 0 {
            expand_pow = bin;
        } else {
            local acc = 1;
            mk_num 1, 1;
            acc = mk_num;
            local i = 1;
            until i > $e or err != "" {
                expand_mul acc, $base;
                acc = expand_mul;
                i++;
            }
            expand_pow = acc;
        }
    }
}

proc expand_expr root {
    if $root == 0 or err != "" {
        expand_expr = 0;
    } else {
        delete ex_done;
        delete ex_val;
        local i = 1;
        until i > node_count {
            add 0 to ex_done;
            add 0 to ex_val;
            i++;
        }
        delete ex_stk_node;
        delete ex_stk_state;
        ex_sp = 0;
        ex_push $root, 0;
        until ex_sp == 0 or err != "" {
            local n = ex_stk_node[ex_sp];
            local st = ex_stk_state[ex_sp];
            ex_sp--;
            if st == 0 {
                if ex_done[n] == 0 {
                    ex_push n, 1;
                    if nd_kind[n] == K.Add or nd_kind[n] == K.Mul {
                        ex_push nd_b[n], 0;
                        ex_push nd_a[n], 0;
                    } elif nd_kind[n] == K.Pow {
                        ex_push nd_a[n], 0;
                    } elif nd_kind[n] == K.PowE {
                        ex_push nd_b[n], 0;
                        ex_push nd_a[n], 0;
                    } elif nd_kind[n] >= K.Sin and nd_kind[n] <= K.Atan {
                        ex_push nd_a[n], 0;
                    } elif nd_kind[n] == K.Unknown {
                        ex_push nd_a[n], 0;
                    }
                }
            } else {
                if ex_done[n] == 0 {
                    local k = nd_kind[n];
                    local d = 0;
                    if k == K.Num or k == K.Var or k == K.Pi or k == K.E or k == K.Float or k == K.UN or k == K.Inf {
                        d = n;
                    } elif k == K.Unknown {
                        mk_genfunc nd_txt[n], ex_val[nd_a[n]];
                        d = mk_genfunc;
                    } elif k == K.Add {
                        mk_add ex_val[nd_a[n]], ex_val[nd_b[n]];
                        d = mk_add;
                    } elif k == K.Mul {
                        expand_mul ex_val[nd_a[n]], ex_val[nd_b[n]];
                        d = expand_mul;
                    } elif k == K.Pow {
                        expand_pow ex_val[nd_a[n]], nd_num[n];
                        d = expand_pow;
                    } elif k == K.PowE {
                        mk_pow_expr ex_val[nd_a[n]], ex_val[nd_b[n]];
                        d = mk_pow_expr;
                    } else {
                        mk_func k, ex_val[nd_a[n]];
                        d = mk_func;
                    }
                    if d != 0 {
                        ex_val[n] = d;
                    }
                    ex_done[n] = 1;
                }
            }
        }
        if err != "" {
            expand_expr = 0;
        } else {
            expand_expr = ex_val[$root];
        }
    }
}
