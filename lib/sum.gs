# Numeric summation and product over a container or an integer range.

list sum_stk;
var sum_acc = 0;

proc sum_flatten c {
    delete sum_stk;
    local sp = 0;
    sp++; add $c to sum_stk;
    until sp == 0 {
        local x = sum_stk[sp];
        sp--;
        if is_container(x) {
            local i = 1;
            until i > nd_den[x] {
                sp++;
                if sp > length(sum_stk) { add ct_elems[nd_num[x] + i - 1] to sum_stk; }
                else { sum_stk[sp] = ct_elems[nd_num[x] + i - 1]; }
                i++;
            }
        } else {
            if sum_acc == 0 { sum_acc = x; }
            else {
                mk_add sum_acc, x;
                sum_acc = mk_add;
            }
        }
    }
}

proc cont_sum c {
    sum_acc = 0;
    sum_flatten $c;
    if sum_acc == 0 {
        mk_num 0, 1;
        cont_sum = mk_num;
    } else {
        rules_simplify sum_acc;
        if err == "" { cont_sum = rules_simplify; } else { cont_sum = 0; }
    }
}

proc prod_flatten c {
    delete sum_stk;
    local sp = 0;
    sp++; add $c to sum_stk;
    until sp == 0 {
        local x = sum_stk[sp];
        sp--;
        if is_container(x) {
            local i = 1;
            until i > nd_den[x] {
                sp++;
                if sp > length(sum_stk) { add ct_elems[nd_num[x] + i - 1] to sum_stk; }
                else { sum_stk[sp] = ct_elems[nd_num[x] + i - 1]; }
                i++;
            }
        } else {
            if sum_acc == 1 { sum_acc = x; }
            else {
                mk_mul sum_acc, x;
                sum_acc = mk_mul;
            }
        }
    }
}

proc cont_prod c {
    mk_num 1, 1;
    sum_acc = mk_num;
    prod_flatten $c;
    rules_simplify sum_acc;
    if err == "" { cont_prod = rules_simplify; } else { cont_prod = 0; }
}

proc sum_range expr, vnode, bnode, enode, is_prod {
    sum_range = 0;
    if nd_kind[$vnode] != K.Var or nd_kind[$bnode] != K.Num or nd_kind[$enode] != K.Num or nd_den[$bnode] != 1 or nd_den[$enode] != 1 {
        set_err "sum 范围必须是整数";
    } else {
        local vn = nd_txt[$vnode];
        local b = nd_num[$bnode];
        local e = nd_num[$enode];
        local step = 1;
        if b > e { step = -1; }
        if abs(e - b) > 10000 {
            set_err "sum 范围过大";
        } else {
            mk_num 0, 1;
            local acc = mk_num;
            if $is_prod == 1 {
                mk_num 1, 1;
                acc = mk_num;
            }
            local k = b;
            local guard = 0;
            until (step > 0 and k > e) or (step < 0 and k < e) or err != "" or guard > 10001 {
                subst_clear;
                mk_num k, 1;
                subst_add vn, mk_num;
                subst_expr $expr;
                local val = subst_expr;
                if err == "" {
                    rules_simplify val;
                    if err == "" { val = rules_simplify; }
                }
                if err == "" {
                    exact_fold val;
                    if err == "" { val = exact_fold; }
                }
                if err == "" {
                    if $is_prod == 1 {
                        mk_mul acc, val;
                        acc = mk_mul;
                    } else {
                        mk_add acc, val;
                        acc = mk_add;
                    }
                }
                k += step;
                guard++;
            }
            if err == "" {
                rules_simplify acc;
                if err == "" { sum_range = rules_simplify; }
            }
        }
    }
}
