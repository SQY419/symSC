# Taylor series and limits.

func series_find_eq(s) {
    local i = 1;
    until i > length($s) or $s[i] == "=" {
        i++;
    }
    return i;
}

proc series_eval_node expr, vname, point {
    subst_clear;
    subst_add $vname, $point;
    subst_expr $expr;
    if err != "" { series_eval_node = 0; } else {
        rules_simplify subst_expr;
        if err != "" { series_eval_node = 0; } else { series_eval_node = rules_simplify; }
    }
}

proc series_eval_value expr, vname, point {
    subst_clear;
    subst_add $vname, $point;
    subst_expr $expr;
    if err != "" {
        series_eval_value = 0;
    } else {
        rules_simplify subst_expr;
        if err != "" { series_eval_value = 0; } else {
            exact_fold rules_simplify;
            if err != "" { series_eval_value = 0; } else { series_eval_value = exact_fold; }
        }
    }
}


proc series_build expr, vname, point, order {
    local f = $expr;
    mk_var $vname;
    local tv = mk_var;
    mk_num -1, 1;
    mk_mul mk_num, $point;
    mk_add tv, mk_mul;
    local t = mk_add;
    # Keep a real Num 0 node as the zero term.  Using the null handle 0 here
    # made a zero Taylor series indistinguishable from a failed construction.
    mk_num 0, 1;
    local sum = mk_num;
    local fact = 1;
    local k = 0;
    until k > $order or err != "" {
        if k > 0 {
            diff_expr f, $vname;
            if err != "" { k = $order + 1; } else {
                rules_simplify diff_expr;
                f = rules_simplify;
            }
        }
        if err == "" {
            series_eval_value f, $vname, $point;
            local c = series_eval_value;
            if err == "" and c != 0 {
                local cf = c;
                if nd_kind[c] == K.Num and nd_num[c] == 0 { cf = 0; }
                if cf != 0 and fact != 1 {
                    mk_num fact, 1;
                    mk_pow mk_num, -1;
                    mk_mul c, mk_pow;
                    cf = mk_mul;
                }
                if cf != 0 {
                    local term = cf;
                    if k > 0 {
                        mk_pow t, k;
                        mk_mul cf, mk_pow;
                        term = mk_mul;
                    }
                    if sum == 0 { sum = term; } else { mk_add sum, term; sum = mk_add; }
                }
            }

        }
        if k < $order { fact *= (k + 1); }
        k++;
    }
    if err == "" { rules_simplify sum; series_build = rules_simplify; } else { series_build = 0; }
}

proc series_dispatch expr, vname, point, order {
    if nd_kind[$point] == K.Inf {
        series_inf $expr, $vname, $order;
        series_dispatch = series_inf;
    } else {
        series_build $expr, $vname, $point, $order;
        series_dispatch = series_build;
    }
}

proc series_split_quotient root {
    delete lim_num_facs;
    delete lim_den_facs;
    delete lim_stk;
    local sp = 0;
    sp++;
    add $root to lim_stk;
    until sp == 0 {
        local x = lim_stk[sp];
        sp--;
        if nd_kind[x] == K.Mul {
            sp++;
            if sp > length(lim_stk) { add nd_b[x] to lim_stk; } else { lim_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(lim_stk) { add nd_a[x] to lim_stk; } else { lim_stk[sp] = nd_a[x]; }
        } elif nd_kind[x] == K.Pow and nd_num[x] < 0 {
            mk_pow nd_a[x], -nd_num[x];
            add mk_pow to lim_den_facs;
        } else {
            add x to lim_num_facs;
        }
    }
}

list lim_num_facs;
list lim_den_facs;
list lim_stk;

proc series_build_product faclist, fallback {
    if length($faclist) == 0 {
        mk_num 1, 1;
        series_build_product = mk_num;
    } else {
        local out = $faclist[1];
        local i = 2;
        until i > length($faclist) {
            mk_mul out, $faclist[i];
            out = mk_mul;
            i++;
        }
        series_build_product = out;
    }
}

func series_has_exp(root) {
    delete ser_scan;
    local found = false;
    local sp = 0;
    sp++; add $root to ser_scan;
    until sp == 0 {
        local x = ser_scan[sp];
        sp--;
        if nd_kind[x] == K.Exp or (nd_kind[x] == K.PowE and nd_kind[nd_a[x]] == K.E) {
            found = true;
            sp = 0;
        } elif nd_kind[x] == K.Add or nd_kind[x] == K.Mul or nd_kind[x] == K.PowE {
            sp++;
            if sp > length(ser_scan) { add nd_b[x] to ser_scan; } else { ser_scan[sp] = nd_b[x]; }
            sp++;
            if sp > length(ser_scan) { add nd_a[x] to ser_scan; } else { ser_scan[sp] = nd_a[x]; }
        } elif nd_kind[x] == K.Pow or (nd_kind[x] >= K.Sin and nd_kind[x] <= K.Atan) or nd_kind[x] == K.Unknown {
            sp++;
            if sp > length(ser_scan) { add nd_a[x] to ser_scan; } else { ser_scan[sp] = nd_a[x]; }
        }
    }
    return found;
}

list ser_scan;

list se_val;
list se_stk_node;
list se_stk_state;
var se_sp = 0;
var se_coef = 0;
var se_ok = false;

func se_linear(ex, vname) {
    se_ok = false;
    se_coef = 0;
    if nd_kind[$ex] == K.Var and nd_txt[$ex] == $vname {
        se_ok = true;
        se_coef = 1;
    } elif nd_kind[$ex] == K.Mul {
        local a = nd_a[$ex];
        local b = nd_b[$ex];
        if nd_kind[a] == K.Num and nd_kind[b] == K.Var and nd_txt[b] == $vname {
            se_ok = true;
            se_coef = nd_num[a] / nd_den[a];
        } elif nd_kind[b] == K.Num and nd_kind[a] == K.Var and nd_txt[a] == $vname {
            se_ok = true;
            se_coef = nd_num[b] / nd_den[b];
        }
    }
}

proc se_rebuild n, tv, vname {
    local k = nd_kind[$n];
    if k == K.Add {
        mk_add se_val[nd_a[$n]], se_val[nd_b[$n]];
        se_rebuild = mk_add;
    } elif k == K.Mul {
        mk_mul se_val[nd_a[$n]], se_val[nd_b[$n]];
        se_rebuild = mk_mul;
    } elif k == K.Pow {
        mk_pow se_val[nd_a[$n]], nd_num[$n];
        se_rebuild = mk_pow;
    } elif k == K.PowE {
        local e = nd_b[$n];
        local lc = se_linear(e, $vname);
        if nd_kind[nd_a[$n]] == K.E and se_ok {
            mk_pow $tv, 0 - se_coef;
            se_rebuild = mk_pow;
        } else {
            mk_pow_expr se_val[nd_a[$n]], se_val[e];
            se_rebuild = mk_pow_expr;
        }
    } elif k == K.Exp {
        local lc2 = se_linear(nd_a[$n], $vname);
        if se_ok {
            mk_pow $tv, 0 - se_coef;
            se_rebuild = mk_pow;
        } else {
            mk_func K.Exp, se_val[nd_a[$n]];
            se_rebuild = mk_func;
        }
    } elif k >= K.Sin and k <= K.Atan {
        mk_func k, se_val[nd_a[$n]];
        se_rebuild = mk_func;
    } elif k == K.Unknown {
        mk_genfunc nd_txt[$n], se_val[nd_a[$n]];
        se_rebuild = mk_genfunc;
    } else {
        se_rebuild = $n;
    }
}

proc series_exp_rewrite root, tv, vname {
    series_exp_rewrite = $root;
    if $root == 0 or err != "" { series_exp_rewrite = 0; } else {
        delete se_val;
        local i = 1;
        until i > node_count { add 0 to se_val; i++; }
        delete se_stk_node;
        delete se_stk_state;
        se_sp = 0;
        se_sp++; add $root to se_stk_node; add 0 to se_stk_state;
        until se_sp == 0 or err != "" {
            local n = se_stk_node[se_sp];
            local st = se_stk_state[se_sp];
            se_sp--;
            if st == 0 {
                se_sp++;
                if se_sp > length(se_stk_node) { add n to se_stk_node; add 1 to se_stk_state; }
                else { se_stk_node[se_sp] = n; se_stk_state[se_sp] = 1; }
                local k = nd_kind[n];
                if k == K.Add or k == K.Mul or k == K.PowE {
                    se_sp++;
                    if se_sp > length(se_stk_node) { add nd_b[n] to se_stk_node; add 0 to se_stk_state; }
                    else { se_stk_node[se_sp] = nd_b[n]; se_stk_state[se_sp] = 0; }
                    se_sp++;
                    if se_sp > length(se_stk_node) { add nd_a[n] to se_stk_node; add 0 to se_stk_state; }
                    else { se_stk_node[se_sp] = nd_a[n]; se_stk_state[se_sp] = 0; }
                } elif k == K.Pow or k == K.Exp or (k >= K.Sin and k <= K.Atan) or k == K.Unknown {
                    se_sp++;
                    if se_sp > length(se_stk_node) { add nd_a[n] to se_stk_node; add 0 to se_stk_state; }
                    else { se_stk_node[se_sp] = nd_a[n]; se_stk_state[se_sp] = 0; }
                }
            } else {
                se_rebuild n, $tv, $vname;
                if err == "" { se_val[n] = se_rebuild; }
            }
        }
        if err != "" { series_exp_rewrite = 0; } else { series_exp_rewrite = se_val[$root]; }
    }
}

proc series_inf expr, vname, order {
    series_inf = 0;
    local use_exp = series_has_exp($expr);
    mk_var "__tser";
    local tv = mk_var;
    mk_num 0, 1;
    local z = mk_num;
    if use_exp {
        series_exp_rewrite $expr, tv, $vname;
        if err != "" or series_exp_rewrite == 0 { series_inf = 0; } else {
            rules_simplify series_exp_rewrite;
            if err != "" { series_inf = 0; } else {
                series_build rules_simplify, "__tser", z, $order;
                if err != "" or series_build == 0 { series_inf = 0; } else {
                    mk_var $vname;
                    local xv = mk_var;
                    mk_neg xv;
                    local nx = mk_neg;
                    mk_var "e";
                    local ev = mk_var;
                    mk_pow_expr ev, nx;
                    local tb = mk_pow_expr;
                    subst_clear;
                    subst_add "__tser", tb;
                    subst_expr series_build;
                    if err == "" {
                        rules_simplify subst_expr;
                        if err == "" { series_inf = rules_simplify; }
                    }
                }
            }
        }
    } else {
        mk_pow tv, -1;
        subst_clear;
        subst_add $vname, mk_pow;
        subst_expr $expr;
        if err != "" { series_inf = 0; } else {
            rules_simplify subst_expr;
            if err != "" { series_inf = 0; } else {
                series_build rules_simplify, "__tser", z, $order;
                if err != "" or series_build == 0 { series_inf = 0; } else {
                    mk_var $vname;
                    mk_pow mk_var, -1;
                    local tb = mk_pow;
                    subst_clear;
                    subst_add "__tser", tb;
                    subst_expr series_build;
                    if err == "" {
                        rules_simplify subst_expr;
                        if err == "" { series_inf = rules_simplify; }
                    }
                }
            }
        }
    }
}

proc limit_eval expr, vname, point {
    subst_clear;
    subst_add $vname, $point;
    subst_expr $expr;
    if err != "" {
        limit_eval = 0;
    } else {
        rules_simplify subst_expr;
        if err != "" { limit_eval = 0; } else {
            exact_fold rules_simplify;
            if err != "" { limit_eval = 0; } else { limit_eval = exact_fold; }
        }
    }
}


func lim_zero(n) {
    return nd_kind[$n] == K.Num and nd_num[$n] == 0;
}

proc series_build_lim_num {
    if length(lim_num_facs) == 0 {
        mk_num 1, 1;
        series_build_lim_num = mk_num;
    } else {
        local out = lim_num_facs[1];
        local i = 2;
        until i > length(lim_num_facs) {
            mk_mul out, lim_num_facs[i];
            out = mk_mul;
            i++;
        }
        series_build_lim_num = out;
    }
}

proc series_build_lim_den {
    if length(lim_den_facs) == 0 {
        mk_num 1, 1;
        series_build_lim_den = mk_num;
    } else {
        local out = lim_den_facs[1];
        local i = 2;
        until i > length(lim_den_facs) {
            mk_mul out, lim_den_facs[i];
            out = mk_mul;
            i++;
        }
        series_build_lim_den = out;
    }
}

proc limit_series_ratio num, den, vname, point {
    local f = $num;
    local g = $den;
    local k = 0;
    lim_ok = false;
    until k > 10 or lim_ok or err != "" {
        limit_eval f, $vname, $point;
        local nv = limit_eval;
        local ne = err;
        limit_eval g, $vname, $point;
        local dv = limit_eval;
        local de = err;
        if ne != "" or de != "" {
            k = 11;
        } elif lim_zero(nv) and lim_zero(dv) {
            diff_expr f, $vname;
            if err == "" { rules_simplify diff_expr; f = rules_simplify; }
            diff_expr g, $vname;
            if err == "" { rules_simplify diff_expr; g = rules_simplify; }
            k++;
        } elif lim_zero(nv) {
            lim_ok = true;
            mk_num 0, 1;
            limit_series_ratio = mk_num;
        } elif lim_zero(dv) {
            lim_ok = false;
            k = 11;
        } else {
            mk_pow dv, -1;
            mk_mul nv, mk_pow;
            rules_simplify mk_mul;
            if err == "" {
                lim_ok = true;
                limit_series_ratio = rules_simplify;
            } else { k = 11; }
        }
    }
}

proc limit_expr expr, vname, point {
    limit_ok = false;
    series_split_quotient $expr;
    if length(lim_den_facs) == 0 {
        limit_eval $expr, $vname, $point;
        if err != "" { set_err "极限无法直接求值"; limit_expr = 0; } else { limit_expr = limit_eval; limit_ok = true; }
    } else {
        series_build_lim_num;
        local num = series_build_lim_num;
        series_build_lim_den;
        local den = series_build_lim_den;
        local onum = num;
        local oden = den;
        limit_series_ratio onum, oden, $vname, $point;
        local k = 0;
        local done = false;
        if lim_ok {
            limit_expr = limit_series_ratio;
            limit_ok = true;
            done = true;
        } else {
            err = "";
        }
        until k > 6 or done or err != "" {
            limit_eval num, $vname, $point;
            local nv = limit_eval;
            local ne = err;
            limit_eval den, $vname, $point;
            local dv = limit_eval;
            local de = err;
            if ne != "" or de != "" {
                set_err "极限无法求值";
                k = 7;
            } elif lim_zero(dv) {
                if lim_zero(nv) {
                    diff_expr num, $vname; rules_simplify diff_expr; num = rules_simplify;
                    diff_expr den, $vname; rules_simplify diff_expr; den = rules_simplify;
                    k++;
                } else {
                    set_err "极限不存在（趋于无穷）";
                    k = 7;
                }
            } elif lim_zero(nv) {
                mk_num 0, 1;
                limit_expr = mk_num;
                limit_ok = true;
                done = true;
            } else {
                mk_pow dv, -1;
                mk_mul nv, mk_pow;
                rules_simplify mk_mul;
                if err == "" {
                    limit_expr = rules_simplify;
                    limit_ok = true;
                    done = true;
                }
            }
        }
        if done == false {
            err = "";
            limit_series_ratio onum, oden, $vname, $point;
            if lim_ok {
                limit_expr = limit_series_ratio;
                limit_ok = true;
            } else {
                set_err "极限无法确定";
                limit_expr = 0;
            }
        }
    }
}

proc limit_inf_expr expr, vname {
    limit_inf_expr = 0;
    limit_inf_lead $expr, $vname;
    if li_ok {
        limit_inf_expr = li_result;
        li_ok = false;
    }
    if limit_inf_expr == 0 and nd_kind[$expr] == K.PowE {
        local base = nd_b[$expr];
        local ex = nd_a[$expr];
        local ok = false;
        if nd_kind[ex] == K.Var and nd_txt[ex] == $vname {
            local one = 0;
            local term = 0;
            if nd_kind[base] == K.Add {
                if nd_kind[nd_a[base]] == K.Num and nd_num[nd_a[base]] == 1 {
                    one = nd_a[base];
                    term = nd_b[base];
                } elif nd_kind[nd_b[base]] == K.Num and nd_num[nd_b[base]] == 1 {
                    one = nd_b[base];
                    term = nd_a[base];
                }
            }
            if one != 0 {
                local c = 0;
                if nd_kind[term] == K.Pow and nd_kind[nd_a[term]] == K.Var and nd_txt[nd_a[term]] == $vname and nd_num[term] == -1 {
                    mk_num 1, 1;
                    c = mk_num;
                } elif nd_kind[term] == K.Mul {
                    local f1 = nd_a[term];
                    local f2 = nd_b[term];
                    if nd_kind[f1] == K.Pow and nd_kind[nd_a[f1]] == K.Var and nd_txt[nd_a[f1]] == $vname and nd_num[f1] == -1 {
                        c = f2;
                    } elif nd_kind[f2] == K.Pow and nd_kind[nd_a[f2]] == K.Var and nd_txt[nd_a[f2]] == $vname and nd_num[f2] == -1 {
                        c = f1;
                    }
                }
                if c != 0 {
                    mk_var "e";
                    mk_pow mk_var, c;
                    rules_simplify mk_pow;
                    limit_inf_expr = rules_simplify;
                }
            }
        }
    }
}
