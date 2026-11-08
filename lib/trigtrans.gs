# Trigonometric rewriting commands.

var tt_mode = 1;
var tt_ok = true;

proc tt_sin x { mk_func K.Sin, $x; tt_sin = mk_func; }
proc tt_cos x { mk_func K.Cos, $x; tt_cos = mk_func; }
proc tt_tan x { mk_func K.Tan, $x; tt_tan = mk_func; }

proc tt_neg x {
    mk_num -1, 1;
    mk_mul mk_num, $x;
    tt_neg = mk_mul;
}

proc tt_div a, b {
    mk_pow $b, -1;
    mk_mul $a, mk_pow;
    tt_div = mk_mul;
}

proc tt_half x {
    mk_num 1, 2;
    mk_mul mk_num, $x;
    tt_half = mk_mul;
}

proc tt_double x {
    mk_num 2, 1;
    mk_mul mk_num, $x;
    tt_double = mk_mul;
}

proc tt_texpand_trig kind, arg {
    tt_texpand_trig = 0;
    if nd_kind[$arg] == K.Add {
        local a = nd_a[$arg];
        local b = nd_b[$arg];
        if $kind == K.Sin {
            tt_sin a; local sa = tt_sin;
            tt_cos b; local cb = tt_cos;
            tt_cos a; local ca = tt_cos;
            tt_sin b; local sb = tt_sin;
            mk_mul sa, cb; local t1 = mk_mul;
            mk_mul ca, sb; local t2 = mk_mul;
            mk_add t1, t2; tt_texpand_trig = mk_add;
        } elif $kind == K.Cos {
            tt_cos a; local ca = tt_cos;
            tt_cos b; local cb = tt_cos;
            tt_sin a; local sa = tt_sin;
            tt_sin b; local sb = tt_sin;
            mk_mul ca, cb; local t1 = mk_mul;
            mk_mul sa, sb; local t2 = mk_mul;
            tt_neg t2; local n2 = tt_neg;
            mk_add t1, n2; tt_texpand_trig = mk_add;
        } elif $kind == K.Tan {
            tt_tan a; local ta = tt_tan;
            tt_tan b; local tb = tt_tan;
            mk_add ta, tb; local num = mk_add;
            mk_mul ta, tb; local prod = mk_mul;
            mk_num 1, 1;
            tt_neg prod; local np = tt_neg;
            mk_add mk_num, np; local den = mk_add;
            tt_div num, den; tt_texpand_trig = tt_div;
        }
    } elif nd_kind[$arg] == K.Mul {
        local a = nd_a[$arg];
        local b = nd_b[$arg];
        local n = 0;
        local u = 0;
        if nd_kind[a] == K.Num and nd_den[a] == 1 and (nd_num[a] == 2 or nd_num[a] == -2) {
            n = nd_num[a]; u = b;
        } elif nd_kind[b] == K.Num and nd_den[b] == 1 and (nd_num[b] == 2 or nd_num[b] == -2) {
            n = nd_num[b]; u = a;
        }
        if u != 0 {
            tt_sin u; local su = tt_sin;
            tt_cos u; local cu = tt_cos;
            if $kind == K.Sin {
                mk_mul su, cu; local p = mk_mul;
                if n < 0 { tt_neg p; tt_texpand_trig = tt_neg; }
                else { tt_double p; tt_texpand_trig = tt_double; }
            } elif $kind == K.Cos {
                mk_mul cu, cu; local c2 = mk_mul;
                mk_mul su, su; local s2 = mk_mul;
                tt_neg s2; local ns2 = tt_neg;
                mk_add c2, ns2; tt_texpand_trig = mk_add;
            } elif $kind == K.Tan {
                mk_mul su, cu; local p = mk_mul;
                if n < 0 { tt_neg p; tt_texpand_trig = tt_neg; }
                else { tt_double p; tt_texpand_trig = tt_double; }
            }
        }
    }
}

proc tt_linear_pow kind, arg {
    tt_linear_pow = 0;
    if $kind == K.Sin {
        tt_double $arg; local d2 = tt_double;
        tt_cos d2; local c2 = tt_cos;
        tt_neg c2; local n2 = tt_neg;
        mk_num 1, 1;
        mk_add mk_num, n2; local sm = mk_add;
        mk_num 1, 2;
        mk_mul mk_num, sm;
        tt_linear_pow = mk_mul;
    } elif $kind == K.Cos {
        tt_double $arg; local d2 = tt_double;
        tt_cos d2; local c2 = tt_cos;
        mk_num 1, 1;
        mk_add mk_num, c2; local sm = mk_add;
        mk_num 1, 2;
        mk_mul mk_num, sm;
        tt_linear_pow = mk_mul;
    }
}

list tt_facs;

proc tt_linear_mul n {
    delete tt_facs;
    local st = 0;
    delete tt_stk;
    st++; add $n to tt_stk;
    until st == 0 {
        local x = tt_stk[st];
        st--;
        if nd_kind[x] == K.Mul {
            st++;
            if st > length(tt_stk) { add nd_b[x] to tt_stk; } else { tt_stk[st] = nd_b[x]; }
            st++;
            if st > length(tt_stk) { add nd_a[x] to tt_stk; } else { tt_stk[st] = nd_a[x]; }
        } else {
            add x to tt_facs;
        }
    }
    local coeff = 1;
    local t1 = 0;
    local t2 = 0;
    local i = 1;
    until i > length(tt_facs) {
        local f = tt_facs[i];
        if nd_kind[f] == K.Num {
            coeff *= nd_num[f] / nd_den[f];
        } elif nd_kind[f] == K.Sin or nd_kind[f] == K.Cos {
            if t1 == 0 { t1 = f; } elif t2 == 0 { t2 = f; }
            else { t2 = -1; }
        } else {
            t2 = -1;
        }
        i++;
    }
    if t1 == 0 or t2 == 0 or t2 == -1 {
        tt_linear_mul = $n;
    } else {
        local a1 = nd_a[t1];
        local a2 = nd_a[t2];
        local k1 = nd_kind[t1];
        local k2 = nd_kind[t2];
        local res = 0;
        if k1 == K.Sin and k2 == K.Sin {
            tt_neg a2; local na2 = tt_neg;
            mk_add a1, na2; local d = mk_add;
            mk_add a1, a2; local s = mk_add;
            tt_cos d; local cd = tt_cos;
            tt_cos s; local cs = tt_cos;
            tt_neg cs; local ncs = tt_neg;
            mk_add cd, ncs;
            mk_num 1, 2;
            mk_mul mk_num, mk_add;
            res = mk_mul;
        } elif k1 == K.Cos and k2 == K.Cos {
            tt_neg a2; local na2 = tt_neg;
            mk_add a1, na2; local d = mk_add;
            mk_add a1, a2; local s = mk_add;
            tt_cos d; local cd = tt_cos;
            tt_cos s; local cs = tt_cos;
            mk_add cd, cs;
            mk_num 1, 2;
            mk_mul mk_num, mk_add;
            res = mk_mul;
        } else {
            mk_add a1, a2; local s = mk_add;
            tt_neg a2; local na2 = tt_neg;
            mk_add a1, na2; local d = mk_add;
            tt_sin s; local ss = tt_sin;
            tt_sin d; local sd = tt_sin;
            mk_add ss, sd;
            mk_num 1, 2;
            mk_mul mk_num, mk_add;
            res = mk_mul;
        }
        if coeff != 1 {
            mk_num coeff, 1;
            mk_mul mk_num, res;
            res = mk_mul;
        }
        tt_linear_mul = res;
    }
}

list tt_stk;

proc tt_one_minus_sq f {
    mk_pow $f, 2; local sq = mk_pow;
    tt_neg sq; local nsq = tt_neg;
    mk_num 1, 1;
    mk_add mk_num, nsq;
    tt_one_minus_sq = mk_add;
}

proc tt_rewrite_pow kind, arg, mode {
    tt_rewrite_pow = 0;
    local t = 0;
    if $mode == 7 {
        if $kind == K.Sin {
            tt_cos $arg; local c = tt_cos;
            tt_one_minus_sq c;
            tt_rewrite_pow = tt_one_minus_sq;
        } elif $kind == K.Tan {
            tt_cos $arg; local c = tt_cos;
            mk_pow c, 2; local c2 = mk_pow;
            tt_one_minus_sq c; local num = tt_one_minus_sq;
            tt_div num, c2;
            tt_rewrite_pow = tt_div;
        }
    } elif $mode == 8 {
        if $kind == K.Cos {
            tt_sin $arg; local s = tt_sin;
            tt_one_minus_sq s;
            tt_rewrite_pow = tt_one_minus_sq;
        } elif $kind == K.Tan {
            tt_sin $arg; local s = tt_sin;
            mk_pow s, 2; local s2 = mk_pow;
            tt_one_minus_sq s; local den = tt_one_minus_sq;
            tt_div s2, den;
            tt_rewrite_pow = tt_div;
        }
    } elif $mode == 9 {
        if $kind == K.Sin {
            tt_tan $arg; local t1 = tt_tan;
            mk_pow t1, 2; local t2 = mk_pow;
            mk_num 1, 1; mk_add mk_num, t2; local den = mk_add;
            tt_div t2, den;
            tt_rewrite_pow = tt_div;
        } elif $kind == K.Cos {
            tt_tan $arg; local t1 = tt_tan;
            mk_pow t1, 2; local t2 = mk_pow;
            mk_num 1, 1; mk_add mk_num, t2; local den = mk_add;
            mk_num 1, 1; tt_div mk_num, den;
            tt_rewrite_pow = tt_div;
        }
    }
}

var ttc_kind = 0;
var ttc_arg = 0;
var ttc_coeff = 0;

proc tt_term_parts term {
    ttc_kind = 0;
    ttc_arg = 0;
    ttc_coeff = 0;
    local k = nd_kind[$term];
    if k == K.Sin or k == K.Cos {
        ttc_kind = k;
        ttc_arg = nd_a[$term];
        mk_num 1, 1;
        ttc_coeff = mk_num;
    } elif k == K.Mul {
        delete ttc_facs;
        delete ttc_stk;
        local sp = 0;
        sp++; add $term to ttc_stk;
        until sp == 0 {
            local x = ttc_stk[sp];
            sp--;
            if nd_kind[x] == K.Mul {
                sp++;
                if sp > length(ttc_stk) { add nd_b[x] to ttc_stk; } else { ttc_stk[sp] = nd_b[x]; }
                sp++;
                if sp > length(ttc_stk) { add nd_a[x] to ttc_stk; } else { ttc_stk[sp] = nd_a[x]; }
            } else { add x to ttc_facs; }
        }
        local tf = 0;
        local cfs = 0;
        local i = 1;
        until i > length(ttc_facs) {
            local f = ttc_facs[i];
            if (nd_kind[f] == K.Sin or nd_kind[f] == K.Cos) and tf == 0 {
                tf = f;
            } elif nd_kind[f] == K.Sin or nd_kind[f] == K.Cos {
                tf = -1;
            } else {
                if cfs == 0 { cfs = f; } else { mk_mul cfs, f; cfs = mk_mul; }
            }
            i++;
        }
        if tf > 0 {
            ttc_kind = nd_kind[tf];
            ttc_arg = nd_a[tf];
            if cfs == 0 { mk_num 1, 1; cfs = mk_num; }
            ttc_coeff = cfs;
        }
    }
}

proc tt_collect_add n {
    if nd_kind[$n] != K.Add {
        tt_collect_add = $n;
    } else {
        delete tt_aterms;
        delete tt_astk;
        local sp = 0;
        sp++; add $n to tt_astk;
        until sp == 0 {
            local x = tt_astk[sp];
            sp--;
            if nd_kind[x] == K.Add {
                sp++;
                if sp > length(tt_astk) { add nd_b[x] to tt_astk; } else { tt_astk[sp] = nd_b[x]; }
                sp++;
                if sp > length(tt_astk) { add nd_a[x] to tt_astk; } else { tt_astk[sp] = nd_a[x]; }
            } else { add x to tt_aterms; }
        }
        if length(tt_aterms) != 2 {
            tt_collect_add = $n;
        } else {
            tt_term_parts tt_aterms[1];
            local k1 = ttc_kind; local a1 = ttc_arg; local c1 = ttc_coeff;
            tt_term_parts tt_aterms[2];
            local k2 = ttc_kind; local a2 = ttc_arg; local c2 = ttc_coeff;
            if k1 == 0 or k2 == 0 or nd_sig[a1] != nd_sig[a2] or (k1 == k2) {
                tt_collect_add = $n;
            } else {
                local A = c1; local B = c2;
                if k1 == K.Cos { A = c2; B = c1; }
                if is_zero(A) { tt_collect_add = $n; } else {
                    mk_pow A, 2; local a2p = mk_pow;
                    mk_pow B, 2; local b2p = mk_pow;
                    mk_add a2p, b2p; local r2 = mk_add;
                    mk_func K.Sqrt, r2; local amp = mk_func;
                    mk_pow A, -1; local ainv = mk_pow;
                    mk_mul B, ainv; local quot = mk_mul;
                    mk_func K.Atan, quot; local ph = mk_func;
                    if nd_kind[A] == K.Num and nd_num[A] < 0 {
                        mk_var "pi"; mk_add ph, mk_var; ph = mk_add;
                    }
                    trig_simplify ph;
                    if err == "" and trig_simplify != 0 { ph = trig_simplify; }
                    mk_add a1, ph; local arg2 = mk_add;
                    tt_sin arg2; mk_mul amp, tt_sin;
                    tt_collect_add = mk_mul;
                }
            }
        }
    }
}

list tt_aterms;
list tt_astk;
list ttc_facs;
list ttc_stk;

list tt_aterms;
list tt_astk;

proc tt_rebuild n {
    local k = nd_kind[$n];
    if k == K.Add {
        mk_add tt_val[nd_a[$n]], tt_val[nd_b[$n]];
        local am = mk_add;
        if tt_mode == 6 { tt_collect_add am; am = tt_collect_add; }
        tt_rebuild = am;
    } elif k == K.Mul {
        mk_mul tt_val[nd_a[$n]], tt_val[nd_b[$n]];
        local m = mk_mul;
        if tt_mode == 2 { tt_linear_mul m; m = tt_linear_mul; }
        if tt_mode == 6 { tt_collect_mul m; m = tt_collect_mul; }
        tt_rebuild = m;
    } elif k == K.Pow {
        local base = nd_a[$n];
        if tt_mode == 2 and nd_num[$n] == 2 and (nd_kind[base] == K.Sin or nd_kind[base] == K.Cos) {
            tt_linear_pow nd_kind[base], nd_a[base];
            tt_rebuild = tt_linear_pow;
        } elif tt_mode >= 7 and tt_mode <= 9 and nd_num[$n] == 2 and nd_kind[base] >= K.Sin and nd_kind[base] <= K.Tan {
            tt_rewrite_pow nd_kind[base], nd_a[base], tt_mode;
            if tt_rewrite_pow != 0 { tt_rebuild = tt_rewrite_pow; }
            else { mk_pow tt_val[base], nd_num[$n]; tt_rebuild = mk_pow; }
        } else {
            mk_pow tt_val[base], nd_num[$n];
            tt_rebuild = mk_pow;
        }
    } elif k == K.PowE {
        mk_pow_expr tt_val[nd_a[$n]], tt_val[nd_b[$n]];
        tt_rebuild = mk_pow_expr;
    } elif k == K.Sin or k == K.Cos or k == K.Tan {
        local arg = tt_val[nd_a[$n]];
        if tt_mode == 1 {
            tt_texpand_trig k, arg;
            if tt_texpand_trig != 0 { tt_rebuild = tt_texpand_trig; }
            else { new_func_raw k, arg; tt_rebuild = new_func_raw; }
        } elif tt_mode == 3 {
            if k == K.Sin {
                mk_var "pi"; mk_num 1, 2; mk_mul mk_num, mk_var; local half = mk_mul;
                tt_neg arg; local na = tt_neg;
                mk_add half, na; local a = mk_add;
                tt_cos a; tt_rebuild = tt_cos;
            } else { new_func_raw k, arg; tt_rebuild = new_func_raw; }
        } elif tt_mode == 4 {
            if k == K.Cos {
                mk_var "pi"; mk_num 1, 2; mk_mul mk_num, mk_var; local half = mk_mul;
                mk_add half, arg; local a = mk_add;
                tt_sin a; tt_rebuild = tt_sin;
            } else { new_func_raw k, arg; tt_rebuild = new_func_raw; }
        } elif tt_mode == 5 {
            tt_half arg; local ha = tt_half;
            tt_tan ha; local t = tt_tan;
            mk_mul t, t; local t2 = mk_mul;
            mk_num 1, 1;
            if k == K.Sin {
                mk_num 2, 1; mk_mul mk_num, t; local num = mk_mul;
                mk_num 1, 1;
                mk_add mk_num, t2; local den = mk_add;
                tt_div num, den; tt_rebuild = tt_div;
            } elif k == K.Cos {
                tt_neg t2; local nt2 = tt_neg;
                mk_add mk_num, nt2; local num = mk_add;
                mk_add mk_num, t2; local den = mk_add;
                tt_div num, den; tt_rebuild = tt_div;
            } else {
                mk_num 2, 1; mk_mul mk_num, t; local num = mk_mul;
                tt_neg t2; local nt2 = tt_neg;
                mk_num 1, 1;
                mk_add mk_num, nt2; local den = mk_add;
                tt_div num, den; tt_rebuild = tt_div;
            }
        } else {
            new_func_raw k, arg; tt_rebuild = new_func_raw;
        }
    } elif k >= K.Sin and k <= K.Atan {
        new_func_raw k, tt_val[nd_a[$n]];
        tt_rebuild = new_func_raw;
    } elif k == K.Unknown {
        mk_genfunc nd_txt[$n], tt_val[nd_a[$n]];
        tt_rebuild = mk_genfunc;
    } else {
        tt_rebuild = $n;
    }
}

list tt_val;
list tt_stk_node;
list tt_stk_state;

proc tt_apply root, mode {
    tt_mode = $mode;
    delete tt_val;
    local i = 1;
    until i > node_count { add 0 to tt_val; i++; }
    delete tt_stk_node; delete tt_stk_state;
    local sp = 0;
    sp++; add $root to tt_stk_node; add 0 to tt_stk_state;
    until sp == 0 or err != "" {
        local n = tt_stk_node[sp];
        local st = tt_stk_state[sp];
        sp--;
        if st == 0 {
            sp++;
            if sp > length(tt_stk_node) { add n to tt_stk_node; add 1 to tt_stk_state; }
            else { tt_stk_node[sp] = n; tt_stk_state[sp] = 1; }
            local k = nd_kind[n];
            if k == K.Add or k == K.Mul or k == K.PowE {
                sp++;
                if sp > length(tt_stk_node) { add nd_b[n] to tt_stk_node; add 0 to tt_stk_state; }
                else { tt_stk_node[sp] = nd_b[n]; tt_stk_state[sp] = 0; }
                sp++;
                if sp > length(tt_stk_node) { add nd_a[n] to tt_stk_node; add 0 to tt_stk_state; }
                else { tt_stk_node[sp] = nd_a[n]; tt_stk_state[sp] = 0; }
            } elif k == K.Pow {
                sp++;
                if sp > length(tt_stk_node) { add nd_a[n] to tt_stk_node; add 0 to tt_stk_state; }
                else { tt_stk_node[sp] = nd_a[n]; tt_stk_state[sp] = 0; }
            } elif (k >= K.Sin and k <= K.Atan) or k == K.Unknown {
                sp++;
                if sp > length(tt_stk_node) { add nd_a[n] to tt_stk_node; add 0 to tt_stk_state; }
                else { tt_stk_node[sp] = nd_a[n]; tt_stk_state[sp] = 0; }
            }
        } else {
            tt_rebuild n;
            if err == "" { tt_val[n] = tt_rebuild; }
        }
    }
    if err != "" { tt_apply = 0; } else { tt_apply = tt_val[$root]; }
}

proc tt_collect_mul n {
    delete tt_cfacs;
    local st = 0;
    delete tt_cstk;
    st++; add $n to tt_cstk;
    until st == 0 {
        local x = tt_cstk[st];
        st--;
        if nd_kind[x] == K.Mul {
            st++;
            if st > length(tt_cstk) { add nd_b[x] to tt_cstk; } else { tt_cstk[st] = nd_b[x]; }
            st++;
            if st > length(tt_cstk) { add nd_a[x] to tt_cstk; } else { tt_cstk[st] = nd_a[x]; }
        } else { add x to tt_cfacs; }
    }
    local c = 1;
    local a = 0;
    local b = 0;
    local i = 1;
    until i > length(tt_cfacs) {
        local f = tt_cfacs[i];
        if nd_kind[f] == K.Num {
            c *= nd_num[f] / nd_den[f];
        } elif nd_kind[f] == K.Sin or nd_kind[f] == K.Cos {
            if a == 0 { a = f; } elif b == 0 { b = f; } else { b = -1; }
        } else { b = -1; }
        i++;
    }
    if a == 0 or b == 0 or b == -1 {
        tt_collect_mul = $n;
    } elif nd_kind[a] != nd_kind[b] and not (nd_kind[a] == K.Sin and nd_kind[b] == K.Cos) and not (nd_kind[a] == K.Cos and nd_kind[b] == K.Sin) {
        tt_collect_mul = $n;
    } elif nd_sig[nd_a[a]] != nd_sig[nd_a[b]] {
        tt_collect_mul = $n;
    } else {
        tt_double nd_a[a]; local d2 = tt_double;
        tt_sin d2; local s2 = tt_sin;
        if c == 2 {
            tt_collect_mul = s2;
        } elif c == 1 {
            mk_num 1, 2;
            mk_mul mk_num, s2;
            tt_collect_mul = mk_mul;
        } else {
            mk_num c, 2;
            mk_mul mk_num, s2;
            tt_collect_mul = mk_mul;
        }
    }
}

list tt_cfacs;
list tt_cstk;
