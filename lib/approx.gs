# Approximate function: evaluate its argument numerically and replace the
# Approx node with a Float node.

list ap_val;
list ap_stk_node;
list ap_stk_state;
var ap_sp = 0;

proc ap_big_pow node {
    ap_big_pow = 0;
    if nd_kind[$node] != K.PowE {
        ap_big_pow = 0;
    } else {
        local b = nd_a[$node];
        local e = nd_b[$node];
        if (nd_kind[b] == K.Num or nd_kind[b] == K.Float) and (nd_kind[e] == K.Num or nd_kind[e] == K.Float or is_big(e)) {
            local bv = 0;
            local ev = 0;
            if nd_kind[b] == K.Num { bv = nd_num[b] / nd_den[b]; } else { bv = nd_num[b]; }
            if nd_kind[e] == K.Num { ev = nd_num[e] / nd_den[e]; } elif nd_kind[e] == K.Float { ev = nd_num[e]; } else { ev = nd_txt[e] + 0; }
            if bv > 0 {
                local lg = log(bv) * ev;
                if abs(lg) > 300 {
                    local ex = floor(lg);
                    local frac = lg - ex;
                    local mm = antiln(frac * 2.302585092994046);
                    if mm >= 10 { mm = mm / 10; ex++; }
                    if mm < 1 { mm = mm * 10; ex--; }
                    mk_bigfloat (fmt_dec(mm) & "e" & big_exp_str(ex));
                    ap_big_pow = mk_bigfloat;
                }
            }
        }
    }
}

proc ap_big id {
    local t = nd_txt[$id];
    local neg = false;
    local p = 1;
    if length(t) > 0 and t[1] == "-" { neg = true; p = 2; }
    local nd = length(t) - p + 1;
    local take = nd;
    if take > 16 { take = 16; }
    local d = substr(t, p, p + take - 1);
    local mt = "";
    if length(d) == 1 {
        mt = d;
    } else {
        mt = substr(d, 1, 1) & "." & substr(d, 2, length(d));
    }
    if neg { mt = "-" & mt; }
    local ex = nd - 1;
    mk_bigfloat mt & "e" & int_str(ex);
    ap_big = mk_bigfloat;
}

proc ap_scalar x {
    ap_scalar = 0;
    if nd_kind[$x] == K.BigFloat {
        ap_scalar = $x;
    } elif is_big($x) {
        ap_big $x;
        ap_scalar = ap_big;
    } else {
        ap_big_pow $x;
        if err == "" and ap_big_pow != 0 {
            ap_scalar = ap_big_pow;
        } else {
            eval_expr $x;
            if err == "" {
                local fl = new_float(eval_expr);
                ap_scalar = fl;
            }
        }
    }
}

proc ap_map_container c {
    ctb_begin nd_kind[$c];
    until ctb_idx[ctb_depth] > nd_den[$c] or err != "" {
        local x = ct_elems[nd_num[$c] + ctb_idx[ctb_depth] - 1];
        if is_container(x) {
            ap_map_container x;
            ctb_add ap_map_container;
        } else {
            ap_scalar x;
            ctb_add ap_scalar;
        }
        ctb_idx[ctb_depth]++;
    }
    if err != "" { ctb_depth--; ap_map_container = 0; }
    else { ctb_end; ap_map_container = ctb_out; }
}

proc approx_rebuild n {
    local k = nd_kind[$n];
    if k == K.Add {
        mk_add ap_val[nd_a[$n]], ap_val[nd_b[$n]];
        approx_rebuild = mk_add;
    } elif k == K.Mul {
        mk_mul ap_val[nd_a[$n]], ap_val[nd_b[$n]];
        approx_rebuild = mk_mul;
    } elif k == K.Pow {
        mk_pow ap_val[nd_a[$n]], nd_num[$n];
        approx_rebuild = mk_pow;
    } elif k == K.PowE {
        mk_pow_expr ap_val[nd_a[$n]], ap_val[nd_b[$n]];
        approx_rebuild = mk_pow_expr;
    } elif k == K.Approx {
        local ch = ap_val[nd_a[$n]];
        if (nd_kind[ch] == K.Big or nd_kind[ch] == K.Var) and substr(nd_txt[ch], 1, 5) == "sqrt(" {
            local st = substr(nd_txt[ch], 6, length(nd_txt[ch]) - 1);
            local sl = find_char(st, "/");
            local qv = 0;
            if sl > 0 {
                local nn = substr(st, 1, sl - 1);
                local dd = substr(st, sl + 1, length(st));
                if dd != "" and dd + 0 != 0 { qv = sqrt((nn + 0) / (dd + 0)); }
            }
            local qf = new_float(qv);
            approx_rebuild = qf;
        } elif nd_kind[ch] == K.Sqrt and is_bigfrac(nd_a[ch]) {
            bigfrac_double nd_a[ch];
            local fv = bigfrac_double;
            if fv >= 0 { local qv = new_float(sqrt(fv)); approx_rebuild = qv; }
            else { approx_rebuild = 0; set_err "sqrt 的定义域错误"; }
        } elif is_container(ch) {
            ap_map_container ch;
            approx_rebuild = ap_map_container;
        } elif nd_kind[ch] == K.BigFloat {
            approx_rebuild = ch;
        } elif is_big(ch) {
            ap_big ch;
            approx_rebuild = ap_big;
        } else {
        ap_big_pow ch;
        if err == "" and ap_big_pow != 0 {
            approx_rebuild = ap_big_pow;
        } else {
        eval_expr ch;
        if err != "" {
            approx_rebuild = 0;
        } else {
            local fl = new_float(eval_expr);
            approx_rebuild = fl;
        }
        }
        }
    } elif k >= K.Sin and k <= K.Atan {
        mk_func k, ap_val[nd_a[$n]];
        approx_rebuild = mk_func;
    } elif k == K.Unknown {
        mk_genfunc nd_txt[$n], ap_val[nd_a[$n]];
        approx_rebuild = mk_genfunc;
    } else {
        approx_rebuild = $n;
    }
}

proc approx_pass root {
    approx_pass = $root;
    if $root == 0 or err != "" {
        approx_pass = 0;
    } else {
        delete ap_val;
        local i = 1;
        until i > node_count {
            add 0 to ap_val;
            i++;
        }
        delete ap_stk_node;
        delete ap_stk_state;
        ap_sp = 0;
        ap_sp++; add $root to ap_stk_node; add 0 to ap_stk_state;
        until ap_sp == 0 or err != "" {
            local n = ap_stk_node[ap_sp];
            local st = ap_stk_state[ap_sp];
            ap_sp--;
            if st == 0 {
                ap_sp++;
                if ap_sp > length(ap_stk_node) { add n to ap_stk_node; add 1 to ap_stk_state; }
                else { ap_stk_node[ap_sp] = n; ap_stk_state[ap_sp] = 1; }
                local k = nd_kind[n];
                if k == K.Add or k == K.Mul or k == K.PowE {
                    ap_sp++;
                    if ap_sp > length(ap_stk_node) { add nd_b[n] to ap_stk_node; add 0 to ap_stk_state; }
                    else { ap_stk_node[ap_sp] = nd_b[n]; ap_stk_state[ap_sp] = 0; }
                    ap_sp++;
                    if ap_sp > length(ap_stk_node) { add nd_a[n] to ap_stk_node; add 0 to ap_stk_state; }
                    else { ap_stk_node[ap_sp] = nd_a[n]; ap_stk_state[ap_sp] = 0; }
                } elif k == K.Pow or (k >= K.Sin and k <= K.Atan) or k == K.Unknown or k == K.Approx {
                    ap_sp++;
                    if ap_sp > length(ap_stk_node) { add nd_a[n] to ap_stk_node; add 0 to ap_stk_state; }
                    else { ap_stk_node[ap_sp] = nd_a[n]; ap_stk_state[ap_sp] = 0; }
                }
            } else {
                approx_rebuild n;
                if err == "" { ap_val[n] = approx_rebuild; }
            }
        }
        if err != "" { approx_pass = 0; } else { approx_pass = ap_val[$root]; }
    }
}
