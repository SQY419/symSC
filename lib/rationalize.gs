# Rationalize simple square-root denominators.

list ra_val;
list ra_stk_node;
list ra_stk_state;

list ra_check;

proc ra_has_sqrt root {
    delete ra_check;
    ra_has_sqrt = false;
    local sp = 0;
    sp++; add $root to ra_check;
    until sp == 0 {
        local n = ra_check[sp];
        sp--;
        local k = nd_kind[n];
        if k == K.Sqrt { ra_has_sqrt = true; sp = 0; }
        elif k == K.Add or k == K.Mul or k == K.PowE {
            sp++;
            if sp > length(ra_check) { add nd_b[n] to ra_check; } else { ra_check[sp] = nd_b[n]; }
            sp++;
            if sp > length(ra_check) { add nd_a[n] to ra_check; } else { ra_check[sp] = nd_a[n]; }
        } elif k == K.Pow or (k >= K.Sin and k <= K.Atan) or k == K.Unknown {
            sp++;
            if sp > length(ra_check) { add nd_a[n] to ra_check; } else { ra_check[sp] = nd_a[n]; }
        }
    }
}

proc ra_den den {
    ra_den = 0;
    pc_has_var $den;
    if pc_has_var {
        ra_den = 0;
    } else {
    ra_has_sqrt $den;
    if ra_has_sqrt == false {
        ra_den = 0;
    } else {
    local k = nd_kind[$den];
    if k == K.Sqrt {
        local u = nd_a[$den];
        mk_pow u, -1; local inv = mk_pow;
        mk_mul $den, inv;
        ra_den = mk_mul;
    } elif k == K.Mul {
        delete ra_facs;
        delete ra_fstk;
        local sp = 0;
        sp++; add $den to ra_fstk;
        until sp == 0 {
            local x = ra_fstk[sp];
            sp--;
            if nd_kind[x] == K.Mul {
                sp++;
                if sp > length(ra_fstk) { add nd_b[x] to ra_fstk; } else { ra_fstk[sp] = nd_b[x]; }
                sp++;
                if sp > length(ra_fstk) { add nd_a[x] to ra_fstk; } else { ra_fstk[sp] = nd_a[x]; }
            } else { add x to ra_facs; }
        }
        local sf = 0;
        local coef = 1;
        local i = 1;
        until i > length(ra_facs) {
            local f = ra_facs[i];
            if nd_kind[f] == K.Sqrt and sf == 0 { sf = f; }
            elif nd_kind[f] == K.Sqrt { sf = -1; }
            else {
                if coef == 1 { coef = f; } else { mk_mul coef, f; coef = mk_mul; }
            }
            i++;
        }
        if sf > 0 {
            local u = nd_a[sf];
            mk_pow u, -1; local uinv = mk_pow;
            mk_mul coef, uinv; local den2 = mk_mul;
            mk_pow den2, -1; local inv2 = mk_pow;
            mk_mul sf, inv2;
            ra_den = mk_mul;
        }
    } elif k == K.Add {
        local a = nd_a[$den];
        local b = nd_b[$den];
        mk_neg b; local nb = mk_neg;
        mk_add a, nb; local num = mk_add;
        mk_pow a, 2; local a2 = mk_pow;
        mk_pow b, 2; local b2 = mk_pow;
        mk_neg b2; local nb2 = mk_neg;
        mk_add a2, nb2; local d2 = mk_add;
        expand_expr d2;
        if err == "" { d2 = expand_expr; }
        if err == "" { rules_simplify d2; if err == "" { d2 = rules_simplify; } }
        mk_pow d2, -1; local inv = mk_pow;
        mk_mul num, inv;
        ra_den = mk_mul;
    }
    }
    }
}

proc ra_rebuild n {
    local k = nd_kind[$n];
    if k == K.Add {
        mk_add ra_val[nd_a[$n]], ra_val[nd_b[$n]];
        ra_rebuild = mk_add;
    } elif k == K.Mul {
        mk_mul ra_val[nd_a[$n]], ra_val[nd_b[$n]];
        ra_rebuild = mk_mul;
    } elif k == K.Pow {
        if nd_num[$n] == -1 {
            ra_den ra_val[nd_a[$n]];
            if ra_den != 0 { ra_rebuild = ra_den; }
            else { mk_pow ra_val[nd_a[$n]], -1; ra_rebuild = mk_pow; }
        } else {
            mk_pow ra_val[nd_a[$n]], nd_num[$n];
            ra_rebuild = mk_pow;
        }
    } elif k == K.PowE {
        mk_pow_expr ra_val[nd_a[$n]], ra_val[nd_b[$n]];
        ra_rebuild = mk_pow_expr;
    } elif k == K.Num or k == K.Var or k == K.Pi or k == K.E or k == K.Float or k == K.UN or k == K.Inf {
        ra_rebuild = $n;
    } elif k == K.Unknown {
        mk_genfunc nd_txt[$n], ra_val[nd_a[$n]];
        ra_rebuild = mk_genfunc;
    } elif k >= K.Sin and k <= K.Atan {
        mk_func k, ra_val[nd_a[$n]];
        ra_rebuild = mk_func;
    } else {
        ra_rebuild = $n;
    }
}

proc rationalize_expr root {
    delete ra_val;
    local i = 1;
    until i > node_count { add 0 to ra_val; i++; }
    delete ra_stk_node;
    delete ra_stk_state;
    local sp = 0;
    sp++; add $root to ra_stk_node; add 0 to ra_stk_state;
    until sp == 0 or err != "" {
        local n = ra_stk_node[sp];
        local st = ra_stk_state[sp];
        sp--;
        if st == 0 {
            sp++;
            if sp > length(ra_stk_node) { add n to ra_stk_node; add 1 to ra_stk_state; }
            else { ra_stk_node[sp] = n; ra_stk_state[sp] = 1; }
            local k = nd_kind[n];
            if k == K.Add or k == K.Mul or k == K.PowE {
                sp++;
                if sp > length(ra_stk_node) { add nd_b[n] to ra_stk_node; add 0 to ra_stk_state; }
                else { ra_stk_node[sp] = nd_b[n]; ra_stk_state[sp] = 0; }
                sp++;
                if sp > length(ra_stk_node) { add nd_a[n] to ra_stk_node; add 0 to ra_stk_state; }
                else { ra_stk_node[sp] = nd_a[n]; ra_stk_state[sp] = 0; }
            } elif k == K.Pow or (k >= K.Sin and k <= K.Atan) or k == K.Unknown {
                sp++;
                if sp > length(ra_stk_node) { add nd_a[n] to ra_stk_node; add 0 to ra_stk_state; }
                else { ra_stk_node[sp] = nd_a[n]; ra_stk_state[sp] = 0; }
            }
        } else {
            ra_rebuild n;
            if err == "" { ra_val[n] = ra_rebuild; }
        }
    }
    if err != "" { rationalize_expr = 0; } else { rationalize_expr = ra_val[$root]; }
}

list ra_facs;
list ra_fstk;
