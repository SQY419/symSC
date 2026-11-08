# n-variate modular GCD/lcm by evaluating all but two variables and
# interpolating the bivariate modular GCD (explicit grid, no recursion).

var ng_nv = 0;
var ng_ex = 0;
var ng_grid = 0;
var ng_mx = 0;
var ng_my = 0;
var ng_ok = true;
var ng_p = 0;
var ng_q = 0;
var ng_mode = 1;
list ng_vars;
list ng_dims;
list ng_strides;
list ng_vals_n;
list ng_vals_d;
list ng_result_n;
list ng_result_d;

proc ng_reset {
    ng_nv = 0;
    ng_ex = 0;
    ng_grid = 0;
    ng_mx = 0;
    ng_my = 0;
    ng_ok = true;
    delete ng_vars;
    delete ng_dims;
    delete ng_strides;
    delete ng_vals_n;
    delete ng_vals_d;
    delete ng_result_n;
    delete ng_result_d;
}

proc ng_collect_vars p, q {
    poly_reset;
    collect_vars_ast $p;
    collect_vars_ast $q;
    ng_nv = pv_count;
    delete ng_vars;
    local i = 1;
    until i > pv_count {
        add pv_name[i] to ng_vars;
        i++;
    }
}

proc ng_degree_terms pid, nv {
    # max exponent per variable in pid; results in ng_dmax
    delete ng_dmax;
    local v = 1;
    until v > $nv {
        add 0 to ng_dmax;
        v++;
    }
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $pid {
            v = 1;
            until v > $nv {
                local e = pt_exp[(t - 1) * $nv + v];
                if e > ng_dmax[v] { ng_dmax[v] = e; }
                v++;
            }
        }
        t++;
    }
}

list ng_dmax;

proc ng_setup p, q {
    ng_reset;
    ng_p = $p;
    ng_q = $q;
    ng_collect_vars $p, $q;
    if ng_nv < 3 {
        ng_ok = false;
    } else {
        poly_reset;
        collect_vars_ast $p;
        collect_vars_ast $q;
        poly_from_ast $p;
        local pp = poly_from_ast;
        poly_from_ast $q;
        local qq = poly_from_ast;
        ng_degree_terms pp, ng_nv;
        delete ng_dp;
        local v = 1;
        until v > ng_nv { add ng_dmax[v] to ng_dp; v++; }
        ng_degree_terms qq, ng_nv;
        delete ng_dq;
        v = 1;
        until v > ng_nv { add ng_dmax[v] to ng_dq; v++; }
        ng_min_terms pp;
        delete ng_minp;
        local v = 1;
        until v > ng_nv { add ng_mins[v] to ng_minp; v++; }
        ng_min_terms qq;
        delete ng_cmins;
        v = 3;
        until v > ng_nv {
            local c = ng_minp[v];
            if ng_mins[v] < c { c = ng_mins[v]; }
            add c to ng_cmins;
            v++;
        }
        ng_bounds 1;
    }
}

proc ng_min_terms pid {
    delete ng_mins;
    local v = 1;
    until v > ng_nv { add 1000000 to ng_mins; v++; }
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $pid {
            v = 1;
            until v > ng_nv {
                local e = pt_exp[(t - 1) * ng_nv + v];
                if e < ng_mins[v] { ng_mins[v] = e; }
                v++;
            }
        }
        t++;
    }
}

proc ng_bounds mode {
    if $mode == 1 {
        ng_mx = ng_dp[1];
        if ng_dq[1] < ng_mx { ng_mx = ng_dq[1]; }
        ng_my = ng_dp[2];
        if ng_dq[2] < ng_my { ng_my = ng_dq[2]; }
    } elif $mode == 2 {
        ng_mx = ng_dp[1] + ng_dq[1];
        ng_my = ng_dp[2] + ng_dq[2];
    } else {
        ng_mx = ng_dp[1] - ng_dq[1];
        ng_my = ng_dp[2] - ng_dq[2];
        if ng_mx < 0 or ng_my < 0 { ng_ok = false; }
    }
    ng_ex = ng_nv - 2;
    delete ng_dims;
    delete ng_lmax;
    ng_grid = 1;
    local v = 3;
    until v > ng_nv {
        local d = 0;
        if $mode == 1 {
            d = ng_dp[v];
            if ng_dq[v] < d { d = ng_dq[v]; }
        } elif $mode == 2 {
            d = ng_dp[v] + ng_dq[v];
        } else {
            d = ng_dp[v] - ng_dq[v];
            if d < 0 { ng_ok = false; }
        }
        local m = d + 1;
        add m to ng_dims;
        local lm = ng_dp[v];
        if ng_dq[v] > lm { lm = ng_dq[v]; }
        add lm to ng_lmax;
        ng_grid *= m;
        v++;
    }
    if ng_grid > 256 {
        ng_ok = false;
    } else {
        delete ng_strides;
        v = 1;
        until v > ng_ex { add 0 to ng_strides; v++; }
        local stride = 1;
        v = ng_ex;
        until v < 1 {
            ng_strides[v] = stride;
            stride *= ng_dims[v];
            v--;
        }
    }
}

list ng_dp;
list ng_dq;
list ng_strides2;

proc ng_eval_roots p, q, point {
    subst_clear;
    local rem = $point;
    local v = 1;
    until v > ng_ex {
        local m = ng_dims[v];
        local coord = (rem % m) + 1;
        rem = floor(rem / m);
        mk_num coord, 1;
        subst_add ng_vars[v + 2], mk_num;
        v++;
    }
    subst_expr $p;
    ng_eval_roots = subst_expr;
    subst_expr $q;
    ng_eval_roots2 = subst_expr;
}

var ng_eval_roots2 = 0;

proc ng_set_cell mono, point, n, d {
    local idx = $mono * ng_grid + $point + 1;
    ng_vals_n[idx] = $n;
    ng_vals_d[idx] = $d;
}

proc ng_run mode {
    ng_mode = $mode;
    ng_bounds $mode;
    local mono_count = (ng_mx + 1) * (ng_my + 1);
    delete ng_vals_n;
    delete ng_vals_d;
    local total = mono_count * ng_grid;
    local i = 1;
    until i > total {
        add 0 to ng_vals_n;
        add 1 to ng_vals_d;
        i++;
    }
    local point = 0;
    until point >= ng_grid or ng_ok == false {
        ng_eval_roots ng_p, ng_q, point;
        local r1 = ng_eval_roots;
        local r2 = ng_eval_roots2;
        bp_begin r1, r2;
        if bp_ok == false {
            ng_ok = false;
        } else {
            bp_dgy = bp_ay;
            if bp_by < bp_dgy { bp_dgy = bp_by; }
            if $mode == 3 {
                bp_gx = bp_bx;
                bp_gy = bp_by;
                delete bp_gn;
                delete bp_gd;
                local gi = 1;
                until gi > length(bp_bn) {
                    add bp_bn[gi] to bp_gn;
                    add bp_bd[gi] to bp_gd;
                    gi++;
                }
                bp_q_div 1;
                if bp_ok == false { ng_ok = false; }
            } else {
                bp_gcd_q;
                if bp_ok == false {
                    ng_ok = false;
                } else {
                    if $mode == 2 {
                        bp_q_mul;
                        bp_h_to_a;
                        bp_q_div 1;
                        if bp_ok == false { ng_ok = false; }
                    }
                }
            }
            if ng_ok {
                if $mode == 1 or $mode == 2 or $mode == 3 {
                    local mi = 0;
                    until mi > ng_mx {
                        local mj = 0;
                        until mj > ng_my {
                            local mono = mi * (ng_my + 1) + mj;
                            local n = 0;
                            local d = 1;
                            if $mode == 2 or $mode == 3 {
                                if mi <= bp_qx and mj <= bp_qy {
                                    local qi = mi * (bp_qy + 1) + mj + 1;
                                    n = bp_qn[qi];
                                    d = bp_qd[qi];
                                }
                            } else {
                                if mi <= bp_gx and mj <= bp_gy {
                                    local gi = mi * (bp_gy + 1) + mj + 1;
                                    n = bp_gn[gi];
                                    d = bp_gd[gi];
                                }
                            }
                            ng_set_cell mono, point, n, d;
                            mj++;
                        }
                        mi++;
                    }
                }
            }
        }
        point++;
    }
    if ng_ok == false {
        ng_ok = false;
    } else {
        ng_interpolate_all mono_count;
    }
}

list ng_iv_n;
list ng_iv_d;
list ng_ic_n;
list ng_ic_d;

proc ng_interp_one_mono mono {
    local d = 1;
    until d > ng_ex {
        local m = ng_dims[d];
        local st = ng_strides[d];
        local blocks = ng_grid / (m * st);
        local block = 0;
        until block >= blocks {
            local off = 0;
            until off >= st {
                local posb = block * m * st + off;
                # gather values
                delete ng_iv_n;
                delete ng_iv_d;
                local q = 0;
                until q >= m {
                    local idx = $mono * ng_grid + posb + q * st + 1;
                    add ng_vals_n[idx] to ng_iv_n;
                    add ng_vals_d[idx] to ng_iv_d;
                    q++;
                }
                # interpolate through points 1..m
                delete ng_ic_n;
                delete ng_ic_d;
                q = 1;
                until q > m { add 0 to ng_ic_n; add 1 to ng_ic_d; q++; }
                local s = 1;
                until s > m {
                    delete ng_basis;
                    q = 1;
                    until q > m { add 0 to ng_basis; q++; }
                    ng_basis[1] = 1;
                    local den = 1;
                    local t = 1;
                    until t > m {
                        if t != s {
                            den *= (s - t);
                            local z = m - 1;
                            until z < 0 {
                                local prev = 0;
                                if z > 0 { prev = ng_basis[z]; }
                                ng_basis[z + 1] = prev - t * ng_basis[z + 1];
                                z--;
                            }
                        }
                        t++;
                    }
                    rat_div ng_iv_n[s], ng_iv_d[s], den, 1;
                    local scale_n = rn;
                    local scale_d = rd;
                    q = 1;
                    until q > m {
                        rat_mul scale_n, scale_d, ng_basis[q], 1;
                        if rok == false {
                            ng_ok = false;
                        } else {
                            local ci = $mono * ng_grid + posb + (q - 1) * st + 1;
                            rat_add ng_ic_n[q], ng_ic_d[q], rn, rd;
                            if rok == false {
                                ng_ok = false;
                            } else {
                                ng_ic_n[q] = rn;
                                ng_ic_d[q] = rd;
                            }
                        }
                        q++;
                    }
                    s++;
                }
                # write coefficients
                q = 0;
                until q >= m {
                    local ci = $mono * ng_grid + posb + q * st + 1;
                    ng_vals_n[ci] = ng_ic_n[q + 1];
                    ng_vals_d[ci] = ng_ic_d[q + 1];
                    q++;
                }
                off++;
            }
            block++;
        }
        d++;
    }
}

list ng_basis;
list ng_exps;

proc ng_interpolate_all mono_count {
    local mono = 0;
    until mono >= $mono_count or ng_ok == false {
        ng_interp_one_mono mono;
        mono++;
    }
}

proc ng_min_extra p, q {
    # common minimum exponent of extra variables in both polynomial ASTs
    # computed from current poly terms is done in ng_setup; simple zero default
    ng_cmin = 0;
}

var ng_cmin = 0;
list ng_cmins;
list ng_mins;
list ng_minp;
list ng_candmin;
list ng_candmax;
list ng_lmax;
list ng_delta;

proc ng_term_ast coeff_n, coeff_d {
    local mono = 0;
    local v = 1;
    until v > ng_nv {
        local e = ng_exps[v];
        if e > 0 {
            mk_var ng_vars[v];
            local vn = mk_var;
            mk_pow vn, e;
            local f = mk_pow;
            if mono == 0 { mono = f; } else { mk_mul mono, f; mono = mk_mul; }
        }
        v++;
    }
    if mono == 0 {
        mk_num $coeff_n, $coeff_d;
        ng_term_ast = mk_num;
    } elif $coeff_n == 1 and $coeff_d == 1 {
        ng_term_ast = mono;
    } else {
        mk_num $coeff_n, $coeff_d;
        local c = mk_num;
        mk_mul c, mono;
        ng_term_ast = mk_mul;
    }
}

proc ng_build_ast {
    # candidate minimum exponent per extra variable
    delete ng_candmin;
    delete ng_candmax;
    local vv = 1;
    until vv > ng_ex { add 1000000 to ng_candmin; add 0 to ng_candmax; vv++; }
    local mm = 0;
    until mm >= (ng_mx + 1) * (ng_my + 1) {
        local qq = 0;
        until qq >= ng_grid {
            if ng_vals_n[mm * ng_grid + qq + 1] != 0 {
                local rr = qq;
                vv = 1;
                until vv > ng_ex {
                    local mm2 = ng_dims[vv];
                    local ee = rr % mm2;
                    if ee < ng_candmin[vv] { ng_candmin[vv] = ee; }
                    if ee > ng_candmax[vv] { ng_candmax[vv] = ee; }
                    rr = floor(rr / mm2);
                    vv++;
                }
            }
            qq++;
        }
        mm++;
    }
    delete ng_delta;
    vv = 1;
    until vv > ng_ex {
        local dd = 0;
        if ng_mode == 1 {
            if ng_cmins[vv] > ng_candmin[vv] { dd = ng_cmins[vv] - ng_candmin[vv]; }
        }
        add dd to ng_delta;
        vv++;
    }
    local sum = 0;
    local mono_count = (ng_mx + 1) * (ng_my + 1);
    local mono = 0;
    until mono >= mono_count or ng_ok == false {
        local mi = floor(mono / (ng_my + 1));
        local mj = mono % (ng_my + 1);
        local q = 0;
        until q >= ng_grid or ng_ok == false {
            local idx = mono * ng_grid + q + 1;
            if ng_vals_n[idx] != 0 {
                # decode extra exponents
                delete ng_exps;
                local v = 1;
                until v > ng_nv { add 0 to ng_exps; v++; }
                ng_exps[1] = mi;
                ng_exps[2] = mj;
                local rem = q;
                v = 1;
                until v > ng_ex {
                    local m = ng_dims[v];
                    ng_exps[v + 2] = (rem % m) + ng_delta[v];
                    rem = floor(rem / m);
                    v++;
                }
                ng_term_ast ng_vals_n[idx], ng_vals_d[idx];
                local term = ng_term_ast;
                if sum == 0 { sum = term; } else { mk_add sum, term; sum = mk_add; }
            }
            q++;
        }
        mono++;
    }
    if sum == 0 {
        mk_num 1, 1;
        sum = mk_num;
    }
    ng_build_ast = sum;
}

proc ng_div_roots a, b {
    ng_setup $a, $b;
    if ng_nv <= 2 {
        bp_begin $a, $b;
        if bp_ok == false {
            ng_div_roots = 0;
        } else {
            bp_gx = bp_bx;
            bp_gy = bp_by;
            delete bp_gn;
            delete bp_gd;
            local i = 1;
            until i > length(bp_bn) {
                add bp_bn[i] to bp_gn;
                add bp_bd[i] to bp_gd;
                i++;
            }
            bp_q_div 1;
            if bp_ok == false { ng_div_roots = 0; } else {
                bp_q_to_ast;
                ng_div_roots = bp_q_to_ast;
            }
        }
    } else {
        if ng_ok == false { ng_div_roots = 0; } else {
            ng_run 3;
            if ng_ok == false { ng_div_roots = 0; } else {
                ng_build_ast;
                ng_div_roots = ng_build_ast;
            }
        }
    }
}

proc ng_try_cancel_fraction root {
    if nd_kind[$root] != K.Mul {
        ng_try_cancel_fraction = 0;
    } else {
        frac_flatten $root;
        delete frac_nums;
        delete frac_dens;
        local i = 1;
        until i > length(frac_facs) {
            local f = frac_facs[i];
            if nd_kind[f] == K.Pow and nd_num[f] < 0 {
                mk_pow nd_a[f], -nd_num[f];
                add mk_pow to frac_dens;
            } else {
                add f to frac_nums;
            }
            i++;
        }
        if length(frac_dens) == 0 {
            ng_try_cancel_fraction = 0;
        } else {
            frac_build_num; local na = frac_build_num;
            frac_build_den; local da = frac_build_den;
            ng_setup na, da;
            if ng_nv <= 2 {
                try_cancel_fraction $root;
                ng_try_cancel_fraction = try_cancel_fraction;
            } elif ng_ok == false {
                ng_try_cancel_fraction = 0;
            } else {
                ng_run 1;
                if ng_ok == false {
                    ng_try_cancel_fraction = 0;
                } else {
                    ng_build_ast; local g = ng_build_ast;
                    if nd_kind[g] == K.Num and nd_num[g] == 1 and nd_den[g] == 1 {
                        ng_try_cancel_fraction = 0;
                    } else {
                        ng_div_roots na, g; local nq = ng_div_roots;
                        if nq == 0 { ng_try_cancel_fraction = 0; } else {
                            ng_div_roots da, g; local dq = ng_div_roots;
                            if dq == 0 { ng_try_cancel_fraction = 0; } else {
                                if nd_kind[dq] == K.Num and nd_num[dq] == 1 and nd_den[dq] == 1 {
                                    ng_try_cancel_fraction = nq;
                                } else {
                                    mk_pow dq, -1;
                                    mk_mul nq, mk_pow;
                                    ng_try_cancel_fraction = mk_mul;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

proc ng_lcm_roots p, q {
    ng_setup $p, $q;
    if ng_ok == false {
        ng_lcm_roots = 0;
    } else {
        ng_run 1;
        if ng_ok == false {
            ng_lcm_roots = 0;
        } else {
            ng_build_ast; local g = ng_build_ast;
            mk_mul $p, $q;
            expand_expr mk_mul;
            if err != "" {
                ng_lcm_roots = 0;
            } else {
                rules_simplify expand_expr;
                if err != "" {
                    ng_lcm_roots = 0;
                } else {
                    ng_div_roots rules_simplify, g;
                    ng_lcm_roots = ng_div_roots;
                }
            }
        }
    }
}

proc ng_monomial_lcm p, q {
    poly_reset;
    collect_vars_ast $p;
    collect_vars_ast $q;
    poly_from_ast $p; local pp = poly_from_ast;
    poly_from_ast $q; local qq = poly_from_ast;
    local cp = 0;
    local cq = 0;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == pp { cp++; }
        if pt_poly[t] == qq { cq++; }
        t++;
    }
    if cp != 1 or cq != 1 {
        ng_monomial_lcm = 0;
    } else {
        delete ng_vars;
        local v = 1;
        until v > pv_count { add pv_name[v] to ng_vars; v++; }
        ng_nv = pv_count;
        delete ng_exps;
        v = 1;
        until v > ng_nv { add 0 to ng_exps; v++; }
        t = 1;
        until t > pt_count {
            if pt_poly[t] == pp {
                v = 1;
                until v > ng_nv {
                    local e = pt_exp[(t - 1) * ng_nv + v];
                    if e > ng_exps[v] { ng_exps[v] = e; }
                    v++;
                }
            }
            if pt_poly[t] == qq {
                v = 1;
                until v > ng_nv {
                    local e = pt_exp[(t - 1) * ng_nv + v];
                    if e > ng_exps[v] { ng_exps[v] = e; }
                    v++;
                }
            }
            t++;
        }
        ng_term_ast 1, 1;
        ng_monomial_lcm = ng_term_ast;
    }
}
