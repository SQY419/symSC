# Bivariate polynomial layer and modular GCD (evaluation/interpolation).
# Supports at most two variables; univariate inputs are treated as y=0.

var bp_ok = true;
var bp_ax = 0;
var bp_ay = 0;
var bp_bx = 0;
var bp_by = 0;
list bp_an;
list bp_ad;
list bp_bn;
list bp_bd;

var bp_gx = 0;
var bp_gy = 0;
var bp_cmx = 0;
var bp_cmy = 0;
list bp_gn;
list bp_gd;

var bp_p1 = 1000003;
var bp_p2 = 1000033;

proc bp_reset {
    bp_ok = true;
    bp_ax = 0;
    bp_ay = 0;
    bp_bx = 0;
    bp_by = 0;
    delete bp_an;
    delete bp_ad;
    delete bp_bn;
    delete bp_bd;
    bp_gx = 0;
    bp_gy = 0;
    delete bp_gn;
    delete bp_gd;
}

proc bp_make_matrix pid, target {
    local mx = 0;
    local my = 0;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $pid {
            local ex = 0;
            local ey = 0;
            if pv_count >= 1 {
                ex = pt_exp[(t - 1) * pv_count + 1];
            }
            if pv_count >= 2 {
                ey = pt_exp[(t - 1) * pv_count + 2];
            }
            if ex > mx {
                mx = ex;
            }
            if ey > my {
                my = ey;
            }
        }
        t++;
    }
    local len = (mx + 1) * (my + 1);
    if $target == 1 {
        bp_ax = mx;
        bp_ay = my;
        delete bp_an;
        delete bp_ad;
        local i = 1;
        until i > len {
            add 0 to bp_an;
            add 1 to bp_ad;
            i++;
        }
    } else {
        bp_bx = mx;
        bp_by = my;
        delete bp_bn;
        delete bp_bd;
        local i = 1;
        until i > len {
            add 0 to bp_bn;
            add 1 to bp_bd;
            i++;
        }
    }
    t = 1;
    until t > pt_count {
        if pt_poly[t] == $pid {
            local ex = 0;
            local ey = 0;
            if pv_count >= 1 {
                ex = pt_exp[(t - 1) * pv_count + 1];
            }
            if pv_count >= 2 {
                ey = pt_exp[(t - 1) * pv_count + 2];
            }
            local idx = ex * (my + 1) + ey + 1;
            if $target == 1 {
                bp_an[idx] = pt_n[t];
                bp_ad[idx] = pt_d[t];
            } else {
                bp_bn[idx] = pt_n[t];
                bp_bd[idx] = pt_d[t];
            }
        }
        t++;
    }
}

proc bp_begin p, q {
    bp_reset;
    poly_reset;
    collect_vars_ast $p;
    collect_vars_ast $q;
    if pv_count > 2 {
        bp_ok = false;
    } else {
        poly_from_ast $p;
        local pp = poly_from_ast;
        poly_from_ast $q;
        local qq = poly_from_ast;
        if poly_ok == false or pp == 0 or qq == 0 {
            bp_ok = false;
        } else {
            bp_make_matrix pp, 1;
            bp_make_matrix qq, 2;
            bp_common_monomial;
        }
    }
}

proc bp_term_ast i, j, n, d {
    local mono = 0;
    if $i > 0 {
        mk_var pv_name[1];
        local v1 = mk_var;
        mk_pow v1, $i;
        mono = mk_pow;
    }
    if $j > 0 {
        if pv_count < 2 {
            bp_term_ast = 0;
        } else {
            mk_var pv_name[2];
            local v2 = mk_var;
            mk_pow v2, $j;
            local f2 = mk_pow;
            if mono == 0 {
                mono = f2;
            } else {
                mk_mul mono, f2;
                mono = mk_mul;
            }
        }
    }
    if mono == 0 {
        mk_num $n, $d;
        bp_term_ast = mk_num;
    } elif $n == 1 and $d == 1 {
        bp_term_ast = mono;
    } else {
        mk_num $n, $d;
        local c = mk_num;
        mk_mul c, mono;
        bp_term_ast = mk_mul;
    }
}

proc bp_matrix_to_ast target {
    local sum = 0;
    if $target == 1 {
        local i = 0;
        until i > bp_ax {
            local j = 0;
            until j > bp_ay {
                local idx = i * (bp_ay + 1) + j + 1;
                if bp_an[idx] != 0 {
                    local cn = bp_an[idx];
                    local cd = bp_ad[idx];
                    bp_term_ast i, j, cn, cd;
                    local term = bp_term_ast;
                    if sum == 0 { sum = term; } else { mk_add sum, term; sum = mk_add; }
                }
                j++;
            }
            i++;
        }
    } else {
        local i = 0;
        until i > bp_gx {
            local j = 0;
            until j > bp_gy {
                local idx = i * (bp_gy + 1) + j + 1;
                if bp_gn[idx] != 0 {
                    local cn = bp_gn[idx];
                    local cd = bp_gd[idx];
                    bp_term_ast i, j, cn, cd;
                    local term = bp_term_ast;
                    if sum == 0 { sum = term; } else { mk_add sum, term; sum = mk_add; }
                }
                j++;
            }
            i++;
        }
    }
    if sum == 0 {
        mk_num 0, 1;
        sum = mk_num;
    }
    bp_matrix_to_ast = sum;
}

# ---------- modular arithmetic ----------

func bp_mod(x, p) {
    local r = $x - floor($x / $p) * $p;
    if r < 0 {
        r += $p;
    }
    return r;
}

proc bp_powmod base, e, p {
    local b = bp_mod($base, $p);
    local r = 1;
    local ee = $e;
    until ee <= 0 {
        if bp_mod(ee, 2) == 1 {
            r = bp_mod(r * b, $p);
        }
        b = bp_mod(b * b, $p);
        ee = floor(ee / 2);
    }
    bp_powmod = r;
}

proc bp_inv a, p {
    bp_powmod $a, $p - 2, $p;
    bp_inv = bp_powmod;
}

proc bp_mod_matrix target, p {
    # Results are stored in bp_mn / bp_md (d=1) for now.
    delete bp_mn;
    if $target == 1 {
        local len = (bp_ax + 1) * (bp_ay + 1);
        local i = 1;
        until i > len {
            local n = bp_an[i];
            local d = bp_ad[i];
            if n == 0 {
                add 0 to bp_mn;
            } else {
                local dm = bp_mod(d, $p);
                bp_inv dm, $p;
                add bp_mod(n * bp_inv, $p) to bp_mn;
            }
            i++;
        }
        bp_mod_matrix = 1;
    } else {
        local len = (bp_bx + 1) * (bp_by + 1);
        local i = 1;
        until i > len {
            local n = bp_bn[i];
            local d = bp_bd[i];
            if n == 0 {
                add 0 to bp_mn;
            } else {
                local dm = bp_mod(d, $p);
                bp_inv dm, $p;
                add bp_mod(n * bp_inv, $p) to bp_mn;
            }
            i++;
        }
        bp_mod_matrix = 2;
    }
}

list bp_mn;
list bp_rm;

proc bp_eval_y target, a, p, n {
    # univariate coefficients in x, length n, into bp_ev
    delete bp_ev;
    local i = 0;
    until i >= $n {
        add 0 to bp_ev;
        i++;
    }
    local mx = bp_ax;
    local my = bp_ay;
    if $target == 2 {
        mx = bp_bx;
        my = bp_by;
    }
    i = 0;
    until i > mx {
        local j = 0;
        local val = 0;
        local ap = 1;
        until j > my {
            local idx = i * (my + 1) + j + 1;
            local c = 0;
            if $target == 1 {
                c = bp_an[idx];
            } else {
                c = bp_bn[idx];
            }
            val = bp_mod(val + c * ap, $p);
            ap = bp_mod(ap * $a, $p);
            j++;
        }
        bp_ev[i + 1] = val;
        i++;
    }
}

# ---------- univariate gcd over F_p ----------

list ug_a;
list ug_b;
list ug_r;
list ug_g;

proc ug_copy_a src {
    delete ug_a;
    local i = 1;
    until i > length($src) {
        add $src[i] to ug_a;
        i++;
    }
}

proc ug_copy_b src {
    delete ug_b;
    local i = 1;
    until i > length($src) {
        add $src[i] to ug_b;
        i++;
    }
}

proc ug_gcd_mod n, p {
    # caller fills ug_a/ug_b, both length n; result in ug_g
    delete ug_g;
    local i = 1;
    until i > $n {
        add 0 to ug_g;
        i++;
    }
    local da = $n - 1;
    until da < 0 or ug_a[da + 1] != 0 {
        da--;
    }
    local db = $n - 1;
    until db < 0 or ug_b[db + 1] != 0 {
        db--;
    }
    local steps = 0;
    until db < 0 or steps > 200 or bp_ok == false {
        delete ug_r;
        i = 1;
        until i > $n {
            add ug_a[i] to ug_r;
            i++;
        }
        local dr = da;
        local lb = ug_b[db + 1];
        bp_inv lb, $p;
        local ilb = bp_inv;
        until dr < db or dr < 0 or steps > 400 {
            local lr = ug_r[dr + 1];
            local f = bp_mod(lr * ilb, $p);
            local shift = dr - db;
            local j = 0;
            until j > db {
                local k = j + shift;
                local prod = bp_mod(f * ug_b[j + 1], $p);
                ug_r[k + 1] = bp_mod(ug_r[k + 1] - prod, $p);
                j++;
            }
            until dr < 0 or ug_r[dr + 1] != 0 {
                dr--;
            }
            steps++;
        }
        # a <- b, b <- r
        delete ug_a;
        i = 1;
        until i > $n {
            add ug_b[i] to ug_a;
            i++;
        }
        da = db;
        delete ug_b;
        i = 1;
        until i > $n {
            add ug_r[i] to ug_b;
            i++;
        }
        db = dr;
        steps++;
    }
    # normalize a monic
    if da >= 0 {
        local lead = ug_a[da + 1];
        bp_inv lead, $p;
        local il = bp_inv;
        i = 0;
        until i > da {
            ug_g[i + 1] = bp_mod(ug_a[i + 1] * il, $p);
            i++;
        }
    }
    ug_g[1] = ug_g[1];
}

# ---------- modular bivariate gcd: evaluate in y, interpolate ----------

list bp_ev;
list bp_sx;
list bp_sc;
var bp_scount = 0;
var bp_sdg = 0;
list bp_cg;
list bp_r1;
list bp_r2;
var bp_dgx = 0;
var bp_dgy = 0;
var bp_last_p = 0;

proc bp_eval_y_mod target, a, p, n {
    delete bp_ev;
    local i = 0;
    until i >= $n {
        add 0 to bp_ev;
        i++;
    }
    local mx = bp_ax;
    local my = bp_ay;
    if $target == 2 {
        mx = bp_bx;
        my = bp_by;
    }
    i = 0;
    until i > mx {
        local j = 0;
        local val = 0;
        local ap = 1;
        until j > my {
            local idx = i * (my + 1) + j + 1;
            local nn = 0;
            local dd = 1;
            if $target == 1 {
                nn = bp_an[idx];
                dd = bp_ad[idx];
            } else {
                nn = bp_bn[idx];
                dd = bp_bd[idx];
            }
            if nn != 0 {
                bp_inv bp_mod(dd, $p), $p;
                local cn = bp_mod(nn * bp_inv, $p);
                val = bp_mod(val + cn * ap, $p);
            }
            ap = bp_mod(ap * $a, $p);
            j++;
        }
        bp_ev[i + 1] = val;
        i++;
    }
}

proc bp_sample_prime p, n {
    delete bp_sx;
    delete bp_sc;
    bp_scount = 0;
    bp_sdg = 1000000;
    local a = 1;
    local limit = bp_dgy + 6;
    until a > limit {
        bp_eval_y_mod 1, a, $p, $n;
        local ea = 0;
        local i = 1;
        until i > $n {
            if bp_ev[i] != 0 { ea = 1; }
            i++;
        }
        bp_eval_y_mod 2, a, $p, $n;
        local eb = 0;
        i = 1;
        until i > $n {
            if bp_ev[i] != 0 { eb = 1; }
            i++;
        }
        if ea == 1 and eb == 1 {
            # need both evals; rebuild A's evaluation into ug_a
            bp_eval_y_mod 1, a, $p, $n;
            delete ug_a;
            local ca = 1;
            until ca > $n {
                add bp_ev[ca] to ug_a;
                ca++;
            }
            bp_eval_y_mod 2, a, $p, $n;
            delete ug_b;
            local cb = 1;
            until cb > $n {
                add bp_ev[cb] to ug_b;
                cb++;
            }
            ug_gcd_mod $n, $p;
            local dg = $n - 1;
            until dg < 0 or ug_g[dg + 1] != 0 {
                dg--;
            }
            # Evaluations at a few unlucky points can produce an
            # artificially high-degree gcd.  The generic gcd is the minimum
            # degree observed over the sample set.
            if dg < bp_sdg {
                bp_sdg = dg;
                delete bp_sx;
                delete bp_sc;
                bp_scount = 0;
            }
            if dg == bp_sdg {
                bp_scount++;
                add a to bp_sx;
                i = 1;
                until i > $n {
                    add ug_g[i] to bp_sc;
                    i++;
                }
            }
        }
        a++;
    }
    if bp_scount < bp_dgy + 1 {
        bp_ok = false;
    }
}

proc bp_interpolate n, p {
    # use first dgy+1 samples; coefficients in bp_cg
    delete bp_cg;
    local m = bp_dgy + 1;
    local len = (bp_sdg + 1) * (bp_dgy + 1);
    local q = 1;
    until q > len {
        add 0 to bp_cg;
        q++;
    }
    local i = 0;
    until i > bp_sdg {
        local s = 1;
        until s > m {
            local xs = bp_sx[s];
            local den = 1;
            local t = 1;
            until t > m {
                if t != s {
                    den = bp_mod(den * (xs - bp_sx[t]), $p);
                }
                t++;
            }
            bp_inv den, $p;
            local invden = bp_inv;
            local sidx = (s - 1) * $n + i;
            local sval = bp_sc[sidx + 1];
            local scale = bp_mod(sval * invden, $p);
            # basis polynomial starts at 1; degree <= m-1
            delete bp_lag;
            local z = 1;
            until z > m + 1 {
                add 0 to bp_lag;
                z++;
            }
            bp_lag[1] = 1;
            t = 1;
            until t > m {
                if t != s {
                    local ptx = bp_sx[t];
                    local d = m - 1;
                    until d < 0 {
                        local prev = 0;
                        if d > 0 {
                            prev = bp_lag[d];
                        }
                        bp_lag[d + 1] = bp_mod(prev - ptx * bp_lag[d + 1], $p);
                        d--;
                    }
                }
                t++;
            }
            local j = 0;
            until j > bp_dgy {
                bp_cg[i * (bp_dgy + 1) + j + 1] = bp_mod(bp_cg[i * (bp_dgy + 1) + j + 1] + bp_mod(scale * bp_lag[j + 1], $p), $p);
                j++;
            }
            s++;
        }
        i++;
    }
    bp_dgx = bp_sdg;
    bp_gy = bp_dgy;
    bp_gx = bp_dgx;
}

list bp_lag;

proc bp_trim_candidate {
    local mx = 0;
    local my = 0;
    local i = 0;
    until i > bp_gx {
        local j = 0;
        until j > bp_gy {
            if bp_gn[i * (bp_gy + 1) + j + 1] != 0 {
                if i > mx { mx = i; }
                if j > my { my = j; }
            }
            j++;
        }
        i++;
    }
    local oldy = bp_gy;
    delete bp_tn;
    delete bp_td;
    i = 0;
    until i > mx {
        local j = 0;
        until j > my {
            local oi = i * (oldy + 1) + j + 1;
            add bp_gn[oi] to bp_tn;
            add bp_gd[oi] to bp_td;
            j++;
        }
        i++;
    }
    delete bp_gn;
    delete bp_gd;
    i = 1;
    until i > length(bp_tn) {
        add bp_tn[i] to bp_gn;
        add bp_td[i] to bp_gd;
        i++;
    }
    bp_gx = mx;
    bp_gy = my;
}

proc bp_candidate_from_cg p {
    # bp_gx/bp_gy set by interpolate; fill bp_gn/gd
    delete bp_gn;
    delete bp_gd;
    local len = (bp_gx + 1) * (bp_gy + 1);
    local i = 1;
    until i > len {
        add 0 to bp_gn;
        add 1 to bp_gd;
        i++;
    }
    i = 0;
    until i > bp_gx {
        local j = 0;
        until j > bp_gy {
            local idx = i * (bp_gy + 1) + j + 1;
            bp_gn[idx] = bp_cg[i * (bp_dgy + 1) + j + 1];
            bp_gd[idx] = 1;
            j++;
        }
        i++;
    }
}

proc bp_mod_rem_zero target, p {
    # uses bp_mn (mod matrix of target) and bp_gn as candidate
    local mx = bp_ax;
    local my = bp_ay;
    if $target == 2 {
        mx = bp_bx;
        my = bp_by;
    }
    delete bp_rm;
    local i = 1;
    local len = (mx + 1) * (my + 1);
    until i > len {
        add bp_mn[i] to bp_rm;
        i++;
    }
    local steps = 0;
    local ok = true;
    until steps > 500 or ok == false {
        # leading term of remainder
        local ri = -1;
        local rj = -1;
        local x = mx;
        until x < 0 or ri >= 0 {
            local y = my;
            until y < 0 or ri >= 0 {
                if bp_rm[x * (my + 1) + y + 1] != 0 {
                    ri = x;
                    rj = y;
                }
                y--;
            }
            x--;
        }
        if ri < 0 {
            ok = true;
            steps = 1000;
        } else {
            # leading of gcd
            local gi = -1;
            local gj = -1;
            x = bp_gx;
            until x < 0 or gi >= 0 {
                local y = bp_gy;
                until y < 0 or gi >= 0 {
                    if bp_gn[x * (bp_gy + 1) + y + 1] != 0 {
                        gi = x;
                        gj = y;
                    }
                    y--;
                }
                x--;
            }
            if gi < 0 or ri < gi or rj < gj {
                ok = false;
            } else {
                local lr = bp_rm[ri * (my + 1) + rj + 1];
                local lg = bp_gn[gi * (bp_gy + 1) + gj + 1];
                bp_inv lg, $p;
                local f = bp_mod(lr * bp_inv, $p);
                local si = ri - gi;
                local sj = rj - gj;
                local a = 0;
                until a > bp_gx {
                    local b = 0;
                    until b > bp_gy {
                        local gv = bp_gn[a * (bp_gy + 1) + b + 1];
                        if gv != 0 {
                            local ti = a + si;
                            local tj = b + sj;
                            local pv = bp_mod(f * gv, $p);
                            local idx = ti * (my + 1) + tj + 1;
                            bp_rm[idx] = bp_mod(bp_rm[idx] - pv, $p);
                        }
                        b++;
                    }
                    a++;
                }
                steps++;
            }
        }
    }
    # check zero
    local allzero = true;
    i = 1;
    until i > len or allzero == false {
        if bp_rm[i] != 0 {
            allzero = false;
        } else {
            i++;
        }
    }
    bp_mod_rem_zero = allzero;
}

proc bp_mod_gcd_candidate p, n {
    bp_sample_prime $p, $n;
    if bp_ok == false or bp_scount < bp_dgy + 1 {
        bp_ok = false;
    } else {
        bp_interpolate $n, $p;
        bp_candidate_from_cg $p;
        bp_trim_candidate;
    }
}

# ---------- CRT and exact division over Q ----------

var bp_c1x = 0;
var bp_c1y = 0;
var bp_c2x = 0;
var bp_c2y = 0;
list bp_r1b;
list bp_r2b;

proc bp_save_candidate which {
    delete bp_tmp;
    local len = (bp_gx + 1) * (bp_gy + 1);
    local i = 1;
    until i > len {
        add bp_gn[i] to bp_tmp;
        i++;
    }
    if $which == 1 {
        bp_c1x = bp_gx;
        bp_c1y = bp_gy;
        delete bp_r1b;
        i = 1;
        until i > len {
            add bp_tmp[i] to bp_r1b;
            i++;
        }
    } else {
        bp_c2x = bp_gx;
        bp_c2y = bp_gy;
        delete bp_r2b;
        i = 1;
        until i > len {
            add bp_tmp[i] to bp_r2b;
            i++;
        }
    }
}

list bp_tmp;
list bp_tn;
list bp_td;

proc bp_crt {
    if bp_c1x != bp_c2x or bp_c1y != bp_c2y {
        bp_ok = false;
    } else {
        bp_gx = bp_c1x;
        bp_gy = bp_c1y;
        delete bp_gn;
        delete bp_gd;
        local inv = 0;
        bp_inv bp_p1, bp_p2;
        inv = bp_inv;
        local prod = bp_p1 * bp_p2;
        local len = (bp_gx + 1) * (bp_gy + 1);
        local i = 1;
        until i > len {
            local r1 = bp_r1b[i];
            local r2 = bp_r2b[i];
            local diff = bp_mod(r2 - r1, bp_p2);
            local t = bp_mod(diff * inv, bp_p2);
            local x = r1 + bp_p1 * t;
            if x > prod / 2 {
                x -= prod;
            }
            add x to bp_gn;
            add 1 to bp_gd;
            i++;
        }
    }
}

# Q dense division; quotient in bp_qn/bp_qd
var bp_qx = 0;
var bp_qy = 0;
list bp_qn;
list bp_qd;
list bp_rn;
list bp_rd;

proc bp_q_div target {
    local ax = bp_ax;
    local ay = bp_ay;
    if $target == 2 {
        ax = bp_bx;
        ay = bp_by;
    }
    if bp_gx > ax or bp_gy > ay {
        bp_ok = false;
    } else {
        bp_qx = ax - bp_gx;
        bp_qy = ay - bp_gy;
        delete bp_qn;
        delete bp_qd;
        delete bp_rn;
        delete bp_rd;
        local lenq = (bp_qx + 1) * (bp_qy + 1);
        local i = 1;
        until i > lenq {
            add 0 to bp_qn;
            add 1 to bp_qd;
            i++;
        }
        local lenr = (ax + 1) * (ay + 1);
        i = 1;
        until i > lenr {
            if $target == 1 {
                add bp_an[i] to bp_rn;
                add bp_ad[i] to bp_rd;
            } else {
                add bp_bn[i] to bp_rn;
                add bp_bd[i] to bp_rd;
            }
            i++;
        }
        local steps = 0;
        local ok = true;
        until steps > 400 or ok == false {
            local ri = -1;
            local rj = -1;
            local x = ax;
            until x < 0 or ri >= 0 {
                local y = ay;
                until y < 0 or ri >= 0 {
                    if bp_rn[x * (ay + 1) + y + 1] != 0 {
                        ri = x;
                        rj = y;
                    }
                    y--;
                }
                x--;
            }
            if ri < 0 {
                steps = 1000;
            } else {
                local gi = -1;
                local gj = -1;
                x = bp_gx;
                until x < 0 or gi >= 0 {
                    local y = bp_gy;
                    until y < 0 or gi >= 0 {
                        if bp_gn[x * (bp_gy + 1) + y + 1] != 0 {
                            gi = x;
                            gj = y;
                        }
                        y--;
                    }
                    x--;
                }
                if gi < 0 or ri < gi or rj < gj {
                    ok = false;
                } else {
                    local rnum = bp_rn[ri * (ay + 1) + rj + 1];
                    local rden = bp_rd[ri * (ay + 1) + rj + 1];
                    local gnum = bp_gn[gi * (bp_gy + 1) + gj + 1];
                    local gden = bp_gd[gi * (bp_gy + 1) + gj + 1];
                    rat_div rnum, rden, gnum, gden;
                    if rok == false {
                        ok = false;
                    } else {
                        local qn = rn;
                        local qd = rd;
                        local qi = ri - gi;
                        local qj = rj - gj;
                        bp_qn[qi * (bp_qy + 1) + qj + 1] = qn;
                        bp_qd[qi * (bp_qy + 1) + qj + 1] = qd;
                        local a = 0;
                        until a > bp_gx or ok == false {
                            local b = 0;
                            until b > bp_gy or ok == false {
                                local gv_n = bp_gn[a * (bp_gy + 1) + b + 1];
                                local gv_d = bp_gd[a * (bp_gy + 1) + b + 1];
                                if gv_n != 0 {
                                    rat_mul qn, qd, gv_n, gv_d;
                                    if rok == false {
                                        ok = false;
                                    } else {
                                        local ti = a + qi;
                                        local tj = b + qj;
                                        local idx = ti * (ay + 1) + tj + 1;
                                        rat_add bp_rn[idx], bp_rd[idx], -rn, rd;
                                        if rok == false {
                                            ok = false;
                                        } else {
                                            bp_rn[idx] = rn;
                                            bp_rd[idx] = rd;
                                        }
                                    }
                                }
                                b++;
                            }
                            a++;
                        }
                    }
                    steps++;
                }
            }
        }
        if ok == false {
            bp_ok = false;
        }
    }
}

# ---------- lcm and quotient output ----------

var bp_hx = 0;
var bp_hy = 0;
list bp_hn;
list bp_hd;

proc bp_q_mul {
    bp_hx = bp_ax + bp_bx;
    bp_hy = bp_ay + bp_by;
    delete bp_hn;
    delete bp_hd;
    local len = (bp_hx + 1) * (bp_hy + 1);
    local i = 1;
    until i > len {
        add 0 to bp_hn;
        add 1 to bp_hd;
        i++;
    }
    local ia = 0;
    until ia > bp_ax {
        local ja = 0;
        until ja > bp_ay {
            local an = bp_an[ia * (bp_ay + 1) + ja + 1];
            local ad = bp_ad[ia * (bp_ay + 1) + ja + 1];
            if an != 0 {
                local ib = 0;
                until ib > bp_bx {
                    local jb = 0;
                    until jb > bp_by {
                        local bn = bp_bn[ib * (bp_by + 1) + jb + 1];
                        local bd = bp_bd[ib * (bp_by + 1) + jb + 1];
                        if bn != 0 {
                            local hi = ia + ib;
                            local hj = ja + jb;
                            local idx = hi * (bp_hy + 1) + hj + 1;
                            rat_mul an, ad, bn, bd;
                            if rok == false {
                                bp_ok = false;
                            } else {
                                local pn = rn;
                                local pd = rd;
                                rat_add bp_hn[idx], bp_hd[idx], pn, pd;
                                if rok == false {
                                    bp_ok = false;
                                } else {
                                    bp_hn[idx] = rn;
                                    bp_hd[idx] = rd;
                                }
                            }
                        }
                        jb++;
                    }
                    ib++;
                }
            }
            ja++;
        }
        ia++;
    }
}

proc bp_q_monic {
    local gi = -1;
    local gj = -1;
    local i = bp_qx;
    until i < 0 or gi >= 0 {
        local j = bp_qy;
        until j < 0 or gi >= 0 {
            if bp_qn[i * (bp_qy + 1) + j + 1] != 0 {
                gi = i;
                gj = j;
            }
            j--;
        }
        i--;
    }
    if gi >= 0 {
        local lead_n = bp_qn[gi * (bp_qy + 1) + gj + 1];
        local lead_d = bp_qd[gi * (bp_qy + 1) + gj + 1];
        i = 0;
        until i > bp_qx {
            local j = 0;
            until j > bp_qy {
                local idx = i * (bp_qy + 1) + j + 1;
                if bp_qn[idx] != 0 {
                    rat_div bp_qn[idx], bp_qd[idx], lead_n, lead_d;
                    if rok == false {
                        bp_ok = false;
                    } else {
                        bp_qn[idx] = rn;
                        bp_qd[idx] = rd;
                    }
                }
                j++;
            }
            i++;
        }
    }
}

proc bp_q_to_ast {
    local sum = 0;
    local i = 0;
    until i > bp_qx {
        local j = 0;
        until j > bp_qy {
            local idx = i * (bp_qy + 1) + j + 1;
            if bp_qn[idx] != 0 {
                local cn = bp_qn[idx];
                local cd = bp_qd[idx];
                bp_term_ast i, j, cn, cd;
                local term = bp_term_ast;
                if sum == 0 {
                    sum = term;
                } else {
                    mk_add sum, term;
                    sum = mk_add;
                }
            }
            j++;
        }
        i++;
    }
    if sum == 0 {
        mk_num 0, 1;
        sum = mk_num;
    }
    bp_q_to_ast = sum;
}

proc bp_common_monomial {
    bp_cmx = 0;
    bp_cmy = 0;
    # min exponents of A
    local mxa = 0;
    local mya = 0;
    local first = true;
    local i = 0;
    until i > bp_ax {
        local j = 0;
        until j > bp_ay {
            if bp_an[i * (bp_ay + 1) + j + 1] != 0 {
                if first {
                    mxa = i; mya = j; first = false;
                } else {
                    if i < mxa { mxa = i; }
                    if j < mya { mya = j; }
                }
            }
            j++;
        }
        i++;
    }
    local mxb = 0;
    local myb = 0;
    first = true;
    i = 0;
    until i > bp_bx {
        local j = 0;
        until j > bp_by {
            if bp_bn[i * (bp_by + 1) + j + 1] != 0 {
                if first {
                    mxb = i; myb = j; first = false;
                } else {
                    if i < mxb { mxb = i; }
                    if j < myb { myb = j; }
                }
            }
            j++;
        }
        i++;
    }
    bp_cmx = mxa;
    if mxb < bp_cmx { bp_cmx = mxb; }
    bp_cmy = mya;
    if myb < bp_cmy { bp_cmy = myb; }
}

proc bp_multiply_missing_monomial {
    local gmx = 1000;
    local gmy = 1000;
    local any = false;
    local i = 0;
    until i > bp_gx {
        local j = 0;
        until j > bp_gy {
            if bp_gn[i * (bp_gy + 1) + j + 1] != 0 {
                if any == false {
                    gmx = i; gmy = j; any = true;
                } else {
                    if i < gmx { gmx = i; }
                    if j < gmy { gmy = j; }
                }
            }
            j++;
        }
        i++;
    }
    local ax = 0;
    local ay = 0;
    if bp_cmx > gmx { ax = bp_cmx - gmx; }
    if bp_cmy > gmy { ay = bp_cmy - gmy; }
    if ax > 0 or ay > 0 {
        local nx = bp_gx + ax;
        local ny = bp_gy + ay;
        delete bp_tn;
        delete bp_td;
        local len = (nx + 1) * (ny + 1);
        i = 1;
        until i > len {
            add 0 to bp_tn;
            add 1 to bp_td;
            i++;
        }
        i = 0;
        until i > bp_gx {
            local j = 0;
            until j > bp_gy {
                local n = bp_gn[i * (bp_gy + 1) + j + 1];
                if n != 0 {
                    local ni = i + ax;
                    local nj = j + ay;
                    bp_tn[ni * (ny + 1) + nj + 1] = n;
                    bp_td[ni * (ny + 1) + nj + 1] = bp_gd[i * (bp_gy + 1) + j + 1];
                }
                j++;
            }
            i++;
        }
        delete bp_gn;
        delete bp_gd;
        i = 1;
        until i > len {
            add bp_tn[i] to bp_gn;
            add bp_td[i] to bp_gd;
            i++;
        }
        bp_gx = nx;
        bp_gy = ny;
    }
}

proc bp_gcd_q {
    local need = bp_ax;
    if bp_bx > need { need = bp_bx; }
    need++;
    bp_mod_gcd_candidate bp_p1, need;
if bp_ok == false { bp_ok = false; } else {
        bp_save_candidate 1;
        bp_mod_gcd_candidate bp_p2, need;
if bp_ok == false { bp_ok = false; } else {
            bp_save_candidate 2;
            bp_crt;
            if bp_ok == false { bp_ok = false; } else {
                bp_multiply_missing_monomial;
                bp_q_div 1;
                if bp_ok == false { bp_ok = false; } else {
                    bp_q_div 2;
                }
            }
        }
    }
}

proc bp_h_to_a {
    delete bp_an;
    delete bp_ad;
    local i = 1;
    until i > length(bp_hn) {
        add bp_hn[i] to bp_an;
        add bp_hd[i] to bp_ad;
        i++;
    }
    bp_ax = bp_hx;
    bp_ay = bp_hy;
}

# ---------- fraction cancellation ----------

list frac_facs;
list frac_num;
list frac_den;
list frac_stk;
list frac_nums;
list frac_dens;

proc frac_flatten root {
    delete frac_facs;
    delete frac_stk;
    local sp = 0;
    sp++;
    add $root to frac_stk;
    until sp == 0 {
        local x = frac_stk[sp];
        sp--;
        if nd_kind[x] == K.Mul {
            sp++;
            if sp > length(frac_stk) { add nd_b[x] to frac_stk; } else { frac_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(frac_stk) { add nd_a[x] to frac_stk; } else { frac_stk[sp] = nd_a[x]; }
        } else {
            add x to frac_facs;
        }
    }
}

proc frac_build_num {
    if length(frac_nums) == 0 {
        mk_num 1, 1;
        frac_build_num = mk_num;
    } else {
        local out = frac_nums[1];
        local i = 2;
        until i > length(frac_nums) {
            mk_mul out, frac_nums[i];
            out = mk_mul;
            i++;
        }
        frac_build_num = out;
    }
}

proc frac_build_den {
    if length(frac_dens) == 0 {
        mk_num 1, 1;
        frac_build_den = mk_num;
    } else {
        local out = frac_dens[1];
        local i = 2;
        until i > length(frac_dens) {
            mk_mul out, frac_dens[i];
            out = mk_mul;
            i++;
        }
        frac_build_den = out;
    }
}

proc tcf_exact na, da {
    tcf_exact = 0;
    poly_reset;
    collect_vars_ast $na;
    collect_vars_ast $da;
    if pv_count == 1 {
        poly_from_ast $na;
        local pp = poly_from_ast;
        poly_from_ast $da;
        local qq = poly_from_ast;
        local maxd = 0;
        local t = 1;
        until t > pt_count {
            if pt_poly[t] == pp or pt_poly[t] == qq {
                if pt_exp[(t - 1) * pv_count + 1] > maxd { maxd = pt_exp[(t - 1) * pv_count + 1]; }
            }
            t++;
        }
        local base = maxd + 1;
        upoly_from_poly pp, base;
        local ua = upoly_from_poly;
        upoly_from_poly qq, base;
        local ub = upoly_from_poly;
        if ua != 0 and ub != 0 {
            upoly_exact_quot ua, ub;
            if upoly_exact_quot != 0 {
                upoly_to_poly upoly_exact_quot, base;
                poly_to_ast upoly_to_poly;
                tcf_exact = poly_to_ast;
            }
        }
    }
}

proc try_cancel_fraction root {
    if nd_kind[$root] != K.Mul {
        try_cancel_fraction = 0;
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
            try_cancel_fraction = 0;
        } else {
            frac_build_num; local na = frac_build_num;
            frac_build_den; local da = frac_build_den;
            tcf_exact = 0;
            if bp_ax > 4 or bp_bx > 4 { tcf_exact na, da; }
            if tcf_exact != 0 {
                try_cancel_fraction = tcf_exact;
                simp_exact = true;
            } else {
            bp_begin na, da;
            if bp_ok == false {
                try_cancel_fraction = 0;
            } else {
                bp_dgy = bp_ay;
                if bp_by < bp_dgy { bp_dgy = bp_by; }
                bp_gcd_q;
                if bp_ok == false {
                    try_cancel_fraction = 0;
                } elif bp_gx == 0 and bp_gy == 0 and bp_gn[1] == 1 and bp_gd[1] == 1 {
                    try_cancel_fraction = 0;
                } else {
                    bp_q_div 1;
                    if bp_ok == false {
                        try_cancel_fraction = 0;
                    } else {
                        bp_q_to_ast; local nq = bp_q_to_ast;
                        bp_q_div 2;
                        if bp_ok == false {
                            try_cancel_fraction = 0;
                        } else {
                            bp_q_to_ast; local dq = bp_q_to_ast;
                            if nd_kind[dq] == K.Num and nd_num[dq] == 1 and nd_den[dq] == 1 {
                                try_cancel_fraction = nq;
                            } else {
                                mk_pow dq, -1;
                                mk_mul nq, mk_pow;
                                try_cancel_fraction = mk_mul;
                            }
                        }
                    }
                }
            }
        }
    }
            }
}
