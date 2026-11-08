# Sparse multivariate polynomials over Q, with a Kronecker-based gcd.
# Terms are records in parallel flat arrays; polynomial IDs group terms.
# This module is deliberately independent of the AST arena.

var pv_count = 0;
list pv_name;

var pt_count = 0;
list pt_poly;
list pt_n;
list pt_d;
list pt_exp;

var poly_count = 0;
var poly_ok = true;
list poly_mono_exp;

var pdiv_ok = false;

var up_count = 0;
list up_start;
list up_len;
list uc_n;
list uc_d;

var up_max_kron = 40000;
var up_max_terms = 4000;

var u_len = 0;
var u_da = 0;
var u_db = 0;
var u_dr = 0;
list u_an;
list u_ad;
list u_bn;
list u_bd;
list u_rn;
list u_rd;

proc poly_reset {
    delete pv_name;
    pv_count = 0;
    delete pt_poly;
    delete pt_n;
    delete pt_d;
    delete pt_exp;
    pt_count = 0;
    poly_count = 0;
    poly_ok = true;
    delete poly_mono_exp;
    delete up_start;
    delete up_len;
    delete uc_n;
    delete uc_d;
    up_count = 0;
    pdiv_ok = false;
}

proc pv_add name {
    local nm = norm_ident($name);
    local i = 1;
    local found = false;
    until i > pv_count or found {
        if pv_name[i] == nm {
            found = true;
        } else {
            i++;
        }
    }
    if found == false {
        pv_count++;
        add nm to pv_name;
    }
}

proc collect_vars_ast root {
    delete poly_vars_stk;
    local sp = 0;
    sp++;
    add $root to poly_vars_stk;
    until sp == 0 {
        local x = poly_vars_stk[sp];
        sp--;
        if nd_kind[x] == K.Var {
            pv_add nd_txt[x];
        } elif nd_kind[x] == K.Add or nd_kind[x] == K.Mul or nd_kind[x] == K.PowE {
            sp++;
            if sp > length(poly_vars_stk) {
                add nd_b[x] to poly_vars_stk;
            } else {
                poly_vars_stk[sp] = nd_b[x];
            }
            sp++;
            if sp > length(poly_vars_stk) {
                add nd_a[x] to poly_vars_stk;
            } else {
                poly_vars_stk[sp] = nd_a[x];
            }
        } elif nd_kind[x] == K.Pow {
            sp++;
            if sp > length(poly_vars_stk) {
                add nd_a[x] to poly_vars_stk;
            } else {
                poly_vars_stk[sp] = nd_a[x];
            }
        } elif nd_kind[x] >= K.Sin and nd_kind[x] <= K.Atan {
            sp++;
            if sp > length(poly_vars_stk) {
                add nd_a[x] to poly_vars_stk;
            } else {
                poly_vars_stk[sp] = nd_a[x];
            }
        }
    }
    # insertion sort variable names
    local i = 2;
    until i > pv_count {
        local x = pv_name[i];
        local j = i;
        until j <= 1 or pv_name[j - 1] <= x {
            pv_name[j] = pv_name[j - 1];
            j--;
        }
        pv_name[j] = x;
        i++;
    }
}

list poly_vars_stk;

func pv_index(name) {
    local i = 1;
    until i > pv_count {
        if pv_name[i] == $name {
            return i;
        }
        i++;
    }
    return 0;
}

func pexp(t, v) {
    if pv_count == 0 {
        return 0;
    }
    return pt_exp[($t - 1) * pv_count + $v];
}

proc poly_new {
    poly_count++;
    poly_new = poly_count;
}

proc poly_add_mono pid, n, d {
    if $n == 0 {
        poly_add_mono = 0;
    } elif pt_count >= up_max_terms {
        poly_ok = false;
        poly_add_mono = 0;
    } else {
        local found = 0;
        local i = 1;
        until i > pt_count or found != 0 {
            if pt_poly[i] == $pid {
                local same = true;
                local v = 1;
                until v > pv_count or same == false {
                    if pt_exp[(i - 1) * pv_count + v] != poly_mono_exp[v] {
                        same = false;
                    } else {
                        v++;
                    }
                }
                if same {
                    found = i;
                }
            }
            i++;
        }
        if found > 0 {
            rat_add pt_n[found], pt_d[found], $n, $d;
            if rok == false {
                poly_ok = false;
            } elif rn == 0 {
                pt_poly[found] = 0;
            } else {
                pt_n[found] = rn;
                pt_d[found] = rd;
            }
        } else {
            pt_count++;
            add $pid to pt_poly;
            add $n to pt_n;
            add $d to pt_d;
            local v = 1;
            until v > pv_count {
                add poly_mono_exp[v] to pt_exp;
                v++;
            }
        }
        poly_add_mono = 0;
    }
}

proc poly_add_term pid, src {
    local v = 1;
    until v > pv_count {
        poly_mono_exp[v] = pt_exp[($src - 1) * pv_count + v];
        v++;
    }
    poly_add_mono $pid, pt_n[$src], pt_d[$src];
}

proc poly_add p, q {
    poly_new;
    local out = poly_new;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            poly_add_term out, t;
        }
        t++;
    }
    t = 1;
    until t > pt_count {
        if pt_poly[t] == $q {
            poly_add_term out, t;
        }
        t++;
    }
    poly_add = out;
}

proc poly_sub p, q {
    poly_new;
    local out = poly_new;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            poly_add_term out, t;
        }
        t++;
    }
    t = 1;
    until t > pt_count {
        if pt_poly[t] == $q {
            local v = 1;
            until v > pv_count {
                poly_mono_exp[v] = pt_exp[(t - 1) * pv_count + v];
                v++;
            }
            poly_add_mono out, -pt_n[t], pt_d[t];
        }
        t++;
    }
    poly_sub = out;
}

proc poly_copy p {
    poly_new;
    local out = poly_new;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            poly_add_term out, t;
        }
        t++;
    }
    poly_copy = out;
}

proc poly_const n, d {
    poly_new;
    local out = poly_new;
    local v = 1;
    until v > pv_count {
        poly_mono_exp[v] = 0;
        v++;
    }
    poly_add_mono out, $n, $d;
    poly_const = out;
}

proc poly_var idx {
    poly_new;
    local out = poly_new;
    local v = 1;
    until v > pv_count {
        poly_mono_exp[v] = 0;
        v++;
    }
    poly_mono_exp[$idx] = 1;
    poly_add_mono out, 1, 1;
    poly_var = out;
}

proc poly_mul p, q {
    poly_new;
    local out = poly_new;
    local i = 1;
    until i > pt_count or poly_ok == false {
        if pt_poly[i] == $p {
            local j = 1;
            until j > pt_count or poly_ok == false {
                if pt_poly[j] == $q {
                    local v = 1;
                    until v > pv_count {
                        poly_mono_exp[v] = pt_exp[(i - 1) * pv_count + v] + pt_exp[(j - 1) * pv_count + v];
                        v++;
                    }
                    rat_mul pt_n[i], pt_d[i], pt_n[j], pt_d[j];
                    if rok == false {
                        poly_ok = false;
                    } else {
                        poly_add_mono out, rn, rd;
                    }
                }
                j++;
            }
        }
        i++;
    }
    poly_mul = out;
}

proc poly_pow p, e {
    poly_const 1, 1;
    local out = poly_const;
    local i = 1;
    until i > $e or poly_ok == false {
        poly_mul out, $p;
        out = poly_mul;
        i++;
    }
    poly_pow = out;
}

func poly_is_zero(p) {
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p and pt_n[t] != 0 {
            return false;
        }
        t++;
    }
    return true;
}

func poly_is_one(p) {
    local count = 0;
    local t = 1;
    local ok = true;
    until t > pt_count {
        if pt_poly[t] == $p and pt_n[t] != 0 {
            count++;
            if pt_n[t] != 1 or pt_d[t] != 1 {
                ok = false;
            }
            local v = 1;
            until v > pv_count {
                if pt_exp[(t - 1) * pv_count + v] != 0 {
                    ok = false;
                }
                v++;
            }
        }
        t++;
    }
    return ok and count == 1;
}

func poly_max_deg(p) {
    local d = 0;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            local v = 1;
            until v > pv_count {
                local e = pt_exp[(t - 1) * pv_count + v];
                if e > d {
                    d = e;
                }
                v++;
            }
        }
        t++;
    }
    return d;
}

func poly_leading(p) {
    local best = 0;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p and pt_n[t] != 0 {
            if best == 0 {
                best = t;
            } else {
                local deciding = true;
                local v = 1;
                until v > pv_count or deciding == false {
                    local a = pt_exp[(t - 1) * pv_count + v];
                    local b = pt_exp[(best - 1) * pv_count + v];
                    if a > b {
                        best = t;
                        deciding = false;
                    } elif a < b {
                        deciding = false;
                    } else {
                        v++;
                    }
                }
            }
        }
        t++;
    }
    return best;
}

func poly_mono_divides(a, b) {
    local v = 1;
    until v > pv_count {
        if pt_exp[($a - 1) * pv_count + v] > pt_exp[($b - 1) * pv_count + v] {
            return false;
        }
        v++;
    }
    return true;
}

proc poly_div_exact a, b {
    pdiv_ok = false;
    if poly_is_zero($b) or poly_ok == false {
        poly_div_exact = 0;
    } else {
        poly_copy $a;
        local rem = poly_copy;
        poly_new;
        local quo = poly_new;
        local steps = 0;
        local ok = true;
        until poly_is_zero(rem) or ok == false or steps > 400 or poly_ok == false {
            local lt_r = poly_leading(rem);
            local lt_b = poly_leading($b);
            if lt_r == 0 or lt_b == 0 or poly_mono_divides(lt_b, lt_r) == false {
                ok = false;
            } else {
                local v = 1;
                until v > pv_count {
                    poly_mono_exp[v] = pt_exp[(lt_r - 1) * pv_count + v] - pt_exp[(lt_b - 1) * pv_count + v];
                    v++;
                }
                rat_div pt_n[lt_r], pt_d[lt_r], pt_n[lt_b], pt_d[lt_b];
                if rok == false {
                    ok = false;
                } else {
                    local qn = rn;
                    local qd = rd;
                    poly_add_mono quo, qn, qd;
                    poly_new;
                    local prod = poly_new;
                    local t = 1;
                    until t > pt_count or poly_ok == false {
                        if pt_poly[t] == $b {
                            local w = 1;
                            until w > pv_count {
                                poly_mono_exp[w] = pt_exp[(t - 1) * pv_count + w] + pt_exp[(lt_r - 1) * pv_count + w] - pt_exp[(lt_b - 1) * pv_count + w];
                                w++;
                            }
                            rat_mul qn, qd, pt_n[t], pt_d[t];
                            if rok == false {
                                poly_ok = false;
                            } else {
                                poly_add_mono prod, rn, rd;
                            }
                        }
                        t++;
                    }
                    poly_sub rem, prod;
                    rem = poly_sub;
                    steps++;
                }
            }
        }
        if poly_is_zero(rem) and poly_ok {
            pdiv_ok = true;
        }
        poly_div_exact = quo;
    }
}

proc poly_monic p {
    local lt = poly_leading($p);
    if lt == 0 {
        poly_const 0, 1;
        poly_monic = poly_const;
    } else {
        poly_new;
        local out = poly_new;
        local t = 1;
        until t > pt_count or poly_ok == false {
            if pt_poly[t] == $p and pt_n[t] != 0 {
                local v = 1;
                until v > pv_count {
                    poly_mono_exp[v] = pt_exp[(t - 1) * pv_count + v];
                    v++;
                }
                rat_div pt_n[t], pt_d[t], pt_n[lt], pt_d[lt];
                if rok == false {
                    poly_ok = false;
                } else {
                    poly_add_mono out, rn, rd;
                }
            }
            t++;
        }
        poly_monic = out;
    }
}

proc poly_strip_monomial p {
    local min_e = 0;
    local have = false;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p and pt_n[t] != 0 {
            if have == false {
                min_e = 0;
                # store mins in a scratch list
                delete poly_min_exp;
                local v = 1;
                until v > pv_count {
                    add pt_exp[(t - 1) * pv_count + v] to poly_min_exp;
                    v++;
                }
                have = true;
            } else {
                local v = 1;
                until v > pv_count {
                    local e = pt_exp[(t - 1) * pv_count + v];
                    if e < poly_min_exp[v] {
                        poly_min_exp[v] = e;
                    }
                    v++;
                }
            }
        }
        t++;
    }
    if have == false {
        poly_strip_monomial = $p;
    } else {
        local all_zero = true;
        local v = 1;
        until v > pv_count {
            if poly_min_exp[v] != 0 {
                all_zero = false;
            }
            v++;
        }
        if all_zero {
            poly_strip_monomial = $p;
        } else {
            poly_new;
            local out = poly_new;
            t = 1;
            until t > pt_count {
                if pt_poly[t] == $p and pt_n[t] != 0 {
                    v = 1;
                    until v > pv_count {
                        poly_mono_exp[v] = pt_exp[(t - 1) * pv_count + v] - poly_min_exp[v];
                        v++;
                    }
                    poly_add_mono out, pt_n[t], pt_d[t];
                }
                t++;
            }
            poly_strip_monomial = out;
        }
    }
}

list poly_min_exp;

# ---------- univariate dense polynomials ----------

proc upoly_new len {
    local start = length(uc_n) + 1;
    local i = 1;
    until i > $len {
        add 0 to uc_n;
        add 1 to uc_d;
        i++;
    }
    up_count++;
    add start to up_start;
    add $len to up_len;
    upoly_new = up_count;
}

func up_n(id, i) {
    return uc_n[up_start[$id] + $i];
}

func up_d(id, i) {
    return uc_d[up_start[$id] + $i];
}

proc up_set id, i, vn, vd {
    uc_n[up_start[$id] + $i] = $vn;
    uc_d[up_start[$id] + $i] = $vd;
}

proc upoly_trim id {
    local l = up_len[$id];
    until l <= 1 or uc_n[up_start[$id] + l - 1] != 0 {
        l--;
    }
    up_len[$id] = l;
}

proc upoly_copy id {
    upoly_new up_len[$id];
    local out = upoly_new;
    local i = 0;
    until i >= up_len[$id] {
        up_set out, i, uc_n[up_start[$id] + i], uc_d[up_start[$id] + i];
        i++;
    }
    upoly_copy = out;
}

func upoly_is_zero(id) {
    local i = 0;
    until i >= up_len[$id] {
        if uc_n[up_start[$id] + i] != 0 {
            return false;
        }
        i++;
    }
    return true;
}

func upoly_deg(id) {
    local l = up_len[$id];
    until l <= 1 or uc_n[up_start[$id] + l - 1] != 0 {
        l--;
    }
    return l - 1;
}

proc upoly_div_rem a, b {
    upoly_copy $a;
    local rem = upoly_copy;
    local db = upoly_deg($b);
    local lbn = up_n($b, db);
    local lbd = up_d($b, db);
    local steps = 0;
    local ok = true;
    until upoly_deg(rem) < db or upoly_is_zero(rem) or ok == false or steps > 400 {
        local dr = upoly_deg(rem);
        local cur_n = up_n(rem, dr);
        local cur_d = up_d(rem, dr);
        rat_div cur_n, cur_d, lbn, lbd;
        if rok == false {
            ok = false;
        } else {
            local f_n = rn;
            local f_d = rd;
            local shift = dr - db;
            local i = 0;
            until i > db {
                local bi_n = up_n($b, i);
                local bi_d = up_d($b, i);
                rat_mul f_n, f_d, bi_n, bi_d;
                if rok == false {
                    ok = false;
                } else {
                    local j = i + shift;
                    rat_add up_n(rem, j), up_d(rem, j), -rn, rd;
                    if rok == false {
                        ok = false;
                    } else {
                        up_set rem, j, rn, rd;
                    }
                }
                i++;
            }
            upoly_trim rem;
            steps++;
        }
    }
    if ok == false {
        poly_ok = false;
    }
    upoly_div_rem = rem;
}

proc upoly_exact_quot a, b {
    upoly_copy $a;
    local rem = upoly_copy;
    local db = upoly_deg($b);
    local lbn = up_n($b, db);
    local lbd = up_d($b, db);
    local qlen = upoly_deg($a) - db + 1;
    if qlen < 1 { qlen = 1; }
    upoly_new qlen;
    local q = upoly_new;
    local steps = 0;
    local ok = true;
    until upoly_is_zero(rem) or upoly_deg(rem) < db or ok == false or steps > 400 {
        local dr = upoly_deg(rem);
        local cur_n = up_n(rem, dr);
        local cur_d = up_d(rem, dr);
        rat_div cur_n, cur_d, lbn, lbd;
        if rok == false {
            ok = false;
        } else {
            local f_n = rn;
            local f_d = rd;
            local shift = dr - db;
            up_set q, shift, f_n, f_d;
            local i = 0;
            until i > db {
                local bi_n = up_n($b, i);
                local bi_d = up_d($b, i);
                rat_mul f_n, f_d, bi_n, bi_d;
                if rok == false {
                    ok = false;
                } else {
                    local j = i + shift;
                    rat_add up_n(rem, j), up_d(rem, j), -rn, rd;
                    if rok == false {
                        ok = false;
                    } else {
                        up_set rem, j, rn, rd;
                    }
                }
                i++;
            }
            upoly_trim rem;
            steps++;
        }
    }
    if ok and upoly_is_zero(rem) {
        upoly_exact_quot = q;
    } else {
        upoly_exact_quot = 0;
    }
}

proc upoly_monic id {
    local d = upoly_deg($id);
    local lead_n = up_n($id, d);
    local lead_d = up_d($id, d);
    local i = 0;
    until i > d {
        rat_div up_n($id, i), up_d($id, i), lead_n, lead_d;
        if rok == false {
            poly_ok = false;
        } else {
            up_set $id, i, rn, rd;
        }
        i++;
    }
    upoly_monic = $id;
}

proc upoly_gcd a, b {
    upoly_copy $a;
    local x = upoly_copy;
    upoly_copy $b;
    local y = upoly_copy;
    local steps = 0;
    until upoly_is_zero(y) or steps > 200 or poly_ok == false {
        upoly_div_rem x, y;
        x = y;
        y = upoly_div_rem;
        steps++;
    }
    upoly_monic x;
    upoly_gcd = upoly_monic;
}

proc upoly_from_poly p, base {
    local b = $base;
    local maxcode = 0;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            local code = 0;
            local pw = 1;
            local v = 1;
            until v > pv_count {
                code += pt_exp[(t - 1) * pv_count + v] * pw;
                pw *= b;
                v++;
            }
            if code > maxcode {
                maxcode = code;
            }
        }
        t++;
    }
    if maxcode > up_max_kron {
        poly_ok = false;
        upoly_from_poly = 0;
    } else {
        upoly_new maxcode + 1;
        local out = upoly_new;
        t = 1;
        until t > pt_count {
            if pt_poly[t] == $p {
                local code = 0;
                local pw = 1;
                local v = 1;
                until v > pv_count {
                    code += pt_exp[(t - 1) * pv_count + v] * pw;
                    pw *= b;
                    v++;
                }
                rat_add up_n(out, code), up_d(out, code), pt_n[t], pt_d[t];
                if rok == false {
                    poly_ok = false;
                } else {
                    up_set out, code, rn, rd;
                }
            }
            t++;
        }
        upoly_from_poly = out;
    }
}

proc upoly_to_poly id, base {
    poly_new;
    local out = poly_new;
    local b = $base;
    local i = 0;
    until i >= up_len[$id] {
        if up_n($id, i) != 0 {
            local code = i;
            local v = 1;
            until v > pv_count {
                poly_mono_exp[v] = code % b;
                code = code / b;
                v++;
            }
            poly_add_mono out, up_n($id, i), up_d($id, i);
        }
        i++;
    }
    upoly_to_poly = out;
}

proc u_reset len {
    delete u_an;
    delete u_ad;
    delete u_bn;
    delete u_bd;
    delete u_rn;
    delete u_rd;
    u_len = $len;
    local i = 1;
    until i > $len {
        add 0 to u_an;
        add 1 to u_ad;
        add 0 to u_bn;
        add 1 to u_bd;
        add 0 to u_rn;
        add 1 to u_rd;
        i++;
    }
    u_da = -1;
    u_db = -1;
    u_dr = -1;
}

proc u_trim_r {
    local d = u_len - 1;
    until d < 0 or u_rn[d + 1] != 0 {
        d--;
    }
    u_dr = d;
}

proc u_load_a p, base {
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            local code = 0;
            local pw = 1;
            local v = 1;
            until v > pv_count {
                code += pt_exp[(t - 1) * pv_count + v] * pw;
                pw *= $base;
                v++;
            }
            rat_add u_an[code + 1], u_ad[code + 1], pt_n[t], pt_d[t];
            if rok == false {
                poly_ok = false;
            } else {
                u_an[code + 1] = rn;
                u_ad[code + 1] = rd;
            }
        }
        t++;
    }
    local d = u_len - 1;
    until d < 0 or u_an[d + 1] != 0 {
        d--;
    }
    u_da = d;
}

proc u_load_b p, base {
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            local code = 0;
            local pw = 1;
            local v = 1;
            until v > pv_count {
                code += pt_exp[(t - 1) * pv_count + v] * pw;
                pw *= $base;
                v++;
            }
            rat_add u_bn[code + 1], u_bd[code + 1], pt_n[t], pt_d[t];
            if rok == false {
                poly_ok = false;
            } else {
                u_bn[code + 1] = rn;
                u_bd[code + 1] = rd;
            }
        }
        t++;
    }
    local d = u_len - 1;
    until d < 0 or u_bn[d + 1] != 0 {
        d--;
    }
    u_db = d;
}

proc u_rem {
    local i = 1;
    until i > u_len {
        u_rn[i] = u_an[i];
        u_rd[i] = u_ad[i];
        i++;
    }
    u_dr = u_da;
    if u_db < 0 {
        poly_ok = false;
    } else {
        local lgn = u_bn[u_db + 1];
        local lgd = u_bd[u_db + 1];
        local steps = 0;
        until u_dr < u_db or u_dr < 0 or steps > 400 or poly_ok == false {
            local rn0 = u_rn[u_dr + 1];
            local rd0 = u_rd[u_dr + 1];
            rat_div rn0, rd0, lgn, lgd;
            if rok == false {
                poly_ok = false;
            } else {
                local fn = rn;
                local fd = rd;
                local shift = u_dr - u_db;
                local j = 0;
                until j > u_db {
                    rat_mul fn, fd, u_bn[j + 1], u_bd[j + 1];
                    if rok == false {
                        poly_ok = false;
                    } else {
                        local k = j + shift;
                        rat_add u_rn[k + 1], u_rd[k + 1], -rn, rd;
                        if rok == false {
                            poly_ok = false;
                        } else {
                            u_rn[k + 1] = rn;
                            u_rd[k + 1] = rd;
                        }
                    }
                    j++;
                }
                u_trim_r;
                steps++;
            }
        }
    }
}

proc u_copy_b_to_a {
    local i = 1;
    until i > u_len {
        u_an[i] = u_bn[i];
        u_ad[i] = u_bd[i];
        i++;
    }
    u_da = u_db;
}

proc u_copy_r_to_b {
    local i = 1;
    until i > u_len {
        u_bn[i] = u_rn[i];
        u_bd[i] = u_rd[i];
        i++;
    }
    u_db = u_dr;
}

proc u_normalize_a {
    if u_da >= 0 {
        local lgn = u_an[u_da + 1];
        local lgd = u_ad[u_da + 1];
        local i = 0;
        until i > u_da or poly_ok == false {
            rat_div u_an[i + 1], u_ad[i + 1], lgn, lgd;
            if rok == false {
                poly_ok = false;
            } else {
                u_an[i + 1] = rn;
                u_ad[i + 1] = rd;
            }
            i++;
        }
    }
}

proc u_to_poly base {
    poly_new;
    local out = poly_new;
    local i = 0;
    until i > u_da {
        if u_an[i + 1] != 0 {
            local code = i;
            local v = 1;
            until v > pv_count {
                poly_mono_exp[v] = code % $base;
                code = code / $base;
                v++;
            }
            poly_add_mono out, u_an[i + 1], u_ad[i + 1];
        }
        i++;
    }
    u_to_poly = out;
}

func poly_max_code(p, base) {
    local mx = 0;
    local t = 1;
    until t > pt_count {
        if pt_poly[t] == $p {
            local code = 0;
            local pw = 1;
            local v = 1;
            until v > pv_count {
                code += pt_exp[(t - 1) * pv_count + v] * pw;
                pw *= $base;
                v++;
            }
            if code > mx {
                mx = code;
            }
        }
        t++;
    }
    return mx;
}

func poly_divides_both(p, q, g) {
    local ok = false;
    poly_div_exact $p, $g;
    if pdiv_ok {
        poly_div_exact $q, $g;
        ok = pdiv_ok;
    }
    return ok;
}

proc poly_shift p, vi, c {
    poly_new;
    local out = poly_new;
    local t = 1;
    until t > pt_count or poly_ok == false {
        if pt_poly[t] == $p and pt_n[t] != 0 {
            local e = pt_exp[(t - 1) * pv_count + $vi];
            local k = 0;
            local bin = 1;
            until k > e or poly_ok == false {
                # bin = C(e,k) * c^(e-k)
                local v = 1;
                until v > pv_count {
                    poly_mono_exp[v] = pt_exp[(t - 1) * pv_count + v];
                    v++;
                }
                poly_mono_exp[$vi] = k;
                rat_mul pt_n[t], pt_d[t], bin, 1;
                if rok == false {
                    poly_ok = false;
                } else {
                    poly_add_mono out, rn, rd;
                }
                # update bin for next k: C(e,k+1)c^(e-k-1)
                if k < e {
                    local num = e - k;
                    # bin * num / (k+1)
                    local bn = bin * num;
                    local bd = k + 1;
                    if abs(bn) > MAX_SAFE {
                        poly_ok = false;
                    } else {
                        bin = bn / bd;
                        # multiply by c for the c^(e-k-1) factor
                        bin = bin * $c;
                        if abs(bin) > MAX_SAFE {
                            poly_ok = false;
                        }
                    }
                }
                k++;
            }
        }
        t++;
    }
    poly_shift = out;
}

proc poly_gcd_via_kron p, q {
    local d = poly_max_deg($p);
    local d2 = poly_max_deg($q);
    if d2 > d {
        d = d2;
    }
    local base = d + 1;
    if base < 2 {
        base = 2;
    }
    local attempts = 0;
    local result = 0;
    until attempts >= 3 or result != 0 or poly_ok == false {
        local c1 = poly_max_code($p, base);
        local c2 = poly_max_code($q, base);
        local maxcode = c1;
        if c2 > maxcode {
            maxcode = c2;
        }
        if maxcode > up_max_kron {
            poly_ok = false;
            result = 0;
        } else {
            u_reset maxcode + 1;
            u_load_a $p, base;
            u_load_b $q, base;
            local gsteps = 0;
            until u_db < 0 or gsteps > 200 or poly_ok == false {
                u_rem;
                u_copy_b_to_a;
                u_copy_r_to_b;
                gsteps++;
            }
            u_normalize_a;
            u_to_poly base;
            local cand = u_to_poly;
            poly_strip_monomial cand;
            local stripped = poly_strip_monomial;
            poly_monic stripped;
            stripped = poly_monic;
            if stripped != 0 and poly_divides_both($p, $q, stripped) {
                result = stripped;
            } else {
                poly_monic cand;
                cand = poly_monic;
                if poly_divides_both($p, $q, cand) {
                    result = cand;
                }
            }
        }
        base++;
        attempts++;
    }
    poly_gcd_via_kron = result;
}

proc poly_gcd p, q {
    if poly_ok == false {
        poly_gcd = 0;
    } elif poly_is_zero($p) {
        poly_monic $q;
        poly_gcd = poly_monic;
    } elif poly_is_zero($q) {
        poly_monic $p;
        poly_gcd = poly_monic;
    } else {
        poly_gcd_via_kron $p, $q;
        if poly_gcd_via_kron == 0 {
            set_err "多项式 gcd 计算失败";
            poly_gcd = 0;
        } else {
            poly_gcd = poly_gcd_via_kron;
        }
    }
}

proc poly_lcm p, q {
    poly_gcd $p, $q;
    local g = poly_gcd;
    if g == 0 or poly_ok == false {
        poly_lcm = 0;
    } else {
        poly_mul $p, $q;
        local prod = poly_mul;
        poly_div_exact prod, g;
        if pdiv_ok == false {
            set_err "多项式 lcm 除法失败";
            poly_lcm = 0;
        } else {
            poly_monic poly_div_exact;
            poly_lcm = poly_monic;
        }
    }
}

proc poly_to_ast p {
    local sum = 0;
    local t = 1;
    until t > pt_count or err != "" {
        if pt_poly[t] == $p and pt_n[t] != 0 {
            local mono = 0;
            local v = 1;
            until v > pv_count {
                local e = pt_exp[(t - 1) * pv_count + v];
                if e > 0 {
                    mk_var pv_name[v];
                    local vnode = mk_var;
                    mk_pow vnode, e;
                    local fac = mk_pow;
                    if mono == 0 {
                        mono = fac;
                    } else {
                        mk_mul mono, fac;
                        mono = mk_mul;
                    }
                }
                v++;
            }
            local term = mono;
            if pt_n[t] != 1 or pt_d[t] != 1 {
                mk_num pt_n[t], pt_d[t];
                local c = mk_num;
                if mono == 0 {
                    term = c;
                } else {
                    mk_mul c, mono;
                    term = mk_mul;
                }
            } elif mono == 0 {
                mk_num pt_n[t], pt_d[t];
                term = mk_num;
            }
            if sum == 0 {
                sum = term;
            } else {
                mk_add sum, term;
                sum = mk_add;
            }
        }
        t++;
    }
    if sum == 0 {
        mk_num 0, 1;
        sum = mk_num;
    }
    poly_to_ast = sum;
}

proc poly_from_ast root {
    poly_ok = true;
    delete poly_mono_exp;
    local z = 1;
    until z > pv_count {
        add 0 to poly_mono_exp;
        z++;
    }
    delete poly_ast_val;
    local i = 1;
    until i > node_count {
        add 0 to poly_ast_val;
        i++;
    }
    delete poly_ast_stk_node;
    delete poly_ast_stk_state;
    local sp = 0;
    sp++;
    add $root to poly_ast_stk_node;
    add 0 to poly_ast_stk_state;
    until sp == 0 or poly_ok == false or err != "" {
        local n = poly_ast_stk_node[sp];
        local st = poly_ast_stk_state[sp];
        sp--;
        if st == 0 {
            sp++;
            if sp > length(poly_ast_stk_node) {
                add n to poly_ast_stk_node;
                add 1 to poly_ast_stk_state;
            } else {
                poly_ast_stk_node[sp] = n;
                poly_ast_stk_state[sp] = 1;
            }
            if nd_kind[n] == K.Add or nd_kind[n] == K.Mul or nd_kind[n] == K.PowE {
                sp++;
                if sp > length(poly_ast_stk_node) {
                    add nd_b[n] to poly_ast_stk_node;
                    add 0 to poly_ast_stk_state;
                } else {
                    poly_ast_stk_node[sp] = nd_b[n];
                    poly_ast_stk_state[sp] = 0;
                }
                sp++;
                if sp > length(poly_ast_stk_node) {
                    add nd_a[n] to poly_ast_stk_node;
                    add 0 to poly_ast_stk_state;
                } else {
                    poly_ast_stk_node[sp] = nd_a[n];
                    poly_ast_stk_state[sp] = 0;
                }
            } elif nd_kind[n] == K.Pow {
                sp++;
                if sp > length(poly_ast_stk_node) {
                    add nd_a[n] to poly_ast_stk_node;
                    add 0 to poly_ast_stk_state;
                } else {
                    poly_ast_stk_node[sp] = nd_a[n];
                    poly_ast_stk_state[sp] = 0;
                }
            } elif nd_kind[n] >= K.Sin and nd_kind[n] <= K.Atan {
                sp++;
                if sp > length(poly_ast_stk_node) {
                    add nd_a[n] to poly_ast_stk_node;
                    add 0 to poly_ast_stk_state;
                } else {
                    poly_ast_stk_node[sp] = nd_a[n];
                    poly_ast_stk_state[sp] = 0;
                }
            }
        } else {
            local k = nd_kind[n];
            local p = 0;
            if k == K.Num {
                poly_const nd_num[n], nd_den[n];
                p = poly_const;
            } elif k == K.Var {
                local vi = pv_index(nd_txt[n]);
                if vi == 0 {
                    poly_ok = false;
                } else {
                    poly_var vi;
                    p = poly_var;
                }
            } elif k == K.Add {
                poly_add poly_ast_val[nd_a[n]], poly_ast_val[nd_b[n]];
                p = poly_add;
            } elif k == K.Mul {
                poly_mul poly_ast_val[nd_a[n]], poly_ast_val[nd_b[n]];
                p = poly_mul;
            } elif k == K.Pow {
                if nd_num[n] < 0 {
                    poly_ok = false;
                } else {
                    poly_pow poly_ast_val[nd_a[n]], nd_num[n];
                    p = poly_pow;
                }
            } else {
                poly_ok = false;
            }
            if poly_ok {
                poly_ast_val[n] = p;
            }
        }
    }
    if poly_ok and err == "" {
        poly_from_ast = poly_ast_val[$root];
    } else {
        poly_from_ast = 0;
    }
}

list poly_ast_val;
list poly_ast_stk_node;
list poly_ast_stk_state;
