var sp_cn = 1;
var sp_cd = 1;
var sp_base = 0;
var sp_big = false;
var sp_bn = "0";

proc push_m id {
    msp++;
    if msp > length(mstk) {
        add $id to mstk;
    } else {
        mstk[msp] = $id;
    }
}

proc push_s id {
    ssp++;
    if ssp > length(sstk) {
        add $id to sstk;
    } else {
        sstk[ssp] = $id;
    }
}

proc push_a id {
    asp++;
    if asp > length(astk) {
        add $id to astk;
    } else {
        astk[asp] = $id;
    }
}

proc push_p id {
    psp++;
    if psp > length(pstk) {
        add $id to pstk;
    } else {
        pstk[psp] = $id;
    }
}

list fac_base;
list fac_exp;
list fac_node;
var fac_count = 0;

list mstk;
var msp = 0;

list sstk;
var ssp = 0;

list astk;
var asp = 0;

list pstk;
var psp = 0;

list add_base;
list add_n;
list add_d;
var add_count = 0;

list comb_base;
list comb_n;
list comb_d;
var comb_count = 0;

list sum_nodes;

proc add_factor base, exp {
    if $exp != 0 and $base != 0 {
        local found = 0;
        local i = 1;
        until i > fac_count {
            if nd_sig[fac_base[i]] == nd_sig[$base] {
                found = i;
                i = fac_count + 1;
            } else {
                i++;
            }
        }
        if found > 0 {
            local ne = fac_exp[found] + $exp;
            if abs(ne) > MAX_EXP {
                set_err "指数过大";
            } else {
                fac_exp[found] = ne;
            }
        } else {
            fac_count++;
            add $base to fac_base;
            add $exp to fac_exp;
        }
    }
}

proc pow_node base, e {
    if $base == 0 {
        pow_node = 0;
    } elif $e == 0 {
        mk_num 1, 1;
        pow_node = mk_num;
    } elif $e == 1 {
        pow_node = $base;
    } elif abs($e) > MAX_EXP {
        set_err "指数过大";
        pow_node = 0;
    } elif nd_kind[$base] == K.Big {
        if $e >= 1 and $e <= MAX_EXP {
            bi_pow_str nd_txt[$base], $e;
            mk_big bi_pow_str;
            mk_pow_raw = mk_big;
        } elif $e == 0 {
            mk_num 1, 1;
            mk_pow_raw = mk_num;
        } else {
            local id = new_node(K.Pow, $base, 0, $e, 1, "");
            if id != 0 {
                nd_sig[id] = "P(" & nd_sig[$base] & "," & int_str($e) & ")";
                nd_deg[id] = 0;
            }
            pow_node = id;
        }
    } elif nd_kind[$base] == K.Num {
        if nd_num[$base] == 0 and $e < 0 {
            mk_undef;
            pow_node = mk_undef;
        } else {
            rat_pow nd_num[$base], nd_den[$base], $e;
            if rok == false {
                pow_node = 0;
            } else {
                mk_num rn, rd;
                pow_node = mk_num;
            }
        }
    } elif nd_kind[$base] == K.Float {
        local fv = float_pow_value(nd_num[$base], $e);
        if err == "" {
            pow_node = new_float(fv);
        } else {
            pow_node = 0;
        }
    } else {
        local b = $base;
        local ee = $e;
        until nd_kind[b] != K.Pow {
            local ne = ee * nd_num[b];
            if abs(ne) > MAX_EXP {
                set_err "指数过大";
                ee = 0;
                b = 0;
            } else {
                ee = ne;
                b = nd_a[b];
            }
        }
        if b == 0 {
            pow_node = 0;
        } elif ee == 0 {
            mk_num 1, 1;
            pow_node = mk_num;
        } elif ee == 1 {
            pow_node = b;
        } elif nd_kind[b] == K.Num {
            rat_pow nd_num[b], nd_den[b], ee;
            if rok == false {
                pow_node = 0;
            } else {
                mk_num rn, rd;
                pow_node = mk_num;
            }
        } elif nd_kind[b] == K.Float {
            local fv = float_pow_value(nd_num[b], ee);
            if err == "" {
                pow_node = new_float(fv);
            } else {
                pow_node = 0;
            }
        } else {
            local id = new_node(K.Pow, b, 0, ee, 1, "");
            nd_sig[id] = "P(" & nd_sig[b] & "," & int_str(ee) & ")";
            if ee > 0 {
                nd_deg[id] = nd_deg[b] * ee;
            } else {
                nd_deg[id] = 0;
            }
            pow_node = id;
        }
    }
}

var sqrt_combining = false;
list cs_base;
list cs_exp;

proc combine_sqrt_factors {
    if sqrt_combining { } else {
        local found = 0;
        local rad_n = 1;
        delete cs_base;
        delete cs_exp;
        local i = 1;
        until i > fac_count {
            local b = fac_base[i];
            local e = fac_exp[i];
            if nd_kind[b] == K.Sqrt and e == 1 and nd_kind[nd_a[b]] == K.Num and nd_den[nd_a[b]] == 1 {
                rad_n *= nd_num[nd_a[b]];
                found = 1;
                i++;
            } else {
                add b to cs_base;
                add e to cs_exp;
                i++;
            }
        }
        if found == 1 and err == "" {
            local kn = 1;
            local rn = rad_n;
            local kk = floor(sqrt(rn));
            until kk < 2 or rn % (kk * kk) == 0 {
                kk--;
            }
            if kk >= 2 {
                kn = kk;
                rn = rn / (kk * kk);
            }
            if kn != 1 {
                mk_num kn, 1;
                add mk_num to cs_base;
                add 1 to cs_exp;
            }
            if rn != 1 {
                mk_num rn, 1;
                local rr = mk_num;
                new_func_raw K.Sqrt, rr;
                add new_func_raw to cs_base;
                add 1 to cs_exp;
            }
            if length(cs_base) > 0 {
                delete fac_base;
                delete fac_exp;
                fac_count = length(cs_base);
                i = 1;
                until i > fac_count {
                    add cs_base[i] to fac_base;
                    add cs_exp[i] to fac_exp;
                    i++;
                }
            }
        }
    }
}

proc build_product cn, cd {
    local out_n = $cn;
    local out_d = $cd;
    if out_n == 0 {
        mk_num 0, 1;
        build_product = mk_num;
    } else {
        combine_sqrt_factors;
        local i = 2;
        until i > fac_count {
            local bb = fac_base[i];
            local ee = fac_exp[i];
            local j = i;
            until j <= 1 or nd_sig[fac_base[j - 1]] <= nd_sig[bb] {
                fac_base[j] = fac_base[j - 1];
                fac_exp[j] = fac_exp[j - 1];
                j--;
            }
            fac_base[j] = bb;
            fac_exp[j] = ee;
            i++;
        }
        delete fac_node;
        local deg = 0;
        local i = 1;
        until i > fac_count or err != "" {
            if fac_exp[i] == 0 {
                i++;
            } else {
                pow_node fac_base[i], fac_exp[i];
                local f = pow_node;
                if f == 0 {
                    i = fac_count + 1;
                } elif nd_kind[f] == K.Num {
                    rat_mul out_n, out_d, nd_num[f], nd_den[f];
                    if rok == false {
                        i = fac_count + 1;
                    } else {
                        out_n = rn;
                        out_d = rd;
                        i++;
                    }
                } else {
                    add f to fac_node;
                    if fac_exp[i] > 0 {
                        deg += nd_deg[fac_base[i]] * fac_exp[i];
                    }
                    i++;
                }
            }
        }
        if err != "" or out_n == 0 {
            mk_num 0, 1;
            build_product = mk_num;
        } else {
            local cur = 0;
            local coef_id = 0;
            local comps = 0;
            if out_n != 1 or out_d != 1 {
                mk_num out_n, out_d;
                coef_id = mk_num;
                cur = coef_id;
                comps = 1;
            }
            local k = 1;
            until k > length(fac_node) {
                local f = fac_node[k];
                if cur == 0 {
                    cur = f;
                } else {
                    cur = new_node(K.Mul, cur, f, 0, 1, "");
                }
                comps++;
                k++;
            }
            if cur == 0 {
                mk_num 1, 1;
                build_product = mk_num;
            } elif comps == 1 {
                build_product = cur;
            } else {
                local s = "M[";
                if coef_id != 0 {
                    s &= nd_sig[coef_id];
                }
                local k = 1;
                until k > length(fac_node) {
                    if length(s) > 1 and s[length(s)] != "[" {
                        s &= ";";
                    }
                    s &= nd_sig[fac_node[k]];
                    k++;
                }
                s &= "]";
                nd_sig[cur] = s;
                nd_deg[cur] = deg;
                build_product = cur;
            }
        }
    }
}

proc mk_mul a, b {
    if is_container($a) or is_container($b) {
        if is_container($a) and is_container($b) {
            cont_mul $a, $b;
            mk_mul = cont_mul;
        } elif is_container($a) and is_scalar_node($b) {
            cont_scale $b, $a;
            mk_mul = cont_scale;
        } elif is_container($b) and is_scalar_node($a) {
            cont_scale $a, $b;
            mk_mul = cont_scale;
        } else {
            set_err "容器乘法不支持";
            mk_mul = 0;
        }
    } elif (is_big($a) or is_big($b)) and (is_big($a) or (nd_kind[$a] == K.Num and nd_den[$a] == 1)) and (is_big($b) or (nd_kind[$b] == K.Num and nd_den[$b] == 1)) {
        local asv = "";
        local bsv = "";
        if is_big($a) { asv = nd_txt[$a]; } else { asv = nd_num[$a]; }
        if is_big($b) { bsv = nd_txt[$b]; } else { bsv = nd_num[$b]; }
        bi_mul_str asv, bsv;
        mk_big bi_mul_str;
        mk_mul = mk_big;
    } elif nd_kind[$a] == K.Inf or nd_kind[$b] == K.Inf {
        if nd_kind[$a] == K.Inf and nd_kind[$b] == K.Inf {
            mk_inf nd_num[$a] * nd_num[$b];
            mk_mul = mk_inf;
        } elif is_zero($a) or is_zero($b) {
            mk_undef;
            mk_mul = mk_undef;
        } elif nd_kind[$a] == K.Inf {
            if nd_kind[$b] == K.Num or nd_kind[$b] == K.Float {
                if nd_num[$b] < 0 { mk_inf -nd_num[$a]; } else { mk_inf nd_num[$a]; }
                mk_mul = mk_inf;
            } else { mk_mul = $a; }
        } else {
            if nd_kind[$a] == K.Num or nd_kind[$a] == K.Float {
                if nd_num[$a] < 0 { mk_inf -nd_num[$b]; } else { mk_inf nd_num[$b]; }
                mk_mul = mk_inf;
            } else { mk_mul = $b; }
        }
    } elif nd_kind[$a] == K.UN or nd_kind[$b] == K.UN {
        mk_undef;
        mk_mul = mk_undef;
    } elif $a == 0 or $b == 0 {
        mk_mul = 0;
    } elif err != "" {
        mk_mul = 0;
    } elif is_zero($a) or is_zero($b) {
        mk_num 0, 1;
        mk_mul = mk_num;
    } elif is_one($a) {
        mk_mul = $b;
    } elif is_one($b) {
        mk_mul = $a;
    } elif is_num_like($a) and is_num_like($b) {
        if nd_kind[$a] == K.Float or nd_kind[$b] == K.Float {
            mk_mul = new_float(num_value($a) * num_value($b));
        } else {
            rat_mul nd_num[$a], nd_den[$a], nd_num[$b], nd_den[$b];
            if rok == false {
                mk_mul = 0;
            } else {
                mk_num rn, rd;
                mk_mul = mk_num;
            }
        }
    } else {
        delete fac_base;
        delete fac_exp;
        fac_count = 0;
        local cn = 1;
        local cd = 1;
        local bigfac = "";
        delete mstk;
        msp = 0;
        push_m $a;
        push_m $b;
        until msp == 0 {
            local x = mstk[msp];
            msp--;
            local k = nd_kind[x];
            if k == K.Mul {
                push_m nd_b[x];
                push_m nd_a[x];
            } elif k == K.Num {
                rat_mul cn, cd, nd_num[x], nd_den[x];
                if rok == false {
                    msp = 0;
                } else {
                    cn = rn;
                    cd = rd;
                }
            } elif k == K.Big {
                if bigfac == "" { bigfac = nd_txt[x]; }
                else { bi_mul_str bigfac, nd_txt[x]; bigfac = bi_mul_str; }
            } elif k == K.Pow {
                local bb = nd_a[x];
                local ee = nd_num[x];
                if nd_kind[bb] == K.Num {
                    rat_pow nd_num[bb], nd_den[bb], ee;
                    if rok == false {
                        msp = 0;
                    } else {
                        rat_mul cn, cd, rn, rd;
                        if rok == false {
                            msp = 0;
                        } else {
                            cn = rn;
                            cd = rd;
                        }
                    }
                } else {
                    add_factor bb, ee;
                }
            } else {
                add_factor x, 1;
            }
        }
        if bigfac != "" and bigfac != "1" {
            mk_big bigfac;
            add_factor mk_big, 1;
        }
        build_product cn, cd;
        mk_mul = build_product;
    }
}

proc mk_neg x {
    if is_container($x) {
        cont_neg $x;
        mk_neg = cont_neg;
    } elif is_big($x) {
        bi_neg_str nd_txt[$x];
        mk_big bi_neg_str;
        mk_neg = mk_big;
    } elif nd_kind[$x] == K.Inf {
        mk_inf -nd_num[$x];
        mk_neg = mk_inf;
    } elif nd_kind[$x] == K.UN {
        mk_undef;
        mk_neg = mk_undef;
    } elif $x == 0 {
        mk_neg = 0;
    } elif nd_kind[$x] == K.Num {
        mk_num -nd_num[$x], nd_den[$x];
        mk_neg = mk_num;
    } elif nd_kind[$x] == K.Float {
        mk_neg = new_float(-nd_num[$x]);
    } else {
        mk_num -1, 1;
        local m = mk_num;
        mk_mul m, $x;
        mk_neg = mk_mul;
    }
}

var surd_big = false;
var surd_ok = false;
var surd_a = 0;
var surd_b = 0;
var surd_d = 0;
list surd_terms;
list surd_stk;

proc surd_add_term term, sign {
    if nd_kind[$term] == K.Num and nd_den[$term] == 1 {
        surd_a = surd_a + $sign * nd_num[$term];
    } else {
        local factors = 0;
        local coeff = $sign;
        local rad = 0;
        local sp = 0;
        delete surd_stk;
        sp++; add $term to surd_stk;
        until sp == 0 {
            local x = surd_stk[sp];
            sp--;
            if nd_kind[x] == K.Mul {
                sp++;
                if sp > length(surd_stk) { add nd_b[x] to surd_stk; } else { surd_stk[sp] = nd_b[x]; }
                sp++;
                if sp > length(surd_stk) { add nd_a[x] to surd_stk; } else { surd_stk[sp] = nd_a[x]; }
            } elif nd_kind[x] == K.Sqrt {
                if factors > 0 or nd_kind[nd_a[x]] != K.Num or nd_den[nd_a[x]] != 1 {
                    surd_ok = false;
                    sp = 0;
                } else {
                    rad = nd_a[x];
                    factors++;
                }
            } elif nd_kind[x] == K.Num and nd_den[x] == 1 {
                coeff = coeff * nd_num[x];
            } else {
                surd_ok = false;
                sp = 0;
            }
        }
        if factors != 1 or surd_ok == false {
            surd_ok = false;
        } else {
            if surd_b != 0 { surd_ok = false; }
            else {
                surd_b = coeff;
                surd_d = nd_num[rad];
            }
        }
    }
}

proc surd_power base, e {
    surd_power = 0;
    surd_big = false;
    if nd_kind[$base] != K.Add or $e < 32 or $e > 50 { surd_power = 0; }
    else {
        local aa = 0;
        local bb = 0;
        local dd = 0;
        local ok = true;
        delete surd_terms;
        delete surd_stk;
        local sp = 0;
        sp++; add $base to surd_stk;
        until sp == 0 {
            local x = surd_stk[sp];
            sp--;
            if nd_kind[x] == K.Add {
                sp++;
                if sp > length(surd_stk) { add nd_b[x] to surd_stk; } else { surd_stk[sp] = nd_b[x]; }
                sp++;
                if sp > length(surd_stk) { add nd_a[x] to surd_stk; } else { surd_stk[sp] = nd_a[x]; }
            } else {
                add x to surd_terms;
            }
        }
        local i = 1;
        until i > length(surd_terms) or ok == false {
            local term = surd_terms[i];
            if nd_kind[term] == K.Num and nd_den[term] == 1 {
                aa = aa + nd_num[term];
            } else {
                local coeff = 1;
                local rad = 0;
                local factors = 0;
                local sp2 = 0;
                delete surd_stk;
                sp2++; add term to surd_stk;
                until sp2 == 0 {
                    local y = surd_stk[sp2];
                    sp2--;
                    if nd_kind[y] == K.Mul {
                        sp2++;
                        if sp2 > length(surd_stk) { add nd_b[y] to surd_stk; } else { surd_stk[sp2] = nd_b[y]; }
                        sp2++;
                        if sp2 > length(surd_stk) { add nd_a[y] to surd_stk; } else { surd_stk[sp2] = nd_a[y]; }
                    } elif nd_kind[y] == K.Sqrt and nd_kind[nd_a[y]] == K.Num and nd_den[nd_a[y]] == 1 and factors == 0 {
                        rad = nd_a[y];
                        factors++;
                    } elif nd_kind[y] == K.Num and nd_den[y] == 1 {
                        coeff = coeff * nd_num[y];
                    } else {
                        ok = false;
                        sp2 = 0;
                    }
                }
                if factors != 1 or bb != 0 {
                    ok = false;
                } else {
                    bb = coeff;
                    dd = nd_num[rad];
                }
            }
            i++;
        }
        if ok == false or bb == 0 or dd <= 1 {
            surd_power = 0;
        } else {
            local astr = "" & aa;
            local bstr = "" & bb;
            local dstr = "" & dd;
            local an = "1";
            local bn = "0";
            local k = 0;
            until k >= $e or err != "" {
                bi_mul_str astr, an;
                local t1 = bi_mul_str;
                bi_mul_str dstr, bstr;
                local db = bi_mul_str;
                bi_mul_str db, bn;
                local t2 = bi_mul_str;
                bi_add_str t1, t2;
                local na = bi_add_str;
                bi_mul_str astr, bn;
                local t3 = bi_mul_str;
                bi_mul_str bstr, an;
                local t4 = bi_mul_str;
                bi_add_str t3, t4;
                local nb = bi_add_str;
                an = na;
                bn = nb;
                k++;
            }
            if err != "" {
                surd_power = 0;
            } elif an == "0" and bn == "0" {
                mk_num 0, 1;
                surd_power = mk_num;
                surd_big = true;
            } else {
                local result = 0;
                if an != "0" {
                    mk_big an;
                    result = mk_big;
                }
                if bn != "0" {
                    mk_big bn;
                    local bt = mk_big;
                    mk_num dd, 1;
                    mk_func K.Sqrt, mk_num;
                    local sv = mk_func;
                    mk_mul bt, sv;
                    local term = mk_mul;
                    if result == 0 { result = term; }
                    else { mk_add result, term; result = mk_add; }
                }
                surd_power = result;
                surd_big = true;
            }
        }
    }
}

proc mk_pow base, e {
    surd_power $base, $e;
    if surd_power != 0 {
        mk_pow = surd_power;
    } else {
        mk_pow_raw $base, $e;
        mk_pow = mk_pow_raw;
    }
}

proc mk_pow_raw base, e {
    if is_container($base) {
        ctb_begin nd_kind[$base];
        until ctb_idx[ctb_depth] > nd_den[$base] {
            mk_pow ct_elems[nd_num[$base] + ctb_idx[ctb_depth] - 1], $e;
            ctb_add mk_pow;
            ctb_idx[ctb_depth]++;
        }
        ctb_end;
        mk_pow_raw = ctb_out;
    } elif nd_kind[$base] == K.Inf {
        if $e > 0 { mk_pow_raw = $base; }
        elif $e == 0 { mk_undef; mk_pow_raw = mk_undef; }
        else { mk_num 0, 1; mk_pow_raw = mk_num; }
    } elif nd_kind[$base] == K.UN {
        mk_undef;
        mk_pow_raw = mk_undef;
    } elif $base == 0 {
        if $e > 0 {
            mk_num 0, 1;
            mk_pow_raw = mk_num;
        } else {
            mk_undef;
            mk_pow_raw = mk_undef;
        }
    } elif err != "" {
        mk_pow_raw = 0;
    } elif $e == 0 {
        if is_zero($base) {
            mk_undef;
            mk_pow_raw = mk_undef;
        } else {
            mk_num 1, 1;
            mk_pow_raw = mk_num;
        }
    } elif $e == 1 {
        mk_pow_raw = $base;
    } elif nd_kind[$base] == K.Num and nd_den[$base] == 1 and $e >= 0 and abs(nd_num[$base]) > 1 and ($e > 15 or abs($e) > MAX_EXP) {
        local btxt = nd_num[$base];
        local etxt = $e;
        bi_pow_str btxt, etxt;
        mk_big bi_pow_str;
        mk_pow_raw = mk_big;
    } elif nd_kind[$base] == K.Num and nd_den[$base] == 1 and $e < 0 and abs($e) > 15 and abs(nd_num[$base]) > 1 {
        # 2^-200 -> 1/2^200.  The big integer module computes the positive
        # power exactly; Pow(big, -1) keeps the reciprocal exact.
        local btxt = nd_num[$base];
        local etxt = 0 - $e;
        bi_pow_str btxt, etxt;
        local stxt = "1/" & bi_pow_str;
        local sid = new_node(K.Var, 0, 0, 0, 1, stxt);
        if sid != 0 {
            nd_sig[sid] = "V" & stxt;
            nd_deg[sid] = 0;
        }
        mk_pow_raw = sid;
    } elif nd_kind[$base] == K.PowE {
        local inn = nd_a[$base];
        mk_num $e, 1;
        local en = mk_num;
        mk_mul nd_b[$base], en;
        local ne = mk_mul;
        mk_pow_expr inn, ne;
        mk_pow_raw = mk_pow_expr;
    } elif nd_kind[$base] == K.Sqrt {
        local u = nd_a[$base];
        if $e % 2 == 0 {
            mk_pow u, $e / 2;
            mk_pow_raw = mk_pow;
        } elif $e > 1 {
            mk_pow u, ($e - 1) / 2;
            local p = mk_pow;
            mk_mul p, $base;
            mk_pow_raw = mk_mul;
        } else {
            # sqrt(u)^1 or sqrt(u)^-odd: keep the radical and its exponent.
            pow_node $base, $e;
            mk_pow_raw = pow_node;
        }
    } elif abs($e) > MAX_EXP {
        set_err "指数过大";
        mk_pow_raw = 0;
    } elif nd_kind[$base] == K.Num {
        if nd_num[$base] == 0 and $e < 0 {
            mk_undef;
            mk_pow_raw = mk_undef;
        } else {
        rat_pow nd_num[$base], nd_den[$base], $e;
        if rok == false {
            mk_pow_raw = 0;
        } else {
            mk_num rn, rd;
            mk_pow_raw = mk_num;
        }
        }
    } elif nd_kind[$base] == K.Float {
        local fv = float_pow_value(nd_num[$base], $e);
        if err == "" {
            mk_pow_raw = new_float(fv);
        } else {
            mk_pow_raw = 0;
        }
    } else {
        local b = $base;
        local ee = $e;
        until nd_kind[b] != K.Pow {
            local ne = ee * nd_num[b];
            if abs(ne) > MAX_EXP {
                set_err "指数过大";
                ee = 0;
                b = 0;
            } else {
                ee = ne;
                b = nd_a[b];
            }
        }
        if b == 0 {
            mk_pow_raw = 0;
        } elif ee == 0 {
            mk_num 1, 1;
            mk_pow_raw = mk_num;
        } elif ee == 1 {
            mk_pow_raw = b;
        } elif nd_kind[b] == K.Num {
            rat_pow nd_num[b], nd_den[b], ee;
            if rok == false {
                mk_pow_raw = 0;
            } else {
                mk_num rn, rd;
                mk_pow_raw = mk_num;
            }
        } elif nd_kind[b] == K.Float {
            local fv = float_pow_value(nd_num[b], ee);
            if err == "" {
                mk_pow_raw = new_float(fv);
            } else {
                mk_pow_raw = 0;
            }
        } elif nd_kind[b] == K.Mul {
            delete fac_base;
            delete fac_exp;
            fac_count = 0;
            local cn = 1;
            local cd = 1;
            delete pstk;
            psp = 0;
            push_p b;
            until psp == 0 {
                local x = pstk[psp];
                psp--;
                local k = nd_kind[x];
                if k == K.Mul {
                    push_p nd_b[x];
                    push_p nd_a[x];
                } elif k == K.Num {
                    rat_pow nd_num[x], nd_den[x], ee;
                    if rok == false {
                        psp = 0;
                    } else {
                        rat_mul cn, cd, rn, rd;
                        if rok == false {
                            psp = 0;
                        } else {
                            cn = rn;
                            cd = rd;
                        }
                    }
                } elif k == K.Pow {
                    local bb = nd_a[x];
                    local e0 = nd_num[x];
                    local ne = e0 * ee;
                    if abs(ne) > MAX_EXP {
                        set_err "指数过大";
                        psp = 0;
                    } else {
                        add_factor bb, ne;
                    }
                } else {
                    add_factor x, ee;
                }
            }
            build_product cn, cd;
            mk_pow_raw = build_product;
        } else {
            pow_node b, ee;
            mk_pow_raw = pow_node;
        }
    }
}

proc split_term x {
    if $x == 0 {
        sp_cn = 0;
        sp_cd = 1;
        sp_base = 0;
    } elif nd_kind[$x] == K.Num {
        sp_cn = nd_num[$x];
        sp_cd = nd_den[$x];
        sp_base = 0;
        sp_big = false;
        sp_bn = "";
    } elif nd_kind[$x] == K.Big {
        sp_cn = 1;
        sp_cd = 1;
        sp_base = 0;
        sp_big = true;
        sp_bn = nd_txt[$x];
    } elif nd_kind[$x] == K.Mul {
        local cn = 1;
        local cd = 1;
        local base = 0;
        local bn = "";
        delete sstk;
        ssp = 0;
        push_s $x;
        until ssp == 0 {
            local y = sstk[ssp];
            ssp--;
            if nd_kind[y] == K.Mul {
                push_s nd_b[y];
                push_s nd_a[y];
            } elif nd_kind[y] == K.Num {
                rat_mul cn, cd, nd_num[y], nd_den[y];
                if rok == false {
                    ssp = 0;
                } else {
                    cn = rn;
                    cd = rd;
                }
            } elif nd_kind[y] == K.Big {
                if bn == "" { bn = nd_txt[y]; }
                else { bi_mul_str bn, nd_txt[y]; bn = bi_mul_str; }
            } else {
                if base == 0 {
                    base = y;
                } else {
                    mk_mul base, y;
                    base = mk_mul;
                }
            }
        }
        sp_cn = cn;
        sp_cd = cd;
        sp_base = base;
        if bn != "" {
            sp_big = true;
            sp_bn = bn;
        } else {
            sp_big = false;
            sp_bn = "";
        }
    } else {
        sp_cn = 1;
        sp_cd = 1;
        sp_base = $x;
        sp_big = false;
        sp_bn = "";
    }
}

proc try_pythagorean {
    local i = 1;
    until i > comb_count {
        if comb_n[i] != 0 and comb_base[i] != 0 {
            local bp = comb_base[i];
            if nd_kind[bp] == K.Pow and nd_num[bp] == 2 and nd_kind[nd_a[bp]] == K.Sin {
                local u = nd_a[nd_a[bp]];
                local j = 1;
                local matched = 0;
                until j > comb_count or matched > 0 {
                    if j != i and comb_n[j] != 0 and comb_base[j] != 0 {
                        local cp = comb_base[j];
                        if nd_kind[cp] == K.Pow and nd_num[cp] == 2 and nd_kind[nd_a[cp]] == K.Cos {
                            local v = nd_a[nd_a[cp]];
                            if nd_sig[u] == nd_sig[v] and comb_n[i] == comb_n[j] and comb_d[i] == comb_d[j] {
                                local cn = comb_n[i];
                                local cd = comb_d[i];
                                comb_n[i] = 0;
                                comb_n[j] = 0;
                                local k = 1;
                                local found = 0;
                                until k > comb_count {
                                    if comb_base[k] == 0 {
                                        found = k;
                                        k = comb_count + 1;
                                    } else {
                                        k++;
                                    }
                                }
                                if found > 0 {
                                    rat_add comb_n[found], comb_d[found], cn, cd;
                                    comb_n[found] = rn;
                                    comb_d[found] = rd;
                                } else {
                                    comb_count++;
                                    add 0 to comb_base;
                                    add cn to comb_n;
                                    add cd to comb_d;
                                }
                                matched = 1;
                            }
                        }
                    }
                    j++;
                }
            }
        }
        i++;
    }
}

func term_order_rank(id) {
    if $id == 0 {
        return 3;
    }
    local k = nd_kind[$id];
    if k == K.Num or k == K.Float {
        return 3;
    } elif k == K.PowE {
        return 2;
    } elif k == K.Mul {
        return 1;
    } elif k == K.Var or k == K.Pi or k == K.E {
        return 0;
    } elif k == K.Pow {
        local b = nd_a[$id];
        if nd_kind[b] == K.Var or nd_kind[b] == K.Pi or nd_kind[b] == K.E {
            return 0;
        }
        return 2;
    }
    return 2;
}

func is_scalar_node(id) {
    return $id != 0 and (nd_kind[$id] == K.Num or nd_kind[$id] == K.Float);
}

proc cont_neg x {
    ctb_begin nd_kind[$x];
    until ctb_idx[ctb_depth] > nd_den[$x] {
        mk_neg ct_elems[nd_num[$x] + ctb_idx[ctb_depth] - 1];
        ctb_add mk_neg;
        ctb_idx[ctb_depth]++;
    }
    ctb_end;
    cont_neg = ctb_out;
}

proc cont_add a, b {
    if nd_kind[$a] != nd_kind[$b] or nd_den[$a] != nd_den[$b] {
        set_err "容器形状不匹配";
        cont_add = 0;
    } else {
        ctb_begin nd_kind[$a];
        until ctb_idx[ctb_depth] > nd_den[$a] {
            mk_add ct_elems[nd_num[$a] + ctb_idx[ctb_depth] - 1], ct_elems[nd_num[$b] + ctb_idx[ctb_depth] - 1];
            ctb_add mk_add;
            ctb_idx[ctb_depth]++;
        }
        ctb_end;
        cont_add = ctb_out;
    }
}

proc cont_scale c, x {
    ctb_begin nd_kind[$x];
    until ctb_idx[ctb_depth] > nd_den[$x] {
        mk_mul $c, ct_elems[nd_num[$x] + ctb_idx[ctb_depth] - 1];
        ctb_add mk_mul;
        ctb_idx[ctb_depth]++;
    }
    ctb_end;
    cont_scale = ctb_out;
}

proc cont_lmul a, b {
    if nd_kind[$a] != nd_kind[$b] or nd_den[$a] != nd_den[$b] {
        set_err "容器形状不匹配";
        cont_lmul = 0;
    } else {
        ctb_begin nd_kind[$a];
        until ctb_idx[ctb_depth] > nd_den[$a] {
            mk_mul ct_elems[nd_num[$a] + ctb_idx[ctb_depth] - 1], ct_elems[nd_num[$b] + ctb_idx[ctb_depth] - 1];
            ctb_add mk_mul;
            ctb_idx[ctb_depth]++;
        }
        ctb_end;
        cont_lmul = ctb_out;
    }
}

proc cont_cross a, b {
    if nd_kind[$a] != K.Vec or nd_kind[$b] != K.Vec or nd_den[$a] != 3 or nd_den[$b] != 3 {
        set_err "cross 需要两个三维向量";
        cont_cross = 0;
    } else {
        local a1 = ct_elems[nd_num[$a]];
        local a2 = ct_elems[nd_num[$a] + 1];
        local a3 = ct_elems[nd_num[$a] + 2];
        local b1 = ct_elems[nd_num[$b]];
        local b2 = ct_elems[nd_num[$b] + 1];
        local b3 = ct_elems[nd_num[$b] + 2];
        mk_mul a2, b3; local t1 = mk_mul;
        mk_mul a3, b2; local t2 = mk_mul;
        mk_neg t2; mk_add t1, mk_neg; local c1 = mk_add;
        mk_mul a3, b1; local t3 = mk_mul;
        mk_mul a1, b3; local t4 = mk_mul;
        mk_neg t4; mk_add t3, mk_neg; local c2 = mk_add;
        mk_mul a1, b2; local t5 = mk_mul;
        mk_mul a2, b1; local t6 = mk_mul;
        mk_neg t6; mk_add t5, mk_neg; local c3 = mk_add;
        ctb_begin K.Vec;
        ctb_add c1; ctb_add c2; ctb_add c3;
        ctb_end;
        cont_cross = ctb_out;
    }
}

proc cont_transpose c {
    if not is_matrix($c) {
        set_err "transpose 需要矩阵";
        cont_transpose = 0;
    } else {
        local rows = nd_den[$c];
        local first = ct_elems[nd_num[$c]];
        local cols = nd_den[first];
        ctb_begin K.Vec;
        local j = 1;
        until j > cols {
            ctb_begin K.Vec;
            local i = 1;
            until i > rows {
                local row = ct_elems[nd_num[$c] + i - 1];
                if nd_den[row] != cols { set_err "矩阵行长度不一致"; }
                else { ctb_add ct_elems[nd_num[row] + j - 1]; }
                i++;
            }
            ctb_end;
            ctb_add ctb_out;
            j++;
        }
        ctb_end;
        cont_transpose = ctb_out;
    }
}

proc cont_det c {
    cont_det = 0;
    if not is_matrix($c) {
        set_err "det 需要方阵";
    } else {
        local n = nd_den[$c];
        if n == 1 {
            cont_det = ct_elems[nd_num[$c]];
        } elif n == 2 {
            local r1 = ct_elems[nd_num[$c]];
            local r2 = ct_elems[nd_num[$c] + 1];
            mk_mul ct_elems[nd_num[r1]], ct_elems[nd_num[r2] + 1];
            local p1 = mk_mul;
            mk_mul ct_elems[nd_num[r1] + 1], ct_elems[nd_num[r2]];
            local p2 = mk_mul;
            mk_neg p2; mk_add p1, mk_neg; cont_det = mk_add;
        } elif n == 3 {
            local r1 = ct_elems[nd_num[$c]];
            local r2 = ct_elems[nd_num[$c] + 1];
            local r3 = ct_elems[nd_num[$c] + 2];
            # a(ei-fh) - b(di-fg) + c(dh-eg)
            mk_mul ct_elems[nd_num[r2] + 1], ct_elems[nd_num[r3] + 2]; local ei = mk_mul;
            mk_mul ct_elems[nd_num[r2] + 2], ct_elems[nd_num[r3] + 1]; local fh = mk_mul;
            mk_neg fh; mk_add ei, mk_neg; local m1 = mk_add;
            mk_mul ct_elems[nd_num[r2]], ct_elems[nd_num[r3] + 2]; local di = mk_mul;
            mk_mul ct_elems[nd_num[r2] + 2], ct_elems[nd_num[r3]]; local fg = mk_mul;
            mk_neg fg; mk_add di, mk_neg; local m2 = mk_add;
            mk_mul ct_elems[nd_num[r2]], ct_elems[nd_num[r3] + 1]; local dh = mk_mul;
            mk_mul ct_elems[nd_num[r2] + 1], ct_elems[nd_num[r3]]; local eg = mk_mul;
            mk_neg eg; mk_add dh, mk_neg; local m3 = mk_add;
            mk_mul ct_elems[nd_num[r1]], m1; local d1 = mk_mul;
            mk_mul ct_elems[nd_num[r1] + 1], m2; local d2 = mk_mul;
            mk_mul ct_elems[nd_num[r1] + 2], m3; local d3 = mk_mul;
            mk_add d1, d2; local s1 = mk_add;
            mk_neg d3; mk_add s1, mk_neg; cont_det = mk_add;
        } else {
            set_err "det 目前只支持 1x1/2x2/3x3";
        }
    }
}

proc cont_cat a, b {
    if not is_container($a) or not is_container($b) {
        set_err "cat 需要两个容器";
        cont_cat = 0;
    } else {
        local kd = K.List;
        if nd_kind[$a] == K.Vec and nd_kind[$b] == K.Vec { kd = K.Vec; }
        ctb_begin kd;
        local j = 1;
        until j > nd_den[$a] {
            ctb_add ct_elems[nd_num[$a] + j - 1];
            j++;
        }
        j = 1;
        until j > nd_den[$b] {
            ctb_add ct_elems[nd_num[$b] + j - 1];
            j++;
        }
        ctb_end;
        cont_cat = ctb_out;
    }
}

proc cont_dot a, b {
    if nd_den[$a] != nd_den[$b] {
        set_err "向量长度不匹配";
        cont_dot = 0;
    } else {
        mk_num 0, 1;
        local sum = mk_num;
        local i = 1;
        until i > nd_den[$a] {
            mk_mul ct_elems[nd_num[$a] + i - 1], ct_elems[nd_num[$b] + i - 1];
            local p = mk_mul;
            mk_add sum, p;
            sum = mk_add;
            i++;
        }
        cont_dot = sum;
    }
}

proc cont_matvec a, b {
    local rows = nd_den[$a];
    local cols = nd_den[ct_elems[nd_num[$a]]];
    if cols != nd_den[$b] {
        set_err "矩阵与向量尺寸不匹配";
        cont_matvec = 0;
    } else {
        ctb_begin K.Vec;
        local i = 1;
        until i > rows {
            local row = ct_elems[nd_num[$a] + i - 1];
            mk_num 0, 1;
            local sum = mk_num;
            local j = 1;
            until j > cols {
                mk_mul ct_elems[nd_num[row] + j - 1], ct_elems[nd_num[$b] + j - 1];
                local p = mk_mul;
                mk_add sum, p;
                sum = mk_add;
                j++;
            }
            ctb_add sum;
            i++;
        }
        ctb_end;
        cont_matvec = ctb_out;
    }
}

proc cont_matmul a, b {
    local rows = nd_den[$a];
    local cols = nd_den[ct_elems[nd_num[$a]]];
    local brows = nd_den[$b];
    local bcols = nd_den[ct_elems[nd_num[$b]]];
    if cols != brows {
        set_err "矩阵尺寸不匹配";
        cont_matmul = 0;
    } else {
        ctb_begin K.Vec;
        local i = 1;
        until i > rows {
            local row = ct_elems[nd_num[$a] + i - 1];
            ctb_begin K.Vec;
            local j = 1;
            until j > bcols {
                mk_num 0, 1;
                local sum = mk_num;
                local k = 1;
                until k > cols {
                    local brow = ct_elems[nd_num[$b] + k - 1];
                    mk_mul ct_elems[nd_num[row] + k - 1], ct_elems[nd_num[brow] + j - 1];
                    local p = mk_mul;
                    mk_add sum, p;
                    sum = mk_add;
                    k++;
                }
                ctb_add sum;
                j++;
            }
            ctb_end;
            ctb_add ctb_out;
            i++;
        }
        ctb_end;
        cont_matmul = ctb_out;
    }
}

proc cont_mul a, b {
    if nd_kind[$a] == K.Vec and nd_kind[$b] == K.Vec {
        if is_matrix($a) and is_matrix($b) {
            cont_matmul $a, $b;
            cont_mul = cont_matmul;
        } elif is_matrix($a) {
            cont_matvec $a, $b;
            cont_mul = cont_matvec;
        } elif is_matrix($b) {
            set_err "不支持向量乘矩阵";
            cont_mul = 0;
        } else {
            cont_dot $a, $b;
            cont_mul = cont_dot;
        }
    } elif nd_kind[$a] == K.List and nd_kind[$b] == K.List {
        cont_lmul $a, $b;
        cont_mul = cont_lmul;
    } else {
        set_err "容器乘法不支持";
        cont_mul = 0;
    }
}

list add_big;
list add_bn;
list comb_big;
list comb_bn;

proc mk_add a, b {
    if is_container($a) or is_container($b) {
        if is_container($a) and is_container($b) {
            cont_add $a, $b;
            mk_add = cont_add;
        } else {
            set_err "容器与标量不能相加";
            mk_add = 0;
        }
    } elif (is_big($a) or is_big($b)) and (is_big($a) or (nd_kind[$a] == K.Num and nd_den[$a] == 1)) and (is_big($b) or (nd_kind[$b] == K.Num and nd_den[$b] == 1)) {
        local asv = "";
        local bsv = "";
        if is_big($a) { asv = nd_txt[$a]; } else { asv = nd_num[$a]; }
        if is_big($b) { bsv = nd_txt[$b]; } else { bsv = nd_num[$b]; }
        bi_add_str asv, bsv;
        mk_big bi_add_str;
        mk_add = mk_big;
    } elif nd_kind[$a] == K.Inf or nd_kind[$b] == K.Inf {
        if nd_kind[$a] == K.Inf and nd_kind[$b] == K.Inf {
            if nd_num[$a] == nd_num[$b] { mk_add = $a; } else { mk_undef; mk_add = mk_undef; }
        } elif nd_kind[$a] == K.Inf { mk_add = $a; }
        else { mk_add = $b; }
    } elif nd_kind[$a] == K.UN or nd_kind[$b] == K.UN {
        mk_undef;
        mk_add = mk_undef;
    } elif $a == 0 or $b == 0 {
        mk_add = 0;
    } elif err != "" {
        mk_add = 0;
    } elif is_zero($a) {
        mk_add = $b;
    } elif is_zero($b) {
        mk_add = $a;
    } elif is_num_like($a) and is_num_like($b) {
        if nd_kind[$a] == K.Float or nd_kind[$b] == K.Float {
            mk_add = new_float(num_value($a) + num_value($b));
        } else {
            rat_add nd_num[$a], nd_den[$a], nd_num[$b], nd_den[$b];
            if rok == false {
                mk_add = 0;
            } else {
                mk_num rn, rd;
                mk_add = mk_num;
            }
        }
    } else {
        delete add_base;
        delete add_n;
        delete add_d;
        delete add_big;
        delete add_bn;
        add_count = 0;
        delete astk;
        asp = 0;
        push_a $a;
        push_a $b;
        until asp == 0 {
            local x = astk[asp];
            asp--;
            if nd_kind[x] == K.Add {
                push_a nd_b[x];
                push_a nd_a[x];
            } else {
                split_term x;
                if err != "" {
                    asp = 0;
                } else {
                    add_count++;
                    add sp_base to add_base;
                    add sp_cn to add_n;
                    add sp_cd to add_d;
                    add sp_big to add_big;
                    add sp_bn to add_bn;
                }
            }
        }
        if err == "" {
            delete comb_base;
            delete comb_n;
            delete comb_d;
            delete comb_big;
            delete comb_bn;
            comb_count = 0;
            local i = 1;
            until i > add_count {
                local found = 0;
                local j = 1;
                until j > comb_count {
                    if comb_base[j] == 0 and add_base[i] == 0 {
                        found = j;
                        j = comb_count + 1;
                    } elif comb_base[j] != 0 and add_base[i] != 0 and nd_sig[comb_base[j]] == nd_sig[add_base[i]] {
                        found = j;
                        j = comb_count + 1;
                    } else {
                        j++;
                    }
                }
                if found > 0 {
                    if add_big[i] or comb_big[found] {
                        if add_d[i] == 1 and comb_d[found] == 1 {
                            local ans = "";
                            local bns = "";
                            if comb_big[found] { ans = comb_bn[found]; } else { ans = "" & comb_n[found]; }
                            if add_big[i] { bns = add_bn[i]; } else { bns = "" & add_n[i]; }
                            bi_add_str ans, bns;
                            comb_bn[found] = bi_add_str;
                            comb_big[found] = true;
                            comb_n[found] = 1;
                            comb_d[found] = 1;
                        } else {
                            rat_add comb_n[found], comb_d[found], add_n[i], add_d[i];
                            comb_n[found] = rn;
                            comb_d[found] = rd;
                            comb_big[found] = false;
                        }
                    } else {
                        rat_add comb_n[found], comb_d[found], add_n[i], add_d[i];
                        comb_n[found] = rn;
                        comb_d[found] = rd;
                    }
                } else {
                    comb_count++;
                    add add_base[i] to comb_base;
                    add add_n[i] to comb_n;
                    add add_d[i] to comb_d;
                    add add_big[i] to comb_big;
                    add add_bn[i] to comb_bn;
                }
                i++;
            }
            if err == "" {
                try_pythagorean;
                delete sum_nodes;
                local i = 1;
                until i > comb_count {
                    if comb_big[i] or comb_n[i] != 0 {
                        local node = 0;
                        if comb_big[i] {
                            if comb_base[i] == 0 {
                                mk_big comb_bn[i];
                                node = mk_big;
                            } else {
                                mk_big comb_bn[i];
                                local c = mk_big;
                                mk_mul c, comb_base[i];
                                node = mk_mul;
                            }
                        } elif comb_base[i] == 0 {
                            mk_num comb_n[i], comb_d[i];
                            node = mk_num;
                        } elif comb_n[i] == 1 and comb_d[i] == 1 {
                            node = comb_base[i];
                        } else {
                            mk_num comb_n[i], comb_d[i];
                            local c = mk_num;
                            mk_mul c, comb_base[i];
                            node = mk_mul;
                        }
                        if node != 0 {
                            add node to sum_nodes;
                        }
                    }
                    i++;
                }
                if length(sum_nodes) == 0 {
                    mk_num 0, 1;
                    mk_add = mk_num;
                } elif length(sum_nodes) == 1 {
                    mk_add = sum_nodes[1];
                } else {
                    local i = 2;
                    until i > length(sum_nodes) {
                        local x = sum_nodes[i];
                        local j = i;
                        local placing = true;
                        until j <= 1 or placing == false {
                            local prev = sum_nodes[j - 1];
                            local keep = false;
                            if nd_deg[prev] > nd_deg[x] {
                                keep = true;
                            } elif nd_deg[prev] == nd_deg[x] {
                                local rp = term_order_rank(prev);
                                local rx = term_order_rank(x);
                                if rp < rx {
                                    keep = true;
                                } elif rp == rx and nd_sig[prev] <= nd_sig[x] {
                                    keep = true;
                                }
                            }
                            if keep {
                                placing = false;
                            } else {
                                sum_nodes[j] = prev;
                                j--;
                            }
                        }
                        sum_nodes[j] = x;
                        i++;
                    }
                    local cur = sum_nodes[1];
                    local i = 2;
                    until i > length(sum_nodes) {
                        cur = new_node(K.Add, cur, sum_nodes[i], 0, 1, "");
                        i++;
                    }
                    local s = "A[";
                    local i = 1;
                    until i > length(sum_nodes) {
                        if i > 1 {
                            s &= ";";
                        }
                        s &= nd_sig[sum_nodes[i]];
                        i++;
                    }
                    s &= "]";
                    nd_sig[cur] = s;
                    local d = nd_deg[sum_nodes[1]];
                    local i = 2;
                    until i > length(sum_nodes) {
                        if nd_deg[sum_nodes[i]] > d {
                            d = nd_deg[sum_nodes[i]];
                        }
                        i++;
                    }
                    nd_deg[cur] = d;
                    mk_add = cur;
                }
            } else {
                mk_add = 0;
            }
        } else {
            mk_add = 0;
        }
    }
}
