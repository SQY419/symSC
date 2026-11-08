# Bring sums of fractions over a common denominator.
# This is intentionally a structural pass: it runs before polynomial
# cancellation, so (x+1)/x + 1/x becomes (x+2)/x and 1 + 1/x becomes
# (x+1)/x.

list fa_terms;
list fa_nums;
list fa_dens;
list fa_stk;
list tf_facs;
list tf_stk;
var tf_num = 0;
var tf_den = 1;
var fa_count = 0;
list fa_mscan;
list fa_uniq;

proc fa_push_terms root {
    delete fa_terms;
    delete fa_stk;
    local sp = 0;
    sp++; add $root to fa_stk;
    until sp == 0 {
        local x = fa_stk[sp];
        sp--;
        if nd_kind[x] == K.Add {
            sp++;
            if sp > length(fa_stk) { add nd_b[x] to fa_stk; } else { fa_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(fa_stk) { add nd_a[x] to fa_stk; } else { fa_stk[sp] = nd_a[x]; }
        } else {
            add x to fa_terms;
        }
    }
}

proc tf_split term {
    delete tf_facs;
    delete tf_stk;
    local sp = 0;
    sp++; add $term to tf_stk;
    until sp == 0 {
        local x = tf_stk[sp];
        sp--;
        if nd_kind[x] == K.Mul {
            sp++;
            if sp > length(tf_stk) { add nd_b[x] to tf_stk; } else { tf_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(tf_stk) { add nd_a[x] to tf_stk; } else { tf_stk[sp] = nd_a[x]; }
        } else {
            add x to tf_facs;
        }
    }
    mk_num 1, 1;
    local num = mk_num;
    mk_num 1, 1;
    local den = mk_num;
    local i = 1;
    until i > length(tf_facs) or err != "" {
        local f = tf_facs[i];
        local is_den = false;
        local dbase = 0;
        if nd_kind[f] == K.Pow and nd_num[f] < 0 {
            is_den = true;
            mk_pow nd_a[f], -nd_num[f];
            dbase = mk_pow;
        } elif nd_kind[f] == K.PowE and nd_kind[nd_b[f]] == K.Num and nd_num[nd_b[f]] < 0 {
            is_den = true;
            mk_num 0 - nd_num[nd_b[f]], nd_den[nd_b[f]];
            local ne = mk_num;
            mk_pow_expr nd_a[f], ne;
            dbase = mk_pow_expr;
        }
        if is_den {
            mk_mul den, dbase;
            den = mk_mul;
        } else {
            mk_mul num, f;
            num = mk_mul;
        }
        i++;
    }
    tf_num = num;
    tf_den = den;
}

func fa_sum_has_mul(root) {
    delete fa_mscan;
    local sp = 0;
    sp++; add $root to fa_mscan;
    until sp == 0 {
        local x = fa_mscan[sp];
        sp--;
        if nd_kind[x] == K.Mul { return true; }
        elif nd_kind[x] == K.Add {
            sp++;
            if sp > length(fa_mscan) { add nd_b[x] to fa_mscan; } else { fa_mscan[sp] = nd_b[x]; }
            sp++;
            if sp > length(fa_mscan) { add nd_a[x] to fa_mscan; } else { fa_mscan[sp] = nd_a[x]; }
        } elif nd_kind[x] == K.Pow or (nd_kind[x] >= K.Sin and nd_kind[x] <= K.Atan) {
            sp++;
            if sp > length(fa_mscan) { add nd_a[x] to fa_mscan; } else { fa_mscan[sp] = nd_a[x]; }
        }
    }
    return false;
}

proc combine_fractions root {
    combine_fractions = 0;
    if $root == 0 or nd_kind[$root] != K.Add or err != "" {
        combine_fractions = 0;
    } else {
        fa_push_terms $root;
        delete fa_nums;
        delete fa_dens;
        local i = 1;
        local has_den = false;
        until i > length(fa_terms) or err != "" {
            tf_split fa_terms[i];
            add tf_num to fa_nums;
            add tf_den to fa_dens;
            if not is_one(tf_den) { has_den = true; }
            i++;
        }
        if has_den == false {
            combine_fractions = 0;
        } else {
            mk_num 1, 1;
            local common = mk_num;
            delete fa_uniq;
            i = 1;
            until i > length(fa_dens) {
                local found = false;
                local j = 1;
                until j > length(fa_uniq) or found {
                    if nd_sig[fa_uniq[j]] == nd_sig[fa_dens[i]] { found = true; }
                    else { j++; }
                }
                if found == false {
                    add fa_dens[i] to fa_uniq;
                    mk_mul common, fa_dens[i];
                    common = mk_mul;
                }
                i++;
            }
            mk_num 0, 1;
            local sum = mk_num;
            i = 1;
            until i > length(fa_nums) {
                local term = 0;
                if nd_sig[fa_dens[i]] == nd_sig[common] {
                    term = fa_nums[i];
                } else {
                    mk_pow fa_dens[i], -1;
                    local inv = mk_pow;
                    mk_mul fa_nums[i], common;
                    local base = mk_mul;
                    mk_mul base, inv;
                    term = mk_mul;
                }
                mk_add sum, term;
                sum = mk_add;
                i++;
            }
            rules_simplify sum;
            if err == "" { sum = rules_simplify; }
            if fa_sum_has_mul(sum) {
                expand_expr sum;
                if err == "" { sum = expand_expr; }
                rules_simplify sum;
                if err == "" { sum = rules_simplify; }
            }
            if err == "" { sum = rules_simplify; }
            mk_pow common, -1;
            local invc = mk_pow;
            mk_mul sum, invc;
            if err == "" {
                combine_fractions = mk_mul;
                frac_combined = true;
            }
            else { combine_fractions = 0; }
        }
    }
}
