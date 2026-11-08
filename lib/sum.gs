# Numeric summation and product over a container or an integer range.

var br_n = "0";
var br_d = "1";
var sum_numeric = true;
var sum_seen_num = false;

proc br_reduce n, d {
    local nn = bi_norm($n);
    local dd = bi_norm($d);
    if dd == "0" {
        set_err "除数为零";
    } else {
        if dd[1] == "-" {
            bi_neg_str nn; nn = bi_neg_str;
            dd = substr(dd, 2, length(dd));
        }
        bi_gcd_str nn, dd;
        local g = bi_gcd_str;
        if g != "1" and g != "0" {
            bi_div_str nn, g; nn = bi_div_str;
            bi_div_str dd, g; dd = bi_div_str;
        }
        if nn == "0" { dd = "1"; }
        br_n = nn;
        br_d = dd;
    }
}

proc br_add_str an, ad, bn, bd {
    bi_mul_str $an, $bd; local x = bi_mul_str;
    bi_mul_str $bn, $ad; local y = bi_mul_str;
    bi_add_str x, y; local n = bi_add_str;
    bi_mul_str $ad, $bd; local d = bi_mul_str;
    br_reduce n, d;
}

proc br_mul_str an, ad, bn, bd {
    bi_mul_str $an, $bn; local n = bi_mul_str;
    bi_mul_str $ad, $bd; local d = bi_mul_str;
    br_reduce n, d;
}

proc br_node {
    if br_d == "1" {
        mk_big br_n;
        br_node = mk_big;
    } else {
        mk_big br_n;
        local num = mk_big;
        mk_big br_d;
        local den = mk_big;
        mk_pow den, -1;
        local inv = mk_pow;
        mk_mul num, inv;
        
        br_node = mk_mul;
    }
}

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
            br_n = "0";
            br_d = "1";
            if $is_prod == 1 { br_n = "1"; }
            sum_seen_num = false;
            local mixed = false;
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
                    if (nd_kind[val] == K.Num or is_big(val)) and mixed == false {
                        local vnstr = "";
                        local vdstr = "1";
                        if nd_kind[val] == K.Num {
                            vnstr = "" & nd_num[val];
                            vdstr = "" & nd_den[val];
                        } else {
                            vnstr = nd_txt[val];
                        }
                        if $is_prod == 1 {
                            br_mul_str br_n, br_d, vnstr, vdstr;
                        } else {
                            br_add_str br_n, br_d, vnstr, vdstr;
                        }
                        sum_seen_num = true;
                    } else {
                        if mixed == false {
                            if sum_seen_num == true {
                                br_node;
                                acc = br_node;
                            }
                            mixed = true;
                        }
                        if $is_prod == 1 {
                            mk_mul acc, val;
                            acc = mk_mul;
                        } else {
                            mk_add acc, val;
                            acc = mk_add;
                        }
                    }
                }
                k += step;
                guard++;
            }
            if err == "" {
                if mixed == false and sum_seen_num == true {
                    br_node;
                    sum_range = br_node;
                } else {
                    rules_simplify acc;
                    if err == "" { sum_range = rules_simplify; }
                }
            }
        }
    }
}
