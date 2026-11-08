# Exact special values and simple induction for sin/cos/tan.

var tg_n = 0;
var tg_d = 1;
var tg_ok = false;

func tg_match(num, den) {
    return tg_n * $den == $num * tg_d;
}

proc tg_pi_coeff arg {
    tg_ok = false;
    if nd_kind[$arg] == K.Pi {
        tg_n = 1; tg_d = 1; tg_ok = true;
    } elif nd_kind[$arg] == K.Num and nd_num[$arg] == 0 {
        tg_n = 0; tg_d = 1; tg_ok = true;
    } elif nd_kind[$arg] == K.Mul {
        local a = nd_a[$arg];
        local b = nd_b[$arg];
        if nd_kind[a] == K.Pi and nd_kind[b] == K.Num {
            tg_n = nd_num[b]; tg_d = nd_den[b]; tg_ok = true;
        } elif nd_kind[b] == K.Pi and nd_kind[a] == K.Num {
            tg_n = nd_num[a]; tg_d = nd_den[a]; tg_ok = true;
        }
    }
}

proc tg_num n, d {
    mk_num $n, $d;
    tg_num = mk_num;
}

proc tg_sqrt2_half {
    mk_num 2, 1;
    local n2 = mk_num;
    mk_func K.Sqrt, n2;
    local s = mk_func;
    mk_num 1, 2;
    mk_mul s, mk_num;
    tg_sqrt2_half = mk_mul;
}

proc tg_sqrt3_half {
    mk_num 3, 1;
    local n3 = mk_num;
    mk_func K.Sqrt, n3;
    local s = mk_func;
    mk_num 1, 2;
    mk_mul s, mk_num;
    tg_sqrt3_half = mk_mul;
}

proc tg_sqrt3 {
    mk_num 3, 1;
    local n3 = mk_num;
    mk_func K.Sqrt, n3;
    tg_sqrt3 = mk_func;
}

proc tg_sqrt3_third {
    mk_num 3, 1;
    local n3 = mk_num;
    mk_func K.Sqrt, n3;
    local s = mk_func;
    mk_num 1, 3;
    mk_mul s, mk_num;
    tg_sqrt3_third = mk_mul;
}

proc tg_sqrt2_val {
    mk_num 2, 1; mk_func K.Sqrt, mk_num; tg_sqrt2_val = mk_func;
}
proc tg_sqrt5_val {
    mk_num 5, 1; mk_func K.Sqrt, mk_num; tg_sqrt5_val = mk_func;
}
proc tg_sqrt6_val {
    mk_num 6, 1; mk_func K.Sqrt, mk_num; tg_sqrt6_val = mk_func;
}
proc tg_sin_pi8 {
    tg_sqrt2_val; local s = tg_sqrt2_val;
    mk_num 2, 1; local two = mk_num;
    mk_neg s; mk_add two, mk_neg; local inside = mk_add;
    mk_func K.Sqrt, inside; local root = mk_func;
    mk_num 1, 2; mk_mul mk_num, root; tg_sin_pi8 = mk_mul;
}
proc tg_cos_pi8 {
    tg_sqrt2_val; local s = tg_sqrt2_val;
    mk_num 2, 1; local two = mk_num;
    mk_add two, s; local inside = mk_add;
    mk_func K.Sqrt, inside; local root = mk_func;
    mk_num 1, 2; mk_mul mk_num, root; tg_cos_pi8 = mk_mul;
}
proc tg_sin_pi5 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 2, 1; mk_mul mk_num, s; local two_s = mk_mul;
    mk_num 10, 1; local ten = mk_num;
    mk_neg two_s; mk_add ten, mk_neg; local inside = mk_add;
    mk_func K.Sqrt, inside; local root = mk_func;
    mk_num 1, 4; mk_mul mk_num, root; tg_sin_pi5 = mk_mul;
}
proc tg_cos_pi5 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 1, 1; local one = mk_num;
    mk_add one, s; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_cos_pi5 = mk_mul;
}
proc tg_sin_2pi5 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 2, 1; mk_mul mk_num, s; local two_s = mk_mul;
    mk_num 10, 1; local ten = mk_num;
    mk_add ten, two_s; local inside = mk_add;
    mk_func K.Sqrt, inside; local root = mk_func;
    mk_num 1, 4; mk_mul mk_num, root; tg_sin_2pi5 = mk_mul;
}
proc tg_cos_2pi5 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 1, 1; local one = mk_num;
    mk_neg one; mk_add s, mk_neg; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_cos_2pi5 = mk_mul;
}
proc tg_sin_pi10 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 1, 1; local one = mk_num;
    mk_neg one; mk_add s, mk_neg; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_sin_pi10 = mk_mul;
}
proc tg_cos_pi10 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 2, 1; mk_mul mk_num, s; local two_s = mk_mul;
    mk_num 10, 1; local ten = mk_num;
    mk_add ten, two_s; local inside = mk_add;
    mk_func K.Sqrt, inside; local root = mk_func;
    mk_num 1, 4; mk_mul mk_num, root; tg_cos_pi10 = mk_mul;
}
proc tg_sin_3pi10 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 1, 1; local one = mk_num;
    mk_add one, s; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_sin_3pi10 = mk_mul;
}
proc tg_cos_3pi10 {
    tg_sqrt5_val; local s = tg_sqrt5_val;
    mk_num 2, 1; mk_mul mk_num, s; local two_s = mk_mul;
    mk_num 10, 1; local ten = mk_num;
    mk_neg two_s; mk_add ten, mk_neg; local inside = mk_add;
    mk_func K.Sqrt, inside; local root = mk_func;
    mk_num 1, 4; mk_mul mk_num, root; tg_cos_3pi10 = mk_mul;
}
proc tg_sin_pi12 {
    tg_sqrt6_val; local s6 = tg_sqrt6_val;
    tg_sqrt2_val; local s2 = tg_sqrt2_val;
    mk_neg s2; mk_add s6, mk_neg; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_sin_pi12 = mk_mul;
}
proc tg_cos_pi12 {
    tg_sqrt6_val; local s6 = tg_sqrt6_val;
    tg_sqrt2_val; local s2 = tg_sqrt2_val;
    mk_add s6, s2; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_cos_pi12 = mk_mul;
}
proc tg_sin_5pi12 {
    tg_sqrt6_val; local s6 = tg_sqrt6_val;
    tg_sqrt2_val; local s2 = tg_sqrt2_val;
    mk_add s6, s2; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_sin_5pi12 = mk_mul;
}
proc tg_cos_5pi12 {
    tg_sqrt6_val; local s6 = tg_sqrt6_val;
    tg_sqrt2_val; local s2 = tg_sqrt2_val;
    mk_neg s2; mk_add s6, mk_neg; local inside = mk_add;
    mk_num 1, 4; mk_mul mk_num, inside; tg_cos_5pi12 = mk_mul;
}
proc tg_sin_idx i {
    if $i == 0 { tg_num 0, 1; tg_sin_idx = tg_num; }
    elif $i == 1 { tg_num 1, 2; tg_sin_idx = tg_num; }
    elif $i == 2 { tg_sqrt2_half; tg_sin_idx = tg_sqrt2_half; }
    elif $i == 3 { tg_sqrt3_half; tg_sin_idx = tg_sqrt3_half; }
    elif $i == 4 { tg_num 1, 1; tg_sin_idx = tg_num; }
    elif $i == 5 { tg_sin_pi8; tg_sin_idx = tg_sin_pi8; }
    elif $i == 6 { tg_cos_pi8; tg_sin_idx = tg_cos_pi8; }
    elif $i == 7 { tg_sin_pi5; tg_sin_idx = tg_sin_pi5; }
    elif $i == 8 { tg_sin_2pi5; tg_sin_idx = tg_sin_2pi5; }
    elif $i == 9 { tg_sin_pi10; tg_sin_idx = tg_sin_pi10; }
    elif $i == 10 { tg_sin_3pi10; tg_sin_idx = tg_sin_3pi10; }
    elif $i == 11 { tg_sin_pi12; tg_sin_idx = tg_sin_pi12; }
    elif $i == 12 { tg_sin_5pi12; tg_sin_idx = tg_sin_5pi12; }
    elif $i == 13 { tg_sin_5pi12; tg_sin_idx = tg_sin_5pi12; }
    else { tg_num 1, 1; tg_sin_idx = tg_num; }
}

proc tg_cos_idx i {
    if $i == 0 { tg_num 1, 1; tg_cos_idx = tg_num; }
    elif $i == 1 { tg_sqrt3_half; tg_cos_idx = tg_sqrt3_half; }
    elif $i == 2 { tg_sqrt2_half; tg_cos_idx = tg_sqrt2_half; }
    elif $i == 3 { tg_num 1, 2; tg_cos_idx = tg_num; }
    elif $i == 4 { tg_num 0, 1; tg_cos_idx = tg_num; }
    elif $i == 5 { tg_cos_pi8; tg_cos_idx = tg_cos_pi8; }
    elif $i == 6 { tg_sin_pi8; tg_cos_idx = tg_sin_pi8; }
    elif $i == 7 { tg_cos_pi5; tg_cos_idx = tg_cos_pi5; }
    elif $i == 8 { tg_cos_2pi5; tg_cos_idx = tg_cos_2pi5; }
    elif $i == 9 { tg_cos_pi10; tg_cos_idx = tg_cos_pi10; }
    elif $i == 10 { tg_cos_3pi10; tg_cos_idx = tg_cos_3pi10; }
    elif $i == 11 { tg_cos_pi12; tg_cos_idx = tg_cos_pi12; }
    elif $i == 12 { tg_cos_5pi12; tg_cos_idx = tg_cos_5pi12; }
    elif $i == 13 { tg_cos_5pi12; mk_neg tg_cos_5pi12; tg_cos_idx = mk_neg; }
    else { tg_num 0, 1; tg_cos_idx = tg_num; }
}

proc tg_tan_idx i {
    if $i == 0 { tg_num 0, 1; tg_tan_idx = tg_num; }
    elif $i == 1 { tg_sqrt3_third; tg_tan_idx = tg_sqrt3_third; }
    elif $i == 2 { tg_num 1, 1; tg_tan_idx = tg_num; }
    elif $i == 3 { tg_sqrt3; tg_tan_idx = tg_sqrt3; }
    elif $i == 4 { mk_undef; tg_tan_idx = mk_undef; }
    elif $i == 5 {
        tg_sqrt2_val; local s2 = tg_sqrt2_val;
        mk_num 1, 1; mk_neg mk_num; mk_add s2, mk_neg; tg_tan_idx = mk_add;
    } elif $i == 6 {
        tg_sqrt2_val; local s2 = tg_sqrt2_val;
        mk_num 1, 1; mk_add s2, mk_num; tg_tan_idx = mk_add;
    } elif $i == 7 {
        tg_sqrt5_val; local s5 = tg_sqrt5_val;
        mk_num 2, 1; mk_mul mk_num, s5; local t = mk_mul;
        mk_num 5, 1; local five = mk_num;
        mk_neg t; mk_add five, mk_neg; local inside = mk_add;
        mk_func K.Sqrt, inside; tg_tan_idx = mk_func;
    } elif $i == 8 {
        tg_sqrt5_val; local s5 = tg_sqrt5_val;
        mk_num 2, 1; mk_mul mk_num, s5; local t = mk_mul;
        mk_num 5, 1; mk_add mk_num, t; local inside = mk_add;
        mk_func K.Sqrt, inside; tg_tan_idx = mk_func;
    } elif $i == 9 {
        tg_sqrt5_val; local s5 = tg_sqrt5_val;
        mk_num 10, 1; mk_mul mk_num, s5; local t = mk_mul;
        mk_num 25, 1; local twentyfive = mk_num;
        mk_neg t; mk_add twentyfive, mk_neg; local inside = mk_add;
        mk_func K.Sqrt, inside; local root = mk_func;
        mk_num 1, 5; mk_mul mk_num, root; tg_tan_idx = mk_mul;
    } elif $i == 10 {
        tg_sqrt5_val; local s5 = tg_sqrt5_val;
        mk_num 10, 1; mk_mul mk_num, s5; local t = mk_mul;
        mk_num 25, 1; mk_add mk_num, t; local inside = mk_add;
        mk_func K.Sqrt, inside; local root = mk_func;
        mk_num 1, 5; mk_mul mk_num, root; tg_tan_idx = mk_mul;
    } elif $i == 11 {
        tg_sqrt3; local s3 = tg_sqrt3;
        mk_num 2, 1; local two = mk_num;
        mk_neg s3; mk_add two, mk_neg; tg_tan_idx = mk_add;
    } elif $i == 12 {
        tg_sqrt3; local s3 = tg_sqrt3;
        mk_num 2, 1; mk_add mk_num, s3; tg_tan_idx = mk_add;
    } elif $i == 13 {
        tg_sqrt3; local s3 = tg_sqrt3;
        mk_num 2, 1; mk_add mk_num, s3; local sum = mk_add; mk_neg sum; tg_tan_idx = mk_neg;
    } else { mk_undef; tg_tan_idx = mk_undef; }
}

func tg_idx(n, d) {
    if $n == 0 { return 0; }
    if $n * 6 == $d { return 1; }
    if $n * 4 == $d { return 2; }
    if $n * 3 == $d { return 3; }
    if $n * 2 == $d { return 4; }
    if $d == 8 and $n == 1 { return 5; }
    if $d == 8 and $n == 3 { return 6; }
    if $d == 5 and $n == 1 { return 7; }
    if $d == 5 and $n == 2 { return 8; }
    if $d == 10 and $n == 1 { return 9; }
    if $d == 10 and $n == 3 { return 10; }
    if $d == 10 and $n == 2 { return 7; }
    if $d == 10 and $n == 4 { return 8; }
    if $d == 12 and $n == 1 { return 11; }
    if $d == 12 and $n == 5 { return 12; }
    if $d == 12 and $n == 7 { return 13; }
    return -1;
}

proc tg_special kind, arg {
    tg_special = 0;
    tg_pi_coeff $arg;
    if tg_ok {
        local n = tg_n;
        local d = tg_d;
        local period = 2 * d;
        n = n % period;
        if n < 0 { n += period; }
        # n/d in [0,2)
        local sign = 1;
        local nn = n;
        if $kind == K.Tan {
            local one = d;
            if n * 2 == d {
                mk_undef;
                tg_special = mk_undef;
            } else {
                if n * 2 > d {
                    sign = -1;
                    nn = 2 * d - n;
                }
                local idx = tg_idx(nn, d);
                if idx < 0 {
                    tg_special = 0;
                } else {
                    tg_tan_idx idx;
                    local v = tg_tan_idx;
                    if v == 0 { tg_special = 0; } elif sign < 0 {
                        mk_num -1, 1; mk_mul mk_num, v; tg_special = mk_mul;
                    } else { tg_special = v; }
                }
            }
        } else {
            if n * 2 <= d {
                nn = n;
            } elif n <= d {
                nn = d - n;
                if $kind == K.Cos { sign = -1; }
            } elif n * 2 <= 3 * d {
                nn = n - d;
                sign = -1;
            } else {
                nn = 2 * d - n;
                sign = -1;
                if $kind == K.Cos { sign = 1; }
            }
            local idx2 = tg_idx(nn, d);
            if idx2 < 0 {
                tg_special = 0;
            } else {
                if $kind == K.Sin { tg_sin_idx idx2; } else { tg_cos_idx idx2; }
                local vv = tg_sin_idx;
                if $kind == K.Cos { vv = tg_cos_idx; }
                if idx2 == 0 and $kind == K.Sin { tg_special = 0; }
                elif vv == 0 { tg_special = 0; }
                elif sign < 0 {
                    mk_num -1, 1; mk_mul mk_num, vv; tg_special = mk_mul;
                } else { tg_special = vv; }
            }
        }
    }
}

proc tg_neg_arg arg {
    tg_neg_arg = 0;
    if nd_kind[$arg] == K.Num and nd_num[$arg] < 0 {
        mk_num -nd_num[$arg], nd_den[$arg];
        tg_neg_arg = mk_num;
    } elif nd_kind[$arg] == K.Mul {
        local a = nd_a[$arg];
        local b = nd_b[$arg];
        if nd_kind[a] == K.Num and nd_num[a] < 0 {
            mk_num -nd_num[a], nd_den[a];
            mk_mul mk_num, b;
            tg_neg_arg = mk_mul;
        } elif nd_kind[b] == K.Num and nd_num[b] < 0 {
            mk_num -nd_num[b], nd_den[b];
            mk_mul mk_num, a;
            tg_neg_arg = mk_mul;
        }
    }
}

var tg_shift_sign = 1;
list tg_terms;
list tg_stk2;

proc tg_pi_shift arg {
    tg_pi_shift = 0;
    tg_shift_sign = 1;
    if nd_kind[$arg] != K.Add {
        tg_pi_shift = 0;
    } else {
        delete tg_terms;
        delete tg_stk2;
        local sp = 0;
        sp++; add $arg to tg_stk2;
        until sp == 0 {
            local x = tg_stk2[sp];
            sp--;
            if nd_kind[x] == K.Add {
                sp++;
                if sp > length(tg_stk2) { add nd_b[x] to tg_stk2; } else { tg_stk2[sp] = nd_b[x]; }
                sp++;
                if sp > length(tg_stk2) { add nd_a[x] to tg_stk2; } else { tg_stk2[sp] = nd_a[x]; }
            } else {
                add x to tg_terms;
            }
        }
        local found = 0;
        local k = 0;
        local i = 1;
        until i > length(tg_terms) or found != 0 {
            tg_pi_coeff tg_terms[i];
            if tg_ok and tg_d == 1 {
                found = i;
                k = tg_n;
            }
            i++;
        }
        if found > 0 {
            delete tg_rest;
            i = 1;
            until i > length(tg_terms) {
                if i != found { add tg_terms[i] to tg_rest; }
                i++;
            }
            if length(tg_rest) == 0 {
                tg_pi_shift = 0;
            } else {
                local rest = tg_rest[1];
                i = 2;
                until i > length(tg_rest) {
                    mk_add rest, tg_rest[i];
                    rest = mk_add;
                    i++;
                }
                if abs(k) % 2 == 1 { tg_shift_sign = -1; }
                tg_pi_shift = rest;
            }
        }
    }
}

list tg_rest;


proc tg_sqrt_1m u {
    mk_num 1, 1;
    local one = mk_num;
    mk_pow $u, 2;
    local sq = mk_pow;
    mk_neg sq;
    local nsq = mk_neg;
    mk_add one, nsq;
    local inside = mk_add;
    mk_func K.Sqrt, inside;
    tg_sqrt_1m = mk_func;
}

proc tg_sqrt_1p u {
    mk_num 1, 1;
    local one = mk_num;
    mk_pow $u, 2;
    local sq = mk_pow;
    mk_add one, sq;
    local inside = mk_add;
    mk_func K.Sqrt, inside;
    tg_sqrt_1p = mk_func;
}

proc tg_div num, den {
    mk_pow $den, -1;
    local inv = mk_pow;
    mk_mul $num, inv;
    tg_div = mk_mul;
}

proc tg_compose kind, arg {
    local u = nd_a[$arg];
    local t = nd_kind[$arg];
    if $kind == K.Sin {
        if t == K.Asin { tg_compose = u; }
        elif t == K.Acos { tg_sqrt_1m u; tg_compose = tg_sqrt_1m; }
        else { tg_sqrt_1p u; local root = tg_sqrt_1p; tg_div u, root; tg_compose = tg_div; }
    } elif $kind == K.Cos {
        if t == K.Asin { tg_sqrt_1m u; tg_compose = tg_sqrt_1m; }
        elif t == K.Acos { tg_compose = u; }
        else { tg_sqrt_1p u; local root = tg_sqrt_1p; mk_num 1, 1; tg_div mk_num, root; tg_compose = tg_div; }
    } else {
        if t == K.Asin {
            tg_sqrt_1m u;
            local root = tg_sqrt_1m;
            tg_div u, root;
            tg_compose = tg_div;
        } elif t == K.Acos {
            tg_sqrt_1m u;
            local root = tg_sqrt_1m;
            tg_div root, u;
            tg_compose = tg_div;
        } else { tg_compose = u; }
    }
}

proc tg_func kind, arg {
    if nd_kind[$arg] >= K.Asin and nd_kind[$arg] <= K.Atan {
        tg_compose $kind, $arg;
        tg_func = tg_compose;
    } elif nd_kind[$arg] == K.Num and nd_num[$arg] == 0 {
        if $kind == K.Sin or $kind == K.Tan { tg_num 0, 1; tg_func = tg_num; }
        else { tg_num 1, 1; tg_func = tg_num; }
    } else {
        tg_special $kind, $arg;
        if tg_special != 0 {
            tg_func = tg_special;
        } else {
            tg_neg_arg $arg;
            if tg_neg_arg != 0 {
                tg_func $kind, tg_neg_arg;
                local v = tg_func;
                if $kind == K.Cos or v == 0 { tg_func = v; }
                else { mk_num -1, 1; mk_mul mk_num, v; tg_func = mk_mul; }
            } else {
                tg_pi_shift $arg;
                if tg_pi_shift != 0 {
                    local sgn = tg_shift_sign;
                    tg_func $kind, tg_pi_shift;
                    local sv = tg_func;
                    if $kind == K.Tan or sv == 0 { tg_func = sv; }
                    elif sgn < 0 {
                        mk_num -1, 1; mk_mul mk_num, sv; tg_func = mk_mul;
                    } else { tg_func = sv; }
                } else {
                    new_func_raw $kind, $arg;
                    tg_func = new_func_raw;
                }
            }
        }
    }
}

proc tg_inverse kind, arg {
    tg_inverse = 0;
    if nd_kind[$arg] == K.Num {
        local n = nd_num[$arg];
        local d = nd_den[$arg];
        if $kind == K.Asin {
            if n == 0 { tg_num 0, 1; tg_inverse = tg_num; }
            elif n * 2 == d { mk_var "pi"; mk_num 1, 6; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
            elif n == d { mk_var "pi"; mk_num 1, 2; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
            elif n * 2 == -d { mk_var "pi"; mk_num -1, 6; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
            elif n == -d { mk_var "pi"; mk_num -1, 2; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
        } elif $kind == K.Acos {
            if n == d { tg_num 0, 1; tg_inverse = tg_num; }
            elif n == 0 { mk_var "pi"; mk_num 1, 2; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
            elif n * 2 == d { mk_var "pi"; mk_num 1, 3; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
            elif n == -d { mk_var "pi"; tg_inverse = mk_var; }
        } elif $kind == K.Atan {
            if n == 0 { tg_num 0, 1; tg_inverse = tg_num; }
            elif n == d { mk_var "pi"; mk_num 1, 4; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
            elif n == -d { mk_var "pi"; mk_num -1, 4; mk_mul mk_var, mk_num; tg_inverse = mk_mul; }
        }
    }
}

proc tg_rebuild n {
    local k = nd_kind[$n];
    if k == K.Add {
        mk_add tg_val[nd_a[$n]], tg_val[nd_b[$n]];
        tg_rebuild = mk_add;
    } elif k == K.Mul {
        mk_mul tg_val[nd_a[$n]], tg_val[nd_b[$n]];
        tg_rebuild = mk_mul;
    } elif k == K.Pow {
        mk_pow tg_val[nd_a[$n]], nd_num[$n];
        tg_rebuild = mk_pow;
    } elif k == K.PowE {
        mk_pow_expr tg_val[nd_a[$n]], tg_val[nd_b[$n]];
        tg_rebuild = mk_pow_expr;
    } elif k == K.Sin or k == K.Cos or k == K.Tan {
        tg_func k, tg_val[nd_a[$n]];
        tg_rebuild = tg_func;
    } elif k == K.Asin or k == K.Acos or k == K.Atan {
        tg_inverse k, tg_val[nd_a[$n]];
        if tg_inverse != 0 { tg_rebuild = tg_inverse; }
        else { new_func_raw k, tg_val[nd_a[$n]]; tg_rebuild = new_func_raw; }
    } elif k >= K.Sin and k <= K.Atan {
        new_func_raw k, tg_val[nd_a[$n]];
        tg_rebuild = new_func_raw;
    } elif k == K.Unknown {
        mk_genfunc nd_txt[$n], tg_val[nd_a[$n]];
        tg_rebuild = mk_genfunc;
    } else {
        tg_rebuild = $n;
    }
}

list tg_val;
list tg_stk_node;
list tg_stk_state;

proc trig_simplify root {
    delete tg_val;
    local i = 1;
    until i > node_count { add 0 to tg_val; i++; }
    delete tg_stk_node;
    delete tg_stk_state;
    local sp = 0;
    sp++;
    add $root to tg_stk_node;
    add 0 to tg_stk_state;
    until sp == 0 or err != "" {
        local n = tg_stk_node[sp];
        local st = tg_stk_state[sp];
        sp--;
        if st == 0 {
            sp++;
            if sp > length(tg_stk_node) { add n to tg_stk_node; add 1 to tg_stk_state; }
            else { tg_stk_node[sp] = n; tg_stk_state[sp] = 1; }
            local k = nd_kind[n];
            if k == K.Add or k == K.Mul or k == K.PowE {
                sp++;
                if sp > length(tg_stk_node) { add nd_b[n] to tg_stk_node; add 0 to tg_stk_state; }
                else { tg_stk_node[sp] = nd_b[n]; tg_stk_state[sp] = 0; }
                sp++;
                if sp > length(tg_stk_node) { add nd_a[n] to tg_stk_node; add 0 to tg_stk_state; }
                else { tg_stk_node[sp] = nd_a[n]; tg_stk_state[sp] = 0; }
            } elif k == K.Pow {
                sp++;
                if sp > length(tg_stk_node) { add nd_a[n] to tg_stk_node; add 0 to tg_stk_state; }
                else { tg_stk_node[sp] = nd_a[n]; tg_stk_state[sp] = 0; }
            } elif (k >= K.Sin and k <= K.Atan) or k == K.Unknown {
                sp++;
                if sp > length(tg_stk_node) { add nd_a[n] to tg_stk_node; add 0 to tg_stk_state; }
                else { tg_stk_node[sp] = nd_a[n]; tg_stk_state[sp] = 0; }
            }
        } else {
            tg_rebuild n;
            if err == "" { tg_val[n] = tg_rebuild; }
        }
    }
    if err != "" { trig_simplify = 0; } else { trig_simplify = tg_val[$root]; }
}
