# Decimal-string arbitrary precision integers.

list big_l1;
list big_l2;
list big_l3;
var bs1 = 1;
var bs2 = 1;
var bi_q = "0";
var bi_r = "0";

func bi_norm(s) {
    local t = trim($s);
    local sg = 1;
    if length(t) > 0 and t[1] == "-" {
        sg = -1;
        t = substr(t, 2, length(t));
    }
    local i = 1;
    until i >= length(t) or t[i] != "0" { i++; }
    if i > length(t) { t = "0"; }
    else { t = substr(t, i, length(t)); }
    if t == "0" { return "0"; }
    if sg < 0 { return "-" & t; }
    return t;
}

proc bi_load1 s {
    local t = bi_norm($s);
    bs1 = 1;
    if length(t) > 0 and t[1] == "-" { bs1 = -1; t = substr(t, 2, length(t)); }
    delete big_l1;
    local i = length(t);
    until i < 1 {
        add digit_value(t[i]) to big_l1;
        i--;
    }
}

proc bi_load2 s {
    local t = bi_norm($s);
    bs2 = 1;
    if length(t) > 0 and t[1] == "-" { bs2 = -1; t = substr(t, 2, length(t)); }
    delete big_l2;
    local i = length(t);
    until i < 1 {
        add digit_value(t[i]) to big_l2;
        i--;
    }
}

proc bi_trim3 {
    until length(big_l3) <= 1 or big_l3[length(big_l3)] != 0 {
        local lidx = length(big_l3);
        delete big_l3[lidx];
    }
}

proc bi_save3 {
    bi_trim3;
    local s = "";
    local i = length(big_l3);
    until i < 1 {
        s = s & big_l3[i];
        i--;
    }
    bi_save3 = bi_norm(s);
}

proc bi_cmp_abs12 {
    if length(big_l1) > length(big_l2) { bi_cmp_abs12 = 1; }
    elif length(big_l1) < length(big_l2) { bi_cmp_abs12 = -1; }
    else {
        local i = length(big_l1);
        local r = 0;
        until i < 1 or r != 0 {
            if big_l1[i] > big_l2[i] { r = 1; }
            elif big_l1[i] < big_l2[i] { r = -1; }
            i--;
        }
        bi_cmp_abs12 = r;
    }
}

proc bi_add_abs12 {
    delete big_l3;
    local carry = 0;
    local i = 1;
    until i > length(big_l1) and i > length(big_l2) and carry == 0 {
        local x = 0;
        local y = 0;
        if i <= length(big_l1) { x = big_l1[i]; }
        if i <= length(big_l2) { y = big_l2[i]; }
        local z = x + y + carry;
        add z % 10 to big_l3;
        carry = floor(z / 10);
        i++;
    }
    if length(big_l3) == 0 { add 0 to big_l3; }
}

proc bi_sub_abs12 {
    delete big_l3;
    local borrow = 0;
    local i = 1;
    until i > length(big_l1) {
        local x = big_l1[i];
        local y = 0;
        if i <= length(big_l2) { y = big_l2[i]; }
        local z = x - y - borrow;
        if z < 0 { z += 10; borrow = 1; } else { borrow = 0; }
        add z to big_l3;
        i++;
    }
    if length(big_l3) == 0 { add 0 to big_l3; }
}

proc bi_mul_abs12 {
    delete big_l3;
    local i = 1;
    until i > length(big_l1) + length(big_l2) {
        add 0 to big_l3;
        i++;
    }
    i = 1;
    until i > length(big_l1) {
        local j = 1;
        until j > length(big_l2) {
            local p = i + j - 1;
            big_l3[p] = big_l3[p] + big_l1[i] * big_l2[j];
            j++;
        }
        i++;
    }
    local carry = 0;
    i = 1;
    until i > length(big_l3) {
        local z = big_l3[i] + carry;
        big_l3[i] = z % 10;
        carry = floor(z / 10);
        i++;
    }
    until carry == 0 {
        add carry % 10 to big_l3;
        carry = floor(carry / 10);
    }
    if length(big_l3) == 0 { add 0 to big_l3; }
}

proc bi_add_dec a, b {
    bi_load1 $a;
    bi_load2 $b;
    if bs1 == bs2 {
        bi_add_abs12;
        bi_save3;
        if bs1 < 0 and bi_save3 != "0" { bi_add_dec = "-" & bi_save3; }
        else { bi_add_dec = bi_save3; }
    } else {
        bi_cmp_abs12;
        if bi_cmp_abs12 == 0 { bi_add_dec = "0"; }
        elif bi_cmp_abs12 > 0 {
            bi_sub_abs12; bi_save3;
            if bs1 < 0 { bi_add_dec = "-" & bi_save3; } else { bi_add_dec = bi_save3; }
        } else {
            bi_sub_abs12; bi_save3;
            if bs2 < 0 { bi_add_dec = "-" & bi_save3; } else { bi_add_dec = bi_save3; }
        }
    }
}

proc bi_neg_str a {
    local t = bi_norm($a);
    if t == "0" { bi_neg_str = "0"; }
    elif t[1] == "-" { bi_neg_str = substr(t, 2, length(t)); }
    else { bi_neg_str = "-" & t; }
}

proc bi_sub_dec a, b {
    bi_neg_str $b;
    bi_add_dec $a, bi_neg_str;
    bi_sub_dec = bi_add_dec;
}

proc bi_mul_dec a, b {
    bi_load1 $a;
    bi_load2 $b;
    bi_mul_abs12;
    bi_save3;
    if (bs1 * bs2 < 0) and bi_save3 != "0" { bi_mul_dec = "-" & bi_save3; }
    else { bi_mul_dec = bi_save3; }
}

list bd_rem;
list bd_q;
var bi_div_q = "0";
var bi_div_r = "0";
var stop_loop = false;
var done_div = false;
var q_break = false;
var q_loop_done = false;
var break_until = false;
var until_break = false;

var bi_a = "0";
var bi_b = "0";

proc bi_cmp_abs_str a, b {
    bi_load1 $a;
    bi_load2 $b;
    bi_cmp_abs12;
    bi_cmp_abs_str = bi_cmp_abs12;
}

proc bi_div_long {
    local aa = bi_norm(bi_a);
    local bb = bi_norm(bi_b);
    if length(bb) > 0 and bb[1] == "-" { bb = substr(bb, 2, length(bb)); }
    if length(aa) > 0 and aa[1] == "-" { aa = substr(aa, 2, length(aa)); }
    local rem = "0";
    local qs = "";
    local i = 1;
    until i > length(aa) {
        if rem == "0" { rem = aa[i]; } else { rem = rem & aa[i]; }
        local q = 0;
        local going = true;
        until going == false {
            bi_cmp_abs_str rem, bb;
            if bi_cmp_abs_str < 0 { going = false; }
            else {
                bi_sub_dec rem, bb;
                rem = bi_sub_dec;
                q++;
            }
        }
        if not (qs == "" and q == 0) { qs = qs & q; }
        i++;
    }
    if qs == "" { qs = "0"; }
    bi_div_q = bi_norm(qs);
    bi_div_r = bi_norm(rem);
}


proc bi_div_str a, b {
    bi_a = $a;
    bi_b = $b;
    bi_div_long;
    bi_div_str = bi_div_q;
}

proc bi_mod_str a, b {
    bi_a = $a;
    bi_b = $b;
    bi_div_long;
    bi_mod_str = bi_div_r;
}

proc bi_pow_str a, e {
    local n = 0;
    local i = 1;
    until i > length($e) {
        n = n * 10 + digit_value($e[i]);
        i++;
    }
    if n > 100000 { set_err "指数过大"; }
    local res = "1";
    local base = $a;
    until n == 0 or err != "" {
        if n % 2 == 1 {
            bi_mul_str res, base;
            if err == "" { res = bi_mul_str; }
        }
        n = floor(n / 2);
        if n > 0 {
            bi_mul_str base, base;
            if err == "" { base = bi_mul_str; }
        }
    }
    bi_pow_str = res;
}


proc bi_gcd_str a, b {
    local x = bi_norm($a);
    local y = bi_norm($b);
    if x[1] == "-" { x = substr(x, 2, length(x)); }
    if y[1] == "-" { y = substr(y, 2, length(y)); }
    until y == "0" {
        bi_mod_str x, y;
        local r = bi_mod_str;
        x = y;
        y = r;
    }
    bi_gcd_str = x;
}

proc bi_lcm_str a, b {
    bi_gcd_str $a, $b;
    local g = bi_gcd_str;
    bi_mul_str $a, $b;
    local p = bi_mul_str;
    bi_div_str p, g;
    bi_lcm_str = bi_div_q;
}

# Base-10^7 chunk arithmetic (fast path for add/sub/mul).
var zc_neg1 = 1;
var zc_neg2 = 1;
list zc_a;
list zc_b;
list zc_r;

proc zc_load1 s {
    local t = bi_norm($s);
    zc_neg1 = 1;
    if length(t) > 0 and t[1] == "-" { zc_neg1 = -1; t = substr(t, 2, length(t)); }
    delete zc_a;
    local n = length(t);
    until n < 1 {
        local st = n - 6;
        if st < 1 { st = 1; }
        local part = substr(t, st, n);
        add part to zc_a;
        n = st - 1;
    }
    if length(zc_a) == 0 { add 0 to zc_a; }
}

proc zc_load2 s {
    local t = bi_norm($s);
    zc_neg2 = 1;
    if length(t) > 0 and t[1] == "-" { zc_neg2 = -1; t = substr(t, 2, length(t)); }
    delete zc_b;
    local n = length(t);
    until n < 1 {
        local st = n - 6;
        if st < 1 { st = 1; }
        add substr(t, st, n) to zc_b;
        n = st - 1;
    }
    if length(zc_b) == 0 { add 0 to zc_b; }
}

proc zc_trim3 {
    until length(zc_r) <= 1 or zc_r[length(zc_r)] != 0 {
        local li = length(zc_r);
        delete zc_r[li];
    }
}

proc zc_save3 {
    zc_trim3;
    local s = "";
    local i = length(zc_r);
    until i < 1 {
        local part = zc_r[i];
        if i == length(zc_r) {
            s = s & part;
        } else {
            local ps = part;
            until length(ps) >= 7 { ps = "0" & ps; }
            s = s & ps;
        }
        i--;
    }
    if s == "" { s = "0"; }
    zc_save3 = bi_norm(s);
}

proc zc_cmp12 {
    if length(zc_a) > length(zc_b) { zc_cmp12 = 1; }
    elif length(zc_a) < length(zc_b) { zc_cmp12 = -1; }
    else {
        local i = length(zc_a);
        local r = 0;
        until i < 1 or r != 0 {
            local x = zc_a[i];
            local y = zc_b[i];
            if x > y { r = 1; }
            elif x < y { r = -1; }
            i--;
        }
        zc_cmp12 = r;
    }
}

proc zc_add_abs {
    delete zc_r;
    local carry = 0;
    local i = 1;
    until i > length(zc_a) and i > length(zc_b) and carry == 0 {
        local x = 0;
        local y = 0;
        if i <= length(zc_a) { x = zc_a[i]; }
        if i <= length(zc_b) { y = zc_b[i]; }
        local z = x + y + carry;
        add z % 10000000 to zc_r;
        carry = floor(z / 10000000);
        i++;
    }
    if length(zc_r) == 0 { add 0 to zc_r; }
}

proc zc_sub_abs {
    delete zc_r;
    local borrow = 0;
    local i = 1;
    until i > length(zc_a) {
        local x = zc_a[i];
        local y = 0;
        if i <= length(zc_b) { y = zc_b[i]; }
        local z = x - y - borrow;
        if z < 0 { z += 10000000; borrow = 1; } else { borrow = 0; }
        add z to zc_r;
        i++;
    }
    if length(zc_r) == 0 { add 0 to zc_r; }
}

proc bi_add_str a, b {
    zc_load1 $a;
    zc_load2 $b;
    if zc_neg1 == zc_neg2 {
        zc_add_abs;
        zc_save3;
        if zc_neg1 < 0 and zc_save3 != "0" { bi_add_str = "-" & zc_save3; }
        else { bi_add_str = zc_save3; }
    } else {
        zc_cmp12;
        if zc_cmp12 == 0 { bi_add_str = "0"; }
        elif zc_cmp12 > 0 {
            zc_sub_abs; zc_save3;
            if zc_neg1 < 0 { bi_add_str = "-" & zc_save3; } else { bi_add_str = zc_save3; }
        } else {
            zc_sub_abs; zc_save3;
            if zc_neg2 < 0 { bi_add_str = "-" & zc_save3; } else { bi_add_str = zc_save3; }
        }
    }
}

proc bi_sub_str a, b {
    bi_neg_str $b;
    bi_add_str $a, bi_neg_str;
    bi_sub_str = bi_add_str;
}

proc bi_mul_str a, b {
    zc_load1 $a;
    zc_load2 $b;
    delete zc_r;
    local i = 1;
    until i > length(zc_a) + length(zc_b) + 1 {
        add 0 to zc_r;
        i++;
    }
    i = 1;
    until i > length(zc_a) {
        local j = 1;
        until j > length(zc_b) {
            local p = i + j - 1;
            local z = zc_r[p] + zc_a[i] * zc_b[j];
            zc_r[p] = z % 10000000;
            zc_r[p + 1] = zc_r[p + 1] + floor(z / 10000000);
            j++;
        }
        i++;
    }
    # final carry
    i = 1;
    until i > length(zc_r) {
        local z = zc_r[i];
        zc_r[i] = z % 10000000;
        if i + 1 <= length(zc_r) { zc_r[i + 1] = zc_r[i + 1] + floor(z / 10000000); }
        i++;
    }
    zc_trim3;
    zc_save3;
    if zc_neg1 * zc_neg2 < 0 and zc_save3 != "0" { bi_mul_str = "-" & zc_save3; }
    else { bi_mul_str = zc_save3; }
}
