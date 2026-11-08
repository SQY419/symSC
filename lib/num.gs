var rn = 0;
var rd = 1;
var rok = false;
var sa = 0;
var sok = false;

func gcd_i(a, b) {
    local x = abs($a);
    local y = abs($b);
    until y == 0 {
        local t = x % y;
        x = y;
        y = t;
    }
    return x;
}

proc rat_norm n, d {
    rn = $n;
    rd = $d;
    rok = false;
    if rd == 0 {
        set_err "除数为零";
    } else {
        if rd < 0 {
            rn = -rn;
            rd = -rd;
        }
        local g = gcd_i(rn, rd);
        if g > 1 {
            rn = rn / g;
            rd = rd / g;
        }
        if abs(rn) > MAX_SAFE or rd > MAX_SAFE {
            set_err "数值超出安全整数范围";
        } else {
            rok = true;
        }
    }
}

proc safe_mul a, b {
    sa = $a * $b;
    if abs(sa) > MAX_SAFE {
        sok = false;
        set_err "数值乘法溢出";
    } else {
        sok = true;
    }
}

proc safe_add a, b {
    sa = $a + $b;
    if abs(sa) > MAX_SAFE {
        sok = false;
        set_err "数值加法溢出";
    } else {
        sok = true;
    }
}

proc rat_add an, ad, bn, bd {
    safe_mul $an, $bd;
    local x = sa;
    local okx = sok;
    safe_mul $bn, $ad;
    local y = sa;
    local oky = sok;
    safe_mul $ad, $bd;
    local d = sa;
    local okd = sok;
    if okx == false or oky == false or okd == false {
        rok = false;
    } else {
        safe_add x, y;
        local n = sa;
        if sok == false {
            rok = false;
        } else {
            rat_norm n, d;
        }
    }
}

proc rat_mul an, ad, bn, bd {
    safe_mul $an, $bn;
    local n = sa;
    local okn = sok;
    safe_mul $ad, $bd;
    local d = sa;
    local okd = sok;
    if okn == false or okd == false {
        rok = false;
    } else {
        rat_norm n, d;
    }
}

proc rat_pow bn, bd, e {
    local n = $bn;
    local d = $bd;
    local neg = $e < 0;
    local k = abs($e);
    if neg and n == 0 {
        set_err "零的负次幂无定义";
        rok = false;
        k = -1;
    }
    if k >= 0 {
        if neg {
            local t = n;
            n = d;
            d = t;
        }
        rn = 1;
        rd = 1;
        rok = true;
        local i = 1;
        until i > k or rok == false {
            rat_mul rn, rd, n, d;
            i++;
        }
    }
}

func int_str(n) {
    if $n == 0 {
        return "0";
    }
    return round($n) & "";
}

func rat_str(n, d) {
    if $d == 1 {
        return int_str($n);
    }
    return int_str($n) & "/" & int_str($d);
}

func pow10_dec(n) {
    local r = 1;
    local i = 1;
    until i > $n {
        r *= 10;
        i++;
    }
    return r;
}

func big_exp_str(n) {
    local a = abs($n);
    if a < 1000000000000000 {
        return int_str(round($n));
    }
    local t = fmt_dec(a);
    local ep = 0;
    local i = 1;
    until i > length(t) {
        if t[i] == "e" { ep = i; i = length(t) + 1; } else { i++; }
    }
    if ep == 0 { return int_str(round($n)); }
    local mant = substr(t, 1, ep - 1);
    local es = substr(t, ep + 1, length(t));
    local ee = 0;
    local p = 1;
    until p > length(es) {
        ee = ee * 10 + digit_value(es[p]);
        p++;
    }
    local digits = "";
    p = 1;
    until p > length(mant) {
        if mant[p] != "." { digits &= mant[p]; }
        p++;
    }
    local pad = ee - (length(digits) - 1);
    until pad <= 0 {
        digits &= "0";
        pad--;
    }
    if $n < 0 { return "-" & digits; }
    return digits;
}

func fmt_dec(x) {
    if $x != $x {
        return "NaN";
    }
    if abs($x) < 0.000000000001 {
        return "0";
    }
    if $x != 0 and abs($x) / 10 == abs($x) {
        if $x < 0 { return "-Infinity"; }
        return "Infinity";
    }
    if abs($x) >= 1000000000000000 {
        local ax = abs($x);
        local ex = floor(log(ax));
        local m = ax / pow10_dec(ex);
        if m >= 10 {
            m = m / 10;
            ex++;
        } elif m < 1 {
            m = m * 10;
            ex--;
        }
        local ms = (round(m * 10000000000) / 10000000000) & "";
        if $x < 0 { return "-" & ms & "e" & int_str(ex); }
        return ms & "e" & int_str(ex);
    }
    if abs($x) < 1000000000000000 and abs($x - round($x)) < 0.000000001 {
        return int_str(round($x));
    }
    return (round($x * 10000000000) / 10000000000) & "";
}

proc rat_div an, ad, bn, bd {
    if $bn == 0 {
        set_err "多项式系数除零";
        rok = false;
    } else {
        rat_mul $an, $ad, $bd, $bn;
    }
}

# Reconstruct a small rational from a floating limit value; otherwise decimal.
func fmt_exact(x, maxden) {
    if abs($x - round($x)) < 0.000000001 {
        return int_str(round($x));
    }
    local q = 1;
    until q > $maxden {
        local p = round($x * q);
        if abs($x - p / q) < 0.000000001 {
            return rat_str(p, q);
        }
        q++;
    }
    return fmt_dec($x);
}
