func new_node(kind, a, b, num, den, txt) {
    if node_count >= MAX_NODES {
        set_err "表达式过大";
        return 0;
    }
    node_count++;
    add $kind to nd_kind;
    add $a to nd_a;
    add $b to nd_b;
    add $num to nd_num;
    add $den to nd_den;
    add $txt to nd_txt;
    add "" to nd_sig;
    add 0 to nd_deg;
    return node_count;
}

proc reset_nodes {
    delete ct_elems;
    delete nd_kind;
    delete nd_a;
    delete nd_b;
    delete nd_num;
    delete nd_den;
    delete nd_txt;
    delete nd_sig;
    delete nd_deg;
    add 0 to nd_kind;
    add 0 to nd_a;
    add 0 to nd_b;
    add 0 to nd_num;
    add 1 to nd_den;
    add "" to nd_txt;
    add "" to nd_sig;
    add 0 to nd_deg;
    node_count = 1;
}

proc mk_bigfloat text {
    local s = $text;
    local ep = 0;
    local i = 1;
    until i > length(s) {
        if s[i] == "e" or s[i] == "E" { ep = i; i = length(s) + 1; }
        else { i++; }
    }
    local mant = s;
    local ex = 0;
    if ep > 0 {
        mant = substr(s, 1, ep - 1);
        local es = substr(s, ep + 1, length(s));
        local sg = 1;
        local p = 1;
        if length(es) > 0 and (es[1] == "+" or es[1] == "-") {
            if es[1] == "-" { sg = 0 - 1; }
            p = 2;
        }
        until p > length(es) or not is_digit_char(es[p]) {
            ex = ex * 10 + digit_value(es[p]);
            p++;
        }
        if sg < 0 { ex = 0 - ex; }
    }
    local neg = false;
    local p = 1;
    if length(mant) > 0 and mant[1] == "-" { neg = true; p = 2; }
    local m = 0;
    local frac = 0;
    local dot = false;
    until p > length(mant) {
        local c = mant[p];
        if c == "." { dot = true; }
        elif is_digit_char(c) {
            m = m * 10 + digit_value(c);
            if dot { frac++; }
        }
        p++;
    }
    until frac <= 0 { m = m / 10; frac--; }
    if neg { m = 0 - m; }
    if m == 0 {
        ex = 0;
    } else {
        until abs(m) < 10 { m = m / 10; ex++; }
        until abs(m) >= 1 { m = m * 10; ex--; }
    }
    local txt = "";
    if m == 0 {
        txt = "0";
    } else {
        txt = fmt_dec(m) & "e" & big_exp_str(ex);
    }
    mk_bigfloat = new_node(K.BigFloat, 0, 0, m, ex, txt);
    if mk_bigfloat != 0 {
        nd_sig[mk_bigfloat] = "BF" & txt;
        nd_deg[mk_bigfloat] = 0;
    }
}

proc mk_num n, d {
    rat_norm $n, $d;
    if rok == false {
        mk_num = 0;
    } elif rn == 0 {
        mk_num = new_node(K.Num, 0, 0, 0, 1, "");
        nd_sig[mk_num] = "N0/1";
        nd_deg[mk_num] = 0;
    } else {
        mk_num = new_node(K.Num, 0, 0, rn, rd, "");
        nd_sig[mk_num] = "N" & rat_str(rn, rd);
        nd_deg[mk_num] = 0;
    }
}

proc mk_big text {
    mk_big = new_node(K.Big, 0, 0, 0, 1, $text);
    if mk_big != 0 {
        nd_sig[mk_big] = "B" & nd_txt[mk_big];
        nd_deg[mk_big] = 0;
    }
}

proc mk_inf sign {
    mk_inf = new_node(K.Inf, 0, 0, $sign, 1, "");
    if mk_inf != 0 {
        nd_sig[mk_inf] = "INF";
        nd_deg[mk_inf] = 0;
    }
}

proc mk_genfunc name, ch {
    mk_genfunc = new_node(K.Unknown, $ch, 0, 0, 1, norm_ident($name));
    if mk_genfunc != 0 {
        nd_sig[mk_genfunc] = "G" & nd_txt[mk_genfunc] & "(" & nd_sig[$ch] & ")";
        nd_deg[mk_genfunc] = 1;
    }
}

func is_container(id) {
    return $id != 0 and (nd_kind[$id] == K.Vec or nd_kind[$id] == K.List);
}

func container_count(id) {
    if not is_container($id) { return 0; }
    return nd_den[$id];
}

func container_item(id, i) {
    if not is_container($id) { return 0; }
    return ct_elems[nd_num[$id] + $i - 1];
}

func is_matrix(id) {
    if $id == 0 or nd_kind[$id] != K.Vec or nd_den[$id] == 0 { return false; }
    local i = 1;
    until i > nd_den[$id] {
        local e = ct_elems[nd_num[$id] + i - 1];
        if nd_kind[e] != K.Vec { return false; }
        i++;
    }
    return true;
}

var ct_kind = 0;
var ct_start = 1;
var ct_count = 0;

func container_index(id, idx) {
    if not is_container($id) {
        set_err "对象不可索引";
        return 0;
    }
    if nd_kind[$idx] != K.Num or nd_den[$idx] != 1 {
        set_err "索引必须是整数";
        return 0;
    }
    local k = nd_num[$idx];
    if k < 1 or k > nd_den[$id] {
        set_err "索引越界";
        return 0;
    }
    return ct_elems[nd_num[$id] + k - 1];
}

proc mk_container {
    mk_container = new_node(ct_kind, 0, 0, ct_start, ct_count, "");
    if mk_container != 0 {
        local s = "";
        if ct_kind == K.Vec { s = "V["; } else { s = "L{"; }
        local i = 1;
        until i > ct_count {
            if i > 1 { s &= ","; }
            s &= nd_sig[ct_elems[ct_start + i - 1]];
            i++;
        }
        s &= "]";
        nd_sig[mk_container] = s;
        nd_deg[mk_container] = 0;
    }
}

list ctb_kind;
list ctb_data;
list ctb_idx;
var ctb_depth = 0;
var ctb_out = 0;

proc ctb_begin kind {
    ctb_depth++;
    if ctb_depth > length(ctb_kind) {
        add $kind to ctb_kind;
        add "" to ctb_data;
        add 1 to ctb_idx;
    } else {
        ctb_kind[ctb_depth] = $kind;
        ctb_data[ctb_depth] = "";
        ctb_idx[ctb_depth] = 1;
    }
}

proc ctb_add id {
    ctb_data[ctb_depth] &= $id & ",";
}

proc ctb_end {
    ct_kind = ctb_kind[ctb_depth];
    ct_start = length(ct_elems) + 1;
    ct_count = 0;
    local data = ctb_data[ctb_depth];
    local p = 1;
    local n = 0;
    until p > length(data) {
        local c = data[p];
        if c == "," {
            add n to ct_elems;
            ct_count++;
            n = 0;
        } else {
            n = n * 10 + digit_value(c);
        }
        p++;
    }
    mk_container;
    ctb_out = mk_container;
    ctb_depth--;
}

proc ctb_begin_any id {
    ctb_begin nd_kind[$id];
}

proc mk_undef {
    mk_undef = new_node(K.UN, 0, 0, 0, 1, "");
    if mk_undef != 0 {
        nd_sig[mk_undef] = "UNDEF";
        nd_deg[mk_undef] = 0;
    }
}

proc mk_var name {
    local nm = norm_ident($name);
    if nm == "undef" {
        mk_undef;
        mk_var = mk_undef;
    } elif nm == "oo" or nm == "inf" or nm == "infinity" {
        mk_inf 1;
        mk_var = mk_inf;
    } elif nm == "pi" {
        mk_var = new_node(K.Pi, 0, 0, 0, 1, "");
        nd_sig[mk_var] = "PI";
    } elif nm == "e" {
        mk_var = new_node(K.E, 0, 0, 0, 1, "");
        nd_sig[mk_var] = "E";
    } else {
        mk_var = new_node(K.Var, 0, 0, 0, 1, nm);
        nd_sig[mk_var] = "V" & nm;
        nd_deg[mk_var] = 1;
    }
}

proc new_func_raw kind, ch {
    new_func_raw = new_node($kind, $ch, 0, 0, 1, "");
    if new_func_raw != 0 {
        nd_sig[new_func_raw] = "F" & $kind & "(" & nd_sig[$ch] & ")";
        nd_deg[new_func_raw] = 1;
    }
}

var lp_base = 0;
var lp_exp = 0;
var lp_ok = false;

proc log_power_parts ex {
    lp_ok = false;
    lp_base = 0;
    lp_exp = 0;
    if nd_kind[$ex] == K.Ln {
        lp_base = nd_a[$ex];
        mk_num 1, 1;
        lp_exp = mk_num;
        lp_ok = true;
    } elif nd_kind[$ex] == K.Mul {
        local a = nd_a[$ex];
        local b = nd_b[$ex];
        if nd_kind[a] == K.Ln and nd_kind[b] != K.Ln {
            lp_base = nd_a[a];
            lp_exp = b;
            lp_ok = true;
        } elif nd_kind[b] == K.Ln and nd_kind[a] != K.Ln {
            lp_base = nd_a[b];
            lp_exp = a;
            lp_ok = true;
        }
    }
}

list cn_stk;
var cn_sp = 0;

proc cont_norm_sq c {
    delete cn_stk;
    cn_sp = 0;
    cn_sp++; add $c to cn_stk;
    mk_num 0, 1;
    local sum = mk_num;
    until cn_sp == 0 or err != "" {
        local x = cn_stk[cn_sp];
        cn_sp--;
        if is_container(x) {
            local i = nd_den[x];
            until i < 1 {
                cn_sp++;
                if cn_sp > length(cn_stk) { add ct_elems[nd_num[x] + i - 1] to cn_stk; }
                else { cn_stk[cn_sp] = ct_elems[nd_num[x] + i - 1]; }
                i--;
            }
        } else {
            mk_pow x, 2;
            local p2 = mk_pow;
            mk_add sum, p2;
            sum = mk_add;
        }
    }
    cont_norm_sq = sum;
}

proc cont_norm c {
    cont_norm_sq $c;
    mk_func K.Sqrt, cont_norm_sq;
    cont_norm = mk_func;
}

proc cont_unitv c {
    cont_norm $c;
    local nv = cont_norm;
    if is_zero(nv) {
        set_err "零向量没有单位向量";
        cont_unitv = 0;
    } else {
        mk_pow nv, -1;
        local inv = mk_pow;
        ctb_begin nd_kind[$c];
        until ctb_idx[ctb_depth] > nd_den[$c] {
            mk_mul ct_elems[nd_num[$c] + ctb_idx[ctb_depth] - 1], inv;
            ctb_add mk_mul;
            ctb_idx[ctb_depth]++;
        }
        ctb_end;
        cont_unitv = ctb_out;
    }
}

proc cont_map_func kind, c {
    ctb_begin nd_kind[$c];
    until ctb_idx[ctb_depth] > nd_den[$c] {
        local x = ct_elems[nd_num[$c] + ctb_idx[ctb_depth] - 1];
        if is_container(x) {
            cont_map_func $kind, x;
            ctb_add cont_map_func;
        } else {
            mk_func $kind, x;
            local r = mk_func;
            rules_simplify r;
            if err == "" { r = rules_simplify; }
            ctb_add r;
        }
        ctb_idx[ctb_depth]++;
    }
    ctb_end;
    cont_map_func = ctb_out;
}

proc mk_func kind, ch {
    if $ch == 0 {
        mk_func = 0;
    } elif nd_kind[$ch] == K.UN {
        mk_undef;
        mk_func = mk_undef;
    } elif is_container($ch) {
        if $kind == K.Length {
            mk_num nd_den[$ch], 1;
            mk_func = mk_num;
        } elif $kind == K.UnitV {
            cont_unitv $ch;
            mk_func = cont_unitv;
        } elif $kind == K.Abs {
            cont_norm $ch;
            mk_func = cont_norm;
        } elif $kind == K.Approx {
            new_func_raw K.Approx, $ch;
            mk_func = new_func_raw;
        } elif $kind == K.Transpose {
            cont_transpose $ch;
            mk_func = cont_transpose;
        } elif $kind == K.Det {
            cont_det $ch;
            mk_func = cont_det;
        } else {
            cont_map_func $kind, $ch;
            mk_func = cont_map_func;
        }
    } elif $kind == K.Sgn and nd_kind[$ch] == K.Inf {
        if nd_num[$ch] < 0 { mk_num -1, 1; } else { mk_num 1, 1; }
        mk_func = mk_num;
    } elif nd_kind[$ch] == K.Inf {
        mk_func = $ch;
    } elif $kind == K.Sgn {
        if nd_kind[$ch] == K.Inf {
            mk_inf nd_num[$ch];
            mk_func = mk_inf;
        } elif nd_kind[$ch] == K.Num {
            if nd_num[$ch] > 0 { mk_num 1, 1; } elif nd_num[$ch] < 0 { mk_num -1, 1; } else { mk_num 0, 1; }
            mk_func = mk_num;
        } else {
            sign_of $ch;
            if sign_of == 1 { mk_num 1, 1; mk_func = mk_num; }
            elif sign_of == -1 { mk_num -1, 1; mk_func = mk_num; }
            elif sign_of == 0 { mk_num 0, 1; mk_func = mk_num; }
            else { mk_genfunc "sgn", $ch; mk_func = mk_genfunc; }
        }
    } elif $kind == K.Abs {
        # Pull a numeric factor out of Abs(c*u) = |c|*Abs(u).  This also
        # handles the common Abs(-x) -> Abs(x) case without relying on sign_of.
        if nd_kind[$ch] == K.Mul {
            local aa = nd_a[$ch];
            local bb = nd_b[$ch];
            if nd_kind[aa] == K.Num {
                local cc = nd_num[aa];
                if cc < 0 { cc = 0 - cc; }
                mk_num cc, nd_den[aa];
                local ac = mk_num;
                mk_func K.Abs, bb;
                local ar = mk_func;
                if is_one(ac) { mk_func = ar; } else { mk_mul ac, ar; mk_func = mk_mul; }
            } elif nd_kind[bb] == K.Num {
                local cc = nd_num[bb];
                if cc < 0 { cc = 0 - cc; }
                mk_num cc, nd_den[bb];
                local ac = mk_num;
                mk_func K.Abs, aa;
                local ar = mk_func;
                if is_one(ac) { mk_func = ar; } else { mk_mul ac, ar; mk_func = mk_mul; }
            } else {
                sign_of $ch;
                if sign_of == 1 or sign_of == 2 { mk_func = $ch; }
                elif sign_of == -1 or sign_of == 3 { mk_neg $ch; mk_func = mk_neg; }
                elif sign_of == 0 { mk_num 0, 1; mk_func = mk_num; }
                else { new_func_raw K.Abs, $ch; mk_func = new_func_raw; }
            }
        } else {
            sign_of $ch;
            if sign_of == 1 or sign_of == 2 { mk_func = $ch; }
            elif sign_of == -1 or sign_of == 3 { mk_neg $ch; mk_func = mk_neg; }
            elif sign_of == 0 { mk_num 0, 1; mk_func = mk_num; }
            else { new_func_raw K.Abs, $ch; mk_func = new_func_raw; }
        }
    } elif $kind == K.Ln and nd_kind[$ch] == K.E {
        mk_num 1, 1;
        mk_func = mk_num;
    } elif $kind == K.Ln and nd_kind[$ch] == K.Num and nd_num[$ch] == 1 and nd_den[$ch] == 1 {
        mk_num 0, 1;
        mk_func = mk_num;
    } elif $kind == K.Ln and nd_kind[$ch] == K.Num and nd_num[$ch] == 0 {
        mk_undef;
        mk_func = mk_undef;
    } elif $kind == K.Ln and nd_kind[$ch] == K.PowE and nd_kind[nd_a[$ch]] == K.E {
        mk_func = nd_b[$ch];
    } elif $kind == K.Exp and nd_kind[$ch] == K.Num and nd_num[$ch] == 0 {
        mk_num 1, 1;
        mk_func = mk_num;
    } elif $kind == K.Exp and nd_kind[$ch] == K.Num and nd_num[$ch] == 1 and nd_den[$ch] == 1 {
        mk_var "e";
        mk_func = mk_var;
    } elif $kind == K.Exp and nd_kind[$ch] == K.Ln {
        mk_func = nd_a[$ch];
    } elif $kind == K.Exp {
        log_power_parts $ch;
        if lp_ok {
            mk_pow_expr lp_base, lp_exp;
            mk_func = mk_pow_expr;
        } else {
            new_func_raw K.Exp, $ch;
            mk_func = new_func_raw;
        }
    } elif $kind == K.Sqrt and nd_kind[$ch] == K.Num {
        local n = nd_num[$ch];
        local d = nd_den[$ch];
        if n == 0 {
            mk_num 0, 1;
            mk_func = mk_num;
        } elif n < 0 {
            new_func_raw K.Sqrt, $ch;
            mk_func = new_func_raw;
        } elif n == 1 and d == 1 {
            mk_num 1, 1;
            mk_func = mk_num;
        } elif n > MAX_SQRT or d > MAX_SQRT {
            new_func_raw K.Sqrt, $ch;
            mk_func = new_func_raw;
        } else {
            local kn = 1;
            local rn = n;
            if n >= 4 {
                local k = floor(sqrt(n));
                until k < 2 or n % (k * k) == 0 {
                    k--;
                }
                if k >= 2 {
                    kn = k;
                    rn = n / (k * k);
                }
            }
            local kd = 1;
            local rd = d;
            if d >= 4 {
                local q = floor(sqrt(d));
                until q < 2 or d % (q * q) == 0 {
                    q--;
                }
                if q >= 2 {
                    kd = q;
                    rd = d / (q * q);
                }
            }
            # Rationalize the denominator: sqrt(rn/rd) = sqrt(rn*rd)/rd.
            if rd > 1 {
                rn = rn * rd;
                kd = kd * rd;
                rd = 1;
            }
            if kn == 1 and kd == 1 {
                new_func_raw K.Sqrt, $ch;
                mk_func = new_func_raw;
            } elif rn == 1 and rd == 1 {
                mk_num kn, kd;
                mk_func = mk_num;
            } else {
                mk_num rn, rd;
                local inner = mk_num;
                new_func_raw K.Sqrt, inner;
                local rad = new_func_raw;
                mk_num kn, kd;
                local coef = mk_num;
                if is_one(coef) {
                    mk_func = rad;
                } else {
                    mk_mul coef, rad;
                    mk_func = mk_mul;
                }
            }
        }
    } elif $kind == K.Sqrt and nd_kind[$ch] == K.Sqrt {
        local inner = nd_a[$ch];
        mk_num 1, 4;
        mk_pow_expr inner, mk_num;
        mk_func = mk_pow_expr;
    } elif $kind == K.Sqrt and (nd_kind[$ch] == K.Pow or nd_kind[$ch] == K.PowE) {
        sqrt_factor $ch;
        mk_func = sqrt_factor;
    } elif $kind == K.Sqrt and nd_kind[$ch] == K.Mul {
        sqrt_product $ch;
        mk_func = sqrt_product;
    } else {
        new_func_raw $kind, $ch;
        mk_func = new_func_raw;
    }
}

list sq_facs;
list sq_stk;
var sq_sp = 0;

proc sqrt_factor f {
    local k = nd_kind[$f];
    if k == K.Pow {
        local e = nd_num[$f];
        if e % 2 == 0 {
            mk_func K.Abs, nd_a[$f];
            local ab = mk_func;
            mk_pow ab, e / 2;
            sqrt_factor = mk_pow;
        } else {
            new_func_raw K.Sqrt, $f;
            sqrt_factor = new_func_raw;
        }
    } elif k == K.PowE {
        local en = nd_b[$f];
        if nd_kind[en] == K.Num and nd_num[en] % 2 == 0 {
            mk_num nd_num[en] / 2, nd_den[en];
            mk_pow_expr nd_a[$f], mk_num;
            sqrt_factor = mk_pow_expr;
        } else {
            new_func_raw K.Sqrt, $f;
            sqrt_factor = new_func_raw;
        }
    } elif k == K.Sqrt {
        local inner = nd_a[$f];
        mk_num 1, 4;
        mk_pow_expr inner, mk_num;
        sqrt_factor = mk_pow_expr;
    } else {
        new_func_raw K.Sqrt, $f;
        sqrt_factor = new_func_raw;
    }
}

proc sqrt_product ch {
    delete sq_facs;
    delete sq_stk;
    sq_sp = 0;
    sq_sp++; add $ch to sq_stk;
    until sq_sp == 0 {
        local x = sq_stk[sq_sp];
        sq_sp--;
        if nd_kind[x] == K.Mul {
            sq_sp++;
            if sq_sp > length(sq_stk) { add nd_b[x] to sq_stk; } else { sq_stk[sq_sp] = nd_b[x]; }
            sq_sp++;
            if sq_sp > length(sq_stk) { add nd_a[x] to sq_stk; } else { sq_stk[sq_sp] = nd_a[x]; }
        } else {
            add x to sq_facs;
        }
    }
    local out = 0;
    local i = 1;
    until i > length(sq_facs) or err != "" {
        local f = sq_facs[i];
        local r = 0;
        if nd_kind[f] == K.Num and nd_num[f] >= 0 {
            mk_func K.Sqrt, f;
            r = mk_func;
        } else {
            sqrt_factor f;
            r = sqrt_factor;
        }
        if out == 0 { out = r; } else { mk_mul out, r; out = mk_mul; }
        i++;
    }
    if err != "" { sqrt_product = 0; }
    elif out == 0 { mk_num 1, 1; sqrt_product = mk_num; }
    else { sqrt_product = out; }
}

func is_int_node(id) {
    return $id != 0 and ((nd_kind[$id] == K.Num and nd_den[$id] == 1) or is_big($id));
}

func int_text(id) {
    if is_big($id) { return nd_txt[$id]; }
    return nd_num[$id];
}

func is_big(id) {
    if $id == 0 or (nd_kind[$id] != K.Var and nd_kind[$id] != K.Big) or length(nd_txt[$id]) == 0 { return false; }
    local c = nd_txt[$id][1];
    local i = 1;
    until i > length(nd_txt[$id]) {
        if nd_txt[$id][i] == "/" { return false; }
        i++;
    }
    return is_digit_char(c) or (c == "-" and length(nd_txt[$id]) > 1 and is_digit_char(nd_txt[$id][2]));
}

func is_zero(id) {
    return $id != 0 and ((nd_kind[$id] == K.Num or nd_kind[$id] == K.Float) and nd_num[$id] == 0 or (is_big($id) and nd_txt[$id] == "0"));
}

func is_one(id) {
    return $id != 0 and ((nd_kind[$id] == K.Num or nd_kind[$id] == K.Float) and nd_num[$id] == 1 and nd_den[$id] == 1 or (is_big($id) and nd_txt[$id] == "1"));
}

func new_float(value) {
    if $value != $value {
        set_err "数值不是有限数";
        return 0;
    }
    local s = fmt_dec($value);
    local id = new_node(K.Float, 0, 0, $value, 1, s);
    if id != 0 {
        nd_sig[id] = "D" & s;
        nd_deg[id] = 0;
    }
    return id;
}

func is_num_like(id) {
    return $id != 0 and (nd_kind[$id] == K.Num or nd_kind[$id] == K.Float);
}

func num_value(id) {
    if $id != 0 and nd_kind[$id] == K.Float {
        return nd_num[$id];
    }
    return nd_num[$id] / nd_den[$id];
}

func float_pow_value(base, e) {
    local k = abs($e);
    local acc = 1;
    local i = 1;
    until i > k {
        acc *= $base;
        i++;
    }
    if $e < 0 {
        if $base == 0 {
            set_err "零的负次幂无定义";
            return 0;
        }
        return 1 / acc;
    }
    return acc;
}

proc mk_pow_expr base, e {
    if nd_kind[$base] == K.UN or nd_kind[$e] == K.UN {
        mk_undef;
        mk_pow_expr = mk_undef;
    } elif nd_kind[$base] == K.E {
        log_power_parts $e;
        if lp_ok {
            mk_pow_expr lp_base, lp_exp;
            mk_pow_expr = mk_pow_expr;
        } else {
            local qid = new_node(K.PowE, $base, $e, 0, 1, "");
            if qid != 0 {
                nd_sig[qid] = "Q(" & nd_sig[$base] & "," & nd_sig[$e] & ")";
                nd_deg[qid] = 0;
            }
            mk_pow_expr = qid;
        }
    } elif nd_kind[$base] == K.Inf {
        if nd_kind[$e] == K.Inf {
            if nd_num[$base] > 0 and nd_num[$e] > 0 {
                mk_inf 1; mk_pow_expr = mk_inf;
            } elif nd_num[$base] > 0 {
                mk_num 0, 1; mk_pow_expr = mk_num;
            } else {
                mk_undef; mk_pow_expr = mk_undef;
            }
        } elif nd_kind[$e] == K.Num {
            if nd_num[$e] > 0 { mk_pow_expr = $base; }
            elif nd_num[$e] == 0 { mk_undef; mk_pow_expr = mk_undef; }
            else { mk_num 0, 1; mk_pow_expr = mk_num; }
        } else {
            mk_undef; mk_pow_expr = mk_undef;
        }
    } elif nd_kind[$e] == K.Inf and (nd_kind[$base] == K.Num or nd_kind[$base] == K.Float or nd_kind[$base] == K.Pi or nd_kind[$base] == K.E) {
        local bv = 0;
        if nd_kind[$base] == K.Num { bv = nd_num[$base] / nd_den[$base]; } elif nd_kind[$base] == K.Float { bv = nd_num[$base]; } else { bv = 2; }
        if bv > 1 {
            mk_inf 1; mk_pow_expr = mk_inf;
        } elif bv == 1 {
            mk_undef; mk_pow_expr = mk_undef;
        } elif bv >= 0 {
            mk_num 0, 1; mk_pow_expr = mk_num;
        } else {
            mk_undef; mk_pow_expr = mk_undef;
        }
    } elif $base == 0 or $e == 0 or err != "" {
        mk_pow_expr = 0;
    } elif is_one($base) {
        mk_num 1, 1;
        mk_pow_expr = mk_num;
    } elif nd_kind[$e] == K.Num and nd_den[$e] == 1 {
        mk_pow $base, nd_num[$e];
        mk_pow_expr = mk_pow;
    } elif is_one($e) {
        mk_pow_expr = $base;
    } elif nd_kind[$base] == K.PowE {
        mk_mul nd_b[$base], $e;
        local ne = mk_mul;
        mk_pow_expr nd_a[$base], ne;
        mk_pow_expr = mk_pow_expr;
    } elif nd_kind[$base] == K.Pow {
        mk_num nd_num[$base], 1;
        local e0 = mk_num;
        mk_mul e0, $e;
        local ne = mk_mul;
        mk_pow_expr nd_a[$base], ne;
        mk_pow_expr = mk_pow_expr;
    } elif nd_kind[$base] == K.Num and nd_den[$base] == 1 and nd_num[$base] > 1 {
        # Pull a square base out, so 4^e becomes 2^(2e).  This is a
        # structural rewrite, not a special case for 4.
        local rt = floor(sqrt(nd_num[$base]));
        if rt * rt == nd_num[$base] and rt > 1 {
            mk_num 2, 1;
            local two = mk_num;
            mk_mul $e, two;
            local ne = mk_mul;
            mk_num rt, 1;
            local rbase = mk_num;
            mk_pow_expr rbase, ne;
            mk_pow_expr = mk_pow_expr;
        } else {
            local id = new_node(K.PowE, $base, $e, 0, 1, "");
            if id != 0 {
                nd_sig[id] = "Q(" & nd_sig[$base] & "," & nd_sig[$e] & ")";
                nd_deg[id] = 0;
            }
            mk_pow_expr = id;
        }
    } else {
        local id = new_node(K.PowE, $base, $e, 0, 1, "");
        if id != 0 {
            nd_sig[id] = "Q(" & nd_sig[$base] & "," & nd_sig[$e] & ")";
            nd_deg[id] = 0;
        }
        mk_pow_expr = id;
    }
}
