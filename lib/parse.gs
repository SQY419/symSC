list os_type;
list os_prec;
list os_text;
var os_count = 0;

list out_stack;
var out_count = 0;

list cs_type;
list cs_start;
list cs_base;
list cs_data;
list cs_index;
var fa_data = 0;
var fa_base = 0;
var fa_name = 0;
list fa_args;
var fa_active = false;
var cs_depth = 0;

proc flush_container_ops {
    local done = false;
    until os_count == 0 or done {
        local tt = os_type[os_count];
        if tt == 5 or tt == 6 {
            done = true;
        } else {
            pop_apply;
            if err != "" { done = true; }
        }
    }
}

proc open_container kind {
    cs_depth++;
    if cs_depth > length(cs_type) {
        add $kind to cs_type;
        add 0 to cs_start;
        add 0 to cs_base;
        add "" to cs_data;
        add false to cs_index;
    } else {
        cs_type[cs_depth] = $kind;
        cs_start[cs_depth] = 0;
        cs_base[cs_depth] = 0;
        cs_data[cs_depth] = "";
        cs_index[cs_depth] = false;
    }
    cs_start[cs_depth] = length(ct_elems) + 1;
    cs_base[cs_depth] = out_count;
    cs_data[cs_depth] = "";
    if $kind == K.Vec {
        push_os 5, 0, "";
    } else {
        push_os 6, 0, "";
    }
}

proc container_element {
    if cs_depth == 0 {
        set_err "列表元素不在列表内";
    } else {
        flush_container_ops;
        if os_count == 0 or (os_type[os_count] != 5 and os_type[os_count] != 6) {
            set_err "列表括号不匹配";
        } elif out_count <= cs_base[cs_depth] {
            set_err "列表元素为空";
        } else {
            local v = out_stack[out_count];
            out_count--;
            cs_data[cs_depth] &= v & ",";
            cs_base[cs_depth] = out_count;
        }
    }
}

proc close_container want {
    if cs_depth == 0 {
        set_err "列表括号不匹配";
    } else {
        flush_container_ops;
        if os_count == 0 or os_type[os_count] != $want {
            set_err "列表括号不匹配";
        } else {
            if cs_base[cs_depth] >= out_count { cs_base[cs_depth] = out_count - 1; }
            if out_count > cs_base[cs_depth] {
                local v = out_stack[out_count];
                out_count--;
                cs_data[cs_depth] &= v & ",";
                cs_base[cs_depth] = out_count;
            }
            ct_kind = cs_type[cs_depth];
            ct_start = length(ct_elems) + 1;
            ct_count = 0;
            local data = cs_data[cs_depth];
            local dp = 1;
            local dn = 0;
            until dp > length(data) {
                local dc = data[dp];
                if dc == "," {
                    add dn to ct_elems;
                    ct_count++;
                    dn = 0;
                } else {
                    dn = dn * 10 + digit_value(dc);
                }
                dp++;
            }
            mk_container;
            if err == "" {
                os_count--;
                push_out mk_container;
                cs_depth--;
            }
        }
    }
}

func func_kind(name) {
    if $name == "sin" {
        return K.Sin;
    } elif $name == "cos" {
        return K.Cos;
    } elif $name == "tan" {
        return K.Tan;
    } elif $name == "exp" {
        return K.Exp;
    } elif $name == "ln" {
        return K.Ln;
    } elif $name == "log" {
        return K.Log;
    } elif $name == "sqrt" {
        return K.Sqrt;
    } elif $name == "abs" {
        return K.Abs;
    } elif $name == "asin" {
        return K.Asin;
    } elif $name == "acos" {
        return K.Acos;
    } elif $name == "atan" {
        return K.Atan;
    } elif $name == "sgn" {
        return K.Sgn;
    } elif $name == "approx" {
        return K.Approx;
    } elif $name == "length" {
        return K.Length;
    } elif $name == "unitv" {
        return K.UnitV;
    } elif $name == "transpose" {
        return K.Transpose;
    } elif $name == "det" {
        return K.Det;
    }
    return -1;
}

proc push_out id {
    out_count++;
    if out_count > length(out_stack) {
        add $id to out_stack;
    } else {
        out_stack[out_count] = $id;
    }
}

proc push_os t, prec, text {
    os_count++;
    if os_count > length(os_type) {
        add $t to os_type;
        add $prec to os_prec;
        add $text to os_text;
    } else {
        os_type[os_count] = $t;
        os_prec[os_count] = $prec;
        os_text[os_count] = $text;
    }
}

proc apply_unary {
    if out_count < 1 {
        set_err "一元运算缺少操作数";
    } else {
        local a = out_stack[out_count];
        out_count--;
        mk_neg a;
        push_out mk_neg;
    }
}

proc apply_bin op {
    if out_count < 2 {
        set_err "运算符缺少操作数";
    } else {
        local b = out_stack[out_count];
        out_count--;
        local a = out_stack[out_count];
        out_count--;
        if $op == "+" {
            mk_add a, b;
            push_out mk_add;
        } elif $op == "-" {
            mk_neg b;
            local nb = mk_neg;
            mk_add a, nb;
            push_out mk_add;
        } elif $op == "*" {
            mk_mul a, b;
            push_out mk_mul;
        } elif $op == "/" {
            if is_big(a) and is_big(b) {
                bi_div_str nd_txt[a], nd_txt[b];
                local bq = bi_div_q;
                bi_mod_str nd_txt[a], nd_txt[b];
                if bi_div_r == "0" {
                    mk_big bq;
                    push_out mk_big;
                } else {
                    mk_pow b, -1;
                    mk_mul a, mk_pow;
                    push_out mk_mul;
                }
            } elif is_zero(b) {
                if nd_kind[a] == K.Num and nd_num[a] != 0 {
                    if nd_num[a] < 0 { mk_inf -1; } else { mk_inf 1; }
                    push_out mk_inf;
                } else {
                    mk_undef;
                    push_out mk_undef;
                }
            } else {
                mk_pow b, -1;
                local inv = mk_pow;
                mk_mul a, inv;
                push_out mk_mul;
            }
        } elif $op == "^" {
            if nd_kind[b] == K.Num and nd_den[b] == 1 {
                local e = nd_num[b];
                mk_pow a, e;
                push_out mk_pow;
            } else {
                mk_pow_expr a, b;
                push_out mk_pow_expr;
            }
        } elif $op == "<" or $op == ">" or $op == "==" {
            local oc = 0;
            if $op == ">" { oc = 1; }
            elif $op == "==" { oc = 2; }
            mk_cmp a, b, oc;
            push_out mk_cmp;
        } else {
            set_err "未知运算符 " & $op;
        }
    }
}

proc apply_func name {
    local k = func_kind($name);
    if out_count < 1 {
        set_err "函数缺少参数";
    } else {
        local a = out_stack[out_count];
        out_count--;
        if k < 0 {
            mk_genfunc $name, a;
            push_out mk_genfunc;
        } else {
            mk_func k, a;
            push_out mk_func;
        }
    }
}

proc pop_apply {
    if os_count > 0 {
        local t = os_type[os_count];
        local prec = os_prec[os_count];
        local text = os_text[os_count];
        os_count--;
        if t == 1 {
            apply_bin text;
        } elif t == 2 {
            apply_unary;
        } elif t == 4 {
            apply_func text;
        } else {
            set_err "括号不匹配";
        }
    }
}

proc open_index {
    cs_depth++;
    if cs_depth > length(cs_type) {
        add K.Vec to cs_type;
        add 0 to cs_start;
        add 0 to cs_base;
        add "" to cs_data;
        add true to cs_index;
    } else {
        cs_type[cs_depth] = K.Vec;
        cs_start[cs_depth] = 0;
        cs_base[cs_depth] = out_count - 1;
        cs_data[cs_depth] = "";
        cs_index[cs_depth] = true;
    }
    cs_base[cs_depth] = out_count - 1;
    push_os 7, 0, "";
}

proc flush_index_ops {
    local done = false;
    until os_count == 0 or done {
        if os_type[os_count] == 7 {
            done = true;
        } else {
            pop_apply;
            if err != "" { done = true; }
        }
    }
}

proc close_index {
    if cs_depth == 0 {
        set_err "索引括号不匹配";
    } else {
        flush_index_ops;
        if os_count == 0 or os_type[os_count] != 7 {
            set_err "索引括号不匹配";
        } elif out_count != cs_base[cs_depth] + 2 {
            set_err "索引只能有一个表达式";
        } else {
            local idx = out_stack[out_count];
            out_count--;
            local base = out_stack[out_count];
            out_count--;
            local ixv = container_index(base, idx);
            if err == "" {
                os_count--;
                push_out ixv;
                cs_depth--;
            }
        }
    }
}

proc flush_fa_ops {
    local done = false;
    until os_count == 0 or done {
        if os_type[os_count] == 8 {
            done = true;
        } else {
            pop_apply;
            if err != "" { done = true; }
        }
    }
}

proc fa_begin fname {
    fa_data = "";
    fa_base = out_count;
    fa_name = $fname;
    fa_active = true;
    push_os 8, 6, $fname;
}

proc fa_add {
    flush_fa_ops;
    if os_count == 0 or os_type[os_count] != 8 {
        set_err "makelist 参数错误";
    } elif out_count <= fa_base {
        set_err "makelist 参数为空";
    } else {
        local v = out_stack[out_count];
        out_count--;
        fa_data &= v & ",";
        fa_base = out_count;
    }
}

proc close_makelist {
    flush_fa_ops;
    if os_count == 0 or os_type[os_count] != 8 {
        set_err "makelist 括号不匹配";
    } else {
        if out_count > fa_base {
            local v = out_stack[out_count];
            out_count--;
            fa_data &= v & ",";
        }
        delete fa_args;
        local data = fa_data;
        local dp = 1;
        local dn = 0;
        until dp > length(data) {
            local dc = data[dp];
            if dc == "," {
                add dn to fa_args;
                dn = 0;
            } else {
                dn = dn * 10 + digit_value(dc);
            }
            dp++;
        }
        if fa_name == "makelist" {
            if length(fa_args) != 4 {
                set_err "makelist 需要 4 个参数";
            } else {
                do_makelist fa_args[1], fa_args[2], fa_args[3], fa_args[4];
                if err == "" {
                    os_count--;
                    push_out do_makelist;
                    fa_active = false;
                }
            }
        } elif fa_name == "cross" {
            if length(fa_args) != 2 {
                set_err "cross 需要 2 个参数";
            } else {
                cont_cross fa_args[1], fa_args[2];
                if err == "" {
                    os_count--;
                    push_out cont_cross;
                    fa_active = false;
                }
            }
        } elif fa_name == "dot" {
            if length(fa_args) != 2 {
                set_err "dot 需要 2 个参数";
            } else {
                cont_dot fa_args[1], fa_args[2];
                if err == "" {
                    os_count--;
                    push_out cont_dot;
                    fa_active = false;
                }
            }
        } elif fa_name == "cat" {
            if length(fa_args) != 2 {
                set_err "cat 需要 2 个参数";
            } else {
                cont_cat fa_args[1], fa_args[2];
                if err == "" {
                    os_count--;
                    push_out cont_cat;
                    fa_active = false;
                }
            }
        } elif fa_name == "sum" or fa_name == "prod" {
            if length(fa_args) == 1 {
                if fa_name == "sum" { cont_sum fa_args[1]; }
                else { cont_prod fa_args[1]; }
                if err == "" {
                    os_count--;
                    if fa_name == "sum" { push_out cont_sum; }
                    else { push_out cont_prod; }
                    fa_active = false;
                }
            } elif length(fa_args) == 4 {
                sum_range fa_args[1], fa_args[2], fa_args[3], fa_args[4], fa_name == "prod";
                if err == "" {
                    os_count--;
                    push_out sum_range;
                    fa_active = false;
                }
            } else {
                set_err "sum/prod 需要 1 或 4 个参数";
            }
        } else {
            set_err "未知多参数函数";
        }
    }
}

func is_atom_prev(t) {
    return $t == T.Num or $t == T.Ident or $t == T.RP or $t == T.RBracket or $t == T.RBrace;
}

func is_unary_context(t) {
    return $t == T.End or $t == T.Op or $t == T.LP or $t == T.Comma or $t == T.LBracket or $t == T.LBrace;
}

proc parse_tokens {
    delete os_type;
    delete os_prec;
    delete os_text;
    os_count = 0;
    delete out_stack;
    out_count = 0;
    parse_ok = true;
    cs_depth = 0;
    fa_active = false;
    local p = 1;
    local prev = T.End;
    until tk_type[p] == T.End or parse_ok == false or err != "" {
        local t = tk_type[p];
        if t == T.Sci {
            mk_bigfloat tk_text[p];
            if err == "" {
                push_out mk_bigfloat;
                p++;
                prev = t;
            } else {
                parse_ok = false;
            }
        } elif t == T.Num {
            if tk_big[p] == true or length(tk_text[p]) > 15 {
                mk_big tk_text[p];
            } else {
                mk_num tk_num[p], tk_den[p];
            }
            if err != "" {
                parse_ok = false;
            } else {
                if tk_big[p] == true or length(tk_text[p]) > 15 {
                    push_out mk_big;
                } else {
                    push_out mk_num;
                }
                p++;
                prev = t;
            }
        } elif t == T.Ident {
            local name = norm_ident(tk_text[p]);
            local bound = bind_lookup(name);
            if bound != 0 {
                push_out bound;
                p++;
                prev = t;
            } elif (name == "makelist" or name == "cross" or name == "dot" or name == "sum" or name == "prod" or name == "cat") and tk_type[p + 1] == T.LP {
                fa_begin name;
                p += 2;
                prev = T.LP;
            } elif tk_type[p + 1] == T.LP {
                push_os 4, 6, name;
                p++;
                prev = T.Ident;
            } elif func_kind(name) >= 0 {
                set_err "函数 " & name & " 需要括号";
                parse_ok = false;
            } else {
                mk_var name;
                if err != "" {
                    parse_ok = false;
                } else {
                    push_out mk_var;
                    p++;
                    prev = t;
                }
            }
        } elif t == T.Op {
            local op = tk_text[p];
            if op == "-" and is_unary_context(prev) {
                push_os 2, 4, "-";
                p++;
                prev = t;
            } elif op == "+" and is_unary_context(prev) {
                p++;
                prev = T.Op;
            } else {
                local prec = 2;
                if op == "*" or op == "/" {
                    prec = 3;
                } elif op == "^" {
                    prec = 5;
                } elif op == "<" or op == ">" or op == "==" {
                    prec = 1;
                }
                local popping = true;
                until os_count == 0 or popping == false {
                    local tt = os_type[os_count];
                    if tt == 1 or tt == 2 {
                        local tp = os_prec[os_count];
                        if tp > prec or (tp == prec and op != "^") {
                            pop_apply;
                        } else {
                            popping = false;
                        }
                    } else {
                        popping = false;
                    }
                }
                if err == "" and parse_ok {
                    push_os 1, prec, op;
                    p++;
                    prev = t;
                }
            }
        } elif t == T.LP {
            push_os 3, 0, "(";
            p++;
            prev = t;
        } elif t == T.RP {
            local found = false;
            local is_make = false;
            until os_count == 0 or found {
                local ot = os_type[os_count];
                if ot == 3 or ot == 8 {
                    found = true;
                    if ot == 8 { is_make = true; }
                } else {
                    pop_apply;
                    if err != "" {
                        found = true;
                        parse_ok = false;
                    }
                }
            }
            if found == false {
                set_err "括号不匹配";
                parse_ok = false;
            } elif parse_ok and is_make {
                close_makelist;
                if err == "" {
                    p++;
                    prev = t;
                } else {
                    parse_ok = false;
                }
            } elif parse_ok {
                os_count--;
                if os_count > 0 and os_type[os_count] == 4 {
                    local fname = os_text[os_count];
                    os_count--;
                    apply_func fname;
                }
                if err == "" {
                    p++;
                    prev = t;
                } else {
                    parse_ok = false;
                }
            }
        } elif t == T.LBracket {
            if is_atom_prev(prev) {
                open_index;
            } else {
                open_container K.Vec;
            }
            p++;
            prev = t;
        } elif t == T.LBrace {
            if tk_type[p + 1] == T.RBrace {
                ctb_begin K.List;
                ctb_end;
                push_out ctb_out;
                p += 2;
                prev = T.RBrace;
            } else {
                open_container K.List;
                p++;
                prev = t;
            }
        } elif t == T.RBracket {
            if cs_depth > 0 and cs_index[cs_depth] {
                close_index;
            } else {
                close_container 5;
            }
            if err == "" { p++; prev = t; } else { parse_ok = false; }
        } elif t == T.RBrace {
            close_container 6;
            if err == "" { p++; prev = t; } else { parse_ok = false; }
        } elif t == T.Comma {
            if cs_depth == 0 and fa_active {
                fa_add;
                if err == "" { p++; prev = t; } else { parse_ok = false; }
            } elif cs_depth == 0 {
                set_err "函数只接受一个参数";
                parse_ok = false;
            } elif cs_depth > 0 and cs_index[cs_depth] {
                set_err "索引只能有一个表达式";
                parse_ok = false;
            } else {
                container_element;
                if err == "" { p++; prev = t; } else { parse_ok = false; }
            }
        } else {
            set_err "无法解析的记号";
            parse_ok = false;
        }
    }
    if parse_ok and err == "" {
        if cs_depth > 0 {
            set_err "列表括号未闭合";
            parse_ok = false;
        }
    }
    if parse_ok and err == "" {
        until os_count == 0 or parse_ok == false or err != "" {
            if os_type[os_count] == 3 or os_type[os_count] == 4 {
                set_err "括号或函数未闭合";
                parse_ok = false;
            } else {
                pop_apply;
                if err != "" {
                    parse_ok = false;
                }
            }
        }
    }
    if parse_ok and err == "" {
        if out_count != 1 {
            set_err "表达式不完整";
            parse_ok = false;
        } else {
            parse_root = out_stack[1];
        }
    }
}

proc parse_text s {
    lex $s;
    if lex_ok == false {
        parse_ok = false;
    } else {
        parse_tokens;
    }
    parse_text = 0;
}
