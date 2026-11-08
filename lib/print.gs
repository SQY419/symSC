var pr_out = 0;

list pr_parts;

list pr_terms;
list pr_ops;
list pr_facs;
list pr_num_facs;
list pr_den_facs;
list pr_stk;
var pr_sp = 0;

list pr_t_type;
list pr_t_node;
list pr_t_text;
list pr_t_prec;
var pr_t_sp = 0;

func pr_func_name(k) {
    if $k == K.Sin {
        return "sin";
    } elif $k == K.Cos {
        return "cos";
    } elif $k == K.Tan {
        return "tan";
    } elif $k == K.Exp {
        return "exp";
    } elif $k == K.Ln {
        return "ln";
    } elif $k == K.Log {
        return "log";
    } elif $k == K.Sqrt {
        return "sqrt";
    } elif $k == K.Abs {
        return "abs";
    } elif $k == K.Asin {
        return "asin";
    } elif $k == K.Acos {
        return "acos";
    } elif $k == K.Atan {
        return "atan";
    }
    return "f";
}

func pr_node_prec(id) {
    if $id == 0 {
        return 4;
    } elif nd_kind[$id] == K.Add {
        return 1;
    } elif nd_kind[$id] == K.Mul {
        return 2;
    } elif nd_kind[$id] == K.Pow or nd_kind[$id] == K.PowE {
        return 3;
    } elif nd_kind[$id] == K.Cmp {
        return 1;
    } elif nd_kind[$id] == K.UN or nd_kind[$id] == K.Inf or nd_kind[$id] == K.Unknown {
        return 4;
    }
    return 4;
}

proc pr_emit text {
    if $text != "" {
        add $text to pr_parts;
    }
}

proc pr_task typ, node, text, prec {
    pr_t_sp++;
    if pr_t_sp > length(pr_t_type) {
        add $typ to pr_t_type;
        add $node to pr_t_node;
        add $text to pr_t_text;
        add $prec to pr_t_prec;
    } else {
        pr_t_type[pr_t_sp] = $typ;
        pr_t_node[pr_t_sp] = $node;
        pr_t_text[pr_t_sp] = $text;
        pr_t_prec[pr_t_sp] = $prec;
    }
}

proc pr_text text {
    pr_task 1, 0, $text, 0;
}

proc pr_node id, prec {
    if $id == 0 {
        pr_text "0";
    } elif $prec > pr_node_prec($id) {
        pr_text ")";
        pr_task 0, $id, "", 0;
        pr_text "(";
    } else {
        pr_task 0, $id, "", $prec;
    }
}

func pr_is_neg(id) {
    if $id == 0 {
        return false;
    }
    if nd_kind[$id] == K.Num or nd_kind[$id] == K.Float {
        return nd_num[$id] < 0;
    }
    if nd_kind[$id] == K.Mul {
        local x = $id;
        until nd_kind[x] != K.Mul {
            x = nd_a[x];
        }
        return nd_kind[x] == K.Num and nd_num[x] < 0;
    }
    return false;
}

proc pr_abs id {
    if pr_is_neg($id) {
        mk_neg $id;
        pr_abs = mk_neg;
    } else {
        pr_abs = $id;
    }
}

proc pr_push_stk id {
    pr_sp++;
    if pr_sp > length(pr_stk) {
        add $id to pr_stk;
    } else {
        pr_stk[pr_sp] = $id;
    }
}

proc pr_flat_add root {
    delete pr_terms;
    delete pr_ops;
    delete pr_stk;
    pr_sp = 0;
    pr_push_stk $root;
    until pr_sp == 0 {
        local x = pr_stk[pr_sp];
        pr_sp--;
        if nd_kind[x] == K.Add {
            pr_push_stk nd_b[x];
            pr_push_stk nd_a[x];
        } else {
            local neg = pr_is_neg(x);
            local t = x;
            if neg {
                pr_abs x;
                t = pr_abs;
            }
            add t to pr_terms;
            if length(pr_terms) == 1 {
                if neg {
                    add "-" to pr_ops;
                } else {
                    add "" to pr_ops;
                }
            } else {
                if neg {
                    add " - " to pr_ops;
                } else {
                    add " + " to pr_ops;
                }
            }
        }
    }
}

proc pr_flat_mul root {
    delete pr_facs;
    delete pr_stk;
    pr_sp = 0;
    pr_push_stk $root;
    until pr_sp == 0 {
        local x = pr_stk[pr_sp];
        pr_sp--;
        if nd_kind[x] == K.Mul {
            pr_push_stk nd_b[x];
            pr_push_stk nd_a[x];
        } else {
            add x to pr_facs;
        }
    }
}

proc pr_pow_operand id {
    local k = nd_kind[$id];
    local parens = false;
    if k == K.Num and (nd_den[$id] != 1 or nd_num[$id] < 0) {
        parens = true;
    } elif k == K.Float and nd_num[$id] < 0 {
        parens = true;
    }
    if parens {
        pr_text ")";
        pr_task 0, $id, "", 0;
        pr_text "(";
    } else {
        pr_node $id, 4;
    }
}

proc pr_handle id {
    if $id == 0 {
        pr_emit "0";
    } elif nd_kind[$id] == K.Num {
        pr_emit rat_str(nd_num[$id], nd_den[$id]);
    } elif nd_kind[$id] == K.Float {
        pr_emit nd_txt[$id];
    } elif nd_kind[$id] == K.Var {
        pr_emit nd_txt[$id];
    } elif nd_kind[$id] == K.Pi {
        pr_emit "pi";
    } elif nd_kind[$id] == K.E {
        pr_emit "e";
    } elif nd_kind[$id] == K.Nil {
        pr_emit "nil";
    } elif nd_kind[$id] == K.Bool {
        pr_emit nd_txt[$id];
    } elif nd_kind[$id] == K.Cmp {
        pr_node nd_a[$id], 2;
        if nd_num[$id] == 0 { pr_text " < "; }
        elif nd_num[$id] == 1 { pr_text " > "; }
        else { pr_text " == "; }
        pr_node nd_b[$id], 2;
    } elif nd_kind[$id] == K.UN {
        pr_emit "undef";
    } elif nd_kind[$id] == K.Big {
        pr_emit nd_txt[$id];
    } elif nd_kind[$id] == K.BigFloat {
        pr_emit nd_txt[$id];
    } elif nd_kind[$id] == K.Inf {
        if nd_num[$id] < 0 { pr_emit "-oo"; } else { pr_emit "oo"; }
    } elif nd_kind[$id] == K.Unknown {
        pr_text ")";
        pr_node nd_a[$id], 0;
        pr_text nd_txt[$id] & "(";
    } elif nd_kind[$id] == K.Sgn {
        pr_text ")";
        pr_node nd_a[$id], 0;
        pr_text "sgn(";
    } elif nd_kind[$id] >= K.Sin and nd_kind[$id] <= K.Atan {
        pr_text ")";
        pr_node nd_a[$id], 0;
        pr_text pr_func_name(nd_kind[$id]) & "(";
    } elif nd_kind[$id] == K.Pow {
        local e = nd_num[$id];
        if e < 0 {
            pr_emit "1/";
            if abs(e) == 1 {
                pr_node nd_a[$id], 4;
            } else {
                pr_text int_str(abs(e));
                pr_text "^";
                pr_node nd_a[$id], 4;
            }
        } else {
            pr_text int_str(e);
            pr_text "^";
            pr_node nd_a[$id], 4;
        }
    } elif nd_kind[$id] == K.PowE {
        pr_pow_operand nd_b[$id];
        pr_text "^";
        pr_pow_operand nd_a[$id];
    } elif nd_kind[$id] == K.Add {
        pr_flat_add $id;
        local i = length(pr_terms);
        until i < 1 {
            pr_node pr_terms[i], 2;
            if pr_ops[i] != "" {
                pr_text pr_ops[i];
            }
            i--;
        }
    } elif nd_kind[$id] == K.Mul {
        pr_flat_mul $id;
        delete pr_num_facs;
        delete pr_den_facs;
        local fi = 1;
        until fi > length(pr_facs) {
            local f = pr_facs[fi];
            if nd_kind[f] == K.Pow and nd_num[f] < 0 {
                mk_pow nd_a[f], -nd_num[f];
                add mk_pow to pr_den_facs;
            } elif nd_kind[f] == K.PowE and nd_kind[nd_b[f]] == K.Num and nd_num[nd_b[f]] < 0 {
                mk_num 0 - nd_num[nd_b[f]], nd_den[nd_b[f]];
                local epos = mk_num;
                mk_pow_expr nd_a[f], epos;
                add mk_pow_expr to pr_den_facs;
            } else {
                add f to pr_num_facs;
            }
            fi++;
        }
        if length(pr_den_facs) > 0 {
            local num = 0;
            if length(pr_num_facs) == 0 {
                mk_num 1, 1;
                num = mk_num;
            } else {
                num = pr_num_facs[1];
                local k = 2;
                until k > length(pr_num_facs) {
                    mk_mul num, pr_num_facs[k];
                    num = mk_mul;
                    k++;
                }
            }
            local den = pr_den_facs[1];
            k = 2;
            until k > length(pr_den_facs) {
                mk_mul den, pr_den_facs[k];
                den = mk_mul;
                k++;
            }
            # numerator / denominator; pull a negative numeric numerator out front
            local neg = false;
            if nd_kind[num] == K.Num and nd_num[num] < 0 {
                neg = true;
                mk_num -nd_num[num], nd_den[num];
                num = mk_num;
            }
            pr_node den, 4;
            pr_text "/";
            pr_pow_operand num;
            if neg {
                pr_text "-";
            }
        } else {
            local start = 1;
            local n = length(pr_facs);
            if n > 0 and nd_kind[pr_facs[1]] == K.Num {
                if nd_num[pr_facs[1]] < 0 {
                    pr_emit "-";
                    mk_num -nd_num[pr_facs[1]], nd_den[pr_facs[1]];
                    pr_facs[1] = mk_num;
                }
                if n > 1 and nd_num[pr_facs[1]] == 1 and nd_den[pr_facs[1]] == 1 {
                    start = 2;
                }
            }
            local i = n;
            until i < start {
                pr_node pr_facs[i], 2;
                if i > start {
                    pr_text "*";
                }
                i--;
            }
            if n == 1 and start == 2 {
                pr_emit "1";
            }
        }
    } elif nd_kind[$id] == K.Vec or nd_kind[$id] == K.List {
        local cn = nd_den[$id];
        local start = nd_num[$id];
        if nd_kind[$id] == K.List {
            pr_text "}";
        } else {
            pr_text "]";
        }
        local ci = cn;
        until ci < 1 {
            if ci < cn { pr_text ", "; }
            pr_node ct_elems[start + ci - 1], 0;
            ci--;
        }
        if nd_kind[$id] == K.List {
            pr_text "{";
        } else {
            pr_text "[";
        }
    } else {
        pr_emit "?";
    }
}

proc pr_expr root {
    delete pr_parts;
    delete pr_t_type;
    delete pr_t_node;
    delete pr_t_text;
    delete pr_t_prec;
    pr_t_sp = 0;
    pr_node $root, 0;
    until pr_t_sp == 0 {
        local typ = pr_t_type[pr_t_sp];
        local node = pr_t_node[pr_t_sp];
        local text = pr_t_text[pr_t_sp];
        pr_t_sp--;
        if typ == 1 {
            pr_emit text;
        } else {
            pr_handle node;
        }
    }
    local buf = "";
    local i = 1;
    until i > length(pr_parts) or length(buf) > MAX_OUTPUT {
        buf &= pr_parts[i];
        i++;
    }
    if length(buf) > MAX_OUTPUT {
        buf = substr(buf, 1, MAX_OUTPUT) & "...";
    }
    pr_out = buf;
    pr_expr = 0;
}
