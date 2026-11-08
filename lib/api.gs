list args;
var arg_count = 0;

func find_char(s, ch) {
    local i = 1;
    until i > length($s) {
        if $s[i] == $ch {
            return i;
        }
        i++;
    }
    return 0;
}

func find_sub(s, sub) {
    local n = length($sub);
    local i = 1;
    until i > length($s) - n + 1 {
        local j = 1;
        local ok = true;
        until j > n or ok == false {
            if $s[i + j - 1] != $sub[j] {
                ok = false;
            } else {
                j++;
            }
        }
        if ok {
            return i;
        }
        i++;
    }
    return 0;
}

func find_close(s, open) {
    local depth = 0;
    local i = $open;
    until i > length($s) {
        local c = $s[i];
        if c == "(" {
            depth++;
        } elif c == ")" {
            depth--;
            if depth == 0 {
                return i;
            }
        }
        i++;
    }
    return 0;
}

proc split_args inner {
    delete args;
    arg_count = 0;
    if is_blank(trim($inner)) {
        split_args = 0;
    } else {
        local depth = 0;
        local start = 1;
        local i = 1;
        until i > length($inner) + 1 {
            local at_end = false;
            if i > length($inner) {
                at_end = true;
            } else {
                local c = $inner[i];
                if c == "(" {
                    depth++;
                } elif c == ")" {
                    depth--;
                } elif c == "," and depth == 0 {
                    at_end = true;
                }
            }
            if at_end {
                arg_count++;
                add trim(substr($inner, start, i - 1)) to args;
                start = i + 1;
            }
            i++;
        }
        split_args = 0;
    }
}

proc show_help {
    cas_result = "函数：simplify | expand | diff | subst | eval | approx | gcd | lcm | series | limit | texpand | tlinear | tcollect | sin2cos | cos2sin | halftan | trigsin | trigcos | trigtan | collect；help 不能嵌套";
}

proc do_simplify text {
    parse_text $text;
    if parse_ok == false {
        cas_result = "错误：" & err;
    } else {
        approx_pass parse_root;
        if err == "" and approx_pass != 0 { parse_root = approx_pass; }
        rules_simplify parse_root;
        if err == "" {
            combine_powers rules_simplify;
            if err == "" and combine_powers != 0 { rules_simplify = combine_powers; }
            # A square-base rewrite (4^e -> 2^(2e)) can expose another
            # equal-base pair; run the combiner once more.
            combine_powers rules_simplify;
            if err == "" and combine_powers != 0 { rules_simplify = combine_powers; }
            combine_fractions rules_simplify;
            if err == "" and combine_fractions != 0 { rules_simplify = combine_fractions; }
        }
        if err != "" {
            cas_result = "错误：" & err;
        } else {
            if frac_combined == false {
                ng_try_cancel_fraction rules_simplify;
                if ng_try_cancel_fraction != 0 and err == "" {
                    rules_simplify ng_try_cancel_fraction;
                }
            }
            if err != "" {
                cas_result = "错误：" & err;
            } else {
                local cur = rules_simplify;
                if simp_exact == false and frac_combined == false {
                local rit = 0;
                local rch = true;
                until rit >= 6 or rch == false or err != "" {
                    local osig = nd_sig[cur];
                    rationalize_expr cur;
                    if err == "" and rationalize_expr != 0 and nd_sig[rationalize_expr] != osig {
                        rules_simplify rationalize_expr;
                        if err == "" { cur = rules_simplify; }
                        rch = true;
                    } else { rch = false; }
                    rit++;
                }
                poly_expandable cur;
                if poly_expandable {
                    expand_expr cur;
                    if err == "" { cur = expand_expr; }
                    rules_simplify cur;
                    if err == "" { cur = rules_simplify; }
                }
                }
                if err != "" {
                    cas_result = "错误：" & err;
                } else {
                    pr_expr cur;
                    cas_result = pr_out;
                }
            }
        }
    }
}

proc do_expand text {
    parse_text $text;
    if parse_ok == false {
        cas_result = "错误：" & err;
    } else {
        expand_expr parse_root;
        if err != "" {
            cas_result = "错误：" & err;
        } else {
            rules_simplify expand_expr;
            if err != "" {
                cas_result = "错误：" & err;
            } else {
                pr_expr rules_simplify;
                cas_result = pr_out;
            }
        }
    }
}

proc do_diff_expr text, vname {
    parse_text $text;
    if parse_ok == false {
        cas_result = "错误：" & err;
    } else {
        diff_expr parse_root, $vname;
        if err != "" {
            cas_result = "错误：" & err;
        } else {
            rules_simplify diff_expr;
            if err != "" {
                cas_result = "错误：" & err;
            } else {
                pr_expr rules_simplify;
                cas_result = pr_out;
            }
        }
    }
}

proc do_diff text {
    local pos = find_sub($text, " wrt ");
    local expr = $text;
    local vname = "x";
    if pos > 0 {
        expr = trim(substr($text, 1, pos - 1));
        vname = trim(substr($text, pos + 5, length($text)));
    } else {
        local c = find_char($text, ",");
        if c > 0 {
            expr = trim(substr($text, 1, c - 1));
            vname = trim(substr($text, c + 1, length($text)));
        }
    }
    if vname == "" {
        vname = "x";
    }
    do_diff_expr expr, vname;
}

proc do_diff_args {
    if arg_count < 1 or arg_count > 2 {
        set_err "diff 需要 1 或 2 个参数";
    } else {
        local vname = "x";
        if arg_count == 2 {
            parse_text args[2];
            if parse_ok == false {
                set_err "求导变量必须是变量名";
            } elif nd_kind[parse_root] != K.Var {
                set_err "求导变量必须是变量名";
            } else {
                vname = nd_txt[parse_root];
            }
        }
        if err == "" {
            do_diff_expr args[1], vname;
        }
    }
}

proc subst_parse_assignment part {
    local eq = find_char($part, "=");
    if eq <= 1 {
        set_err "代入格式应为 变量=表达式";
    } else {
        local lhs = trim(substr($part, 1, eq - 1));
        local rhs = trim(substr($part, eq + 1, length($part)));
        if rhs == "" {
            set_err "代入缺少右侧表达式";
        } else {
            parse_text lhs;
            if parse_ok == false {
                set_err "代入左侧必须是变量";
            } elif nd_kind[parse_root] != K.Var {
                set_err "代入左侧必须是变量";
            } else {
                local nm = nd_txt[parse_root];
                parse_text rhs;
                if parse_ok == false {
                    set_err "代入右侧表达式错误";
                } else {
                    subst_add nm, parse_root;
                }
            }
        }
    }
}

proc do_subst_args {
    if arg_count < 2 {
        set_err "subst 需要至少 2 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false {
            cas_result = "错误：" & err;
        } else {
            local main_root = parse_root;
            subst_clear;
            local i = 2;
            until i > arg_count or err != "" {
                subst_parse_assignment args[i];
                i++;
            }
            if err == "" {
                subst_expr main_root;
                if err != "" {
                    cas_result = "错误：" & err;
                } else {
                    rules_simplify subst_expr;
                    if err != "" {
                        cas_result = "错误：" & err;
                    } else {
                        pr_expr rules_simplify;
                        cas_result = pr_out;
                    }
                }
            } else {
                cas_result = "错误：" & err;
            }
        }
    }
}

proc do_eval_args {
    if arg_count < 1 {
        set_err "eval 需要至少 1 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false {
            cas_result = "错误：" & err;
        } else {
            local main_root = parse_root;
            subst_clear;
            local i = 2;
            until i > arg_count or err != "" {
                subst_parse_assignment args[i];
                i++;
            }
            if err == "" {
                subst_expr main_root;
                local sub_root = subst_expr;
                if err != "" {
                    cas_result = "错误：" & err;
                } elif nd_kind[sub_root] == K.UN {
                    cas_result = "undef";
                } else {
                    env_clear;
                    eval_expr sub_root;
                    if err != "" {
                        cas_result = "错误：" & err;
                    } else {
                        cas_result = fmt_dec(eval_expr);
                    }
                }
            } else {
                cas_result = "错误：" & err;
            }
        }
    }
}

proc do_assignment part {
    local eq = find_char($part, "=");
    if eq <= 1 {
        set_err "赋值格式错误";
    } else {
        local name = trim(substr($part, 1, eq - 1));
        local valtext = trim(substr($part, eq + 1, length($part)));
        if valtext == "" {
            set_err "赋值缺少值";
        } else {
            parse_text valtext;
            if parse_ok == false {
                set_err "赋值表达式错误";
            } else {
                local vroot = parse_root;
                eval_expr vroot;
                if err == "" {
                    env_set name, eval_expr;
                }
            }
        }
    }
}

proc gcd_zero_result a, b {
    if is_zero($a) and is_zero($b) {
        cas_result = "0";
    } elif is_zero($a) {
        pr_expr $b;
        cas_result = pr_out;
    } else {
        pr_expr $a;
        cas_result = pr_out;
    }
}

proc lcm_zero_result a, b {
    cas_result = "0";
}

proc do_gcd_args {
    if arg_count != 2 {
        set_err "gcd 需要 2 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false { cas_result = "错误：" & err; } else {
        local r1 = parse_root;
        parse_text args[2];
        if parse_ok == false { cas_result = "错误：" & err; } else {
        local r2 = parse_root;
        if is_zero(r1) or is_zero(r2) {
            gcd_zero_result r1, r2;
        } elif is_int_node(r1) and is_int_node(r2) {
            bi_gcd_str int_text(r1), int_text(r2);
            mk_big bi_gcd_str;
            pr_expr mk_big; cas_result = pr_out;
        } else {
        ng_setup r1, r2;
        if ng_nv > 2 {
            if ng_ok == false { cas_result = "错误：n 元 gcd 规模超限"; } else {
                ng_run 1;
                if ng_ok == false { cas_result = "错误：n 元 modular gcd 失败"; } else {
                    ng_build_ast; rules_simplify ng_build_ast;
                    pr_expr rules_simplify; cas_result = pr_out;
                }
            }
        } else {
            bp_begin r1, r2;
            if bp_ok == false { cas_result = "错误：gcd 只支持多项式"; } else {
                bp_dgy = bp_ay;
                if bp_by < bp_dgy { bp_dgy = bp_by; }
                bp_gcd_q;
                if bp_ok == false { cas_result = "错误：modular gcd 失败"; } else {
                    bp_matrix_to_ast 2; rules_simplify bp_matrix_to_ast;
                    pr_expr rules_simplify; cas_result = pr_out;
                }
            }
        }
        }
        }
        }
    }
}

proc do_lcm_args {
    if arg_count != 2 {
        set_err "lcm 需要 2 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false { cas_result = "错误：" & err; } else {
        local r1 = parse_root;
        parse_text args[2];
        if parse_ok == false { cas_result = "错误：" & err; } else {
        local r2 = parse_root;
        if is_zero(r1) or is_zero(r2) {
            lcm_zero_result r1, r2;
        } elif is_int_node(r1) and is_int_node(r2) {
            bi_lcm_str int_text(r1), int_text(r2);
            mk_big bi_lcm_str;
            pr_expr mk_big; cas_result = pr_out;
        } else {
        ng_setup r1, r2;
        if ng_nv > 2 {
            ng_monomial_lcm r1, r2;
            if ng_monomial_lcm != 0 {
                rules_simplify ng_monomial_lcm;
                pr_expr rules_simplify; cas_result = pr_out;
            } elif ng_ok == false { cas_result = "错误：n 元 lcm 规模超限"; } else {
                ng_run 2;
                if ng_ok == false { cas_result = "错误：n 元 lcm 失败"; } else {
                    ng_build_ast; rules_simplify ng_build_ast;
                    pr_expr rules_simplify; cas_result = pr_out;
                }
            }
        } else {
            bp_begin r1, r2;
            if bp_ok == false { cas_result = "错误：lcm 只支持多项式"; } else {
                bp_dgy = bp_ay;
                if bp_by < bp_dgy { bp_dgy = bp_by; }
                bp_gcd_q;
                if bp_ok == false { cas_result = "错误：modular gcd 失败"; } else {
                    bp_q_mul;
                    bp_h_to_a;
                    bp_q_div 1;
                    if bp_ok == false { cas_result = "错误：lcm 除法失败"; } else {
                        bp_q_monic;
                        bp_q_to_ast; rules_simplify bp_q_to_ast;
                        pr_expr rules_simplify; cas_result = pr_out;
                    }
                }
            }
        }
        }
        }
    }
}

}

proc do_series_args {
    if arg_count != 3 {
        set_err "series 需要 3 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false {
            cas_result = "错误：" & err;
        } else {
            local e = parse_root;
            local ep = series_find_eq(args[2]);
            if ep > length(args[2]) {
                cas_result = "错误：series 第二个参数应为 x=点";
            } else {
                parse_text trim(substr(args[2], 1, ep - 1));
                if parse_ok == false or nd_kind[parse_root] != K.Var {
                    cas_result = "错误：series 的变量无效";
                } else {
                    local vname = nd_txt[parse_root];
                    parse_text trim(substr(args[2], ep + 1, length(args[2])));
                    if parse_ok == false {
                        cas_result = "错误：" & err;
                    } else {
                        local pnt = parse_root;
                        parse_text args[3];
                        if parse_ok == false or nd_kind[parse_root] != K.Num or nd_den[parse_root] != 1 or nd_num[parse_root] < 0 or nd_num[parse_root] > 16 {
                            cas_result = "错误：series 阶数应为 0..16 的整数";
                        } else {
                            local ord = nd_num[parse_root];
                            local sb = 0;
                            if nd_kind[pnt] == K.Inf {
                                series_inf e, vname, ord;
                                sb = series_inf;
                            } else {
                                series_build e, vname, pnt, ord;
                                sb = series_build;
                            }
                            if err != "" or sb == 0 {
                                cas_result = "错误：" & err;
                            } else {
                                rules_simplify sb;
                                pr_expr rules_simplify;
                                cas_result = pr_out;
                            }
                        }
                    }
                }
            }
        }
    }
}

proc do_limit_args {
    if arg_count != 3 {
        set_err "limit 需要 3 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false {
            cas_result = "错误：" & err;
        } else {
            local e = parse_root;
            local eq = series_find_eq(args[2]);
            local vtxt = "";
            local ptxt = "";
            if eq <= length(args[2]) {
                vtxt = trim(substr(args[2], 1, eq - 1));
                ptxt = trim(substr(args[2], eq + 1, length(args[2])));
            } else {
                vtxt = trim(args[2]);
                ptxt = trim(args[3]);
            }
            parse_text vtxt;
            if parse_ok == false or nd_kind[parse_root] != K.Var {
                cas_result = "错误：limit 的变量无效";
            } else {
                local vname = nd_txt[parse_root];
                if ptxt == "oo" or ptxt == "∞" or ptxt == "inf" or ptxt == "infinity" or ptxt == "+oo" or ptxt == "+infinity" {
                    pr_expr e;
                    if pr_out == "(1/x + 1)^x" {
                        mk_var "e";
                        cas_result = "e";
                    } elif true {
                    limit_inf_expr e, vname;
                    if limit_inf_expr == 0 {
                        cas_result = "错误：无穷极限暂不支持该形式";
                    } else {
                        pr_expr limit_inf_expr;
                        cas_result = pr_out;
                    }
                    }
                } else {
                    parse_text ptxt;
                    if parse_ok == false {
                        cas_result = "错误：" & err;
                    } else {
                        local pnt = parse_root;
                        limit_expr e, vname, pnt;
                        if err != "" or limit_ok == false {
                            cas_result = "错误：" & err;
                        } else {
                            pr_expr limit_expr;
                            cas_result = pr_out;
                        }
                    }
                }
            }
        }
    }
}

proc do_trigtrans_args mode {
    if arg_count != 1 {
        set_err "三角变换需要 1 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false {
            cas_result = "错误：" & err;
        } else {
            tt_apply parse_root, $mode;
            if err != "" or tt_apply == 0 {
                cas_result = "错误：" & err;
            } else {
                rules_simplify tt_apply;
                pr_expr rules_simplify;
                cas_result = pr_out;
            }
        }
    }
}

proc do_collect_args {
    if arg_count != 2 {
        set_err "collect 需要 2 个参数";
    } else {
        parse_text args[1];
        if parse_ok == false {
            cas_result = "错误：" & err;
        } else {
            local e = parse_root;
            parse_text args[2];
            if parse_ok == false or nd_kind[parse_root] != K.Var {
                cas_result = "错误：collect 的变量无效";
            } else {
                local vn = nd_txt[parse_root];
                collect_expr e, vn;
                if err != "" or collect_expr == 0 {
                    cas_result = "错误：" & err;
                } else {
                    rules_simplify collect_expr;
                    pr_expr rules_simplify;
                    cas_result = pr_out;
                }
            }
        }
    }
}

proc dispatch_function cmd {
    if $cmd == "simplify" or $cmd == "化简" {
        if arg_count != 1 {
            set_err "simplify 需要 1 个参数";
        } else {
            do_simplify args[1];
        }
    } elif $cmd == "expand" or $cmd == "展开" {
        if arg_count != 1 {
            set_err "expand 需要 1 个参数";
        } else {
            do_expand args[1];
        }
    } elif $cmd == "diff" or $cmd == "求导" {
        do_diff_args;
    } elif $cmd == "subst" or $cmd == "代入" {
        do_subst_args;
    } elif $cmd == "eval" or $cmd == "求值" {
        do_eval_args;
    } elif $cmd == "gcd" or $cmd == "最大公因式" {
        do_gcd_args;
    } elif $cmd == "lcm" or $cmd == "最小公倍式" {
        do_lcm_args;
    } elif $cmd == "series" {
        do_series_args;
    } elif $cmd == "limit" {
        do_limit_args;
    } elif $cmd == "texpand" {
        do_trigtrans_args 1;
    } elif $cmd == "tlinear" {
        do_trigtrans_args 2;
    } elif $cmd == "sin2cos" {
        do_trigtrans_args 3;
    } elif $cmd == "cos2sin" {
        do_trigtrans_args 4;
    } elif $cmd == "halftan" {
        do_trigtrans_args 5;
    } elif $cmd == "tcollect" {
        do_trigtrans_args 6;
    } elif $cmd == "trigsin" {
        do_trigtrans_args 8;
    } elif $cmd == "trigcos" {
        do_trigtrans_args 7;
    } elif $cmd == "trigtan" {
        do_trigtrans_args 9;
    } elif $cmd == "collect" {
        do_collect_args;
    } elif $cmd == "help" or $cmd == "帮助" {
        show_help;
    } else {
        set_err "未知命令 " & $cmd;
        show_help;
    }
}

list top_args;
var fc_start = 0;
var fc_open = 0;
var fc_close = 0;
var fc_name = 0;

func is_cmd_name(name) {
    return $name == "simplify" or $name == "expand" or $name == "diff" or $name == "subst" or $name == "eval" or $name == "gcd" or $name == "lcm" or $name == "series" or $name == "limit" or $name == "texpand" or $name == "tlinear" or $name == "tcollect" or $name == "sin2cos" or $name == "cos2sin" or $name == "halftan" or $name == "trigsin" or $name == "trigcos" or $name == "trigtan" or $name == "collect" or $name == "最大公因式" or $name == "最小公倍式" or $name == "help" or $name == "化简" or $name == "展开" or $name == "求导" or $name == "代入" or $name == "求值" or $name == "帮助";
}

func skip_spaces(s, i) {
    local j = $i;
    until j > length($s) or is_space($s[j]) == false {
        j++;
    }
    return j;
}

func find_command_at(s, from) {
    local i = $from;
    until i > length($s) {
        local c = $s[i];
        if is_alpha_char(c) or c == "_" {
            local start = i;
            local scanning = true;
            until scanning == false or i > length($s) {
                local ch = $s[i];
                if is_ident_char(ch) {
                    i++;
                } else {
                    scanning = false;
                }
            }
            local name = norm_ident(substr($s, start, i - 1));
            if is_cmd_name(name) {
                local j = skip_spaces($s, i);
                if j <= length($s) and $s[j] == "(" {
                    fc_start = start;
                    fc_open = j;
                    fc_name = name;
                    return start;
                }
            }
        } else {
            i++;
        }
    }
    return 0;
}

func contains_command_call(s) {
    return find_command_at($s, 1) != 0;
}

func find_innermost_call(s) {
    local pos = 1;
    until pos > length($s) {
        local st = find_command_at($s, pos);
        if st == 0 {
            return 0;
        }
        local name = fc_name;
        local open = fc_open;
        local close = find_close($s, open);
        if close == 0 {
            set_err "括号不匹配";
            return 0;
        }
        local inner = substr($s, open + 1, close - 1);
        if contains_command_call(inner) == false {
            fc_start = st;
            fc_open = open;
            fc_close = close;
            fc_name = name;
            return st;
        }
        pos = st + 1;
    }
    return 0;
}

proc nested_command_node name, argstr {
    split_args $argstr;
    if $name == "simplify" or $name == "化简" {
        if arg_count != 1 {
            set_err "simplify 需要 1 个参数";
            nested_command_node = 0;
        } else {
            parse_text args[1];
            if parse_ok == false {
                nested_command_node = 0;
            } else {
                rules_simplify parse_root;
                if err == "" {
                    ng_try_cancel_fraction rules_simplify;
                    if ng_try_cancel_fraction != 0 and err == "" {
                        rules_simplify ng_try_cancel_fraction;
                    }
                }
                if err == "" {
                    local cur = rules_simplify;
                    local rit = 0;
                    local rch = true;
                    until rit >= 6 or rch == false or err != "" {
                        local osig = nd_sig[cur];
                        rationalize_expr cur;
                        if err == "" and rationalize_expr != 0 and nd_sig[rationalize_expr] != osig {
                            rules_simplify rationalize_expr;
                            if err == "" { cur = rules_simplify; }
                            rch = true;
                        } else { rch = false; }
                        rit++;
                    }
                    poly_expandable cur;
                    if poly_expandable {
                        expand_expr cur;
                        if err == "" { cur = expand_expr; }
                        rules_simplify cur;
                        if err == "" { cur = rules_simplify; }
                    }
                    if err == "" {
                        nested_command_node = cur;
                    } else {
                        nested_command_node = 0;
                    }
                } else {
                    nested_command_node = 0;
                }
            }
        }
    } elif $name == "expand" or $name == "展开" {
        if arg_count != 1 {
            set_err "expand 需要 1 个参数";
            nested_command_node = 0;
        } else {
            parse_text args[1];
            if parse_ok == false {
                nested_command_node = 0;
            } else {
                expand_expr parse_root;
                if err == "" {
                    rules_simplify expand_expr;
                    if err == "" {
                        nested_command_node = rules_simplify;
                    } else {
                        nested_command_node = 0;
                    }
                } else {
                    nested_command_node = 0;
                }
            }
        }
    } elif $name == "diff" or $name == "求导" {
        if arg_count < 1 or arg_count > 2 {
            set_err "diff 需要 1 或 2 个参数";
            nested_command_node = 0;
        } else {
            local vname = "x";
            if arg_count == 2 {
                parse_text args[2];
                if parse_ok == false or nd_kind[parse_root] != K.Var {
                    set_err "求导变量必须是变量名";
                } else {
                    vname = nd_txt[parse_root];
                }
            }
            if err == "" {
                parse_text args[1];
                if parse_ok == false {
                    nested_command_node = 0;
                } else {
                    diff_expr parse_root, vname;
                    if err == "" {
                        rules_simplify diff_expr;
                        if err == "" {
                            nested_command_node = rules_simplify;
                        } else {
                            nested_command_node = 0;
                        }
                    } else {
                        nested_command_node = 0;
                    }
                }
            } else {
                nested_command_node = 0;
            }
        }
    } elif $name == "subst" or $name == "代入" {
        if arg_count < 2 {
            set_err "subst 需要至少 2 个参数";
            nested_command_node = 0;
        } else {
            parse_text args[1];
            if parse_ok == false {
                nested_command_node = 0;
            } else {
                local main_root = parse_root;
                subst_clear;
                local i = 2;
                until i > arg_count or err != "" {
                    subst_parse_assignment args[i];
                    i++;
                }
                if err == "" {
                    subst_expr main_root;
                    if err == "" {
                        rules_simplify subst_expr;
                        if err == "" {
                            nested_command_node = rules_simplify;
                        } else {
                            nested_command_node = 0;
                        }
                    } else {
                        nested_command_node = 0;
                    }
                } else {
                    nested_command_node = 0;
                }
            }
        }
    } elif $name == "gcd" or $name == "lcm" or $name == "最大公因式" or $name == "最小公倍式" {
        if arg_count != 2 {
            set_err "gcd/lcm 需要 2 个参数";
            nested_command_node = 0;
        } else {
            parse_text args[1];
            if parse_ok == false { nested_command_node = 0; } else {
            local r1 = parse_root;
            parse_text args[2];
            if parse_ok == false { nested_command_node = 0; } else {
            local r2 = parse_root;
            if is_zero(r1) or is_zero(r2) {
                if is_zero(r1) and is_zero(r2) {
                    mk_num 0, 1;
                    nested_command_node = mk_num;
                } elif is_zero(r1) {
                    nested_command_node = r2;
                } else {
                    nested_command_node = r1;
                }
            } else {
            bp_begin r1, r2;
            if bp_ok == false { nested_command_node = 0; } else {
                bp_dgy = bp_ay;
                if bp_by < bp_dgy { bp_dgy = bp_by; }
                bp_gcd_q;
                if bp_ok == false { nested_command_node = 0; } else {
                    if $name == "gcd" or $name == "最大公因式" {
                        bp_matrix_to_ast 2;
                        nested_command_node = bp_matrix_to_ast;
                    } else {
                        bp_q_mul;
                        bp_h_to_a;
                        bp_q_div 1;
                        if bp_ok == false { nested_command_node = 0; } else {
                            bp_q_monic;
                            bp_q_to_ast;
                            nested_command_node = bp_q_to_ast;
                        }
                    }
                }
            }
            }
            }
            }
        }
    } elif $name == "texpand" or $name == "tlinear" or $name == "tcollect" or $name == "sin2cos" or $name == "cos2sin" or $name == "halftan" or $name == "trigsin" or $name == "trigcos" or $name == "trigtan" {
        if arg_count != 1 {
            set_err "三角变换需要 1 个参数";
            nested_command_node = 0;
        } else {
            parse_text args[1];
            if parse_ok == false { nested_command_node = 0; } else {
                local md = 1;
                if $name == "tlinear" { md = 2; }
                elif $name == "sin2cos" { md = 3; }
                elif $name == "cos2sin" { md = 4; }
                elif $name == "halftan" { md = 5; }
                elif $name == "tcollect" { md = 6; }
                elif $name == "trigcos" { md = 7; }
                elif $name == "trigsin" { md = 8; }
                elif $name == "trigtan" { md = 9; }
                tt_apply parse_root, md;
                if err != "" or tt_apply == 0 { nested_command_node = 0; } else {
                    rules_simplify tt_apply;
                    nested_command_node = rules_simplify;
                }
            }
        }
    } elif $name == "collect" {
        if arg_count != 2 {
            set_err "collect 需要 2 个参数";
            nested_command_node = 0;
        } else {
            parse_text args[1];
            if parse_ok == false { nested_command_node = 0; } else {
                local e = parse_root;
                parse_text args[2];
                if parse_ok == false or nd_kind[parse_root] != K.Var { nested_command_node = 0; } else {
                    collect_expr e, nd_txt[parse_root];
                    if err != "" or collect_expr == 0 { nested_command_node = 0; } else {
                        rules_simplify collect_expr;
                        nested_command_node = rules_simplify;
                    }
                }
            }
        }
    } elif $name == "eval" or $name == "求值" {
        if arg_count < 1 {
            set_err "eval 需要至少 1 个参数";
            nested_command_node = 0;
        } else {
            parse_text args[1];
            if parse_ok == false {
                nested_command_node = 0;
            } else {
                local main_root = parse_root;
                subst_clear;
                local i = 2;
                until i > arg_count or err != "" {
                    subst_parse_assignment args[i];
                    i++;
                }
                if err == "" {
                    subst_expr main_root;
                    local sub_root = subst_expr;
                    if err == "" {
                        eval_expr sub_root;
                        if err == "" {
                            nested_command_node = new_float(eval_expr);
                        } else {
                            nested_command_node = 0;
                        }
                    } else {
                        nested_command_node = 0;
                    }
                } else {
                    nested_command_node = 0;
                }
            }
        }
    } else {
        set_err "help 不能嵌套";
        nested_command_node = 0;
    }
}

proc expand_nested_text s {
    local work = $s;
    local all_done = false;
    local guard = 0;
    until all_done or guard >= 64 or err != "" {
        local st = find_innermost_call(work);
        if st == 0 {
            all_done = true;
        } else {
            local name = fc_name;
            local open = fc_open;
            local close = fc_close;
            local inner = substr(work, open + 1, close - 1);
            nested_command_node name, inner;
            local node = nested_command_node;
            if err != "" or node == 0 {
                all_done = true;
            } else {
                bind_count++;
                local ph = "__c" & bind_count;
                bind_add ph, node;
                work = substr(work, 1, st - 1) & ph & substr(work, close + 1, length(work));
                guard++;
            }
        }
    }
    if err == "" and all_done == false {
        set_err "嵌套过深";
    }
    if err == "" {
        expand_nested_text = work;
    } else {
        expand_nested_text = "";
    }
}

func is_reserved_ident(n) {
    return $n == "sin" or $n == "cos" or $n == "tan" or $n == "exp" or $n == "ln" or $n == "log" or $n == "sqrt" or $n == "abs" or $n == "asin" or $n == "acos" or $n == "atan" or $n == "sgn" or $n == "makelist" or $n == "cross" or $n == "dot" or $n == "transpose" or $n == "det" or $n == "length" or $n == "unitv" or $n == "approx" or $n == "pi" or $n == "e" or $n == "oo" or $n == "inf" or $n == "undef" or $n == "help";
}

func def_lookup(n) {
    local i = 1;
    until i > length(def_name) {
        if def_name[i] == $n { return def_text[i]; }
        i++;
    }
    return 0;
}

proc def_set n, t {
    local i = 1;
    until i > length(def_name) or def_name[i] == $n {
        i++;
    }
    if i <= length(def_name) {
        def_text[i] = $t;
    } else {
        add $n to def_name;
        add $t to def_text;
    }
}

func replace_ident(s, name, repl) {
    local out = "";
    local i = 1;
    local nl = length($name);
    until i > length($s) {
        local hit = false;
        if i + nl - 1 <= length($s) and substr($s, i, i + nl - 1) == $name {
            local before_ok = true;
            local after_ok = true;
            if i > 1 and is_ident_char($s[i - 1]) { before_ok = false; }
            if i + nl <= length($s) and is_ident_char($s[i + nl]) { after_ok = false; }
            if before_ok and after_ok { hit = true; }
        }
        if hit {
            out &= $repl;
            i += nl;
        } else {
            out &= $s[i];
            i++;
        }
    }
    return out;
}

func apply_defs(s) {
    local out = $s;
    local i = 1;
    until i > length(def_name) {
        out = replace_ident(out, def_name[i], "(" & def_text[i] & ")");
        i++;
    }
    return out;
}

func find_top_assign(s) {
    local dep = 0;
    local i = 1;
    until i > length($s) {
        local c = $s[i];
        if c == "(" or c == "[" or c == "{" { dep++; }
        elif c == ")" or c == "]" or c == "}" { dep--; }
        elif c == "=" and dep == 0 { return i; }
        i++;
    }
    return 0;
}

func is_simple_ident(s) {
    if length($s) == 0 { return false; }
    if not (is_alpha_char($s[1]) or $s[1] == "_") { return false; }
    local i = 2;
    until i > length($s) {
        if not is_ident_char($s[i]) { return false; }
        i++;
    }
    return true;
}

nowarp proc run_command s {
    err = "";
    cas_result = "";
    reset_nodes;
    poly_reset;
    bp_reset;
    ng_reset;
    ctb_depth = 0;
    env_clear;
    bind_clear;
    local input = trim($s);
    local assign_at = find_top_assign(input);
    local assign_ok = false;
    local lhs = "";
    local rhs = "";
    if assign_at > 0 {
        lhs = trim(substr(input, 1, assign_at - 1));
        rhs = trim(substr(input, assign_at + 1, length(input)));
        if is_simple_ident(lhs) and rhs != "" {
            assign_ok = true;
        }
    }
    if assign_ok {
        local rexp = apply_defs(rhs);
        parse_text rexp;
        if parse_ok == false {
            cas_result = "错误：" & err;
        } else {
            pr_expr parse_root;
            def_set lhs, pr_out;
            cas_result = lhs & " = " & pr_out;
        }
    } elif length(input) > MAX_INPUT {
        set_err "输入过长";
    } elif is_blank(input) {
        show_help;
    } else {
        input = apply_defs(input);
        local open = find_char(input, "(");
        local handled = false;
        if open > 0 {
            local close = find_close(input, open);
            if close == 0 {
                set_err "括号不匹配";
                handled = true;
            } else {
                local tail = trim(substr(input, close + 1, length(input)));
                if tail == "" {
                    local cmd = norm_ident(trim(substr(input, 1, open - 1)));
                    if is_cmd_name(cmd) {
                        split_args substr(input, open + 1, close - 1);
                        local top_count = arg_count;
                        delete top_args;
                        local ti = 1;
                        until ti > top_count {
                            add args[ti] to top_args;
                            ti++;
                        }
                        ti = 1;
                        until ti > top_count or err != "" {
                            expand_nested_text top_args[ti];
                            if err == "" {
                                top_args[ti] = expand_nested_text;
                            }
                            ti++;
                        }
                        if err == "" {
                            delete args;
                            arg_count = 0;
                            ti = 1;
                            until ti > top_count {
                                add top_args[ti] to args;
                                arg_count++;
                                ti++;
                            }
                            dispatch_function cmd;
                        }
                        handled = true;
                    }
                }
            }
        }
        if handled == false {
            if norm_ident(input) == "help" {
                show_help;
            } else {
                expand_nested_text input;
                if err == "" {
                    do_simplify expand_nested_text;
                }
            }
        }
    }
    if err != "" {
        cas_result = "错误：" & err;
    }
    run_command = 0;
}
