list tk_big;
func substr(s, a, b) {
    local i = $a;
    local buf = "";
    until i > $b {
        buf &= $s[i];
        i++;
    }
    return buf;
}

var lex_big = false;

proc lex_num_text t {
    local i = 1;
    lex_big = false;
    local n = 0;
    local d = 1;
    local dot = false;
    local digits = 0;
    until i > length($t) {
        local c = $t[i];
        if c == "." {
            if dot {
                set_err "数字格式错误";
                i = length($t) + 1;
            } else {
                dot = true;
                i++;
            }
        } elif is_digit_char(c) {
            local v = digit_value(c);
            if v < 0 {
                set_err "数字格式错误";
                i = length($t) + 1;
            } else {
                safe_mul n, 10;
                if sok == false {
                    lex_big = true;
                    err = "";
                    i = length($t) + 1;
                } else {
                    local p = sa;
                    safe_add p, v;
                    if sok == false {
                        lex_big = true;
                        err = "";
                        i = length($t) + 1;
                    } else {
                        n = sa;
                        if dot {
                            safe_mul d, 10;
                            if sok == false {
                                i = length($t) + 1;
                            } else {
                                d = sa;
                            }
                        }
                        digits++;
                        i++;
                    }
                }
            }
        } else {
            set_err "数字格式错误";
            i = length($t) + 1;
        }
    }
    if digits == 0 {
        set_err "数字缺少数字位";
        lex_ok = false;
    } elif lex_big {
        lex_n = 0;
        lex_d = 1;
    } elif err == "" {
        rat_norm n, d;
        if rok == false {
            lex_ok = false;
        } else {
            lex_n = rn;
            lex_d = rd;
        }
    } else {
        lex_ok = false;
    }
}

proc add_token t, text, pos {
    token_count++;
    if token_count > length(tk_type) {
        add $t to tk_type;
        add $text to tk_text;
        add $pos to tk_pos;
        add lex_n to tk_num;
        add lex_d to tk_den;
        add lex_big to tk_big;
    } else {
        tk_type[token_count] = $t;
        tk_text[token_count] = $text;
        tk_pos[token_count] = $pos;
        tk_num[token_count] = lex_n;
        tk_den[token_count] = lex_d;
        tk_big[token_count] = lex_big;
    }
}

proc lex s {
    delete tk_type;
    delete tk_text;
    delete tk_pos;
    delete tk_num;
    delete tk_den;
    delete tk_big;
    token_count = 0;
    lex_ok = true;
    local i = 1;
    until i > length($s) or lex_ok == false {
        local c = $s[i];
        if is_space(c) {
            i++;
        } elif is_digit_char(c) or c == "." {
            local start = i;
            local dot = false;
            local digits = 0;
            local scanning = true;
            local sci = false;
            until scanning == false or i > length($s) {
                local d = $s[i];
                if is_digit_char(d) {
                    digits++;
                    i++;
                } elif d == "." and dot == false {
                    dot = true;
                    i++;
                } else {
                    scanning = false;
                }
            }
            if i <= length($s) and ($s[i] == "e" or $s[i] == "E") {
                local j = i + 1;
                if j <= length($s) and ($s[j] == "+" or $s[j] == "-") { j++; }
                local ed = 0;
                local sc2 = true;
                until sc2 == false or j > length($s) {
                    if is_digit_char($s[j]) {
                        ed++;
                        j++;
                    } else {
                        sc2 = false;
                    }
                }
                if ed > 0 { i = j; sci = true; }
            }
            local text = substr($s, start, i - 1);
            if digits == 0 {
                set_err "数字缺少数字位";
                lex_ok = false;
            } elif sci {
                add_token T.Sci, text, start;
            } else {
                lex_num_text text;
                if lex_ok {
                    add_token T.Num, text, start;
                }
            }
        } elif is_alpha_char(c) or c == "_" {
            local start = i;
            local scanning = true;
            until scanning == false or i > length($s) {
                if is_ident_char($s[i]) {
                    i++;
                } else {
                    scanning = false;
                }
            }
            local text = substr($s, start, i - 1);
            add_token T.Ident, text, start;
        } elif c == "+" or c == "-" or c == "*" or c == "/" or c == "^" {
            add_token T.Op, c, i;
            i++;
        } elif c == "<" or c == ">" {
            add_token T.Op, c, i;
            i++;
        } elif c == "=" {
            if i < length($s) and $s[i + 1] == "=" {
                add_token T.Op, "==", i;
                i += 2;
            } else {
                add_token T.Op, "=", i;
                i++;
            }
        } elif c == "(" {
            add_token T.LP, c, i;
            i++;
        } elif c == ")" {
            add_token T.RP, c, i;
            i++;
        } elif c == "," {
            add_token T.Comma, c, i;
            i++;
        } elif c == "[" {
            add_token T.LBracket, c, i;
            i++;
        } elif c == "]" {
            add_token T.RBracket, c, i;
            i++;
        } elif c == "{" {
            add_token T.LBrace, c, i;
            i++;
        } elif c == "}" {
            add_token T.RBrace, c, i;
            i++;
        } else {
            set_err "未知字符 " & c;
            lex_ok = false;
        }
    }
    if lex_ok {
        lex_n = 0;
        lex_d = 1;
        add_token T.End, "", i;
    }
    lex = 0;
}
