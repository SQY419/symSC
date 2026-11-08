list df_done;
list df_val;
list df_stk_node;
list df_stk_state;
var df_sp = 0;

proc df_push id, state {
    df_sp++;
    if df_sp > length(df_stk_node) {
        add $id to df_stk_node;
        add $state to df_stk_state;
    } else {
        df_stk_node[df_sp] = $id;
        df_stk_state[df_sp] = $state;
    }
}

proc diff_expr root, var_name {
    local v = norm_ident($var_name);
    if $root == 0 or err != "" {
        diff_expr = 0;
    } else {
        delete df_done;
        delete df_val;
        local i = 1;
        until i > node_count {
            add 0 to df_done;
            add 0 to df_val;
            i++;
        }
        delete df_stk_node;
        delete df_stk_state;
        df_sp = 0;
        df_push $root, 0;
        until df_sp == 0 or err != "" {
            local n = df_stk_node[df_sp];
            local st = df_stk_state[df_sp];
            df_sp--;
            if st == 0 {
                if df_done[n] == 0 {
                    df_push n, 1;
                    if nd_kind[n] == K.Add or nd_kind[n] == K.Mul {
                        df_push nd_b[n], 0;
                        df_push nd_a[n], 0;
                    } elif nd_kind[n] == K.Pow {
                        df_push nd_a[n], 0;
                    } elif nd_kind[n] == K.PowE {
                        df_push nd_b[n], 0;
                        df_push nd_a[n], 0;
                    } elif nd_kind[n] >= K.Sin and nd_kind[n] <= K.Atan {
                        df_push nd_a[n], 0;
                    }
                }
            } else {
                if df_done[n] == 0 {
                    local k = nd_kind[n];
                    local d = 0;
                    if k == K.Num or k == K.Pi or k == K.E or k == K.Float {
                        mk_num 0, 1;
                        d = mk_num;
                    } elif k == K.Var {
                        if nd_txt[n] == v {
                            mk_num 1, 1;
                            d = mk_num;
                        } else {
                            mk_num 0, 1;
                            d = mk_num;
                        }
                    } elif k == K.Add {
                        mk_add df_val[nd_a[n]], df_val[nd_b[n]];
                        d = mk_add;
                    } elif k == K.Mul {
                        mk_mul df_val[nd_a[n]], nd_b[n];
                        local p1 = mk_mul;
                        mk_mul nd_a[n], df_val[nd_b[n]];
                        local p2 = mk_mul;
                        mk_add p1, p2;
                        d = mk_add;
                    } elif k == K.Pow {
                        local e = nd_num[n];
                        if e == 0 {
                            mk_num 0, 1;
                            d = mk_num;
                        } else {
                            mk_pow nd_a[n], e - 1;
                            local p = mk_pow;
                            mk_num e, 1;
                            local c = mk_num;
                            mk_mul c, p;
                            local cp = mk_mul;
                            mk_mul cp, df_val[nd_a[n]];
                            d = mk_mul;
                        }
                    } elif k == K.PowE {
                        local ba = nd_a[n];
                        local be = nd_b[n];
                        if nd_kind[be] == K.Num {
                            mk_num nd_num[be] - nd_den[be], nd_den[be];
                            local em1 = mk_num;
                            mk_pow_expr ba, em1;
                            local p = mk_pow_expr;
                            mk_num nd_num[be], nd_den[be];
                            local c = mk_num;
                            mk_mul c, p;
                            local cp = mk_mul;
                            mk_mul cp, df_val[ba];
                            d = mk_mul;
                        } else {
                            mk_pow_expr ba, be;
                            local pw = mk_pow_expr;
                            mk_func K.Ln, ba;
                            local lna = mk_func;
                            mk_mul df_val[be], lna;
                            local t1 = mk_mul;
                            mk_mul be, df_val[ba];
                            local bda = mk_mul;
                            mk_pow ba, -1;
                            local inv = mk_pow;
                            mk_mul bda, inv;
                            local t2 = mk_mul;
                            mk_add t1, t2;
                            local sum = mk_add;
                            mk_mul pw, sum;
                            d = mk_mul;
                        }
                    } elif k == K.Sin {
                        mk_func K.Cos, nd_a[n];
                        local f = mk_func;
                        mk_mul f, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Cos {
                        mk_func K.Sin, nd_a[n];
                        local f = mk_func;
                        mk_neg f;
                        local nf = mk_neg;
                        mk_mul nf, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Tan {
                        mk_func K.Cos, nd_a[n];
                        local f = mk_func;
                        mk_pow f, -2;
                        local q = mk_pow;
                        mk_mul q, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Exp {
                        mk_func K.Exp, nd_a[n];
                        local f = mk_func;
                        mk_mul f, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Ln {
                        mk_pow nd_a[n], -1;
                        local q = mk_pow;
                        mk_mul q, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Log {
                        mk_pow nd_a[n], -1;
                        local q = mk_pow;
                        mk_num 10, 1;
                        local ten = mk_num;
                        mk_func K.Ln, ten;
                        local ln10 = mk_func;
                        mk_pow ln10, -1;
                        local inv = mk_pow;
                        mk_mul q, inv;
                        local q2 = mk_mul;
                        mk_mul q2, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Sqrt {
                        mk_func K.Sqrt, nd_a[n];
                        local f = mk_func;
                        mk_pow f, -1;
                        local inv = mk_pow;
                        mk_num 1, 2;
                        local half = mk_num;
                        mk_mul half, inv;
                        local q = mk_mul;
                        mk_mul q, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Abs {
                        mk_func K.Abs, nd_a[n];
                        local f = mk_func;
                        mk_pow f, -1;
                        local inv = mk_pow;
                        mk_mul nd_a[n], inv;
                        local q = mk_mul;
                        mk_mul q, df_val[nd_a[n]];
                        d = mk_mul;
                    } elif k == K.Asin or k == K.Acos {
                        mk_pow nd_a[n], 2;
                        local u2 = mk_pow;
                        mk_neg u2;
                        local nu2 = mk_neg;
                        mk_num 1, 1;
                        local one = mk_num;
                        mk_add one, nu2;
                        local inner = mk_add;
                        mk_func K.Sqrt, inner;
                        local sq = mk_func;
                        mk_pow sq, -1;
                        local inv = mk_pow;
                        mk_mul inv, df_val[nd_a[n]];
                        if k == K.Acos {
                            mk_neg mk_mul;
                            d = mk_neg;
                        } else {
                            d = mk_mul;
                        }
                    } elif k == K.Atan {
                        mk_pow nd_a[n], 2;
                        local u2 = mk_pow;
                        mk_num 1, 1;
                        local one = mk_num;
                        mk_add one, u2;
                        local den = mk_add;
                        mk_pow den, -1;
                        local inv = mk_pow;
                        mk_mul inv, df_val[nd_a[n]];
                        d = mk_mul;
                    }
                    if d != 0 {
                        df_val[n] = d;
                    }
                    df_done[n] = 1;
                }
            }
        }
        if err != "" {
            diff_expr = 0;
        } else {
            diff_expr = df_val[$root];
        }
    }
}
