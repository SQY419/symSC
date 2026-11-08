# Exact constant folding for limits and series.

list ex_val;
list ex_stk_node;
list ex_stk_state;

proc ex_rebuild n {
    local k = nd_kind[$n];
    if k == K.Add {
        mk_add ex_val[nd_a[$n]], ex_val[nd_b[$n]];
        ex_rebuild = mk_add;
    } elif k == K.Mul {
        mk_mul ex_val[nd_a[$n]], ex_val[nd_b[$n]];
        ex_rebuild = mk_mul;
    } elif k == K.Pow {
        mk_pow ex_val[nd_a[$n]], nd_num[$n];
        ex_rebuild = mk_pow;
    } elif k == K.PowE {
        mk_pow_expr ex_val[nd_a[$n]], ex_val[nd_b[$n]];
        ex_rebuild = mk_pow_expr;
    } elif (k >= K.Sin and k <= K.Tan) or (k >= K.Asin and k <= K.Atan) {
        mk_func k, ex_val[nd_a[$n]];
        local f = mk_func;
        trig_simplify f;
        if err == "" and trig_simplify != 0 { ex_rebuild = trig_simplify; }
        else { ex_rebuild = f; }
    } elif k == K.Exp {
        local a = ex_val[nd_a[$n]];
        if nd_kind[a] == K.Num and nd_num[a] == 0 {
            mk_num 1, 1; ex_rebuild = mk_num;
        } else { mk_func K.Exp, a; ex_rebuild = mk_func; }
    } elif k == K.Ln {
        local a = ex_val[nd_a[$n]];
        if nd_kind[a] == K.Num and nd_num[a] == 1 and nd_den[a] == 1 {
            mk_num 0, 1; ex_rebuild = mk_num;
        } elif nd_kind[a] == K.E {
            mk_num 1, 1; ex_rebuild = mk_num;
        } else { mk_func K.Ln, a; ex_rebuild = mk_func; }
    } elif k == K.Abs {
        local a = ex_val[nd_a[$n]];
        if nd_kind[a] == K.Num {
            mk_num abs(nd_num[a]), nd_den[a]; ex_rebuild = mk_num;
        } else { mk_func K.Abs, a; ex_rebuild = mk_func; }
    } elif k == K.Sqrt {
        local a = ex_val[nd_a[$n]];
        mk_func K.Sqrt, a;
        ex_rebuild = mk_func;
    } elif k == K.Unknown {
        mk_genfunc nd_txt[$n], ex_val[nd_a[$n]];
        ex_rebuild = mk_genfunc;
    } else {
        ex_rebuild = $n;
    }
}

proc exact_fold root {
    delete ex_val;
    local i = 1;
    until i > node_count { add 0 to ex_val; i++; }
    delete ex_stk_node; delete ex_stk_state;
    local sp = 0;
    sp++; add $root to ex_stk_node; add 0 to ex_stk_state;
    until sp == 0 or err != "" {
        local n = ex_stk_node[sp];
        local st = ex_stk_state[sp];
        sp--;
        if st == 0 {
            sp++;
            if sp > length(ex_stk_node) { add n to ex_stk_node; add 1 to ex_stk_state; }
            else { ex_stk_node[sp] = n; ex_stk_state[sp] = 1; }
            local k = nd_kind[n];
            if k == K.Add or k == K.Mul or k == K.PowE {
                sp++;
                if sp > length(ex_stk_node) { add nd_b[n] to ex_stk_node; add 0 to ex_stk_state; }
                else { ex_stk_node[sp] = nd_b[n]; ex_stk_state[sp] = 0; }
                sp++;
                if sp > length(ex_stk_node) { add nd_a[n] to ex_stk_node; add 0 to ex_stk_state; }
                else { ex_stk_node[sp] = nd_a[n]; ex_stk_state[sp] = 0; }
            } elif k == K.Pow or k == K.Sin or k == K.Cos or k == K.Tan or k == K.Asin or k == K.Acos or k == K.Atan or k == K.Exp or k == K.Ln or k == K.Abs or k == K.Sqrt or k == K.Unknown {
                sp++;
                if sp > length(ex_stk_node) { add nd_a[n] to ex_stk_node; add 0 to ex_stk_state; }
                else { ex_stk_node[sp] = nd_a[n]; ex_stk_state[sp] = 0; }
            }
        } else {
            ex_rebuild n;
            if err == "" { ex_val[n] = ex_rebuild; }
        }
    }
    if err != "" { exact_fold = 0; } else { exact_fold = ex_val[$root]; }
}
