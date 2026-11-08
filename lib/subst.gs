list sub_name;
list sub_node;
var sub_count = 0;

list sb_done;
list sb_val;
list sb_stk_node;
list sb_stk_state;
var sb_sp = 0;

proc subst_clear {
    delete sub_name;
    delete sub_node;
    sub_count = 0;
}

proc subst_add name, node {
    local nm = norm_ident($name);
    local i = 1;
    local found = 0;
    until i > sub_count {
        if sub_name[i] == nm {
            found = i;
            i = sub_count + 1;
        } else {
            i++;
        }
    }
    if found > 0 {
        sub_node[found] = $node;
    } else {
        sub_count++;
        add nm to sub_name;
        add $node to sub_node;
    }
}

func subst_lookup(name) {
    local i = 1;
    until i > sub_count {
        if sub_name[i] == $name {
            return sub_node[i];
        }
        i++;
    }
    return 0;
}

proc sb_push id, state {
    sb_sp++;
    if sb_sp > length(sb_stk_node) {
        add $id to sb_stk_node;
        add $state to sb_stk_state;
    } else {
        sb_stk_node[sb_sp] = $id;
        sb_stk_state[sb_sp] = $state;
    }
}

proc subst_expr root {
    if $root == 0 or err != "" {
        subst_expr = 0;
    } else {
        delete sb_done;
        delete sb_val;
        local i = 1;
        until i > node_count {
            add 0 to sb_done;
            add 0 to sb_val;
            i++;
        }
        delete sb_stk_node;
        delete sb_stk_state;
        sb_sp = 0;
        sb_push $root, 0;
        until sb_sp == 0 or err != "" {
            local n = sb_stk_node[sb_sp];
            local st = sb_stk_state[sb_sp];
            sb_sp--;
            if st == 0 {
                if sb_done[n] == 0 {
                    sb_push n, 1;
                    if nd_kind[n] == K.Add or nd_kind[n] == K.Mul {
                        sb_push nd_b[n], 0;
                        sb_push nd_a[n], 0;
                    } elif nd_kind[n] == K.Pow {
                        sb_push nd_a[n], 0;
                    } elif nd_kind[n] == K.PowE {
                        sb_push nd_b[n], 0;
                        sb_push nd_a[n], 0;
                    } elif nd_kind[n] >= K.Sin and nd_kind[n] <= K.Atan {
                        sb_push nd_a[n], 0;
                    }
                }
            } else {
                if sb_done[n] == 0 {
                    local k = nd_kind[n];
                    local d = n;
                    if k == K.Var {
                        local r = subst_lookup(nd_txt[n]);
                        if r != 0 {
                            d = r;
                        }
                    } elif k == K.Add {
                        mk_add sb_val[nd_a[n]], sb_val[nd_b[n]];
                        d = mk_add;
                    } elif k == K.Mul {
                        mk_mul sb_val[nd_a[n]], sb_val[nd_b[n]];
                        d = mk_mul;
                    } elif k == K.Pow {
                        mk_pow sb_val[nd_a[n]], nd_num[n];
                        d = mk_pow;
                    } elif k == K.PowE {
                        mk_pow_expr sb_val[nd_a[n]], sb_val[nd_b[n]];
                        d = mk_pow_expr;
                    } elif k >= K.Sin and k <= K.Atan {
                        mk_func k, sb_val[nd_a[n]];
                        d = mk_func;
                    }
                    if d != 0 {
                        sb_val[n] = d;
                    }
                    sb_done[n] = 1;
                }
            }
        }
        if err != "" {
            subst_expr = 0;
        } else {
            subst_expr = sb_val[$root];
        }
    }
}
