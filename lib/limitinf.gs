# Leading-term analysis for limits at +infinity.
#
# This is a compact Gruntz-style comparison for polynomial/radical expressions.
# Every subexpression gets a pair (growth order, leading coefficient):
#   x -> (1, 1), constants -> (0, c)
#   multiply -> orders add, coefficients multiply
#   power -> order scales, coefficient is raised to the power
#   sqrt -> order halves, coefficient is square-rooted
# The limit is then read from the sign of the order and the coefficient.

list li_ord;
list li_co;
list li_good;
list li_stk_node;
list li_stk_state;
var li_sp = 0;
var li_ok = false;
var li_result = 0;

proc li_push node, state {
    li_sp++;
    if li_sp > length(li_stk_node) {
        add $node to li_stk_node;
        add $state to li_stk_state;
    } else {
        li_stk_node[li_sp] = $node;
        li_stk_state[li_sp] = $state;
    }
}

proc li_value node {
    local k = nd_kind[$node];
    if k == K.Num or k == K.Float or k == K.Pi or k == K.E or k == K.Inf {
        li_ord[$node] = 0;
        li_co[$node] = $node;
        li_good[$node] = true;
    } elif k == K.Var and nd_txt[$node] == lim_vname {
        li_ord[$node] = 1;
        mk_num 1, 1;
        li_co[$node] = mk_num;
        li_good[$node] = true;
    } elif k == K.Var or k == K.Unknown {
        li_ord[$node] = 0;
        li_co[$node] = $node;
        li_good[$node] = true;
    } elif k == K.Add {
        local a = nd_a[$node];
        local b = nd_b[$node];
        if li_good[a] and li_good[b] {
            if li_ord[a] > li_ord[b] {
                li_ord[$node] = li_ord[a];
                li_co[$node] = li_co[a];
                li_good[$node] = true;
            } elif li_ord[b] > li_ord[a] {
                li_ord[$node] = li_ord[b];
                li_co[$node] = li_co[b];
                li_good[$node] = true;
            } else {
                mk_add li_co[a], li_co[b];
                local c = mk_add;
                if is_zero(c) {
                    li_good[$node] = false;
                } else {
                    li_ord[$node] = li_ord[a];
                    li_co[$node] = c;
                    li_good[$node] = true;
                }
            }
        } else {
            li_good[$node] = false;
        }
    } elif k == K.Mul {
        local a = nd_a[$node];
        local b = nd_b[$node];
        if li_good[a] and li_good[b] {
            li_ord[$node] = li_ord[a] + li_ord[b];
            mk_mul li_co[a], li_co[b];
            li_co[$node] = mk_mul;
            li_good[$node] = err == "" and not is_zero(li_co[$node]);
        } else {
            li_good[$node] = false;
        }
    } elif k == K.Pow {
        local a = nd_a[$node];
        local e = nd_num[$node];
        if li_good[a] {
            li_ord[$node] = li_ord[a] * e;
            mk_pow li_co[a], e;
            li_co[$node] = mk_pow;
            li_good[$node] = err == "";
        } else {
            li_good[$node] = false;
        }
    } elif k == K.PowE {
        local a = nd_a[$node];
        local e = nd_b[$node];
        if li_good[a] and nd_kind[e] == K.Num {
            li_ord[$node] = li_ord[a] * nd_num[e] / nd_den[e];
            mk_pow_expr li_co[a], e;
            li_co[$node] = mk_pow_expr;
            li_good[$node] = err == "";
        } else {
            li_good[$node] = false;
        }
    } elif k == K.Sqrt {
        local a = nd_a[$node];
        if li_good[a] {
            li_ord[$node] = li_ord[a] / 2;
            mk_func K.Sqrt, li_co[a];
            li_co[$node] = mk_func;
            li_good[$node] = err == "";
        } else {
            li_good[$node] = false;
        }
    } elif k == K.Abs {
        local a = nd_a[$node];
        if li_good[a] {
            li_ord[$node] = li_ord[a];
            mk_func K.Abs, li_co[a];
            li_co[$node] = mk_func;
            li_good[$node] = err == "";
        } else {
            li_good[$node] = false;
        }
    } else {
        li_good[$node] = false;
    }
}

var lim_vname = 0;

proc limit_inf_lead root, vname {
    lim_vname = $vname;
    li_ok = false;
    li_result = 0;
    if $root == 0 or err != "" {
        limit_inf_lead = 0;
    } else {
        delete li_ord;
        delete li_co;
        delete li_good;
        local i = 1;
        until i > node_count {
            add 0 to li_ord;
            add 0 to li_co;
            add false to li_good;
            i++;
        }
        delete li_stk_node;
        delete li_stk_state;
        li_sp = 0;
        li_push $root, 0;
        until li_sp == 0 or err != "" {
            local n = li_stk_node[li_sp];
            local st = li_stk_state[li_sp];
            li_sp--;
            if st == 0 {
                li_push n, 1;
                local k = nd_kind[n];
                if k == K.Add or k == K.Mul or k == K.PowE {
                    li_push nd_b[n], 0;
                    li_push nd_a[n], 0;
                } elif k == K.Pow or k == K.Sqrt or k == K.Abs {
                    li_push nd_a[n], 0;
                }
            } else {
                li_value n;
            }
        }
        if err != "" or not li_good[$root] {
            limit_inf_lead = 0;
        } else {
            local order = li_ord[$root];
            local co = li_co[$root];
            if order > 0 {
                sign_of co;
                local sg = sign_of;
                if sg == 1 { mk_inf 1; li_result = mk_inf; li_ok = true; }
                elif sg == -1 { mk_inf -1; li_result = mk_inf; li_ok = true; }
                else { li_ok = false; }
            } elif order == 0 {
                rules_simplify co;
                if err == "" { li_result = rules_simplify; li_ok = true; }
            } else {
                mk_num 0, 1;
                li_result = mk_num;
                li_ok = true;
            }
            if li_ok { limit_inf_lead = li_result; } else { limit_inf_lead = 0; }
        }
    }
}
