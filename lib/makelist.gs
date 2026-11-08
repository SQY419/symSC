# makelist(expr, var, begin, end) -> {expr(begin), ..., expr(end)}
# Values are evaluated with the ordinary substitution/simplification pipeline.

proc do_makelist ex, vn, bn, en {
    do_makelist = 0;
    if nd_kind[$vn] != K.Var {
        set_err "makelist 变量无效";
    } elif nd_kind[$bn] != K.Num or nd_den[$bn] != 1 or nd_kind[$en] != K.Num or nd_den[$en] != 1 {
        set_err "makelist 范围必须是整数";
    } else {
        local vname = nd_txt[$vn];
        local lo = nd_num[$bn];
        local hi = nd_num[$en];
        ctb_begin K.List;
        local i = lo;
        until i > hi or err != "" {
            subst_clear;
            mk_num i, 1;
            subst_add vname, mk_num;
            subst_expr $ex;
            if err == "" {
                rules_simplify subst_expr;
            }
            if err == "" {
                combine_powers rules_simplify;
                if combine_powers != 0 { rules_simplify = combine_powers; }
            }
            if err == "" {
                exact_fold rules_simplify;
                if err == "" { ctb_add exact_fold; }
            }
            i++;
        }
        if err == "" {
            ctb_end;
            do_makelist = ctb_out;
        } else {
            ctb_depth--;
        }
    }
}
