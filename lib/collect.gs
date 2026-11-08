# Collect an expression by powers of one variable.

list col_terms;
list col_stk;
list col_facs;
var col_k = 0;
var col_coeff = 0;

func col_is_x(n, vname) {
    return nd_kind[$n] == K.Var and nd_txt[$n] == $vname;
}

proc col_build_coeff {
    if length(col_facs) == 0 {
        mk_num 1, 1;
        col_coeff = mk_num;
    } else {
        local out = col_facs[1];
        local i = 2;
        until i > length(col_facs) {
            mk_mul out, col_facs[i];
            out = mk_mul;
            i++;
        }
        col_coeff = out;
    }
}

proc col_split term, vname {
    col_k = 0;
    delete col_facs;
    delete col_stk;
    local sp = 0;
    sp++; add $term to col_stk;
    until sp == 0 {
        local x = col_stk[sp];
        sp--;
        if nd_kind[x] == K.Mul {
            sp++;
            if sp > length(col_stk) { add nd_b[x] to col_stk; } else { col_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(col_stk) { add nd_a[x] to col_stk; } else { col_stk[sp] = nd_a[x]; }
        } elif col_is_x(x, $vname) {
            col_k++;
        } elif nd_kind[x] == K.Pow and col_is_x(nd_a[x], $vname) and nd_den[x] == 1 {
            col_k += nd_num[x];
        } else {
            add x to col_facs;
        }
    }
    col_build_coeff;
}

proc collect_expr root, vname {
    expand_expr $root;
    local e = expand_expr;
    if err != "" { collect_expr = 0; } else {
        delete col_terms;
        delete col_stk;
        local sp = 0;
        sp++; add e to col_stk;
        until sp == 0 {
            local x = col_stk[sp];
            sp--;
            if nd_kind[x] == K.Add {
                sp++;
                if sp > length(col_stk) { add nd_b[x] to col_stk; } else { col_stk[sp] = nd_b[x]; }
                sp++;
                if sp > length(col_stk) { add nd_a[x] to col_stk; } else { col_stk[sp] = nd_a[x]; }
            } else { add x to col_terms; }
        }
        delete col_ks;
        delete col_cs;
        local i = 1;
        until i > length(col_terms) {
            col_split col_terms[i], $vname;
            local k = col_k;
            local c = col_coeff;
            local found = 0;
            local j = 1;
            until j > length(col_ks) or found != 0 {
                if col_ks[j] == k { found = j; }
                j++;
            }
            if found > 0 {
                mk_add col_cs[found], c;
                col_cs[found] = mk_add;
            } else {
                add k to col_ks;
                add c to col_cs;
            }
            i++;
        }
        local sum = 0;
        i = 1;
        until i > length(col_ks) {
            local k = col_ks[i];
            local c = col_cs[i];
            local term = c;
            if k != 0 {
                mk_var $vname;
                local xv = mk_var;
                mk_pow xv, k;
                mk_mul c, mk_pow;
                term = mk_mul;
            }
            if sum == 0 { sum = term; } else { mk_add sum, term; sum = mk_add; }
            i++;
        }
        if sum == 0 { mk_num 0, 1; sum = mk_num; }
        collect_expr = sum;
    }
}

list col_ks;
list col_cs;
