# Conservative test: can this expression be safely expanded as a polynomial?

list pc_stk;
var pc_bad = false;

proc pc_has_var root {
    pc_has_var = false;
    delete pc_stk;
    local sp = 0;
    sp++; add $root to pc_stk;
    until sp == 0 {
        local n = pc_stk[sp];
        sp--;
        local k = nd_kind[n];
        if k == K.Var { pc_has_var = true; sp = 0; }
        elif k == K.Add or k == K.Mul or k == K.PowE {
            sp++;
            if sp > length(pc_stk) { add nd_b[n] to pc_stk; } else { pc_stk[sp] = nd_b[n]; }
            sp++;
            if sp > length(pc_stk) { add nd_a[n] to pc_stk; } else { pc_stk[sp] = nd_a[n]; }
        } elif k == K.Pow or (k >= K.Sin and k <= K.Atan) or k == K.Sgn or k == K.Unknown {
            sp++;
            if sp > length(pc_stk) { add nd_a[n] to pc_stk; } else { pc_stk[sp] = nd_a[n]; }
        }
    }
}

proc poly_expandable root {
    delete pc_stk;
    local sp = 0;
    sp++; add $root to pc_stk;
    local bad = false;
    until sp == 0 or bad {
        local n = pc_stk[sp];
        sp--;
        local k = nd_kind[n];
        if k == K.Vec or k == K.List or k == K.BigFloat or k == K.Big or (k == K.Pow and nd_kind[nd_a[n]] == K.Big and nd_num[n] < 0) {
            bad = true;
        } elif k == K.PowE or (k >= K.Sin and k <= K.Atan) or k == K.Sgn or k == K.Unknown {
            pc_has_var n;
            if pc_has_var { bad = true; }
        } elif k == K.Pow {
            if nd_num[n] < 0 or nd_den[n] != 1 { bad = true; }
            else {
                sp++;
                if sp > length(pc_stk) { add nd_a[n] to pc_stk; } else { pc_stk[sp] = nd_a[n]; }
            }
        } elif k == K.Add or k == K.Mul {
            sp++;
            if sp > length(pc_stk) { add nd_b[n] to pc_stk; } else { pc_stk[sp] = nd_b[n]; }
            sp++;
            if sp > length(pc_stk) { add nd_a[n] to pc_stk; } else { pc_stk[sp] = nd_a[n]; }
        } elif k == K.UN or k == K.Inf {
            # allowed; expand handles them
        }
    }
    poly_expandable = (bad == false);
}
