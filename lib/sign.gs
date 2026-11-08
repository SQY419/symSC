# Simple exact sign analysis: 1 positive, 0 zero, 2 nonnegative,
# 3 nonpositive, -1 negative, 4 unknown.

list sa_terms;
list sa_stk;

proc sign_collect_add n {
    delete sa_terms;
    delete sa_stk;
    local sp = 0;
    sp++; add $n to sa_stk;
    until sp == 0 {
        local x = sa_stk[sp];
        sp--;
        if nd_kind[x] == K.Add {
            sp++;
            if sp > length(sa_stk) { add nd_b[x] to sa_stk; } else { sa_stk[sp] = nd_b[x]; }
            sp++;
            if sp > length(sa_stk) { add nd_a[x] to sa_stk; } else { sa_stk[sp] = nd_a[x]; }
        } else { add x to sa_terms; }
    }
}

proc sign_of n {
    local k = nd_kind[$n];
    if k == K.Num or k == K.Float {
        if nd_num[$n] > 0 { sign_of = 1; }
        elif nd_num[$n] < 0 { sign_of = -1; }
        else { sign_of = 0; }
    } elif k == K.Pi or k == K.E {
        sign_of = 1;
    } elif k == K.Inf {
        if nd_num[$n] < 0 { sign_of = -1; } else { sign_of = 1; }
    } elif k == K.UN or k == K.Var or k == K.Unknown {
        sign_of = 4;
    } elif k == K.Sqrt {
        if is_zero(nd_a[$n]) { sign_of = 0; } else { sign_of = 2; }
    } elif k == K.Abs {
        sign_of = 2;
    } elif k == K.Exp {
        sign_of = 1;
    } elif k == K.Sin or k == K.Cos or k == K.Tan or k == K.Asin or k == K.Acos or k == K.Atan or k == K.Ln or k == K.Sgn {
        sign_of = 4;
    } elif k == K.Pow {
        local e = nd_num[$n];
        if nd_den[$n] == 1 and e % 2 == 0 {
            sign_of = 2;
        } elif nd_den[$n] == 1 {
            sign_of nd_a[$n];
        } else {
            sign_of = 4;
        }
    } elif k == K.Mul {
        local sp = 0;
        delete sa_stk;
        sp++; add $n to sa_stk;
        local neg = 0;
        local zero = false;
        local unk = false;
        local weak = 0;
        until sp == 0 {
            local x = sa_stk[sp];
            sp--;
            if nd_kind[x] == K.Mul {
                sp++;
                if sp > length(sa_stk) { add nd_b[x] to sa_stk; } else { sa_stk[sp] = nd_b[x]; }
                sp++;
                if sp > length(sa_stk) { add nd_a[x] to sa_stk; } else { sa_stk[sp] = nd_a[x]; }
            } else {
                sign_of x;
                local s = sign_of;
                if s == 0 { zero = true; }
                elif s == -1 { neg++; }
                elif s == 2 { weak = 2; }
                elif s == 3 { weak = 3; }
                elif s == 4 { unk = true; }
            }
        }
        if zero { sign_of = 0; }
        elif unk { sign_of = 4; }
        elif weak != 0 {
            if weak == 2 {
                if neg % 2 == 1 { sign_of = 3; } else { sign_of = 2; }
            } else {
                if neg % 2 == 1 { sign_of = 2; } else { sign_of = 3; }
            }
        } elif neg % 2 == 1 { sign_of = -1; }
        else { sign_of = 1; }
    } elif k == K.Add {
        sign_collect_add $n;
        local pos = 0;
        local neg = 0;
        local zero = 0;
        local nonneg = 0;
        local nonpos = 0;
        local unk = 0;
        local sin_term = 0;
        local i = 1;
        until i > length(sa_terms) {
            local t = sa_terms[i];
            local s = 0;
            sign_of t;
            s = sign_of;
            if s == 1 { pos++; }
            elif s == -1 { neg++; }
            elif s == 0 { zero++; }
            elif s == 2 { nonneg++; }
            elif s == 3 { nonpos++; }
            else {
                unk++;
                if nd_kind[t] == K.Sin or nd_kind[t] == K.Cos { sin_term = t; }
            }
            i++;
        }
        if unk == 0 {
            if neg == 0 and pos > 0 { sign_of = 1; }
            elif neg == 0 and pos == 0 {
                if nonpos > 0 and nonneg == 0 { sign_of = 3; }
                elif nonneg > 0 and nonpos == 0 { sign_of = 2; }
                else { sign_of = 0; }
            } elif pos == 0 and nonneg == 0 { sign_of = -1; }
            elif pos == 0 and nonneg == 0 and neg > 0 { sign_of = -1; }
            else { sign_of = 4; }
        } elif unk == 1 and sin_term != 0 {
            # sin/cos with a constant offset: range [-1,1]
            local c = 0;
            i = 1;
            until i > length(sa_terms) {
                local t = sa_terms[i];
                if nd_kind[t] == K.Num { c += nd_num[t] / nd_den[t]; }
                i++;
            }
            if c > 1 { sign_of = 1; }
            elif c == 1 { sign_of = 2; }
            elif c < -1 { sign_of = -1; }
            elif c == -1 { sign_of = 3; }
            else { sign_of = 4; }
        } else {
            sign_of = 4;
        }
    } else {
        sign_of = 4;
    }
}

