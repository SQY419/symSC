list ev_done;
list ev_val;
list ev_stk_node;
list ev_stk_state;
var ev_sp = 0;

list env_name;
list env_val;
var env_count = 0;

var env_v = 0;
var env_ok = false;

proc env_clear {
    delete env_name;
    delete env_val;
    env_count = 0;
}

proc env_set name, value {
    local nm = norm_ident($name);
    local i = 1;
    local found = 0;
    until i > env_count {
        if env_name[i] == nm {
            found = i;
            i = env_count + 1;
        } else {
            i++;
        }
    }
    if found > 0 {
        env_val[found] = $value;
    } else {
        env_count++;
        add nm to env_name;
        add $value to env_val;
    }
}

proc env_lookup name {
    env_ok = false;
    env_v = 0;
    local i = 1;
    until i > env_count or env_ok {
        if env_name[i] == $name {
            env_v = env_val[i];
            env_ok = true;
        } else {
            i++;
        }
    }
    if env_ok == false {
        set_err "未赋值变量 " & $name;
    }
}

proc ev_push id, state {
    ev_sp++;
    if ev_sp > length(ev_stk_node) {
        add $id to ev_stk_node;
        add $state to ev_stk_state;
    } else {
        ev_stk_node[ev_sp] = $id;
        ev_stk_state[ev_sp] = $state;
    }
}

proc pow_value x, e {
    local k = abs($e);
    local acc = 1;
    local i = 1;
    until i > k {
        acc *= $x;
        i++;
    }
    if $e < 0 {
        if $x == 0 {
            set_err "零的负次幂无定义";
            pow_value = 0;
        } else {
            pow_value = 1 / acc;
        }
    } else {
        pow_value = acc;
    }
}
proc pow_real_value x, e {
    if $e != $e {
        set_err "指数不是有限数";
        pow_real_value = 0;
    } elif $e == round($e) {
        pow_value $x, $e;
        pow_real_value = pow_value;
    } elif $x > 0 {
        local v = antiln(ln($x) * $e);
        if v != v {
            set_err "数值结果不是有限数";
            pow_real_value = 0;
        } else {
            pow_real_value = v;
        }
    } elif $x == 0 {
        if $e > 0 {
            pow_real_value = 0;
        } else {
            set_err "零的负次幂无定义";
            pow_real_value = 0;
        }
    } else {
        set_err "负数的非整数次幂需要复数";
        pow_real_value = 0;
    }
}

proc eval_func kind, x {
    local v = 0;
    if $kind == K.Sin {
        v = sin($x * 57.29577951308232);
    } elif $kind == K.Cos {
        v = cos($x * 57.29577951308232);
    } elif $kind == K.Tan {
        v = tan($x * 57.29577951308232);
    } elif $kind == K.Exp {
        v = antiln($x);
    } elif $kind == K.Ln {
        if $x <= 0 {
            set_err "ln 的定义域错误";
        } else {
            v = ln($x);
        }
    } elif $kind == K.Log {
        if $x <= 0 {
            set_err "log 的定义域错误";
        } else {
            v = log($x);
        }
    } elif $kind == K.Sqrt {
        if $x < 0 {
            set_err "sqrt 的定义域错误";
        } else {
            v = sqrt($x);
        }
    } elif $kind == K.Abs {
        v = abs($x);
    } elif $kind == K.Asin {
        if abs($x) > 1 {
            set_err "asin 的定义域错误";
        } else {
            v = asin($x) / 57.29577951308232;
        }
    } elif $kind == K.Acos {
        if abs($x) > 1 {
            set_err "acos 的定义域错误";
        } else {
            v = acos($x) / 57.29577951308232;
        }
    } elif $kind == K.Atan {
        v = atan($x) / 57.29577951308232;
    }
    if v != v {
        set_err "数值结果不是有限数";
        eval_func = 0;
    } else {
        eval_func = v;
    }
}

proc eval_expr root {
    if $root == 0 or err != "" {
        eval_expr = 0;
    } else {
        delete ev_done;
        delete ev_val;
        local i = 1;
        until i > node_count {
            add 0 to ev_done;
            add 0 to ev_val;
            i++;
        }
        delete ev_stk_node;
        delete ev_stk_state;
        ev_sp = 0;
        ev_push $root, 0;
        until ev_sp == 0 or err != "" {
            local n = ev_stk_node[ev_sp];
            local st = ev_stk_state[ev_sp];
            ev_sp--;
            if st == 0 {
                if ev_done[n] == 0 {
                    ev_push n, 1;
                    if nd_kind[n] == K.Add or nd_kind[n] == K.Mul {
                        ev_push nd_b[n], 0;
                        ev_push nd_a[n], 0;
                    } elif nd_kind[n] == K.Pow {
                        ev_push nd_a[n], 0;
                    } elif nd_kind[n] == K.PowE {
                        ev_push nd_b[n], 0;
                        ev_push nd_a[n], 0;
                    } elif nd_kind[n] >= K.Sin and nd_kind[n] <= K.Atan {
                        ev_push nd_a[n], 0;
                    }
                }
            } else {
                if ev_done[n] == 0 {
                    local k = nd_kind[n];
                    local v = 0;
                    if k == K.Num {
                        v = nd_num[n] / nd_den[n];
                    } elif k == K.Float {
                        v = nd_num[n];
                    } elif k == K.Big {
                        v = nd_txt[n] + 0;
                    } elif k == K.BigFloat {
                        v = nd_num[n] * antiln(nd_den[n] * ln(10));
                    } elif k == K.Inf {
                        v = nd_num[n] * 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
                    } elif k == K.Var {
                        env_lookup nd_txt[n];
                        if env_ok {
                            v = env_v;
                        }
                    } elif k == K.Pi {
                        v = 3.141592653589793;
                    } elif k == K.E {
                        v = 2.718281828459045;
                    } elif k == K.Add {
                        v = ev_val[nd_a[n]] + ev_val[nd_b[n]];
                    } elif k == K.Mul {
                        v = ev_val[nd_a[n]] * ev_val[nd_b[n]];
                    } elif k == K.Pow {
                        pow_value ev_val[nd_a[n]], nd_num[n];
                        v = pow_value;
                    } elif k == K.PowE {
                        pow_real_value ev_val[nd_a[n]], ev_val[nd_b[n]];
                        v = pow_real_value;
                    } else {
                        eval_func k, ev_val[nd_a[n]];
                        v = eval_func;
                    }
                    if err == "" {
                        ev_val[n] = v;
                        ev_done[n] = 1;
                    }
                }
            }
        }
        if err != "" {
            eval_expr = 0;
        } else {
            eval_expr = ev_val[$root];
        }
    }
}
