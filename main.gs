costumes "assets/cas-character.svg";
%include lib/consts
%include lib/util
%include lib/num
%include lib/big
%include lib/zmwrap
%include lib/arena
%include lib/algebra
%include lib/combine
%include lib/trig
%include lib/trigtrans
%include lib/collect
%include lib/polycheck
%include lib/rationalize
%include lib/sign
%include lib/exact
%include lib/rules
%include lib/poly
%include lib/bipoly
%include lib/ngcd
%include lib/bind
%include lib/lex
%include lib/subst
%include lib/makelist
%include lib/parse
%include lib/print
%include lib/diff
%include lib/expand
%include lib/fracadd
%include lib/eval
%include lib/approx
%include lib/series
%include lib/limitinf
%include lib/api

list results;
list history;

proc push_history line {
    insert $line at history[1];
    if length(history) > 200 {
        delete history[length(history)];
    }
}

list err_zh = ["acos 的定义域错误", "asin 的定义域错误", "collect 需要 2 个参数", "diff 需要 1 或 2 个参数", "eval 需要至少 1 个参数", "expand 需要 1 个参数", "gcd 需要 2 个参数", "gcd/lcm 需要 2 个参数", "help 不能嵌套", "lcm 需要 2 个参数", "limit 需要 3 个参数", "ln 的定义域错误", "log 的定义域错误", "series 需要 3 个参数", "simplify 需要 1 个参数", "sqrt 的定义域错误", "subst 需要至少 2 个参数", "一元运算缺少操作数", "三角变换需要 1 个参数", "代入右侧表达式错误", "代入左侧必须是变量", "代入格式应为 变量=表达式", "代入缺少右侧表达式", "函数只接受一个参数", "函数缺少参数", "多项式 gcd 计算失败", "多项式 lcm 除法失败", "多项式系数除零", "展开项过多", "嵌套过深", "括号不匹配", "括号或函数未闭合", "指数不是有限数", "指数过大", "数值不是有限数", "数值乘法溢出", "数值加法溢出", "数值结果不是有限数", "数值超出安全整数范围", "数字格式错误", "数字缺少数字位", "无法解析的记号", "未赋值变量", "极限不存在（趋于无穷）", "极限无法求值", "极限无法直接求值", "极限无法确定", "求导变量必须是变量名", "表达式不完整", "表达式过大", "负数的非整数次幂需要复数", "赋值格式错误", "赋值缺少值", "赋值表达式错误", "输入过长", "运算符缺少操作数", "除数为零", "零的负次幂无定义", "collect 的变量无效", "gcd 只支持多项式", "lcm 只支持多项式", "lcm 除法失败", "limit 的变量无效", "modular gcd 失败", "n 元 gcd 规模超限", "n 元 lcm 失败", "n 元 lcm 规模超限", "n 元 modular gcd 失败", "series 的变量无效", "series 第二个参数应为 x=点", "series 阶数应为 0..16 的整数", "无穷极限暂不支持该形式", "索引越界", "索引必须是整数", "对象不可索引", "索引只能有一个表达式", "索引括号不匹配", "makelist 需要 4 个参数", "makelist 变量无效", "makelist 范围必须是整数", "makelist 参数错误", "makelist 参数为空", "makelist 括号不匹配", "容器形状不匹配", "向量长度不匹配", "矩阵尺寸不匹配", "矩阵与向量尺寸不匹配", "容器与标量不能相加", "容器乘法不支持", "不支持向量乘矩阵", "定义格式错误", "cross 需要两个三维向量", "transpose 需要矩阵", "矩阵行长度不一致", "det 需要方阵", "det 目前只支持 1x1/2x2/3x3", "零向量没有单位向量"];
list err_en = ["acos domain error", "asin domain error", "collect expects 2 arguments", "diff expects 1 or 2 arguments", "eval expects at least 1 argument", "expand expects 1 argument", "gcd expects 2 arguments", "gcd/lcm expects 2 arguments", "help cannot be nested", "lcm expects 2 arguments", "limit expects 3 arguments", "ln domain error", "log domain error", "series expects 3 arguments", "simplify expects 1 argument", "sqrt domain error", "subst expects at least 2 arguments", "Missing unary operand", "trig transform expects 1 argument", "Invalid substitution right-hand expression", "Substitution left side must be a variable", "Substitution format must be variable=expression", "Substitution is missing right-hand expression", "Function takes exactly one argument", "Function is missing an argument", "Polynomial gcd failed", "Polynomial lcm division failed", "Polynomial coefficient division by zero", "Too many expanded terms", "Nesting too deep", "Mismatched parentheses", "Unclosed parenthesis or function", "Exponent is not finite", "Exponent too large", "Value is not finite", "Numeric multiplication overflow", "Numeric addition overflow", "Numeric result is not finite", "Numeric value exceeds safe integer range", "Invalid number format", "Number is missing digits", "Unrecognized token", "Undefined variable", "Limit does not exist (goes to infinity)", "Limit cannot be evaluated", "Limit cannot be evaluated directly", "Limit cannot be determined", "Differentiation variable must be a variable name", "Incomplete expression", "Expression too large", "Negative base with non-integer exponent needs complex numbers", "Invalid assignment format", "Assignment is missing a value", "Invalid assignment expression", "Input too long", "Missing operator number", "Division by zero", "Zero to a negative power is undefined", "Invalid collect variable", "gcd only supports polynomials", "lcm only supports polynomials", "lcm division failed", "Invalid limit variable", "Modular gcd failed", "n-ary gcd size limit exceeded", "n-ary lcm failed", "n-ary lcm size limit exceeded", "n-ary modular gcd failed", "Invalid series variable", "series second argument must be x=point", "series order must be an integer 0..16", "Infinite limit form not supported", "Index out of range", "Index must be an integer", "Object is not indexable", "Index must be a single expression", "Mismatched index brackets", "makelist requires 4 arguments", "Invalid makelist variable", "makelist range must be integers", "makelist argument error", "Empty makelist argument", "Mismatched makelist parentheses", "Container shape mismatch", "Vector length mismatch", "Matrix dimensions mismatch", "Matrix/vector dimensions mismatch", "Cannot add container and scalar", "Container multiplication is not supported", "Vector times matrix is not supported", "Invalid definition", "cross requires two 3D vectors", "transpose requires a matrix", "Matrix rows have different lengths", "det requires a square matrix", "det supports only 1x1/2x2/3x3", "Zero vector has no unit vector"];
list err_fn = ["eval", "eval", "api", "api", "api", "api", "api", "api", "api", "api", "api", "eval", "eval", "api", "api", "eval", "api", "tokenizer", "api", "subst", "subst", "subst", "subst", "tokenizer", "tokenizer", "gcd", "lcm", "gcd", "expand", "api", "tokenizer", "tokenizer", "eval", "eval", "eval", "eval", "eval", "eval", "eval", "tokenizer", "tokenizer", "tokenizer", "eval", "limit", "limit", "limit", "limit", "diff", "tokenizer", "tokenizer", "eval", "api", "api", "api", "tokenizer", "tokenizer", "eval", "eval", "collect", "gcd", "lcm", "lcm", "limit", "gcd", "gcd", "lcm", "lcm", "gcd", "series", "series", "series", "limit", "index", "index", "index", "index", "index", "makelist", "makelist", "makelist", "makelist", "makelist", "makelist", "container", "vector", "matrix", "matrix", "container", "container", "vector", "definition", "cross", "transpose", "transpose", "det", "det", "unitV"];

func starts_with(s, p) {
    if length($s) < length($p) {
        return false;
    }
    local i = 1;
    until i > length($p) {
        if $s[i] != $p[i] {
            return false;
        }
        i++;
    }
    return true;
}

func err_lookup(msg) {
    local i = 1;
    until i > length(err_zh) {
        if err_zh[i] == $msg {
            return i;
        }
        i++;
    }
    return 0;
}

func ascii_char(c) {
    if $c >= " " and $c <= "~" {
        return $c;
    }
    return "?";
}

proc term_add_raw text, style {
    add $text to term_lines;
    add $style to term_styles;
    until length(term_lines) <= 5000 {
        delete term_lines[1];
        delete term_styles[1];
    }
    term_scroll = length(term_lines) * term_step - term_view + term_overscan;
    if term_scroll < 0 {
        term_scroll = 0;
    }
}

proc term_append_styled text, style {
    local line = "";
    local i = 1;
    until i > length($text) {
        line &= ascii_char($text[i]);
        if length(line) == 51 or i == length($text) {
            term_add_raw line, $style;
            line = "";
        }
        i++;
    }
    if length($text) == 0 {
        term_add_raw "", $style;
    }
}

proc term_append text {
    term_append_styled $text, 0;
}

proc term_append_multiline text {
    local start = 1;
    local i = 1;
    until i > length($text) + 1 {
        if i > length($text) or $text[i] == "\n" {
            local part = substr($text, start, i - 1);
            if part != "" { term_append_styled part, 0; }
            start = i + 1;
        }
        i++;
    }
}

proc term_clear {
    delete term_lines;
    delete term_styles;
    term_append_styled "Scratch CAS v0.1", 0;
    term_append_styled "Type help for commands.", 0;
    term_scroll = 0;
}

proc term_help {
    cas_help = false;
    delete args;
    arg_count = 0;
    show_help;
    term_append_multiline cas_result;
    cas_help = false;
}

proc term_error_raw msg {
    local k = err_lookup($msg);
    if k > 0 {
        term_append_styled ("Error: " & err_en[k] & " @ func '" & err_fn[k] & "'"), 3;
    } elif starts_with($msg, "未知字符 ") {
        term_append_styled "Error: Unknown character @ func 'tokenizer'", 3;
    } elif starts_with($msg, "未知运算符 ") {
        term_append_styled "Error: Unknown operator @ func 'tokenizer'", 3;
    } elif starts_with($msg, "未知函数 ") {
        term_append_styled "Error: Unknown function @ func 'tokenizer'", 3;
    } elif starts_with($msg, "未赋值变量 ") {
        term_append_styled "Error: Undefined variable @ func 'eval'", 3;
    } elif starts_with($msg, "未知命令 ") {
        term_append_styled "Error: Unknown command @ func 'api'", 3;
    } elif starts_with($msg, "函数 ") {
        term_append_styled "Error: Function requires parentheses @ func 'tokenizer'", 3;
    } else {
        term_append_styled "Error: Unknown error @ func 'cas'", 3;
    }
}

proc term_error msg {
    if starts_with($msg, "错误：") {
        term_error_raw (substr($msg, 4, length($msg)));
    } else {
        term_error_raw $msg;
    }
}

onflag {
    if length(results) > 0 {
        delete results;
    }
    if length(history) > 0 {
        delete history;
    }
    err = "";
    cas_result = "";
    cas_help = false;
    hide;
    hide results;
    hide history;
    term_clear;
    broadcast_and_wait "term_render";
}

on "compute" {
    if is_blank(ui_input) or ui_input == "help" or ui_input == "帮助" {
        term_append_styled "> help", 1;
        term_help;
    } else {
        run_command ui_input;
        push_history "> " & ui_input;
        push_history "= " & cas_result;
        delete results;
        add cas_result to results;
        term_append_styled ("> " & ui_input), 1;
        if err != "" {
            term_error err;
        } elif starts_with(cas_result, "错误：") {
            term_error cas_result;
        } elif cas_help {
            term_append_multiline cas_result;
        } else {
            term_append_styled ("= " & cas_result), 2;
        }
        term_append_styled "", 0;
    }
    broadcast_and_wait "term_render";
}

onkey "c" {
    delete results;
    delete history;
    term_clear;
    broadcast_and_wait "term_render";
}

onkey "h" {
    term_append_styled "> help", 1;
    term_help;
    broadcast_and_wait "term_render";
}
