# CAS constants, arena, token and work lists.

enum T {
    End, Num, Ident, Op, LP, RP, Comma, LBracket, RBracket, LBrace, RBrace, Sci
}

enum K {
    Num, Var, Add, Mul, Pow,
    Sin, Cos, Tan, Exp, Ln, Log, Sqrt, Abs, Asin, Acos, Atan,
    Pi, E, Float, PowE, UN, Inf, Unknown, Sgn, Big, Vec, List, Approx, BigFloat, Length, UnitV, Transpose, Det
}

var MAX_NODES = 32768;
var MAX_SAFE = 9007199254740991;
var MAX_EXP = 64;
var MAX_TERMS = 128;
var MAX_SQRT = 1000000;
var MAX_INPUT = 512;
var MAX_OUTPUT = 8192;

var err = 0;
var cas_result = 0;
var cas_help = false;

var node_count = 1;
var lex_ok = true;
var token_count = 0;
var parse_ok = true;
var parse_root = 0;
var simp_exact = false;
var frac_combined = false;

list nd_kind;
list nd_a;
list nd_b;
list nd_num;
list nd_den;
list nd_txt;
list nd_sig;
list nd_deg;
list ct_elems;
list def_name;
list def_text;

list tk_type;
list tk_text;
list tk_pos;
list tk_num;
list tk_den;

list up_letters = ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z"];
list lo_letters = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"];
list digit_chars = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];
