proc set_err msg {
    if err == "" {
        err = $msg;
    }
}

func trim(s) {
    local a = 1;
    local b = length($s);
    until a > b or $s[a] != " " {
        a++;
    }
    until b < a or $s[b] != " " {
        b--;
    }
    local buf = "";
    until a > b {
        buf &= $s[a];
        a++;
    }
    return buf;
}

# Test blankness by length instead of comparing with "".  This keeps numeric
# values such as the literal 0 out of the empty-string branch entirely.
func is_blank(s) {
    return length($s) == 0;
}

func is_space(c) {
    # Prefix a non-numeric string before comparing.  TurboWarp's compiled "="
    # can otherwise treat a numeric-looking character ("0") as equal to "\t"
    # (both coerce to 0), making the digit 0 be skipped as whitespace.
    return ("[" & $c) == "[ " or ("[" & $c) == "[\t" or ("[" & $c) == "[\n" or ("[" & $c) == "[\r";
}

func is_digit_char(c) {
    return $c >= "0" and $c <= "9";
}

func is_alpha_char(c) {
    return ($c >= "a" and $c <= "z") or ($c >= "A" and $c <= "Z");
}

func is_ident_char(c) {
    return is_alpha_char($c) or is_digit_char($c) or $c == "_";
}

func lower_char(c) {
    local idx = $c in up_letters;
    if idx > 0 {
        return lo_letters[idx];
    }
    return $c;
}

func norm_ident(s) {
    local i = 1;
    local buf = "";
    until i > length($s) {
        buf &= lower_char($s[i]);
        i++;
    }
    return buf;
}

func digit_value(c) {
    return ($c in digit_chars) - 1;
}
