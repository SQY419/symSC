# Call the zm sprite for big add/sub/mul through shared stage variables.

proc zm_big_add a, b {
    zm_a = $a;
    zm_b = $b;
    zm_a = zm_a & "";
    zm_b = zm_b & "";
    broadcast_and_wait "zm_add";
    zm_big_add = zm_out;
}

proc zm_big_sub a, b {
    zm_a = $a;
    zm_b = $b;
    zm_a = zm_a & "";
    zm_b = zm_b & "";
    broadcast_and_wait "zm_sub";
    zm_big_sub = zm_out;
}

proc zm_big_mul a, b {
    zm_a = $a;
    zm_b = $b;
    zm_a = zm_a & "";
    zm_b = zm_b & "";
    broadcast_and_wait "zm_mul";
    zm_big_mul = zm_out;
}
