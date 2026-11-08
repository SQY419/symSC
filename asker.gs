costumes "assets/blank.svg";

onflag {
    hide;
    forever {
        ask "输入表达式";
        ui_input = answer();
        broadcast_and_wait "compute";
    }
}
