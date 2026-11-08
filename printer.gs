costumes "assets/glyphs/ascii_032.svg" as "space", "assets/glyphs/ascii_033.svg" as "!", "assets/glyphs/ascii_034.svg" as "\"", "assets/glyphs/ascii_035.svg" as "#", "assets/glyphs/ascii_036.svg" as "$", "assets/glyphs/ascii_037.svg" as "%", "assets/glyphs/ascii_038.svg" as "&", "assets/glyphs/ascii_039.svg" as "'", "assets/glyphs/ascii_040.svg" as "(", "assets/glyphs/ascii_041.svg" as ")", "assets/glyphs/ascii_042.svg" as "*", "assets/glyphs/ascii_043.svg" as "+", "assets/glyphs/ascii_044.svg" as ",", "assets/glyphs/ascii_045.svg" as "-", "assets/glyphs/ascii_046.svg" as ".", "assets/glyphs/ascii_047.svg" as "/", "assets/glyphs/ascii_048.svg" as "0", "assets/glyphs/ascii_049.svg" as "1", "assets/glyphs/ascii_050.svg" as "2", "assets/glyphs/ascii_051.svg" as "3", "assets/glyphs/ascii_052.svg" as "4", "assets/glyphs/ascii_053.svg" as "5", "assets/glyphs/ascii_054.svg" as "6", "assets/glyphs/ascii_055.svg" as "7", "assets/glyphs/ascii_056.svg" as "8", "assets/glyphs/ascii_057.svg" as "9", "assets/glyphs/ascii_058.svg" as ":", "assets/glyphs/ascii_059.svg" as ";", "assets/glyphs/ascii_060.svg" as "<", "assets/glyphs/ascii_061.svg" as "=", "assets/glyphs/ascii_062.svg" as ">", "assets/glyphs/ascii_063.svg" as "?", "assets/glyphs/ascii_064.svg" as "@", "assets/glyphs/ascii_065.svg" as "A", "assets/glyphs/ascii_066.svg" as "B", "assets/glyphs/ascii_067.svg" as "C", "assets/glyphs/ascii_068.svg" as "D", "assets/glyphs/ascii_069.svg" as "E", "assets/glyphs/ascii_070.svg" as "F", "assets/glyphs/ascii_071.svg" as "G", "assets/glyphs/ascii_072.svg" as "H", "assets/glyphs/ascii_073.svg" as "I", "assets/glyphs/ascii_074.svg" as "J", "assets/glyphs/ascii_075.svg" as "K", "assets/glyphs/ascii_076.svg" as "L", "assets/glyphs/ascii_077.svg" as "M", "assets/glyphs/ascii_078.svg" as "N", "assets/glyphs/ascii_079.svg" as "O", "assets/glyphs/ascii_080.svg" as "P", "assets/glyphs/ascii_081.svg" as "Q", "assets/glyphs/ascii_082.svg" as "R", "assets/glyphs/ascii_083.svg" as "S", "assets/glyphs/ascii_084.svg" as "T", "assets/glyphs/ascii_085.svg" as "U", "assets/glyphs/ascii_086.svg" as "V", "assets/glyphs/ascii_087.svg" as "W", "assets/glyphs/ascii_088.svg" as "X", "assets/glyphs/ascii_089.svg" as "Y", "assets/glyphs/ascii_090.svg" as "Z", "assets/glyphs/ascii_091.svg" as "[", "assets/glyphs/ascii_092.svg" as "\\", "assets/glyphs/ascii_093.svg" as "]", "assets/glyphs/ascii_094.svg" as "^", "assets/glyphs/ascii_095.svg" as "_", "assets/glyphs/ascii_096.svg" as "`", "assets/glyphs/ascii_097.svg" as "a", "assets/glyphs/ascii_098.svg" as "b", "assets/glyphs/ascii_099.svg" as "c", "assets/glyphs/ascii_100.svg" as "d", "assets/glyphs/ascii_101.svg" as "e", "assets/glyphs/ascii_102.svg" as "f", "assets/glyphs/ascii_103.svg" as "g", "assets/glyphs/ascii_104.svg" as "h", "assets/glyphs/ascii_105.svg" as "i", "assets/glyphs/ascii_106.svg" as "j", "assets/glyphs/ascii_107.svg" as "k", "assets/glyphs/ascii_108.svg" as "l", "assets/glyphs/ascii_109.svg" as "m", "assets/glyphs/ascii_110.svg" as "n", "assets/glyphs/ascii_111.svg" as "o", "assets/glyphs/ascii_112.svg" as "p", "assets/glyphs/ascii_113.svg" as "q", "assets/glyphs/ascii_114.svg" as "r", "assets/glyphs/ascii_115.svg" as "s", "assets/glyphs/ascii_116.svg" as "t", "assets/glyphs/ascii_117.svg" as "u", "assets/glyphs/ascii_118.svg" as "v", "assets/glyphs/ascii_119.svg" as "w", "assets/glyphs/ascii_120.svg" as "x", "assets/glyphs/ascii_121.svg" as "y", "assets/glyphs/ascii_122.svg" as "z", "assets/glyphs/ascii_123.svg" as "{", "assets/glyphs/ascii_124.svg" as "|", "assets/glyphs/ascii_125.svg" as "}", "assets/glyphs/ascii_126.svg" as "~";


# Terminal print engine.  The sprite is hidden; stamp still draws hidden sprites.
# Font metrics baked into the costumes:
#   advance = 19.2px at size 100, line height = 47.36px
#   print size 45 -> advance 9.0, line step 24 in render_term
var print_x = 0;
var print_idx = 0;
var term_size = 45;
var term_x = 228;
var term_y = 165;

# Same custom block as print (1).sb3, with the space costume corrected to the
# actual "space" costume instead of "~".
nowarp proc print_text text, size, x, y {
    switch_costume "space";
    set_size $size;
    print_x = $x + $size / 10;
    print_idx = 0;
    repeat length($text) {
        print_idx++;
        if $text[print_idx] == " " {
            switch_costume "space";
        } else {
            switch_costume $text[print_idx];
        }
        goto print_x, $y - $size * 0.16;
        stamp;
        print_x += $size / 5;
    }
}

proc set_style style {
    if $style == 1 {
        # input: black
        set_color_effect 0;
        set_brightness_effect 0 - 100;
        set_ghost_effect 0;
    } elif $style == 2 {
        # result: blue (red base, hue 240 deg = 133.33 on Scratch's 0..200 scale)
        set_color_effect 133.33;
        set_brightness_effect 0;
        set_ghost_effect 0;
    } elif $style == 3 {
        # error: red
        set_color_effect 0;
        set_brightness_effect 0;
        set_ghost_effect 0;
    } else {
        # hints/help/header: gray (black + ghost 50)
        set_color_effect 0;
        set_brightness_effect 0 - 100;
        set_ghost_effect 50;
    }
}

proc render_term {
    erase_all;
    local first = floor(term_scroll / term_step) + 1;
    local i = first;
    local y = term_y + term_scroll - (first - 1) * term_step;
    until i > length(term_lines) or y < -240 {
        if y <= 240 {
            set_style term_styles[i];
            print_text term_lines[i], term_size, 0 - term_x, y;
        }
        y -= term_step;
        i++;
    }
}

proc scroll_drag dy {
    term_scroll += $dy;
    if term_scroll < 0 {
        term_scroll = 0;
    }
    local max_scroll = length(term_lines) * term_step - term_view + term_overscan;
    if max_scroll < 0 {
        max_scroll = 0;
    }
    if term_scroll > max_scroll {
        term_scroll = max_scroll;
    }
    render_term;
}

proc drag_to mouse_y_now {
    local dy = $mouse_y_now - drag_last_y;
    if dy != 0 {
        drag_last_y = $mouse_y_now;
        scroll_drag dy;
    }
}

var drag_active = 0;
var drag_last_y = 0;

onflag {
    hide;
    forever {
        if mouse_down() {
            if drag_active == 0 {
                drag_active = 1;
                drag_last_y = mouse_y();
            } else {
                drag_to mouse_y();
            }
        } else {
            drag_active = 0;
        }
    }
}

on "term_render" {
    render_term;
}
