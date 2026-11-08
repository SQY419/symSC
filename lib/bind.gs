list bind_name;
list bind_node;
var bind_count = 0;

proc bind_clear {
    delete bind_name;
    delete bind_node;
    bind_count = 0;
}

proc bind_add name, node {
    local nm = norm_ident($name);
    local i = 1;
    local found = 0;
    until i > bind_count {
        if bind_name[i] == nm {
            found = i;
            i = bind_count + 1;
        } else {
            i++;
        }
    }
    if found > 0 {
        bind_node[found] = $node;
    } else {
        bind_count++;
        add nm to bind_name;
        add $node to bind_node;
    }
}

func bind_lookup(name) {
    local i = 1;
    until i > bind_count {
        if bind_name[i] == $name {
            return bind_node[i];
        }
        i++;
    }
    return 0;
}
