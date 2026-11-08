costumes "blank.svg";
%include data/cases
list results;
list finished;

%include lib/consts
%include lib/util
%include lib/num
%include lib/big
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
%include lib/sum
%include lib/bigfrac
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

proc run_cases {
    if length(results) > 0 {
        delete results;
    }
    if length(finished) > 0 {
        delete finished;
    }
    local i = 1;
    until i > length(cases) {
        run_command cases[i];
        add cas_result to results;
        i++;
    }
    add 1 to finished;
}

onflag {
    run_cases;
}
