# nearley grammar for formulas

line -> "|":* _ "L":? _ expr             {% ([indent, _1, isnew, _, form]) => ({ indent: indent.length + (isnew ? 1 : 0), isnew, form }) %}

expr -> un_expr {% _ => _[0] %} | bin_expr               {% _ => _[0] %}

un_expr -> "(" _ expr _ ")"               {% ([_, _1, e, _2, _3]) => e %}
         | quantifier _ [a-z] _ un_expr      {% ([op, _ , v, _2, e]) => ({op: synonym_base(op[0]), e, v: v[0]}) %}
         | unary_operator _ un_expr          {% ([op, _ , e]) => ({op: synonym_base(op[0]), e}) %}
         | nullary_operator               {% ([op]) => ({op: synonym_base(op[0])}) %}
         | [A-Z] [a-z]:+                  {% ([rel, vars]) => ({rel: rel[0], vs: vars.map(v => v[0]) })  %}
         | [A-SU-Z]                          {% rel => ({rel: rel[0], vs: [] })  %}

bin_expr -> expr _ binary_operator _ expr  {% ([e1, _1 , op, _2, e2]) => ({op: synonym_base(op[0]), e1, e2}) %}

binary_operator -> "/\\" | "&" | "&&" | "*" | "." |
                   "\\/" |  "|" | "||" | "+" | "," |
                   "->" | "=>" | ">" |
                   "<->" | "<=>" | "=" | "<>"
unary_operator -> "¬" | "~" | "-"
nullary_operator -> "#" | "_|_" | "T"
quantifier -> "A" | "@" | "E"
_ -> [ \n\t\r]:*
