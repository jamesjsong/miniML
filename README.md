An Interpreter for OCaml

This program uses three models to evaluate expressions: substitution semantics, dynamically scoped environment, and lexically scoped environment.

Substitution semantics is used by substituting like for like. For instance, in an expression like "let x = 4 in x + x", x is replaced by 4, x + x by 4 + 4, and 4 + 4 is then evaluated to 8.

A lexically scoped environment model behaves the same way as the substitution semantics, but stores the values of variables in an environment. So in the above expression, "x + x" would be evaluated in an environment where "x -> 4".

A dynamically scoped environment behaves like the lexically scoped environment, except that the values of variables in the environment are updated if before the evaluation, a variable is defined with another value.

For instance, take the expression "let x = 2 in let f y = x * y in let x = 1 in f 21". In the lexically environment, "21" is applied to the function "f" in an environment where "x -> 2", which is the value of the variable when the function "f" was *defined*. In the dynamic environment, "x -> 1" when the function is applied, since that is the value of "x" when the function is *applied*. So in the lexically scoped environment, the expression evaluates to 42, whereas in the dynamically scoped one, we get 21.
