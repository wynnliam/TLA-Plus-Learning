\* Liam Wynn, 3/20/2020, TLA+ Learning

\* This demo shows how to specify simple operators in TLA+.

---- MODULE operators ----
EXTENDS TLC, Naturals

Five == 5 \* Defines an operator Five

\* Five + 5 \* Outputs 10

IsFive(x) == x = 5

\* IsFive(3) \* Outputs FALSE

SumWithFive(a, b) == a + b + 5

\* { Five, SumWithFive(Five, Five) } \* Outputs {5, 15}

Neq(a, b) == a /= b

\* HIGHER ORDER OPERATORS
Sum(a, b) == a + b
Do(op(_,_), a, b) == op(a, b)

\* Do(Sum, 1, 2) \* Outputs 3

\* RECURSIVE OPERATORS
RECURSIVE SetReduce(_, _, _)

SetReduce(Op(_, _), S, val) == IF S = {} THEN val
                               ELSE LET s == CHOOSE s \in S: TRUE
                               IN SetReduce(Op, S \ {s}, Op(s, val))
                               
\* SetReduce(Sum, 2..9, 0) \* outputs 44

IsCommutative(op(_,_), a, b) == op(a, b) = op(b, a)

====