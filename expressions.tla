\* Liam Wynn, 3/20/2020, TLA+ Learning

\* This demo shows basic expressions in TLA+.

\* An expression is anything that follows ==, =, := or \in.

---- MODULE expressions ----
EXTENDS TLC, Naturals

\* Note that these must be ran in the constant expression evaluator.

\* LOGICAL JUNCTIONS

\* Rules of thumb:

\* - If two logical operators are on the same level of indentation,
\* they are part of the same level of expression.

\* - If a logical operator is on a higher level of indentation,
\* it’s part of the previous operator statement.

\* - Use only one type of operator per level of indentation

\* /\TRUE
\*   \/ TRUE
\* /\ FALSE \* (T v T) ^ F

\* /\ TRUE
\*   \/ TRUE
\*   \/ FALSE

\* \/ TRUE
\* \/ TRUE
\*   /\ FALSE \* T v (T ^ F)

\* LET-IN

\* Whitespace does not matter in LET-IN expressions.

\* LET IsEven(x) == x % 2 = 0
\* IN IsEven(5)

A == LET IsEven(x) == x % 2 = 0
         Five == 5
     IN IsEven(Five)
     
B == LET IsEven(x) == LET Two == 2
                          Zero == 0
                      IN x % Two = Zero
         Five == 5
     IN IsEven(Five)
     
\* IF-THEN-ELSE

IsEven(x) == IF x % 2 = 0
             THEN TRUE
             ELSE FALSE
             
\* CASE

DummyCase(x) == CASE x = 1 -> TRUE
                  [] x = 2 -> TRUE
                  [] x = 3 -> 7
                  [] OTHER -> FALSE
                  
\* Note that the following might or might not be true!
\* CASE TRUE -> FALSE
\*   [] TRUE -> TRUE
====