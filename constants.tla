\* Liam Wynn, 3/29/2020, TLA+ Learning

\* In this demo, I introduce constants. Now
\* constants need to be coupled with a TLC model.
\* Constants are values that you can change without
\* modifying the code.

---- MODULE constants ----

EXTENDS TLC, Sequences, Integers

CONSTANTS TSIZE, TSPACES
CONSTANT SOLUTION

FullTower[n \in 1..TSIZE] == n
Board[n \in 1..TSPACES] == IF n = 1 THEN FullTower ELSE <<>>

                     \* correct spaces
IsSensical(state) == /\ Len(state) = TSPACES
                     \* Numbers do not exceed TSIZE
                     /\ \A tower \in DOMAIN state:
                        \A disc \in DOMAIN state[tower]:
                          state[tower][disc] \in 1..TSIZE
                     \* All numbers appear
                     /\ \A n \in 1..TSIZE:
                        \E tower \in DOMAIN state:
                           \E disc \in DOMAIN state[tower]:
                              n = state[tower][disc]
                              
ASSUME IsSensical(SOLUTION)

(* --algorithm hanoi
variables tower = Board

define
  D == DOMAIN tower
end define;

begin
while TRUE do
  assert tower[TSPACES] /= SOLUTION;
  with from \in {x \in D : tower[x]  /= <<>>},
       to \in {
                y \in D:
                  \/ tower[y] = <<>>
                  \/ Head(tower[from]) < Head(tower[y])
              }
  do
    tower[from] := Tail(tower[from]) ||
    tower[to] := <<Head(tower[from])>> \o tower[to]
  end with;
end while;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLE tower

(* define statement *)
D == DOMAIN tower


vars == << tower >>

Init == (* Global variables *)
        /\ tower = Board

Next == /\ Assert(tower[TSPACES] /= SOLUTION, 
                  "Failure of assertion at line 41, column 3.")
        /\ \E from \in {x \in D : tower[x]  /= <<>>}:
             \E to \in {
                         y \in D:
                           \/ tower[y] = <<>>
                           \/ Head(tower[from]) < Head(tower[y])
                       }:
               tower' = [tower EXCEPT ![from] = Tail(tower[from]),
                                      ![to] = <<Head(tower[from])>> \o tower[to]]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

====
