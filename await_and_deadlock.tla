\* Liam Wynn, 3/31/2020, TLA+ Learning

\* Demonstrates the "await" command that will
\* block a step until a condition is met. This
\* demo also shows a situation where deadlock
\* can occur!

------------------------- MODULE await_and_deadlock -------------------------

EXTENDS Naturals, TLC

(* --algorithm await_and_deadlock

variable x = 0;

process one = 1
begin
  A:
    x := x - 1;
  B:
    x := x * 3;
end process

process two = 2
begin
  C:
    \* Gives us deadlock! If you execute A and then B before C,
    \* then x is -3, and -3 < 1. So this system will freeze because
    \* it's waiting on this condition to be true.
    await x > 1;
    x := x + 1;
  D:
    assert x /= 0;
end process

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self = 2 -> "C"]

A == /\ pc[1] = "A"
     /\ x' = x - 1
     /\ pc' = [pc EXCEPT ![1] = "B"]

B == /\ pc[1] = "B"
     /\ x' = x * 3
     /\ pc' = [pc EXCEPT ![1] = "Done"]

one == A \/ B

C == /\ pc[2] = "C"
     /\ x > 1
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![2] = "D"]

D == /\ pc[2] = "D"
     /\ Assert(x /= 0, "Failure of assertion at line 30, column 5.")
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ x' = x

two == C \/ D

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 31 16:59:15 PDT 2020 by alparslan
\* Created Tue Mar 31 16:50:04 PDT 2020 by alparslan
