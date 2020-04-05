\* Liam Wynn, 4/5/2020, TLA+ Learning

\* How to check invariants between processes.

----------------------- MODULE concurrent_invariants -----------------------

EXTENDS TLC, Integers

(* --algorithm example

process foo \in 1..2
variable x \in 1..2
begin
  Bleh:
    skip
end process

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES pc, x

vars == << pc, x >>

ProcSet == (1..2)

Init == (* Process foo *)
        /\ x \in [1..2 -> 1..2]
        /\ pc = [self \in ProcSet |-> "Bleh"]

Bleh(self) == /\ pc[self] = "Bleh"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ x' = x

foo(self) == Bleh(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: foo(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* TO check that the sum of x is not 4, we do as follows:
CorrectSum == x[1] + x[2] /= 4

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Apr 05 15:33:47 PDT 2020 by alparslan
\* Created Sun Apr 05 15:28:06 PDT 2020 by alparslan
