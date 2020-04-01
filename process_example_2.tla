\* Liam Wynn, 3/31/2020, TLA+ Learning

------------------------- MODULE process_example_2 -------------------------

EXTENDS Naturals, TLC


(* --algorithm cycle_process

\* Recall that processes run CONCURRENTLY.
\* so in this case, each copy of cycle runs
\* concurrently. So it does find a way to fail
\* the assertion.

\* This example makes TLA+ very cool: it finds
\* errors in systems that are very hard for
\* the human mind to keep track of.
variables x = 0;
process cycle \in 1..3
begin
  A:
    x := x + 1;
  B:
    x := 0;
  C:
    assert x /= 2;
end process

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ x' = x + 1
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ x' = 0
           /\ pc' = [pc EXCEPT ![self] = "C"]

C(self) == /\ pc[self] = "C"
           /\ Assert(x /= 2, "Failure of assertion at line 18, column 5.")
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

cycle(self) == A(self) \/ B(self) \/ C(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: cycle(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 31 16:49:09 PDT 2020 by alparslan
\* Created Tue Mar 31 16:38:48 PDT 2020 by alparslan
