\* Liam Wynn, 3/31/2020, TLA+ Learning

\* Demonstrates a simple concurrent system
\* This will fail the model checker because
\* There is a sequence of steps that exists
\* where the assertion can fail.

------------------------- MODULE process_example_1 -------------------------

EXTENDS Naturals, TLC

(* --algorithm example_process

\* x is a global variable shared by all processes.
variables x = 0;

\* In a particular process, the labels denote
\* particular steps. So in this case, A runs first
\* and then B.
process one = 1
begin
  A:
    x := x - 1;
  B:
    x := x * 3;
end process

\* Here is a second process. This runs CONCURRENTLY
\* with process 1.
process two = 2
begin
  C:
    x := x + 1;
  D:
    assert x /= 0;
end process

end algorithm *)
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
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![2] = "D"]

D == /\ pc[2] = "D"
     /\ Assert(x /= 0, "Failure of assertion at line 35, column 5.")
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
\* Last modified Tue Mar 31 16:38:19 PDT 2020 by alparslan
\* Created Tue Mar 31 16:31:20 PDT 2020 by alparslan
