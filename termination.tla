\* Liam Wynn, 4/21/2020, TLA+ Learning

\* Tick the "Termination" in a model and see 
\* if this terminates (spoiler: it doesn't!)

\* The system can simply choose not to run
\* any step at all.

\* We add the "fairness" keyword to the process.
\* From Leslie Lamport himself:
\* "The keyword fair means that no process can stop
\* forever if it can always take a step"

---------------------------- MODULE termination ----------------------------
EXTENDS TLC, Integers

(* --algorithm counter
variable x = 0;

fair process counter = "counter"
begin Count:
  while x < 10 do
    x := x + 1;
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"counter"}

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> "Count"]

Count == /\ pc["counter"] = "Count"
         /\ IF x < 10
               THEN /\ x' = x + 1
                    /\ pc' = [pc EXCEPT !["counter"] = "Count"]
               ELSE /\ pc' = [pc EXCEPT !["counter"] = "Done"]
                    /\ x' = x

counter == Count

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == counter
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(counter)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Apr 21 15:43:15 PDT 2020 by alparslan
\* Created Tue Apr 21 15:32:59 PDT 2020 by alparslan
