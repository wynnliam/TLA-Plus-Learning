\* Liam Wynn, 3/31/2020, TLA+ Learning

\* This is a classic problem in concurrency.
\* The parameters of the problem are as follows:

\*
\*    - There are N philosophers sitting around a circular table.
\*    - Between every two philosophers is a fork, with N forks in all.
\*    - A philosopher needs to pick up both adjacent forks to eat.
\*      As soon as they finish eating, they put down both forks.
\*    - A philosopher can only pick up one fork at a time.
\*    - If a philosopher picks up a fork and does not have a
\*      second, they will hold the first fork while waiting for the second.


------------------------ MODULE dining_philosophers ------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NumPhilosophers, NULL

ASSUME NumPhilosophers > 0

NP == NumPhilosophers

(* --algorithm dining_philosophers

variables forks = [fork \in 1..NP |-> NULL]

define

LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in { LeftFork(p), RightFork(p) }: forks[x] = p }

AvailableForks(p) ==
  { x \in { LeftFork(p), RightFork(p) }: forks[x] = NULL} 

end define;

process philosopher \in 1..NP
variables hungry = TRUE;
begin P:
  while hungry do
    with fork \in AvailableForks(self) do
      forks[fork] := self;
    end with;
    
    Eat:
      if Cardinality(HeldForks(self)) = 2 then
        hungry := FALSE;
        forks[LeftFork(self)] := NULL ||
        forks[RightFork(self)] := NULL;
      end if;
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES forks, pc

(* define statement *)
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in { LeftFork(p), RightFork(p) }: forks[x] = p }

AvailableForks(p) ==
  { x \in { LeftFork(p), RightFork(p) }: forks[x] = NULL}

VARIABLE hungry

vars == << forks, pc, hungry >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks = [fork \in 1..NP |-> NULL]
        (* Process philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF hungry[self]
                 THEN /\ \E fork \in AvailableForks(self):
                           forks' = [forks EXCEPT ![fork] = self]
                      /\ pc' = [pc EXCEPT ![self] = "Eat"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ forks' = forks
           /\ UNCHANGED hungry

Eat(self) == /\ pc[self] = "Eat"
             /\ IF Cardinality(HeldForks(self)) = 2
                   THEN /\ hungry' = [hungry EXCEPT ![self] = FALSE]
                        /\ forks' = [forks EXCEPT ![LeftFork(self)] = NULL,
                                                  ![RightFork(self)] = NULL]
                   ELSE /\ TRUE
                        /\ UNCHANGED << forks, hungry >>
             /\ pc' = [pc EXCEPT ![self] = "P"]

philosopher(self) == P(self) \/ Eat(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NP: philosopher(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 31 17:23:16 PDT 2020 by alparslan
\* Created Tue Mar 31 17:12:50 PDT 2020 by alparslan
