\* Liam Wynn, 4/1/2020, TLA+ Learning

\* Reimplements the Dining Philosophers problem, but with the use
\* of macros and procedures.

---------------- MODULE dining_philosophers_with_procedures ----------------

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
    { x \in {LeftFork(p), RightFork(p)} : forks[x] = p }
    
  AvailableForks(p) ==
    { x \in {LeftFork(p), RightFork(p)} : forks[x] = NULL }
end define

macro set_fork(fork, val) begin
  forks[fork] := val;
end macro;

macro take_a_fork() begin
  with fork \in AvailableForks(self) do
    set_fork(fork, self);
  end with;
end macro;

macro drop_a_fork() begin
  await AvailableForks(self) = {};
  with fork \in HeldForks(self) do
    set_fork(fork, NULL);
  end with;
end macro;

procedure attempt_eat() begin
Eat:
  if Cardinality(HeldForks(self)) = 2 then
    hungry := FALSE;
    forks[LeftFork(self)] := NULL ||
    forks[RightFork(self)] := NULL;
  end if;
  return;
end procedure;

process philosopher \in 1..NP
variables hungry = TRUE;
begin P:
  while hungry do
    either
      take_a_fork();
    or
      drop_a_fork();
    end either;
    call attempt_eat();
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES forks, pc, stack

(* define statement *)
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in {LeftFork(p), RightFork(p)} : forks[x] = p }

AvailableForks(p) ==
  { x \in {LeftFork(p), RightFork(p)} : forks[x] = NULL }

VARIABLE hungry

vars == << forks, pc, stack, hungry >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks = [fork \in 1..NP |-> NULL]
        (* Process philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "P"]

Eat(self) == /\ pc[self] = "Eat"
             /\ IF Cardinality(HeldForks(self)) = 2
                   THEN /\ hungry' = [hungry EXCEPT ![self] = FALSE]
                        /\ forks' = [forks EXCEPT ![LeftFork(self)] = NULL,
                                                  ![RightFork(self)] = NULL]
                   ELSE /\ TRUE
                        /\ UNCHANGED << forks, hungry >>
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

attempt_eat(self) == Eat(self)

P(self) == /\ pc[self] = "P"
           /\ IF hungry[self]
                 THEN /\ \/ /\ \E fork \in AvailableForks(self):
                                 forks' = [forks EXCEPT ![fork] = self]
                         \/ /\ AvailableForks(self) = {}
                            /\ \E fork \in HeldForks(self):
                                 forks' = [forks EXCEPT ![fork] = NULL]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "attempt_eat",
                                                               pc        |->  "P" ] >>
                                                           \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "Eat"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << forks, stack >>
           /\ UNCHANGED hungry

philosopher(self) == P(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: attempt_eat(self))
           \/ (\E self \in 1..NP: philosopher(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Apr 01 19:52:21 PDT 2020 by alparslan
\* Created Wed Apr 01 19:28:41 PDT 2020 by alparslan
