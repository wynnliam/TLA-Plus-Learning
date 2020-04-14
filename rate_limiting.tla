\* Liam Wynn, 4/11/2020, TLA+ Learning

\* From: https://learntla.com/concurrency/example/

\* As part of your project, you need to call a third party API.
\* There are two types of calls you need to make:

\*    1. A GET for a collection of objects. Each call will return 
\*    some results and, potentially, a pagination token.
    
\*    2. A GET for a single object, followed by, if necessary,
\*     a PUT to update it.

\* There is a known rate limit of N calls per unit of time on
\* this API, and you do not want to exceed this. The first
\* type may make an arbitrary number of calls, but it’s
\* less critical and you are comfortable waiting between
\* calls. For the second, it will make either 1 or 2 calls;
\* however, being higher priority, you want to immediately
\* update the object if necessary. With these constraints
\* in mind, how do you guarantee you never exceed the rate limit?

\* Constraints: N calls you cannot exceed
\* First call type: 1 call.
\* Second 1 to 2 calls.


--------------------------- MODULE rate_limiting ---------------------------

EXTENDS Integers, TLC

(* --algorithm api
variables made_calls = 0, max_calls \in 5..10, reserved_calls = 0;

macro make_calls(n)
begin
  made_calls := made_calls + n;
  assert made_calls <= max_calls;
end macro;

macro reserve(n)
begin
  await made_calls + reserved_calls + n <= max_calls;
  reserved_calls := reserved_calls + n;
end macro;

process reset_limit = -1
begin
  Reset:
    while TRUE do
      made_calls := 0;
    end while
end process;

process get_collection = 0
begin
  GCGetCalls:
    reserve(1);
  Request:
    make_calls(1);
    reserved_calls := reserved_calls - 1;
    either goto Request
    or skip
    end either;
end process;

process get_put \in 1..3
begin
  GPGetCalls:
    reserve(2);
  Call:
    with c \in {1, 2} do
      make_calls(c)
    end with;
    reserved_calls := reserved_calls - 2;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES made_calls, max_calls, reserved_calls, pc

vars == << made_calls, max_calls, reserved_calls, pc >>

ProcSet == {-1} \cup {0} \cup (1..3)

Init == (* Global variables *)
        /\ made_calls = 0
        /\ max_calls \in 5..10
        /\ reserved_calls = 0
        /\ pc = [self \in ProcSet |-> CASE self = -1 -> "Reset"
                                        [] self = 0 -> "GCGetCalls"
                                        [] self \in 1..3 -> "GPGetCalls"]

Reset == /\ pc[-1] = "Reset"
         /\ made_calls' = 0
         /\ pc' = [pc EXCEPT ![-1] = "Reset"]
         /\ UNCHANGED << max_calls, reserved_calls >>

reset_limit == Reset

GCGetCalls == /\ pc[0] = "GCGetCalls"
              /\ made_calls + reserved_calls + 1 <= max_calls
              /\ reserved_calls' = reserved_calls + 1
              /\ pc' = [pc EXCEPT ![0] = "Request"]
              /\ UNCHANGED << made_calls, max_calls >>

Request == /\ pc[0] = "Request"
           /\ made_calls' = made_calls + 1
           /\ Assert(made_calls' <= max_calls, 
                     "Failure of assertion at line 38, column 3 of macro called at line 60, column 5.")
           /\ reserved_calls' = reserved_calls - 1
           /\ \/ /\ pc' = [pc EXCEPT ![0] = "Request"]
              \/ /\ TRUE
                 /\ pc' = [pc EXCEPT ![0] = "Done"]
           /\ UNCHANGED max_calls

get_collection == GCGetCalls \/ Request

GPGetCalls(self) == /\ pc[self] = "GPGetCalls"
                    /\ made_calls + reserved_calls + 2 <= max_calls
                    /\ reserved_calls' = reserved_calls + 2
                    /\ pc' = [pc EXCEPT ![self] = "Call"]
                    /\ UNCHANGED << made_calls, max_calls >>

Call(self) == /\ pc[self] = "Call"
              /\ \E c \in {1, 2}:
                   /\ made_calls' = made_calls + c
                   /\ Assert(made_calls' <= max_calls, 
                             "Failure of assertion at line 38, column 3 of macro called at line 73, column 7.")
              /\ reserved_calls' = reserved_calls - 2
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED max_calls

get_put(self) == GPGetCalls(self) \/ Call(self)

Next == reset_limit \/ get_collection
           \/ (\E self \in 1..3: get_put(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Apr 13 21:02:48 PDT 2020 by alparslan
\* Created Sat Apr 11 09:41:38 PDT 2020 by alparslan
