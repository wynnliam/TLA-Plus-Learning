\* Liam Wynn, 4/5/2020, TLA+ Learning

------------------------------- MODULE labels -------------------------------

\* Labels represent steps/single moments in time.


(* --algorithm some_algorithm

\* Rule: The first line in a process has to have a label.
\* That includes the first begin
process some_process
begin
  Foo:
    skip;
    
\* A label must come before a while statement
  Foo2:
    while FALSE do
      skip;
    end while;
    
\* A label must come after a call, return, or goto.
A:
  skip;
B:
  goto A;
Foo3: \* Must have, even if we don't reach it
  skip;
  
\* IF you've a flow-control statement (if/either/whatever),
\* and one possible branch has a label init, the whole control
\* structure must be followed by a label.
either
  X:
    skip;
or
  skip;
Foo4: \* Must have, even if we don't use because of X.
  skip;
  
\* No labels in with statements!
with p \in {1, 2} do
  Foo5: \* Illegal!
    skip;
end with;

\* You cannot assign to a variable more than once in a label:
Bar1:
  x := 1;
  q := 2; \* Valid
Bar2:
  x := 3;
  x := 4; \* Invalid!
end process;

end algorithm; *)

=============================================================================
\* Modification History
\* Last modified Sun Apr 05 15:22:52 PDT 2020 by alparslan
\* Created Sun Apr 05 15:13:25 PDT 2020 by alparslan
