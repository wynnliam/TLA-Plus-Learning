\* Liam Wynn, 3/21/2020, TLA+ Learning

---- MODULE tuples_and_structures ----

EXTENDS Naturals, Sequences

\* TUPLES

\* Note that tuples are 1 indexed

x == <<4, 5, 6>>
y == x[1] + x[2] + x[3] \* 15

\* DOMAIN gives you the set of all numbers
\* from 1 to the length of a tuple. So
\* z == {1, 2}
z == LET hello == <<"hello", "world">>
     IN DOMAIN hello
     
\* The following are available because
\* we extend Sequences

head_demo == Head(<<1, 2>>) \* Gives 1
tail_demo == Tail(<<1, 2, 3, 4>>) \* Gives <<2, 3, 4>>
combine == <<1>> \o <<2>> \* Gives <<1, 2>>
len_demo == Len(<<1, 2, 3>>) \* Gives 3

reverse_if_two(some_tuple) == IF Len(some_tuple) = 2
                             THEN Tail(some_tuple) \o <<Head(some_tuple)>>
                             ELSE some_tuple
                             
\* SETS OF TUPLES

\* Demonstrates the Cartesian Product
\* Gives the set of all 2-tuples (x, y) where x is in
\* (a..h) and y is in (1..8)
chess_board == {"a", "b", "c", "d", "e", "f", "g", "h" } \X (1..8)

\* Can use the \in operator to determine if something is in a set
a_2_is_in == <<"a", 2>> \in chess_board \* outputs TRUE

\* Can use the \notin operator to determine if something
\* is not in a set
b_10_not_in == <<"b", 10>> \notin chess_board \* outputs TRUE

\* You can use multiple \X operators, but paranthesis matter!
set_a == {"a1", "a2", "a3"}
set_b == {"b1", "b2", "b3"}
set_c == {"c1", "c2", "c3"}

cross_1 == set_a \X set_b \X set_c \* <<a1, b1, c1>> \in cross_1
cross_2 == set_a \X (set_b \X set_c) \*<<a1, <<b1, c1>>>> \in cross_2
cross_3 == (set_a \X set_b) \X set_c \*<<<<a1, b1>>, c1>> \in cross_3

\* STRUCTURES
\* Structures are hashes. They have keys and values. You specify them
\* with [key |-> value].

structure_demo == [a |-> 1, b |-> {2, 3}]

\* How to access a structure
item_1 == structure_demo.a \* has value 1
item_2 == structure_demo["b"] \* have value {2, 3}

\* Another way to construct structures
another_structure == [a : {1}, b : {2, 3}]

\* Gives the set of all keys in the structure
domain_of_structure == DOMAIN structure_demo

====