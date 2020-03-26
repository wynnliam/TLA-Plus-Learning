\* Liam Wynn, 3/26/2020, TLA+ Learning

---- MODULE sets ----

EXTENDS Naturals

\* FILTERING
\* We can filter a set with the following syntax:

\* {x \in S : P(x)}
\* Where S is a set, and P(x) is a boolean predicate

odds_between_one_and_eight == {x \in 1..8 : x % 2 = 1}
\* Outputs {1, 3, 5, 7}

\* Set of tuples where you can filter according to a relationship.
set_ten == 1..10
ordered_pairs == {<<x, y>> \in set_ten \X set_ten : x >= y}

\* Nested Filtering:

set_hundred == 1..100
\* Give all odd values from 1 to 100 such that the value is greater than 50
nested_filtered_set == {x \in {y \in set_hundred : y % 2 /= 0} : x > 50}
\* Cleaner method for specifying nested filters using AND
nested_filtered_and_clean_set ==
{ x \in set_hundred : x % 2 /= 0 /\ x > 50 }

\* MAPPING

\* If you want to apply a function that transforms every item in a set,
\* we use mapping. It has the following syntax:

\* {P(x) : x \in S} where P is some function and S is a set.

squares_from_one_to_ten == {x * x : x \in set_ten}
\* Output is: {1, 4, 9, 16, 25, 36, 49, 64, 81, 100}

even_odd_status_one_to_ten == {x % 2 = 0 : x \in set_ten}
\* Outputs {FALSE, TRUE}. This is because all items in a set are unique.
\* In other words, you can't have the set {F, T, F, T, F, T, ....}
\* because there are multiple F's and T's in that set. So the correct
\* set is {F, T}

\* What does this give you?
mystery_map == { x + y : x \in 0..9, y \in { y * 10 : y \in 0..9 } }
\* It's all values between 0 and 99. We take each value from 0 to 9
\* and add those to each value in 0, 10, 20, ..., 90

====