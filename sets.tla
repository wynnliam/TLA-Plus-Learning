\* Liam Wynn, 3/26/2020, TLA+ Learning

---- MODULE sets ----

EXTENDS Naturals, FiniteSets

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

\* Defines the range of a tuple of values
Range(T) == {T[x] : x \in DOMAIN T}

\* CHOOSE
\* Choose an item in a set where some predicate holds. The syntax:

\* CHOOSE x \in S : P(x)

some_odd_val_from_1_to_8 == CHOOSE x \in 1..8 : x % 2 /= 0
\* Will return a single item x in 1..8 where x % 2 /= 0.
\* TLC doesn't branch. The number is arbitrary, but it's always
\* the same one. On my machine, it's 1.

\* Uncomment this line and evaluate in the expression runner
\* bad_choose == CHOOSE x \in 1..8 : x > 8
\* Will throw an error! Using CHOOSE implies there is at least
\* one item in the set where the predicate holds.

\* SET OPERATORS

is_in_set == 1 \in set_ten \* Outputs TRUE
is_not_in_set == 11 \notin set_ten \* Outputs TRUE
is_subset == {1, 2, 3} \subseteq set_ten \* Outputs TRUE

double_in_set(s1, s2) == { x * 2 : x \in s1} \subseteq s2

union_demo == {1, 2} \union {2, 3} \* Outputs {1, 2, 3}
intersect_demo == {1, 2} \intersect {2, 3} \* Outputs {2}
diff_demo == {1, 2} \ {2, 3} \*Outputs {1}
power_demo == SUBSET {1, 2}
\* Outputs all subsets of {1, 2}: {{}, {1}, {2}, {1, 2}}
flat_demo == UNION {{1}, {1, 2}, {5}}
\* Outputs the flattened union: {1, 2, 5}

\* Note that sets is a tuple of sets
found_op(item, sets) == item \in UNION Range(sets)

\* Some neat FiniteSets operations
is_finite_demo == IsFiniteSet(1..1000)
cardinality_demo == Cardinality(1..100)

get_all_sets_of_two(set) == {sub \in SUBSET set : Cardinality(sub) = 2}
====