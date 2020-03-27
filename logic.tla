\* Liam Wynn, 3/27/2020, TLA+ Learning

\* This explores propositional logic in TLA+. So we'll see
\* how to do logic quantifiers (existential and universal)
\* as well as implication (if A then B, and A if and only if B)

---- MODULE logic ----

EXTENDS Naturals

\* Existential Quantifier
\* Wherein we want to assert or see if some element exists where
\* something is true.

\* For this, we use the \E operator. The syntax is:
\* \E x \in S : P(x)
\* This reads "There is at least one x in the set S where P(x) is true.

set_ten == 1..10
HasEvenNumber(S) == \E x \in S : x % 2 = 0
\* HasEvenNumber(set_ten) evaluates to TRUE

\* ~\E is the opposite: there is no value in x where predicate holds.
greater_than_ten == ~\E x \in set_ten : x > 10
\* Evaluates to true - there is no item in set_ten greater than 10.

(*
    Assuming Sum(S) returns the sum of the elements of S,
    write an operator that, for a given set of integers S
    and integer N, returns if there are N elements in S
    that sum to 0.
*)

\* sums_to_zero(S, n) == \E set \in SUBSET S : Sum(set) = 0 /\ Cardinality(set)  = n
\* I assume the Sum function exists. Since it doesn't, this won't compile. Hence,
\* it's commented out.

\* Universal Quantifier
\* Wherein we want to assert to see if a predicate holds for
\* all elements in a set.

\* For this, we use \A. The syntax is:
\* \A x \in S : P(x)
\* This translates to: "For all x in S, P(x) is true".
\* The reverse of this is ~\A, so it reads "Not all x in S have P(x)"

OnlyEvenNumbers(S) == \A x \in S : x % 2 = 0
\* OnlyEvenNumbers(set_ten) is FALSE

\* WARNING: \A x \in {} : FALSE is still true
empty_set_test_1 == \A x \in {} : FALSE
empty_set_test_2 == \A x \in {} : TRUE
\* Both of these are true because we say it's vacuously true.
\* For all items in the empty set, some predicate either holds or
\* doesn't hold. Well no items exist in the empty set, so the
\* predicate vacuously holds.

commutative_test(S, op(_,_)) == \A x \in S, y \in S : op(x, y) = op(y, x)

\* Logical Implication
\* The syntax for this is "P => Q", which reads: "If P then Q". However,
\* this language seems to imply a relationship of time "If P is true, then Q
\* will follow at some point in the future". This is not correct. It is better
\* to think of it as "For Q to be true, P must also be true", either at the
\* the same time or prior to Q. An instructive example: "If I am eating tacos,
\* then I am eating". "I am eating" is a necessary condition to eating tacos,
\* but eating tacos is a sufficient condition to eating.

implication_t_t == TRUE => TRUE \* If I eat tacos, I eat lunch
implication_t_f == TRUE => FALSE \* I am not eating, but am eating tacos
implication_f_t == FALSE => TRUE \* I am not eating tacos, but I am eating
implication_f_f == FALSE => FALSE \* I am not eating tacos and I am not eating in general.

\* Don't need implication to do this, but I figured it's an example
\* of how it might be used.
max_of_set(S) == CHOOSE x \in S : \A y \in S : y /= x => y < x

\* Double Implication
\* Either both predicates are true or both predicates are false
\* P <=> Q = P => Q /\ Q => P

dimplication == <<TRUE <=> TRUE, TRUE <=> FALSE, FALSE <=> TRUE, FALSE <=> FALSE>>

\* As I showed above, CHOOSE can be combined with predicate logic
\* to be a powerful thing.

IsPrime(x) == x > 1 /\ ~\E d \in 2..(x - 1) : x % d = 0
LargestPrime(S) == CHOOSE x \in S:
                    /\ IsPrime(x)
                    /\ \A y \in S:
                        IsPrime(y) => y <= x

====