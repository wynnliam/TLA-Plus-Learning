\* Liam Wynn, 3/29/2020, TLA+ Learning

\* Functions in TLA != Functions/Procedures/Methods
\* in other languages - those are operators.

\* Instead, functions are like hashes/dictionaries,
\* but the value is determined programatically.

\* Syntax for defining functions:

\* Function == [s \in S |-> foo]
\* Function[s \in S] == foo

\* where foo is an equation or whatever.

---- MODULE functions ----

EXTENDS Naturals, FiniteSets, Sequences

Range(T) == {T[x] : x \in DOMAIN T}

Doubles == [n \in Nat |-> 2 * n]
Sum(S) == [x, y \in S |-> x + y]

\* Call the function like f[X] just like
\* sets and tuples, because sets and tuples are
\* functions! They are functions over the domain
\* 1..n

\* To access Sum, you would do Sum(S)[x, y] where
\* x, y are in S. Sum constructs a function whose
\* domain is the set of all tuples in S \X S.

\* Thus, DOMAIN gives you all the values your function
\* is defined on.

\* Sets of functions have the form:
\* SetOfFunctions == [A -> B]

\* Use |-> to have one function that maps a domain
\* to a specific range. Use -> when you want a set
\* of functions that maps a domain to a range.

MultCross(S, n) == [1..n -> S]
Seq_(S, n) == UNION {[1..m -> S] : m \in 1..n}

\* TERRIBLE SORTING ALGORITHM
\* Generate all possible permutations, and then choose the one that is sorted.

IsSorted(T) == \A x \in 1..Len(T):
                 \A y \in x..Len(T):
                   T[x] <= T[y]

\* Given n, give every permutation of the sequence 1..n                   
PermutationKey(n) == {key \in [1..n -> 1..n] : Range(key) = 1..n}

\* Given a tuple, give every possible permutation of that tuple.
PermutationsOf(T) == {[x \in 1..Len(T) |-> T[P[x]]] : P \in PermutationKey(Len(T))}

\* Now, choose the one permutation of a set of tuples that is sorted.
Sort(T) == CHOOSE sorted_tuple \in PermutationsOf(T) : IsSorted(sorted_tuple)
====