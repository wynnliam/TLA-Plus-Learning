\* Liam Wynn, 3/31/2020, TLA+ Learning

---- MODULE arbitrage ----

EXTENDS Integers
CONSTANTS Items, MaxPrice, Vendors, MaxActions

I == Items
V == Vendors
P == 1..MaxPrice

ValidMarkets == LET Markets ==[V \X I -> [buy : P, sell : P]]
                IN {m \in Markets :
                    \A item \in I, vendor \in V \X V:
                      m[<<vendor[1], item>>].buy <= m[<<vendor[2], item>>].sell
                   }

(* --algorithm market

variables market \in ValidMarkets,
          backpack = {}, \* Items we have
          actions = 0,
          profit = 0;
          
begin
  Act:
    while actions < MaxActions do
      either
        Buy:
          with v \in V, i \in Items \ backpack do
          profit := profit - market[<<v, i>>].sell;
          backpack := backpack \union {i};
          end with;
      or
        Sell:
          with v \in V, i \in backpack do
            profit := profit + market[<<v, i>>].buy;
            backpack := backpack \ {i};
          end with;
      end either;
      Loop:
        actions := actions + 1;
    end while;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES market, backpack, actions, profit, pc

vars == << market, backpack, actions, profit, pc >>

Init == (* Global variables *)
        /\ market \in ValidMarkets
        /\ backpack = {}
        /\ actions = 0
        /\ profit = 0
        /\ pc = "Act"

Act == /\ pc = "Act"
       /\ IF actions < MaxActions
             THEN /\ \/ /\ pc' = "Buy"
                     \/ /\ pc' = "Sell"
             ELSE /\ pc' = "Done"
       /\ UNCHANGED << market, backpack, actions, profit >>

Loop == /\ pc = "Loop"
        /\ actions' = actions + 1
        /\ pc' = "Act"
        /\ UNCHANGED << market, backpack, profit >>

Buy == /\ pc = "Buy"
       /\ \E v \in V:
            \E i \in Items \ backpack:
              /\ profit' = profit - market[<<v, i>>].sell
              /\ backpack' = (backpack \union {i})
       /\ pc' = "Loop"
       /\ UNCHANGED << market, actions >>

Sell == /\ pc = "Sell"
        /\ \E v \in V:
             \E i \in backpack:
               /\ profit' = profit + market[<<v, i>>].buy
               /\ backpack' = backpack \ {i}
        /\ pc' = "Loop"
        /\ UNCHANGED << market, actions >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Act \/ Loop \/ Buy \/ Sell
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

NoArbitrage == profit <= 0

====
