--------------------------- MODULE foxes_rabbits ---------------------------
EXTENDS Integers

VARIABLES
    animals, \* = {"foxes", "rabbits"};
    left, \* = [a \in animals |-> Nat\]
    right,
    boat



Init == 
    /\ animals = {"foxes", "rabbits"}
    /\ left = [a \in animals |-> 3]
    /\ right = [a \in animals |-> 0]
    /\ boat = [a \in animals |-> 0]
    /\ \A a \in animals: left[a] = 3
    /\ \A a \in animals: right[a] = 0
    /\ \A a \in animals: boat[a] = 0

BoatIsEmpty == \A a \in animals: boat[a] = 0
   
LoadBoatFromLeft(f, r) ==
    /\ BoatIsEmpty
    /\ f <= r \* boat state will be valid after loading
    /\ left["foxes"] >= f /\ left["rabbits"] >= r
    /\ (left["foxes"] - f) <= (left["rabbits"] - r) \* left state will be valid after loading
    /\ boat'["foxes"] = f
    /\ boat'["rabbits"] = r
    /\ left'["foxes"] = left["foxes"] - f
    /\ left'["rabbits"] = left["rabbits"] - r

LoadBoatFromRight(f, r) ==
    /\ BoatIsEmpty
    /\ f <= r \* boat state will be valid after loading
    /\ right["foxes"] >= f /\ right["rabbits"] >= r
    /\ (right["foxes"] - f) <= (right["rabbits"] - r) \* right state will be valid after loading
    /\ boat'["foxes"] = f
    /\ boat'["rabbits"] = r
    /\ right'["foxes"] = right["foxes"] - f
    /\ right'["rabbits"] = right["rabbits"] - r

UnloadBoatToLeft ==
    /\ ~BoatIsEmpty
    /\ (left["foxes"] + boat["foxes"]) <= (left["rabbits"] + boat["rabbits"])
    /\ left'["foxes"] = left["foxes"] + boat["foxes"]
    /\ left'["rabbits"] = left["rabbits"] + boat["rabbits"]
    /\ boat'["foxes"] = 0
    /\ boat'["rabbits"] = 0

UnloadBoatToRight ==
    /\ ~BoatIsEmpty
    /\ (right["foxes"] + boat["foxes"]) <= (right["rabbits"] + boat["rabbits"])
    /\ right'["foxes"] = right["foxes"] + boat["foxes"]
    /\ right'["rabbits"] = right["rabbits"] + boat["rabbits"]
    /\ boat'["foxes"] = 0
    /\ boat'["rabbits"] = 0

Next ==
    \/ \E f,r \in 0..3 : LoadBoatFromLeft(f,r)
    \/ \E f,r \in 0..3 : LoadBoatFromRight(f,r)
    \/ UnloadBoatToLeft
    \/ UnloadBoatToRight

TerminationCondition ==
    /\ \A a \in animals: left[a] = 0
    /\ \A a \in animals: right[a] = 3
    /\ \A a \in animals: boat[a] = 0


=============================================================================
\* Modification History
\* Last modified Sun Jun 30 15:55:41 PDT 2024 by ben
\* Created Sun Jun 30 10:57:27 PDT 2024 by ben
