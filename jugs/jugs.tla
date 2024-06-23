-------------------------------- MODULE jugs --------------------------------
(***************************************************************************)
(* From the Lamport TLA+ Course Lecture 4                                  *)
(* Jugs example                                                            *)
(* To see the procedure for filling the big jug w/ 4 gal, run with         *)
(* deadlock detection and the invariant big /= 4                           *)
(*                                                                         *)
(***************************************************************************)
EXTENDS Integers
VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big \in 0..5

Init == /\ small = 0
        /\ big = 0

FillSmall == /\ small' = 3
             /\ big' = big

FillBig == /\ small' = small
           /\ big' = 5

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ small' = small
            /\ big' = 0

SmallToBig == \/ /\ big + small <= 5
                 /\ big' = big + small
                 /\ small' = 0
              \/ /\ big + small > 5
                 /\ big' = 5
                 /\ small' = small - (5-big)

BigToSmall == \/ /\ big + small <= 3
                 /\ big' = 0
                 /\ small' = big + small
              \/ /\ big + small > 3
                 /\ small' = 3
                 /\ big' = big - (3-small)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall


=============================================================================
\* Modification History
\* Last modified Sun Jun 23 09:52:43 PDT 2024 by ben
\* Created Sun Jun 16 15:43:23 PDT 2024 by ben
