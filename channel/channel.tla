------------------------------ MODULE channel ------------------------------
\* From Ch 3 of Specifying Systems (Lamport)
EXTENDS Naturals
CONSTANTS Data
VARIABLES chan

TypeInvariant == chan \in [val:Data, rdy:{0,1}, ack:{0,1}]

Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy \*w why?  Why not any value in {0..1} ?

Send(d) == /\ chan.ack = chan.rdy
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1-@]

Receive == /\ chan.rdy /= chan.ack
           /\ chan' = [chan EXCEPT !.ack = 1-@]

Next == \/ \exists d \in Data : Send(d)
        \/ Receive

Spec == Init /\ [][Next]_chan

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sun Jun 23 16:31:27 PDT 2024 by ben
\* Created Sun Jun 23 16:05:00 PDT 2024 by ben
