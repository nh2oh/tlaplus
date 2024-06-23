----------------------------- MODULE hour_clock -----------------------------
\* From Ch 2 of Specifying Systems (Lamport)
EXTENDS Naturals
VARIABLES hr

HCinit == hr \in {1..12}

HCnext == \/ (hr < 12) /\ (hr' = hr+1)
          \/ (hr = 12) /\ (hr' = 1)

HC == HCinit /\ [][HCnext]_hr


=============================================================================
\* Modification History
\* Last modified Sun Jun 23 10:14:25 PDT 2024 by ben
\* Created Sun Jun 23 10:08:32 PDT 2024 by ben
