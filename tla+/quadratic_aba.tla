------------------------------ MODULE quadratic_aba ------------------------------

(*
To reduce computations and for simplicity, compare to the pseudocode:
1. The prevote stage is abstracted into "bset0", "bset1" and "bset01".
2. The "bsetX" stage is static, and the bsets of the honest nodes are (eventually) consistent.
3. Byzantine nodes are fixed and always in the first F nodes.
4. We observed that the nodes only receive n-f finalvote-random, followed by next-prevote-random.
*)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS N, F, guardR1, guardR2

VARIABLES sent,
          step,
          prevoteState,
          nextPrevote, (* prevotes of the second round *)
          decide

ASSUME NF ==
  /\ guardR1 \in Nat
  /\ guardR2 \in Nat
  /\ N \in Nat
  /\ F \in Nat
  /\ (N > F) /\ (F >= 0)
  /\ guardR1 > N \div 3
  /\ guardR2 > (2 * N) \div 3

Proc == 1 .. N
vars == << sent, step, prevoteState, decide, nextPrevote >>
vars_except_sent == << step, prevoteState, decide, nextPrevote >>
vars_except_sent_step == << prevoteState, decide, nextPrevote >>
vars_except_step_prevoteState == << sent, decide, nextPrevote >>
vars_except_nextPrevote == << prevoteState, sent, step, decide >>
vars_except_decide_nextPrevote== << prevoteState, sent, step >>
vars_except_decide == << prevoteState, sent, step, nextPrevote >>

rounds == 0 .. 1

UNDEFINED == "-"
PREPARED == "PREPARED"
BSET0 == "bset0"
BSET1 == "bset1"
BSET01 == "bset01"

PREVOTE == "prevote"
VOTE0 == "vote0"
VOTE1 == "vote1"
MAINVOTE0 == "mainvote0"
MAINVOTE1 == "mainvote1"
MAINVOTEx == "mainvotex"
FINALVOTE0 == "finalvote0"
FINALVOTE1 == "finalvote1"
FINALVOTEx == "finalvote*"

NEXTPREVOTE0 == "0"
NEXTPREVOTE1 == "1"
NEXTPREVOTEx == "random"

DECIDE0 == "0"
DECIDE1 == "1"
DECIDEx == "x"

Step == {
    VOTE0,
    VOTE1,
    MAINVOTE0,
    MAINVOTE1,
    MAINVOTEx,
    FINALVOTE0,
    FINALVOTE1,
    FINALVOTEx
}

Init ==  
  /\ sent = [i \in Proc |-> [j \in Proc |-> [s \in Step |-> 0]]]
  /\ step = [ i \in Proc |-> UNDEFINED ] (* undefined -> prevote -> vote -> mainvote -> finalvote *)
  /\ decide = [ i \in Proc |-> UNDEFINED] (* unknown / decide 0 / decide 1 / decide x *)
  /\ nextPrevote = [ i \in Proc |-> UNDEFINED](* unknown / prevote 0 / prevote 1 / prevote random *)
  /\ prevoteState = [ i \in Proc |-> UNDEFINED] (* unkonwn / bset0 / bset1 / bset01 *)

byzSet == {i \in Proc: i <= F}
honestSet == {i \in Proc: i > F}

SubsetProcGuard1 == {i \in SUBSET Proc: Cardinality(i) = guardR1}
SubsetProcGuard2 == {i \in SUBSET Proc: Cardinality(i) = guardR2}

ArrSum(s) == LET
  RECURSIVE Helper(_)
  Helper(s_) == IF s_ = <<>> THEN 0 ELSE
  Head(s_) + Helper(Tail(s_))
IN Helper(s)

VoteSumS(i, _step, _set) == 
    ArrSum([s \in Proc |-> IF s \in _set THEN sent[s][i][_step] ELSE 0])
VoteSum(i, _step) == 
    ArrSum([s \in Proc |-> sent[s][i][_step]])

Vote0(sender) ==
  /\ step[sender] = PREVOTE
  /\ \/ prevoteState[sender] = BSET0
     \/ prevoteState[sender] = BSET01
  /\ \E i \in SubsetProcGuard1: \A j \in i: \/ prevoteState[j] = BSET0
                                            \/ prevoteState[j] = BSET01
  /\ step' = [step EXCEPT ![sender] = VOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = VOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

Vote1(sender) ==
  /\ step[sender] = PREVOTE
  /\ \/ prevoteState[sender] = BSET1
     \/ prevoteState[sender] = BSET01
  /\ \E i \in SubsetProcGuard1: \A j \in i: \/ prevoteState[j] = BSET1
                                            \/ prevoteState[j] = BSET01
  /\ step' = [step EXCEPT ![sender] = VOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = VOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

MainVote0(sender) ==
  /\ VoteSum(sender, VOTE0) >= guardR2
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ \/ prevoteState[sender] = BSET0
     \/ prevoteState[sender] = BSET01
  /\ step' = [step EXCEPT ![sender] = MAINVOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

MainVote1(sender) ==
  /\ VoteSum(sender, VOTE1) >= guardR2
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ \/ prevoteState[sender] = BSET1
     \/ prevoteState[sender] = BSET01
  /\ step' = [step EXCEPT ![sender] = MAINVOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

MainVoteX(sender) ==
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ prevoteState[sender] = BSET01
  /\ step' = [step EXCEPT ![sender] = MAINVOTEx]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTEx THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

FinalVote0(sender) ==
  /\ VoteSum(sender, VOTE0) >= guardR1
  /\ VoteSum(sender, MAINVOTE0) >= guardR2
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
     \/ step[sender] = MAINVOTEx
  /\ step' = [step EXCEPT ![sender] = FINALVOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

FinalVote1(sender) ==
  /\ VoteSum(sender, VOTE1) >= guardR1
  /\ VoteSum(sender, MAINVOTE1) >= guardR2
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
     \/ step[sender] = MAINVOTEx
  /\ step' = [step EXCEPT ![sender] = FINALVOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

FinalVoteStar(sender) ==
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
     \/ step[sender] = MAINVOTEx
  /\ prevoteState[sender] = BSET01
  /\ \/ /\ \/ VoteSum(sender, VOTE1) >= guardR1
           \/ VoteSum(sender, VOTE0) >= guardR1
        /\ \E i \in SubsetProcGuard2: /\ \A j \in {k \in i: k > F}: \/ step[j] = MAINVOTE0
                                                                    \/ step[j] = MAINVOTE1
                                                                    \/ step[j] = MAINVOTEx
                                                                    \/ step[j] = FINALVOTE0
                                                                    \/ step[j] = FINALVOTE1
                                                                    \/ step[j] = FINALVOTEx
                                      /\ ~\A j \in i: sent[j][sender][MAINVOTE1] = 1
                                      /\ ~\A j \in i: sent[j][sender][MAINVOTE0] = 1
     \/ VoteSum(sender, MAINVOTEx) >= guardR2
  /\ step' = [step EXCEPT ![sender] = FINALVOTEx]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTEx THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED vars_except_sent_step

Prepare ==
  \/ /\ step[1] = UNDEFINED
     /\ \/ \E i \in byzSet:
           \/ \E k \in honestSet:
               /\ \A s \in {MAINVOTE0, MAINVOTE1, MAINVOTEx}: sent[i][k][s] = 0
               \** symmetry
               /\ \/ /\ \A j \in {t \in honestSet: t < k}: sent[i][j][MAINVOTE0] = 1
                     /\ \/ sent' = [sent EXCEPT ![i] = [m \in Proc |-> IF m = k THEN [_s \in Step |-> IF _s = MAINVOTE1 THEN 1 ELSE sent[i][m][_s]] ELSE sent[i][m]]]
                        \/ sent' = [sent EXCEPT ![i] = [m \in Proc |-> IF m = k THEN [_s \in Step |-> IF _s = MAINVOTE0 THEN 1 ELSE sent[i][m][_s]] ELSE sent[i][m]]]
                  \/ /\ \A j \in {t \in honestSet: t < k}: sent[i][j][MAINVOTE1] = 1
                     /\ \/ sent' = [sent EXCEPT ![i] = [m \in Proc |-> IF m = k THEN [_s \in Step |-> IF _s = MAINVOTE1 THEN 1 ELSE sent[i][m][_s]] ELSE sent[i][m]]]
                        \/ sent' = [sent EXCEPT ![i] = [m \in Proc |-> IF m = k THEN [_s \in Step |-> IF _s = MAINVOTEx THEN 1 ELSE sent[i][m][_s]] ELSE sent[i][m]]]
                  \/ sent' = [sent EXCEPT ![i] = [m \in Proc |-> IF m = k THEN [_s \in Step |-> IF _s = MAINVOTEx THEN 1 ELSE sent[i][m][_s]] ELSE sent[i][m]]]
     /\ UNCHANGED vars_except_sent
  \/ /\ step[1] = UNDEFINED
     /\ step' = [step EXCEPT ![1] = PREPARED]
     /\ \/ \E i \in byzSet:
           \/ \E k \in honestSet:
               /\ \A s \in {FINALVOTE0, FINALVOTE1, FINALVOTEx}: sent[i][k][s] = 0
               /\ \E s \in {FINALVOTE0, FINALVOTE1, FINALVOTEx}: sent' = [sent EXCEPT ![i] = [m \in Proc |-> IF m = k THEN [_s \in Step |-> IF s = _s THEN 1 ELSE sent[i][m][_s]] ELSE sent[i][m]]]
     /\ UNCHANGED vars_except_sent_step
  \/ /\ step[1] = PREPARED
     /\ step' = [j \in Proc |-> PREVOTE]
     /\ /\ \/ prevoteState' = [j \in Proc |-> IF j > F THEN BSET0 ELSE UNDEFINED]
           \/ prevoteState' = [j \in Proc |-> IF j > F THEN BSET1 ELSE UNDEFINED]
           \/ prevoteState' = [j \in Proc |-> IF j > F THEN BSET01 ELSE UNDEFINED]
        /\ UNCHANGED vars_except_step_prevoteState

Consume(sender) ==
  /\ decide[sender] = UNDEFINED
  /\ nextPrevote[sender] = UNDEFINED
  /\ \/ /\ step[1] # PREVOTE
        /\ Prepare
     \/ /\ step[1] = PREVOTE
        /\ \E s \in Step:
           /\ \/ /\ s = VOTE0
                 /\ Vote0(sender)
              \/ /\ s = VOTE1
                 /\ Vote1(sender)
              \/ /\ s = MAINVOTE0
                 /\ MainVote0(sender)
              \/ /\ s = MAINVOTE1
                 /\ MainVote1(sender)
              \/ /\ s = MAINVOTEx
                 /\ MainVoteX(sender)
              \/ /\ s = FINALVOTE0
                 /\ FinalVote0(sender)
              \/ /\ s = FINALVOTE1
                 /\ FinalVote1(sender)
              \/ /\ s = FINALVOTEx
                 /\ FinalVoteStar(sender)
  
Decide1(i) ==
  /\ VoteSum(i, MAINVOTE1) >= guardR1
  /\ VoteSum(i, FINALVOTE1) >= guardR2
  /\ decide' = [decide EXCEPT ![i] = DECIDE1]
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE1]
  /\ UNCHANGED vars_except_decide_nextPrevote

Decide0(i) ==
  /\ VoteSum(i, MAINVOTE0) >= guardR1
  /\ VoteSum(i, FINALVOTE0) >= guardR2
  /\ decide' = [decide EXCEPT ![i] = DECIDE0]
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE0]
  /\ UNCHANGED vars_except_decide_nextPrevote

NextPrevote0(i) ==
  /\ VoteSum(i, MAINVOTE0) >= guardR1
  /\ prevoteState[i] = BSET01
  /\ \E x \in SubsetProcGuard2:
                           /\ \A j \in x: \/ sent[j][i][FINALVOTE0] = 1 
                                          \/ sent[j][i][FINALVOTEx] = 1
                           /\ \E j \in x: sent[j][i][FINALVOTEx] = 1
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE0]
  /\ UNCHANGED vars_except_nextPrevote

NextPrevote1(i) ==
  /\ VoteSum(i, MAINVOTE1) >= guardR1
  /\ prevoteState[i] = BSET01
  /\ \E x \in SubsetProcGuard2: /\ \A j \in x: \/ sent[j][i][FINALVOTE1] = 1 
                                               \/ sent[j][i][FINALVOTEx] = 1
                                /\ \E j \in x: sent[j][i][FINALVOTEx] = 1
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE1]
  /\ UNCHANGED vars_except_nextPrevote

NextPrevoteRandom(i) ==
  /\ prevoteState[i] = BSET01
  /\ VoteSum(i, FINALVOTEx) >= guardR2
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTEx]
  /\ UNCHANGED vars_except_nextPrevote

Decide(i) ==
  /\ decide[i] = UNDEFINED
  /\ \/ /\ nextPrevote[i] = UNDEFINED
        /\ \/ step[i] = FINALVOTE0
           \/ step[i] = FINALVOTE1
           \/ step[i] = FINALVOTEx
        /\ \/ Decide1(i)
           \/ Decide0(i)
           \/ NextPrevote0(i)
           \/ NextPrevote1(i)
           \/ NextPrevoteRandom(i)
     \/ /\ nextPrevote[i] # UNDEFINED
        /\ \A j \in honestSet: nextPrevote[j] # UNDEFINED
        /\ \/ \A j \in honestSet: nextPrevote[j] = NEXTPREVOTE0
              (* eventually decide0 *)
              /\ decide' = [decide EXCEPT ![i] = DECIDE0]
           \/ \A j \in honestSet: nextPrevote[j] = NEXTPREVOTE1
              (* eventually decide1 *)
              /\ decide' = [decide EXCEPT ![i] = DECIDE1]
           \/ \E j \in honestSet: nextPrevote[j] = NEXTPREVOTEx
              (* eventually decidex *)
              /\ decide' = [decide EXCEPT ![i] = DECIDEx]
        /\ UNCHANGED vars_except_decide

Next == \E self \in honestSet :
           \/ Consume(self)
           \/ Decide(self)
           \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in honestSet : \/ Consume(self)
                                                \/ Decide(self))

(* Liveness and correctness check *)


(* It's obvious that once every honest node prevotes v, eventually, every honest node will mainvote v. *)

(* If all correct replicas propose iv[r] = v in round r, then any correct replica that enters round r + 1 sets iv[r+1] as v. *)
Lemma9 ==
  /\ []((\A i \in honestSet: step[i] = MAINVOTE0 /\ prevoteState[i] = BSET0) => <>(\A i \in honestSet : nextPrevote[i] = NEXTPREVOTE0 ))
  /\ []((\A i \in honestSet: step[i] = MAINVOTE1 /\ prevoteState[i] = BSET1) => <>(\A i \in honestSet : nextPrevote[i] = NEXTPREVOTE1 ))

(* If all correct replicas propose v in round r, then for any r′ > r , any correct replica that enters round r′ sets ivr′ as v.*)
(* Lemma10 *)

(* If a correct replica pi sends finalvote[r](v), at least one correct replica has proposed iv[r] = v̄ and broadcast prevote[r](v̄). *)
(* Lemma11 *)

(* If all correct replicas propose v, then any correct replica that terminates decides v. *)
Theorem12 ==
  /\ []((\A i \in honestSet: step[i] = MAINVOTE1) => <>(~\E i \in honestSet : decide[i] = DECIDE0 ))
  /\ []((\A i \in honestSet: step[i] = MAINVOTE0) => <>(~\E i \in honestSet : decide[i] = DECIDE1 ))

(* If a correct replica pi sends mainvote[r](v), any correct replica p_j only sends mainvote[r](v) or mainvote[r][∗] *)
Lemma13 ==
  /\ []((\E i \in honestSet: step[i] = MAINVOTE0) => <>(\A i \in honestSet : sent[i][1][MAINVOTE0] = 1 \/ sent[i][1][MAINVOTEx] = 1))
  /\ []((\E i \in honestSet: step[i] = MAINVOTE1) => <>(\A i \in honestSet : sent[i][1][MAINVOTE1] = 1 \/ sent[i][1][MAINVOTEx] = 1))

(* If a correct replica pi sends finalvote[r](v), any correct replica p_j only sends finalvote[r](v) or finalvote[r](x). *)
Lemma14 ==
  /\ []((\E i \in honestSet: step[i] = FINALVOTE0) => <>(\A i \in honestSet : nextPrevote[i] = NEXTPREVOTE0 \/ nextPrevote[i] = NEXTPREVOTEx))
  /\ []((\E i \in honestSet: step[i] = FINALVOTE1) => <>(\A i \in honestSet : nextPrevote[i] = NEXTPREVOTE1 \/ nextPrevote[i] = NEXTPREVOTEx))

(* If a correct replica pi decides v in round r , any correct replica that enters round r + 1 sets iv[r+1] as v. *)
Lemma15 ==
  /\ []((\E i \in honestSet: decide[i] = DECIDE0) => <>(\A i \in honestSet : nextPrevote[i] = NEXTPREVOTE0))
  /\ []((\E i \in honestSet: decide[i] = DECIDE1) => <>(\A i \in honestSet : nextPrevote[i] = NEXTPREVOTE1))

(* If a correct replica decides v, then any correct replica that terminates decides v *)
Theorem16 == 
  /\ []((\E i \in honestSet: decide[i] = DECIDE0) => <>(\A i \in honestSet : decide[i] = DECIDE0))
  /\ []((\E i \in honestSet: decide[i] = DECIDE1) => <>(\A i \in honestSet : decide[i] = DECIDE1))
  /\ []((\E i \in honestSet: decide[i] = DECIDEx) => <>(\A i \in honestSet : decide[i] = DECIDEx))

(* If a correct replica pi sends vote[r](v) for v ∈ {0,1}, any correct replica eventually accepts vote[r](v). *)
(* Lemma17 *)

(* If a correct replica pi broadcasts a mainvote[r](v) or a mainvote[r](∗) message given that v ∈ {0,1}, any correct replica accepts the mainvote[r]() message from pi. *)
(* Lemma18 *)

(* If a correct replica pi broadcasts a finalvote[r](v) or a finalvote[r](∗) message given that v ∈ {0, 1}, any correct replica accepts the finalvote[r]() message. *)
(* Lemma19 *)

(* Let v1 ∈ {0,1} and v2 ∈ {0,1}. If a correct replica pi receives only n − f finalvote[r](x) and finalvote[r](v1) messages, another correct replica p_j only receives n− f finalvote[r](v2) and finalvote[r](x) messages, v1 = v2. *)
(* Lemma20 *)

(* Every correct replica eventually decides some value. *)
Theorem21 == 
   []<>( \/ \A i \in honestSet : \/ decide[i] = DECIDE0
                                 \/ decide[i] = DECIDE1
                                 \/ decide[i] = DECIDEx
       )

(* No correct replica decides twice. *)
Theorem22 == 
    /\ [](\A i \in honestSet: decide[i] = DECIDE0 => <>(decide[i] = DECIDE0))
    /\ [](\A i \in honestSet: decide[i] = DECIDE1 => <>(decide[i] = DECIDE1))
    /\ [](\A i \in honestSet: decide[i] = DECIDEx => <>(decide[i] = DECIDEx))

=============================================================================
