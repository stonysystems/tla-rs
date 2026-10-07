--------------------------- MODULE ZabModel ---------------------------

EXTENDS Integers, FiniteSets, Sequences, Naturals

CONSTANT Server

CONSTANT MAXEPOCH

CONSTANT NullPoint

ASSUME ServerFinite == IsFiniteSet(Server)
ASSUME MaxEpochNat == MAXEPOCH \in Nat \ {0}
ASSUME NullPointNotServer == NullPoint \notin Server

LOOKING   == "LOOKING"
FOLLOWING == "FOLLOWING"
LEADING   == "LEADING"

ELECTION        == "ELECTION"
DISCOVERY       == "DISCOVERY"
SYNCHRONIZATION == "SYNCHRONIZATION"
BROADCAST       == "BROADCAST"

CEPOCH    == "CEPOCH"
NEWEPOCH  == "NEWEPOCH"
ACKEPOCH  == "ACKEPOCH"
NEWLEADER == "NEWLEADER"
ACKLD     == "ACKLD"
COMMITLD  == "COMMITLD"
PROPOSE   == "PROPOSE"
ACK       == "ACK"
COMMIT    == "COMMIT"
Quorums == {Q \in SUBSET Server: Cardinality(Q)*2 > Cardinality(Server)}

BootstrapZxid == <<0, 1>>
BootstrapTxn == [ zxid   |-> BootstrapZxid,
                  value  |-> 0,
                  ackSid |-> Server,
                  epoch  |-> 0 ]
BootstrapProposalMsgs ==
    { [ source |-> s,
        epoch  |-> 0,
        zxid   |-> BootstrapZxid,
        data   |-> 0 ] : s \in Server }

VARIABLES state,          
          zabState,       
                          
          acceptedEpoch,  
                          
          currentEpoch,   
                          
          history,        
                          
          lastCommitted   

VARIABLES learners,       
          cepochRecv,     

          ackeRecv,       

          ackldRecv,      
                          
          sendCounter     

VARIABLES connectInfo 

VARIABLE  leaderOracle  

VARIABLE  msgs       

VARIABLES epochLeader,       
          proposalMsgsLog   

serverVars == <<state, zabState, acceptedEpoch, currentEpoch, 
                history, lastCommitted>>

leaderVars == <<learners, cepochRecv, ackeRecv, ackldRecv, 
                sendCounter>>

followerVars == connectInfo

electionVars == leaderOracle

msgVars == msgs

verifyVars == <<proposalMsgsLog, epochLeader>>

vars == <<serverVars, leaderVars, followerVars, electionVars,
          msgVars, verifyVars>>

Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m

IsLeader(s)   == state[s] = LEADING
IsFollower(s) == state[s] = FOLLOWING
IsLooking(s)  == state[s] = LOOKING

IsQuorum(s) == s \in Quorums

IsMyLearner(i, j) == j \in learners[i]
IsMyLeader(i, j)  == connectInfo[i] = j
HasNoLeader(i)    == connectInfo[i] = NullPoint
HasLeader(i)      == connectInfo[i] /= NullPoint

ZxidCompare(zxid1, zxid2) == \/ zxid1[1] > zxid2[1]
                             \/ /\ zxid1[1] = zxid2[1]
                                /\ zxid1[2] > zxid2[2]

ZxidEqual(zxid1, zxid2) == zxid1[1] = zxid2[1] /\ zxid1[2] = zxid2[2]

TxnZxidEqual(txn, z) == txn.zxid[1] = z[1] /\ txn.zxid[2] = z[2]

PendingCEPOCH(i, j)    == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = CEPOCH
PendingNEWEPOCH(i, j)  == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = NEWEPOCH
PendingACKEPOCH(i, j)  == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = ACKEPOCH
PendingNEWLEADER(i, j) == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = NEWLEADER
PendingACKLD(i, j)     == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = ACKLD
PendingCOMMITLD(i, j)  == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = COMMITLD
PendingPROPOSE(i, j)   == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = PROPOSE
PendingACK(i, j)       == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = ACK
PendingCOMMIT(i, j)    == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = COMMIT

Send(i, j, m) == msgs' = [msgs EXCEPT ![i][j] = Append(msgs[i][j], m)]

Discard(i, j) == msgs' = IF msgs[i][j] /= << >> THEN [msgs EXCEPT ![i][j] = Tail(msgs[i][j])]
                                                ELSE msgs

Reply(i, j, m) == msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                       ![i][j] = Append(msgs[i][j], m)]

Clean(i, j) == msgs' = [msgs EXCEPT ![j][i] = << >>, ![i][j] = << >>]   
CleanInputBuffer(S) == msgs' = [s \in Server |-> 
                                    [v \in Server |-> IF v \in S THEN << >>
                                                      ELSE msgs[s][v] ] ]

Broadcast(i, m) ==
        LET ackeRecv_quorum == {a \in ackeRecv[i]: a.connected = TRUE }
            sid_ackeRecv == { a.sid: a \in ackeRecv_quorum }
        IN msgs' = [msgs EXCEPT ![i] = [v \in Server |-> IF /\ v \in sid_ackeRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]  

DiscardAndBroadcast(i, j, m) ==
        LET ackldRecv_quorum == {a \in ackldRecv[i]: a.connected = TRUE }
            sid_ackldRecv == { a.sid: a \in ackldRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in sid_ackldRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]  

DiscardAndBroadcastNEWEPOCH(i, j, m) ==
        LET new_cepochRecv_quorum == {c \in cepochRecv'[i]: c.connected = TRUE }
            new_sid_cepochRecv == { c.sid: c \in new_cepochRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in new_sid_cepochRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]

DiscardAndBroadcastNEWLEADER(i, j, m) ==
        LET new_ackeRecv_quorum == {a \in ackeRecv'[i]: a.connected = TRUE }
            new_sid_ackeRecv == { a.sid: a \in new_ackeRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in new_sid_ackeRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]

DiscardAndBroadcastCOMMITLD(i, j, m) ==
        LET new_ackldRecv_quorum == {a \in ackldRecv'[i]: a.connected = TRUE }
            new_sid_ackldRecv == { a.sid: a \in new_ackldRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in new_sid_ackldRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]

InitServerVars == /\ state         = [s \in Server |-> LOOKING]
                  /\ zabState      = [s \in Server |-> ELECTION]
                  /\ acceptedEpoch = [s \in Server |-> 0]
                  /\ currentEpoch  = [s \in Server |-> 0]
                  /\ history       = [s \in Server |-> <<BootstrapTxn>>]
                  /\ lastCommitted = [s \in Server |-> [ index |-> 1,
                                                         zxid  |-> BootstrapZxid ] ]

InitLeaderVars == /\ learners       = [s \in Server |-> {}]
                  /\ cepochRecv     = [s \in Server |-> {}]
                  /\ ackeRecv       = [s \in Server |-> {}]
                  /\ ackldRecv      = [s \in Server |-> {}]
                  /\ sendCounter    = [s \in Server |-> 0]

InitFollowerVars == connectInfo = [s \in Server |-> NullPoint]

InitElectionVars == leaderOracle = NullPoint

InitMsgVars == msgs = [s \in Server |-> [v \in Server |-> << >>] ]

InitVerifyVars == /\ proposalMsgsLog    = BootstrapProposalMsgs
                  /\ epochLeader        = [i \in 1..MAXEPOCH |-> {} ]

Init == /\ InitServerVars
        /\ InitLeaderVars
        /\ InitFollowerVars
        /\ InitElectionVars
        /\ InitVerifyVars
        /\ InitMsgVars

FollowerShutdown(i) == 
        /\ state'    = [state      EXCEPT ![i] = LOOKING]
        /\ zabState' = [zabState   EXCEPT ![i] = ELECTION]
        /\ connectInfo' = [connectInfo EXCEPT ![i] = NullPoint]

LeaderShutdown(i) ==
        /\ LET S == learners[i]
           IN /\ state' = [s \in Server |-> IF s \in S THEN LOOKING ELSE state[s] ]
              /\ zabState' = [s \in Server |-> IF s \in S THEN ELECTION ELSE zabState[s] ]
              /\ connectInfo' = [s \in Server |-> IF s \in S THEN NullPoint ELSE connectInfo[s] ]
              /\ CleanInputBuffer(S)
        /\ learners'   = [learners   EXCEPT ![i] = {}]

SwitchToFollower(i) ==
        /\ state' = [state EXCEPT ![i] = FOLLOWING]
        /\ zabState' = [zabState EXCEPT ![i] = DISCOVERY]

SwitchToLeader(i) ==
        /\ state' = [state EXCEPT ![i] = LEADING]
        /\ zabState' = [zabState EXCEPT ![i] = DISCOVERY]
        /\ learners' = [learners EXCEPT ![i] = {i}]
        /\ cepochRecv' = [cepochRecv EXCEPT ![i] = { [ sid       |-> i,
                                                       connected |-> TRUE,
                                                       epoch     |-> acceptedEpoch[i] ] }]
        /\ ackeRecv' = [ackeRecv EXCEPT ![i] = { [ sid           |-> i,
                                                   connected     |-> TRUE,
                                                   peerLastEpoch |-> currentEpoch[i],
                                                   peerHistory   |-> history[i] ] }]
        /\ ackldRecv' = [ackldRecv EXCEPT ![i] = { [ sid       |-> i,
                                                     connected |-> TRUE ] }]
        /\ sendCounter' = [sendCounter EXCEPT ![i] = 0]

RemoveCepochRecv(set, sid) ==
        LET sid_cepochRecv == {s.sid: s \in set}
        IN IF sid \notin sid_cepochRecv THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid       |-> sid,
                                  connected |-> FALSE,
                                  epoch     |-> info.epoch ]
                IN (set \ {info}) \union {new_info}

RemoveAckeRecv(set, sid) ==
        LET sid_ackeRecv == {s.sid: s \in set}
        IN IF sid \notin sid_ackeRecv THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid |-> sid,
                                  connected |-> FALSE,
                                  peerLastEpoch |-> info.peerLastEpoch,
                                  peerHistory   |-> info.peerHistory ]
                IN (set \ {info}) \union {new_info}

RemoveAckldRecv(set, sid) ==
        LET sid_ackldRecv == {s.sid: s \in set}
        IN IF sid \notin sid_ackldRecv THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid |-> sid,
                                  connected |-> FALSE ]
                IN (set \ {info}) \union {new_info}

RemoveLearner(i, j) ==
        /\ learners'   = [learners   EXCEPT ![i] = @ \ {j}] 
        /\ cepochRecv' = [cepochRecv EXCEPT ![i] = RemoveCepochRecv(@, j) ]
        /\ ackeRecv'   = [ackeRecv   EXCEPT ![i] = RemoveAckeRecv(@, j) ]
        /\ ackldRecv'  = [ackldRecv  EXCEPT ![i] = RemoveAckldRecv(@, j) ]

UpdateLeader(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= i
        /\ leaderOracle' = i
        /\ SwitchToLeader(i)
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, 
                followerVars, verifyVars, msgVars>>

FollowLeader(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= NullPoint
        /\ \/ /\ leaderOracle = i
              /\ SwitchToLeader(i)
           \/ /\ leaderOracle /= i
              /\ SwitchToFollower(i)
              /\ UNCHANGED leaderVars
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, 
                electionVars, followerVars, verifyVars, msgVars>>

Timeout(i, j) ==

        /\ IsLeader(i)   /\ IsMyLearner(i, j)
        /\ IsFollower(j) /\ IsMyLeader(j, i)
        /\ LET newLearners == learners[i] \ {j}
           IN \/ /\ IsQuorum(newLearners)  
                 /\ RemoveLearner(i, j)
                 /\ FollowerShutdown(j)
                 /\ Clean(i, j)
              \/ /\ ~IsQuorum(newLearners) 
                 /\ LeaderShutdown(i)
                 /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv>>
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted,
                       sendCounter, electionVars, verifyVars>>

Restart(i) ==

        /\ \/ /\ IsLooking(i)
              /\ UNCHANGED <<state, zabState, learners, followerVars, msgVars,
                    cepochRecv, ackeRecv, ackldRecv>>
           \/ /\ IsFollower(i)
              /\ LET connectedWithLeader == HasLeader(i)
                 IN \/ /\ connectedWithLeader
                       /\ LET leader == connectInfo[i]
                              newLearners == learners[leader] \ {i}
                          IN 
                          \/ /\ IsQuorum(newLearners)  
                             /\ RemoveLearner(leader, i)
                             /\ FollowerShutdown(i)
                             /\ Clean(leader, i)
                          \/ /\ ~IsQuorum(newLearners) 
                             /\ LeaderShutdown(leader)
                             /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv>>
                    \/ /\ ~connectedWithLeader
                       /\ FollowerShutdown(i)
                       /\ CleanInputBuffer({i})
                       /\ UNCHANGED <<learners, cepochRecv, ackeRecv, ackldRecv>>
           \/ /\ IsLeader(i)
              /\ LeaderShutdown(i)
              /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv>>
        /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> 0,
                                                           zxid  |-> <<0, 0>> ] ]
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history,
                       sendCounter, leaderOracle, verifyVars>>

ConnectAndFollowerSendCEPOCH(i, j) ==
        /\ IsLeader(i) /\ \lnot IsMyLearner(i, j)
        /\ IsFollower(j) /\ HasNoLeader(j) /\ leaderOracle = i
        /\ learners'   = [learners   EXCEPT ![i] = @ \union {j}]
        /\ connectInfo' = [connectInfo EXCEPT ![j] = i]
        /\ Send(j, i, [ mtype  |-> CEPOCH,
                        mepoch |-> acceptedEpoch[j] ]) 
        /\ UNCHANGED <<serverVars, electionVars, verifyVars, cepochRecv,
                       ackeRecv, ackldRecv, sendCounter>>

CepochRecvQuorumFormed(i) == LET sid_cepochRecv == {c.sid: c \in cepochRecv[i]}
                             IN IsQuorum(sid_cepochRecv)
CepochRecvBecomeQuorum(i) == LET sid_cepochRecv == {c.sid: c \in cepochRecv'[i]}
                             IN IsQuorum(sid_cepochRecv)

UpdateCepochRecv(oldSet, sid, peerEpoch) ==
        LET sid_set == {s.sid: s \in oldSet}
        IN IF sid \in sid_set
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                    new_info == [ sid       |-> sid,
                                  connected |-> TRUE,
                                  epoch     |-> peerEpoch ]
                IN ( oldSet \ {old_info} ) \union {new_info}
           ELSE LET follower_info == [ sid       |-> sid,
                                       connected |-> TRUE,
                                       epoch     |-> peerEpoch ]
                IN oldSet \union {follower_info}

DetermineNewEpoch(i) ==
        LET epoch_cepochRecv == {c.epoch: c \in cepochRecv'[i]}
        IN Maximum(epoch_cepochRecv) + 1

LeaderProcessCEPOCH(i, j) ==

        /\ IsLeader(i)
        /\ PendingCEPOCH(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLearner(i, j)
           IN /\ infoOk
              /\ \/ 
                    /\ ~CepochRecvQuorumFormed(i)
                    /\ \/ /\ zabState[i] = DISCOVERY

                       \/ /\ zabState[i] /= DISCOVERY

                    /\ cepochRecv' = [cepochRecv EXCEPT ![i] = UpdateCepochRecv(@, j, msg.mepoch) ]
                    /\ \/ 
                          
                          /\ CepochRecvBecomeQuorum(i)
                          /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = DetermineNewEpoch(i)]
                          /\ LET m == [ mtype  |-> NEWEPOCH,
                                        mepoch |-> acceptedEpoch'[i] ]
                             IN DiscardAndBroadcastNEWEPOCH(i, j, m)
                       \/ 
                          /\ ~CepochRecvBecomeQuorum(i)
                          /\ Discard(j, i)
                          /\ UNCHANGED acceptedEpoch
                 \/ 
                    /\ CepochRecvQuorumFormed(i)
                    /\ cepochRecv' = [cepochRecv EXCEPT ![i] = UpdateCepochRecv(@, j, msg.mepoch) ]
                    /\ Reply(i, j, [ mtype  |-> NEWEPOCH,
                                     mepoch |-> acceptedEpoch[i] ])
                    /\ UNCHANGED <<acceptedEpoch>>
        /\ UNCHANGED <<state, zabState, currentEpoch, history, lastCommitted, learners, 
                       ackeRecv, ackldRecv, sendCounter, followerVars,
                       electionVars, proposalMsgsLog, epochLeader>>

FollowerProcessNEWEPOCH(i, j) ==
        /\ IsFollower(i)
        /\ PendingNEWEPOCH(i, j)
        /\ LET msg     == msgs[j][i][1]
               infoOk  == IsMyLeader(i, j)
               stateOk == zabState[i] = DISCOVERY
               epochOk == msg.mepoch >= acceptedEpoch[i]
           IN /\ infoOk
              /\ \/ 
                    /\ epochOk
                    /\ \/ /\ stateOk
                          /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = msg.mepoch]
                          /\ LET m == [ mtype    |-> ACKEPOCH,
                                        mepoch   |-> currentEpoch[i],
                                        mhistory |-> history[i] ]
                             IN Reply(i, j, m)
                          /\ zabState' = [zabState EXCEPT ![i] = SYNCHRONIZATION]

                       \/ /\ ~stateOk

                          /\ Discard(j, i)
                          /\ UNCHANGED <<acceptedEpoch, zabState>>
                    /\ UNCHANGED <<followerVars, learners, cepochRecv, ackeRecv,
                            ackldRecv, state>>
                 \/ 
                    /\ ~epochOk
                    /\ FollowerShutdown(i)
                    /\ LET leader == connectInfo[i]
                       IN /\ Clean(i, leader)
                          /\ RemoveLearner(leader, i)
                    /\ UNCHANGED <<acceptedEpoch>>
        /\ UNCHANGED <<currentEpoch, history, lastCommitted, sendCounter,
                    electionVars, proposalMsgsLog, epochLeader>>

AckeRecvQuorumFormed(i) == LET sid_ackeRecv == {a.sid: a \in ackeRecv[i]}
                           IN IsQuorum(sid_ackeRecv)
AckeRecvBecomeQuorum(i) == LET sid_ackeRecv == {a.sid: a \in ackeRecv'[i]}
                           IN IsQuorum(sid_ackeRecv)

UpdateAckeRecv(oldSet, sid, peerEpoch, peerHistory) ==
        LET sid_set == {s.sid: s \in oldSet}
            follower_info == [ sid           |-> sid,
                               connected     |-> TRUE,
                               peerLastEpoch |-> peerEpoch,
                               peerHistory   |-> peerHistory ]
        IN IF sid \in sid_set 
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                IN (oldSet \ {old_info}) \union {follower_info}
           ELSE oldSet \union {follower_info}

SetPacketsForChecking(set, src, ep, his, cur, end) ==
        set \union { [ source |-> src,
                       epoch  |-> ep,
                       zxid   |-> his[idx].zxid,
                       data   |-> his[idx].value ] : idx \in cur..end }

LastZxidOfHistory(his) == IF Len(his) = 0 THEN <<0, 0>>
                          ELSE his[Len(his)].zxid

MoreResentOrEqual(ss1, ss2) == \/ ss1.currentEpoch > ss2.currentEpoch
                               \/ /\ ss1.currentEpoch = ss2.currentEpoch
                                  /\ ~ZxidCompare(ss2.lastZxid, ss1.lastZxid)

DetermineInitialHistory(i) ==
        LET set == ackeRecv'[i]
            ss_set == { [ sid          |-> a.sid,
                          currentEpoch |-> a.peerLastEpoch,
                          lastZxid     |-> LastZxidOfHistory(a.peerHistory) ]
                        : a \in set }
            selected == CHOOSE ss \in ss_set: 
                            \A ss1 \in (ss_set \ {ss}): MoreResentOrEqual(ss, ss1)
            info == CHOOSE f \in set: f.sid = selected.sid
        IN info.peerHistory

InitAcksidHelper(txns, src) ==
        [i \in 1..Len(txns) |-> [ zxid   |-> txns[i].zxid,
                                   value  |-> txns[i].value,
                                   ackSid |-> {src},
                                   epoch  |-> txns[i].epoch ]]

InitAcksid(i, his) == InitAcksidHelper(his, i)

LeaderProcessACKEPOCH(i, j) ==
        /\ IsLeader(i)
        /\ PendingACKEPOCH(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLearner(i, j)
           IN /\ infoOk
              /\ \/ 
                    /\ AckeRecvQuorumFormed(i)
                    /\ ackeRecv' = [ackeRecv EXCEPT ![i] = UpdateAckeRecv(@, j, 
                                            msg.mepoch, msg.mhistory) ]
                    /\ LET toSend == history[i] 
                           m == [ mtype    |-> NEWLEADER,
                                  mepoch   |-> acceptedEpoch[i],
                                  mhistory |-> toSend ]
                           set_forChecking == SetPacketsForChecking({ }, i, 
                                        acceptedEpoch[i], toSend, 1, Len(toSend))
                       IN 
                       /\ Reply(i, j, m) 
                       /\ proposalMsgsLog' = proposalMsgsLog \union set_forChecking
                    /\ UNCHANGED <<currentEpoch, history, 
                                   zabState, epochLeader>>
                 \/ 
                    /\ ~AckeRecvQuorumFormed(i)
                    /\ \/ /\ zabState[i] = DISCOVERY

                       \/ /\ zabState[i] /= DISCOVERY

                    /\ ackeRecv' = [ackeRecv EXCEPT ![i] = UpdateAckeRecv(@, j, 
                                            msg.mepoch, msg.mhistory) ]
                    /\ \/ 
                          
                          /\ AckeRecvBecomeQuorum(i)
                          /\ 
                             LET newLeaderEpoch == acceptedEpoch[i] IN 
                             /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newLeaderEpoch]
                             /\ epochLeader' = [epochLeader EXCEPT ![newLeaderEpoch] 
                                                = @ \union {i} ] 
                          /\ 
                             LET initialHistory == DetermineInitialHistory(i) IN 
                             history' = [history EXCEPT ![i] = InitAcksid(i, initialHistory) ]
                          /\ 
                             zabState' = [zabState EXCEPT ![i] = SYNCHRONIZATION]
                          /\ 
                             LET toSend == history'[i] 
                                 m == [ mtype    |-> NEWLEADER,
                                        mepoch   |-> acceptedEpoch[i],
                                        mhistory |-> toSend ]
                                 set_forChecking == SetPacketsForChecking({ }, i, 
                                            acceptedEpoch[i], toSend, 1, Len(toSend))
                             IN 
                             /\ DiscardAndBroadcastNEWLEADER(i, j, m)
                             /\ proposalMsgsLog' = proposalMsgsLog \union set_forChecking
                       \/ 
                          /\ ~AckeRecvBecomeQuorum(i)
                          /\ Discard(j, i)
                          /\ UNCHANGED <<currentEpoch, history, zabState, 
                                     proposalMsgsLog, epochLeader>>
        /\ UNCHANGED <<state, acceptedEpoch, lastCommitted, learners, cepochRecv, ackldRecv, 
                sendCounter, followerVars, electionVars>>

FollowerProcessNEWLEADER(i, j) ==
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               epochOk == acceptedEpoch[i] = msg.mepoch
               stateOk == zabState[i] = SYNCHRONIZATION
           IN /\ infoOk
              /\ \/ 
                    /\ ~epochOk
                    /\ FollowerShutdown(i)
                    /\ LET leader == connectInfo[i]
                       IN /\ Clean(i, leader)
                          /\ RemoveLearner(leader, i)
                    /\ UNCHANGED <<currentEpoch, history>>
                 \/ 
                    /\ epochOk
                    /\ \/ /\ stateOk

                       \/ /\ ~stateOk

                    /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i]]
                    /\ history' = [history EXCEPT ![i] = msg.mhistory] 
                    /\ LET m == [ mtype |-> ACKLD,
                                  mzxid |-> LastZxidOfHistory(history'[i]) ]
                       IN Reply(i, j, m)
                    /\ UNCHANGED <<followerVars, state, zabState, learners, cepochRecv,
                                    ackeRecv, ackldRecv>>
        /\ UNCHANGED <<acceptedEpoch, lastCommitted, sendCounter, electionVars, 
                proposalMsgsLog, epochLeader>>

AckldRecvQuorumFormed(i) == LET sid_ackldRecv == {a.sid: a \in ackldRecv[i]}
                            IN IsQuorum(sid_ackldRecv)
AckldRecvBecomeQuorum(i) == LET sid_ackldRecv == {a.sid: a \in ackldRecv'[i]}
                            IN IsQuorum(sid_ackldRecv)

UpdateAckldRecv(oldSet, sid) ==
        LET sid_set == {s.sid: s \in oldSet}
            follower_info == [ sid       |-> sid,
                               connected |-> TRUE ]
        IN IF sid \in sid_set
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                IN (oldSet \ {old_info}) \union {follower_info}
           ELSE oldSet \union {follower_info}

LastZxid(i) == LastZxidOfHistory(history[i])

UpdateAcksidHelper(txns, target, endZxid) ==
        LET boundary == CHOOSE b \in 0..Len(txns) :
                /\ (\A k \in 1..b : ~ZxidCompare(txns[k].zxid, endZxid))
                /\ (b < Len(txns) => ZxidCompare(txns[b+1].zxid, endZxid))
        IN [i \in 1..Len(txns) |->
                IF i <= boundary
                THEN [ zxid   |-> txns[i].zxid,
                       value  |-> txns[i].value,
                       ackSid |-> IF target \in txns[i].ackSid
                                  THEN txns[i].ackSid
                                  ELSE txns[i].ackSid \union {target},
                       epoch  |-> txns[i].epoch ]
                ELSE txns[i] ]

UpdateAcksid(his, target, endZxid) == UpdateAcksidHelper(his, target, endZxid)

LeaderProcessACKLD(i, j) ==
        /\ IsLeader(i)
        /\ PendingACKLD(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLearner(i, j)
           IN /\ infoOk
              /\ \/ 
                    /\ ~AckldRecvQuorumFormed(i)
                    /\ \/ /\ zabState[i] = SYNCHRONIZATION

                       \/ /\ zabState[i] /= SYNCHRONIZATION

                    /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateAckldRecv(@, j) ]
                    /\ history' = [history EXCEPT ![i] = UpdateAcksid(@, j, msg.mzxid)]
                    /\ \/ 
                          
                          /\ AckldRecvBecomeQuorum(i)
                          /\ lastCommitted' = [lastCommitted EXCEPT 
                                                    ![i] = [ index |-> Len(history[i]),
                                                             zxid  |-> LastZxid(i) ] ]
                          /\ zabState' = [zabState EXCEPT ![i] = BROADCAST]
                          /\ LET m == [ mtype |-> COMMITLD,
                                        mzxid |-> LastZxid(i) ]
                             IN DiscardAndBroadcastCOMMITLD(i, j, m)
                       \/ 
                          /\ ~AckldRecvBecomeQuorum(i)
                          /\ Discard(j, i)
                          /\ UNCHANGED <<zabState, lastCommitted>>
                 \/ 
                    /\ AckldRecvQuorumFormed(i)
                    /\ \/ /\ zabState[i] = BROADCAST

                       \/ /\ zabState[i] /= BROADCAST

                    /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateAckldRecv(@, j) ]
                    /\ history' = [history EXCEPT ![i] = UpdateAcksid(@, j, msg.mzxid)]
                    /\ Reply(i, j, [ mtype |-> COMMITLD,
                                     mzxid |-> lastCommitted[i].zxid ])
                    /\ UNCHANGED <<zabState, lastCommitted>>
        /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, learners, cepochRecv, ackeRecv, 
                    sendCounter, followerVars, electionVars, proposalMsgsLog, epochLeader>>

ZxidToIndexHepler(his, zxid, cur, appeared) == 
        LET matches == {i \in cur..Len(his) : TxnZxidEqual(his[i], zxid)}
        IN IF appeared = TRUE THEN (IF matches = {} THEN Len(his) + 1 ELSE -1)
           ELSE CASE Cardinality(matches) = 0 -> Len(his) + 1
                []   Cardinality(matches) = 1 -> CHOOSE i \in matches : TRUE
                []   OTHER -> -1

ZxidToIndex(his, zxid) == IF ZxidEqual( zxid, <<0, 0>> ) THEN 0
                          ELSE IF Len(his) = 0 THEN 1
                               ELSE LET len == Len(his) IN
                                    IF \E idx \in 1..len: TxnZxidEqual(his[idx], zxid)
                                    THEN ZxidToIndexHepler(his, zxid, 1, FALSE)
                                    ELSE len + 1

FollowerProcessCOMMITLD(i, j) ==
        /\ IsFollower(i)
        /\ PendingCOMMITLD(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               index == IF ZxidEqual(msg.mzxid, <<0, 0>>) THEN 0
                        ELSE ZxidToIndex(history[i], msg.mzxid)
               logOk == index >= 0 /\ index <= Len(history[i])
           IN /\ infoOk
              /\ \/ /\ logOk

                 \/ /\ ~logOk

              /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> index,
                                                                 zxid  |-> msg.mzxid ] ]
              /\ zabState' = [zabState EXCEPT ![i] = BROADCAST]
              /\ Discard(j, i)
        /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, history, leaderVars, 
                    followerVars, electionVars, proposalMsgsLog, epochLeader>>

IncZxid(s, zxid) == IF currentEpoch[s] = zxid[1] THEN <<zxid[1], zxid[2] + 1>>
                    ELSE <<currentEpoch[s], 1>>

LeaderProcessRequest(i) ==

        /\ IsLeader(i)
        /\ zabState[i] = BROADCAST
        /\ LET request_value == 1 
               newTxn == [ zxid   |-> IncZxid(i, LastZxid(i)),
                           value  |-> request_value,
                           ackSid |-> {i},
                           epoch  |-> currentEpoch[i] ]
           IN history' = [history EXCEPT ![i] = Append(@, newTxn) ]
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, lastCommitted,
                    leaderVars, followerVars, electionVars, msgVars, verifyVars>>

CurrentCounter(i) == IF LastZxid(i)[1] = currentEpoch[i] THEN LastZxid(i)[2]
                     ELSE 0

LeaderBroadcastPROPOSE(i) == 
        /\ IsLeader(i)
        /\ zabState[i] = BROADCAST
        /\ sendCounter[i] < CurrentCounter(i) 
        /\ LET toSendCounter == sendCounter[i] + 1
               toSendZxid == <<currentEpoch[i], toSendCounter>>
               toSendIndex == ZxidToIndex(history[i], toSendZxid)
               toSendTxn == history[i][toSendIndex]
               m_proposal == [ mtype |-> PROPOSE,
                               mzxid |-> toSendTxn.zxid,
                               mdata |-> toSendTxn.value ]
               m_proposal_forChecking == [ source |-> i,
                                           epoch  |-> currentEpoch[i],
                                           zxid   |-> toSendTxn.zxid,
                                           data   |-> toSendTxn.value ]
           IN /\ sendCounter' = [sendCounter EXCEPT ![i] = toSendCounter]
              /\ Broadcast(i, m_proposal)
              /\ proposalMsgsLog' = proposalMsgsLog \union {m_proposal_forChecking}
        /\ UNCHANGED <<serverVars, learners, cepochRecv, ackeRecv, ackldRecv, 
                followerVars, electionVars, epochLeader>>

IsNextZxid(curZxid, nextZxid) ==
            \/ 
               /\ nextZxid[2] = 1
               /\ curZxid[1] < nextZxid[1]
            \/ 
               /\ nextZxid[2] > 1
               /\ curZxid[1] = nextZxid[1]
               /\ curZxid[2] + 1 = nextZxid[2]

FollowerProcessPROPOSE(i, j) ==
        /\ IsFollower(i)
        /\ PendingPROPOSE(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               isNext == IsNextZxid(LastZxid(i), msg.mzxid)
               newTxn == [ zxid   |-> msg.mzxid,
                           value  |-> msg.mdata,
                           ackSid |-> {},
                           epoch  |-> currentEpoch[i] ]
               m_ack == [ mtype |-> ACK,
                          mzxid |-> msg.mzxid ]
           IN /\ infoOk
              /\ \/ /\ isNext
                    /\ history' = [history EXCEPT ![i] = Append(@, newTxn)]
                    /\ Reply(i, j, m_ack)

                 \/ /\ ~isNext
                    /\ LET index == ZxidToIndex(history[i], msg.mzxid)
                           exist == index > 0 /\ index <= Len(history[i])
                       IN \/ /\ exist

                          \/ /\ ~exist

                    /\ Discard(j, i)
                    /\ UNCHANGED history
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, lastCommitted,
                    leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>

LeaderTryToCommit(s, index, zxid, newTxn, follower) ==
        LET allTxnsBeforeCommitted == lastCommitted[s].index >= index - 1

            hasAllQuorums == IsQuorum(newTxn.ackSid)

            ordered == lastCommitted[s].index + 1 = index
                    
        IN \/ /\ 
                 \/ ~allTxnsBeforeCommitted
                 \/ ~hasAllQuorums
              /\ Discard(follower, s)
              /\ UNCHANGED <<lastCommitted>>
           \/ /\ allTxnsBeforeCommitted
              /\ hasAllQuorums
              /\ \/ /\ ~ordered

                 \/ /\ ordered

              /\ lastCommitted' = [lastCommitted EXCEPT ![s] = [ index |-> index,
                                                                 zxid  |-> zxid ] ]
              /\ LET m_commit == [ mtype |-> COMMIT,
                                   mzxid |-> zxid ]
                 IN DiscardAndBroadcast(s, follower, m_commit)

LastAckIndexFromFollower(i, j) == 
        LET set_index == {idx \in 1..Len(history[i]): j \in history[i][idx].ackSid }
        IN Maximum(set_index)

LeaderProcessACK(i, j) ==
        /\ IsLeader(i)
        /\ PendingACK(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLearner(i, j)
               index == ZxidToIndex(history[i], msg.mzxid)
               exist == index >= 1 /\ index <= Len(history[i]) 
               outstanding == lastCommitted[i].index < Len(history[i]) 
               hasCommitted == ~ZxidCompare(msg.mzxid, lastCommitted[i].zxid)
               ackIndex == LastAckIndexFromFollower(i, j)
               monotonicallyInc == \/ ackIndex = -1
                                   \/ ackIndex + 1 = index
           IN /\ infoOk
              /\ \/ /\ exist
                    /\ monotonicallyInc
                    /\ LET txn == history[i][index]
                           txnAfterAddAck == [ zxid   |-> txn.zxid,
                                               value  |-> txn.value,
                                               ackSid |-> txn.ackSid \union {j} ,
                                               epoch  |-> txn.epoch ]   
                       IN
                       /\ history' = [history EXCEPT ![i][index] = txnAfterAddAck ]
                       /\ \/ /\ 
                                
                                \/ ~outstanding
                                \/ hasCommitted
                             /\ Discard(j, i)
                             /\ UNCHANGED <<lastCommitted>>
                          \/ /\ outstanding
                             /\ ~hasCommitted
                             /\ LeaderTryToCommit(i, index, msg.mzxid, txnAfterAddAck, j)
                 \/ /\ \/ ~exist
                       \/ ~monotonicallyInc

                    /\ Discard(j, i)
                    /\ UNCHANGED <<history, lastCommitted>>
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, leaderVars,
                    followerVars, electionVars, proposalMsgsLog, epochLeader>>

FollowerProcessCOMMIT(i, j) ==
        /\ IsFollower(i)
        /\ PendingCOMMIT(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               pending == lastCommitted[i].index < Len(history[i])
           IN /\ infoOk
              /\ \/ /\ ~pending

                    /\ UNCHANGED <<lastCommitted>>
                 \/ /\ pending
                    /\ LET firstElement == history[i][lastCommitted[i].index + 1]
                           match == ZxidEqual(firstElement.zxid, msg.mzxid)
                       IN
                       \/ /\ ~match

                          /\ UNCHANGED lastCommitted
                       \/ /\ match
                          /\ lastCommitted' = [lastCommitted EXCEPT ![i] = 
                                            [ index |-> lastCommitted[i].index + 1,
                                              zxid  |-> firstElement.zxid ] ]

        /\ Discard(j, i)
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, history,
                    leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>

Next ==
        
        \/ \E i \in Server:    UpdateLeader(i)
        \/ \E i \in Server:    FollowLeader(i)
        
        \/ \E i, j \in Server: Timeout(i, j)
        \/ \E i \in Server:    Restart(i)
        
        \/ \E i, j \in Server: ConnectAndFollowerSendCEPOCH(i, j)
        \/ \E i, j \in Server: LeaderProcessCEPOCH(i, j)
        \/ \E i, j \in Server: FollowerProcessNEWEPOCH(i, j)
        \/ \E i, j \in Server: LeaderProcessACKEPOCH(i, j)
        \/ \E i, j \in Server: FollowerProcessNEWLEADER(i, j)
        \/ \E i, j \in Server: LeaderProcessACKLD(i, j)
        \/ \E i, j \in Server: FollowerProcessCOMMITLD(i, j)
        
        \/ \E i \in Server:    LeaderProcessRequest(i)
        \/ \E i \in Server:    LeaderBroadcastPROPOSE(i)
        \/ \E i, j \in Server: FollowerProcessPROPOSE(i, j)
        \/ \E i, j \in Server: LeaderProcessACK(i, j)
        \/ \E i, j \in Server: FollowerProcessCOMMIT(i, j)

Spec == Init /\ [][Next]_vars

=============================================================================
