---- MODULE GuidedTrace ----
EXTENDS ZkV3_7_0Defs
CONSTANT A, B, C
VARIABLE pc, edge
SimulationValue == {0}
TaggedFLEReceiveNotmsg(i,j) == /\ FLEReceiveNotmsg(i,j) /\ edge' = <<"Receive",i,j>>
TaggedFLENotmsgTimeout(i) == /\ FLENotmsgTimeout(i) /\ edge' = <<"Timeout",i,i>>
TaggedFLEHandleNotmsg(i) == /\ FLEHandleNotmsg(i) /\ edge' = <<"Handle",i,i>>
TaggedFLEWaitNewNotmsg(i) == /\ FLEWaitNewNotmsg(i) /\ edge' = <<"Wait",i,i>>
TaggedConnectAndFollowerSendFOLLOWERINFO(i,j) == /\ ConnectAndFollowerSendFOLLOWERINFO(i,j) /\ edge' = <<"Connect",i,j>>
TaggedLeaderProcessFOLLOWERINFO(i,j) == /\ LeaderProcessFOLLOWERINFO(i,j) /\ edge' = <<"FollowerInfo",i,j>>
TaggedFollowerProcessLEADERINFO(i,j) == /\ FollowerProcessLEADERINFO(i,j) /\ edge' = <<"LeaderInfo",i,j>>
TaggedLeaderProcessACKEPOCH(i,j) == /\ LeaderProcessACKEPOCH(i,j) /\ edge' = <<"AckEpoch",i,j>>
TaggedLeaderSyncFollower(i,j) == /\ LeaderSyncFollower(i,j) /\ edge' = <<"Sync",i,j>>
TaggedFollowerProcessSyncMessage(i,j) == /\ FollowerProcessSyncMessage(i,j) /\ edge' = <<"SyncMessage",i,j>>
TaggedFollowerProcessPROPOSALInSync(i,j) == /\ FollowerProcessPROPOSALInSync(i,j) /\ edge' = <<"ProposalSync",i,j>>
TaggedFollowerProcessCOMMITInSync(i,j) == /\ FollowerProcessCOMMITInSync(i,j) /\ edge' = <<"CommitSync",i,j>>
TaggedFollowerProcessNEWLEADER(i,j) == /\ FollowerProcessNEWLEADER(i,j) /\ edge' = <<"NewLeader",i,j>>
TaggedLeaderProcessACKLD(i,j) == /\ LeaderProcessACKLD(i,j) /\ edge' = <<"AckLd",i,j>>
TaggedFollowerProcessUPTODATE(i,j) == /\ FollowerProcessUPTODATE(i,j) /\ edge' = <<"UpToDate",i,j>>
TaggedLeaderProcessRequest(i) == /\ LeaderProcessRequest(i) /\ edge' = <<"Request",i,i>>
TaggedFollowerProcessPROPOSAL(i,j) == /\ FollowerProcessPROPOSAL(i,j) /\ edge' = <<"Proposal",i,j>>
TaggedLeaderProcessACK(i,j) == /\ LeaderProcessACK(i,j) /\ edge' = <<"Ack",i,j>>
TaggedFollowerProcessCOMMIT(i,j) == /\ FollowerProcessCOMMIT(i,j) /\ edge' = <<"Commit",i,j>>
TaggedNodeCrash(i) == /\ NodeCrash(i) /\ edge' = <<"Crash",i,i>>
TaggedNodeStart(i) == /\ NodeStart(i) /\ edge' = <<"Start",i,i>>
HealthyNext ==  
        
            \/ \E i, j \in Server: TaggedFLEReceiveNotmsg(i, j)
            \/ \E i \in Server:    TaggedFLENotmsgTimeout(i)
            \/ \E i \in Server:    TaggedFLEHandleNotmsg(i)
            \/ \E i \in Server:    TaggedFLEWaitNewNotmsg(i)
        
        
            \/ \E i, j \in Server: TaggedConnectAndFollowerSendFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: TaggedLeaderProcessFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessLEADERINFO(i, j)
            \/ \E i, j \in Server: TaggedLeaderProcessACKEPOCH(i, j)
            \/ \E i, j \in Server: TaggedLeaderSyncFollower(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessSyncMessage(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessPROPOSALInSync(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessCOMMITInSync(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessNEWLEADER(i, j)
            \/ \E i, j \in Server: TaggedLeaderProcessACKLD(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessUPTODATE(i, j)
        
            \/ \E i, j \in Server: TaggedFollowerProcessPROPOSAL(i, j)
            \/ \E i, j \in Server: TaggedLeaderProcessACK(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessCOMMIT(i, j)
DiscoveryNext ==  
        
            \/ \E i, j \in Server: TaggedFLEReceiveNotmsg(i, j)
            \/ \E i \in Server:    TaggedFLENotmsgTimeout(i)
            \/ \E i \in Server:    TaggedFLEHandleNotmsg(i)
            \/ \E i \in Server:    TaggedFLEWaitNewNotmsg(i)
        
        
            \/ \E i, j \in Server: TaggedConnectAndFollowerSendFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: TaggedLeaderProcessFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: TaggedFollowerProcessLEADERINFO(i, j)
            \/ \E i, j \in Server: TaggedLeaderProcessACKEPOCH(i, j)
        
WantLeader(i) == \A j \in Server \ {i}: state'[j] /= LEADING
Done == CASE pc = 0 -> /\ state[A] = LEADING /\ \A i \in Server: zabState[i] = BROADCAST
          [] pc = 3 -> /\ currentEpoch[B] = 2 /\ zabState[B] = SYNCHRONIZATION /\ zabState[C] = SYNCHRONIZATION
          [] pc = 6 -> /\ currentEpoch[A] = 3 /\ zabState[A] = SYNCHRONIZATION /\ zabState[C] = SYNCHRONIZATION
          [] pc = 7 -> /\ connectInfo[C].syncMode = SNAP /\ lastCommitted[C].index = 2
          [] pc = 10 -> /\ currentEpoch[B] = 4 /\ zabState[B] = SYNCHRONIZATION /\ zabState[C] = SYNCHRONIZATION
          [] pc = 11 -> /\ zabState[B] = BROADCAST /\ zabState[C] = BROADCAST
          [] OTHER -> FALSE
Step == CASE pc = 0 -> /\ HealthyNext /\ WantLeader(A)
          [] pc = 1 -> TaggedLeaderProcessRequest(A)
          [] pc = 2 -> TaggedNodeCrash(A)
          [] pc = 3 -> /\ DiscoveryNext /\ WantLeader(B)
          [] pc = 4 -> TaggedNodeCrash(B)
          [] pc = 5 -> TaggedNodeStart(A)
          [] pc = 6 -> /\ DiscoveryNext /\ WantLeader(A)
          [] pc = 7 -> TaggedLeaderSyncFollower(A,C) \/ TaggedFollowerProcessSyncMessage(C,A)
          [] pc = 8 -> TaggedNodeCrash(A)
          [] pc = 9 -> TaggedNodeStart(B)
          [] pc = 10 -> /\ DiscoveryNext /\ WantLeader(B)
          [] pc = 11 -> TaggedLeaderSyncFollower(B,C) \/ TaggedFollowerProcessSyncMessage(C,B) \/ TaggedFollowerProcessNEWLEADER(C,B) \/ TaggedLeaderProcessACKLD(B,C) \/ TaggedFollowerProcessUPTODATE(C,B)
          [] pc = 12 -> TaggedLeaderProcessRequest(B)
          [] pc = 13 -> TaggedFollowerProcessPROPOSAL(C,B)
          [] pc = 14 -> TaggedLeaderProcessACK(B,C)
          [] OTHER -> /\ UNCHANGED vars /\ edge' = <<"Stutter",A,A>>
GuidedInit == Init /\ pc = 0 /\ edge = <<"Stutter",A,A>>
GuidedNext == IF Done THEN /\ pc' = pc + 1 /\ UNCHANGED vars /\ edge' = <<"Stutter",A,A>>
                     ELSE /\ Step /\ pc' = IF pc \in {1,2,4,5,8,9,12,13,14} THEN pc+1 ELSE pc
GuidedSpec == GuidedInit /\ [][GuidedNext]_<<vars,pc,edge>>
====
