---- MODULE Guided ----
EXTENDS ZkV3_7_0Defs
CONSTANT A, B, C
VARIABLE pc
SimulationValue == {0}
HealthyNext ==  
        
            \/ \E i, j \in Server: FLEReceiveNotmsg(i, j)
            \/ \E i \in Server:    FLENotmsgTimeout(i)
            \/ \E i \in Server:    FLEHandleNotmsg(i)
            \/ \E i \in Server:    FLEWaitNewNotmsg(i)
        
        
            \/ \E i, j \in Server: ConnectAndFollowerSendFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: LeaderProcessFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: FollowerProcessLEADERINFO(i, j)
            \/ \E i, j \in Server: LeaderProcessACKEPOCH(i, j)
            \/ \E i, j \in Server: LeaderSyncFollower(i, j)
            \/ \E i, j \in Server: FollowerProcessSyncMessage(i, j)
            \/ \E i, j \in Server: FollowerProcessPROPOSALInSync(i, j)
            \/ \E i, j \in Server: FollowerProcessCOMMITInSync(i, j)
            \/ \E i, j \in Server: FollowerProcessNEWLEADER(i, j)
            \/ \E i, j \in Server: LeaderProcessACKLD(i, j)
            \/ \E i, j \in Server: FollowerProcessUPTODATE(i, j)
        
            \/ \E i, j \in Server: FollowerProcessPROPOSAL(i, j)
            \/ \E i, j \in Server: LeaderProcessACK(i, j)
            \/ \E i, j \in Server: FollowerProcessCOMMIT(i, j)
DiscoveryNext ==  
        
            \/ \E i, j \in Server: FLEReceiveNotmsg(i, j)
            \/ \E i \in Server:    FLENotmsgTimeout(i)
            \/ \E i \in Server:    FLEHandleNotmsg(i)
            \/ \E i \in Server:    FLEWaitNewNotmsg(i)
        
        
            \/ \E i, j \in Server: ConnectAndFollowerSendFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: LeaderProcessFOLLOWERINFO(i, j)
            \/ \E i, j \in Server: FollowerProcessLEADERINFO(i, j)
            \/ \E i, j \in Server: LeaderProcessACKEPOCH(i, j)
        
WantLeader(i) == \A j \in Server \ {i}: state'[j] /= LEADING
Done == CASE pc = 0 -> /\ state[A] = LEADING /\ \A i \in Server: zabState[i] = BROADCAST
          [] pc = 3 -> /\ currentEpoch[B] = 2 /\ zabState[B] = SYNCHRONIZATION /\ zabState[C] = SYNCHRONIZATION
          [] pc = 6 -> /\ currentEpoch[A] = 3 /\ zabState[A] = SYNCHRONIZATION /\ zabState[C] = SYNCHRONIZATION
          [] pc = 7 -> /\ connectInfo[C].syncMode = SNAP /\ lastCommitted[C].index = 2
          [] pc = 10 -> /\ currentEpoch[B] = 4 /\ zabState[B] = SYNCHRONIZATION /\ zabState[C] = SYNCHRONIZATION
          [] pc = 11 -> /\ zabState[B] = BROADCAST /\ zabState[C] = BROADCAST
          [] OTHER -> FALSE
Step == CASE pc = 0 -> /\ HealthyNext /\ WantLeader(A)
          [] pc = 1 -> LeaderProcessRequest(A)
          [] pc = 2 -> NodeCrash(A)
          [] pc = 3 -> /\ DiscoveryNext /\ WantLeader(B)
          [] pc = 4 -> NodeCrash(B)
          [] pc = 5 -> NodeStart(A)
          [] pc = 6 -> /\ DiscoveryNext /\ WantLeader(A)
          [] pc = 7 -> LeaderSyncFollower(A,C) \/ FollowerProcessSyncMessage(C,A)
          [] pc = 8 -> NodeCrash(A)
          [] pc = 9 -> NodeStart(B)
          [] pc = 10 -> /\ DiscoveryNext /\ WantLeader(B)
          [] pc = 11 -> LeaderSyncFollower(B,C) \/ FollowerProcessSyncMessage(C,B) \/ FollowerProcessNEWLEADER(C,B) \/ LeaderProcessACKLD(B,C) \/ FollowerProcessUPTODATE(C,B)
          [] pc = 12 -> LeaderProcessRequest(B)
          [] pc = 13 -> FollowerProcessPROPOSAL(C,B)
          [] pc = 14 -> LeaderProcessACK(B,C)
          [] OTHER -> UNCHANGED vars
GuidedInit == Init /\ pc = 0
GuidedNext == IF Done THEN /\ pc' = pc + 1 /\ UNCHANGED vars
                     ELSE /\ Step /\ pc' = IF pc \in {1,2,4,5,8,9,12,13,14} THEN pc+1 ELSE pc
GuidedSpec == GuidedInit /\ [][GuidedNext]_<<vars,pc>>
====
