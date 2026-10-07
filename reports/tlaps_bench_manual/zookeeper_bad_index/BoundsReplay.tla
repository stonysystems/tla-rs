---- MODULE BoundsReplay ----
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
        
FixedAction ==
    CASE pc = 0 -> /\ FLENotmsgTimeout(A) /\ edge' = <<"Timeout",A,A>>
    [] pc = 1 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 2 -> /\ FLEReceiveNotmsg(B,A) /\ edge' = <<"Receive",B,A>>
    [] pc = 3 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 4 -> /\ FLEReceiveNotmsg(A,B) /\ edge' = <<"Receive",A,B>>
    [] pc = 5 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 6 -> /\ FLEWaitNewNotmsg(A) /\ edge' = <<"Wait",A,A>>
    [] pc = 7 -> /\ FLEWaitNewNotmsg(B) /\ edge' = <<"Wait",B,B>>
    [] pc = 8 -> /\ FLEReceiveNotmsg(C,A) /\ edge' = <<"Receive",C,A>>
    [] pc = 9 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 10 -> /\ ConnectAndFollowerSendFOLLOWERINFO(A,B) /\ edge' = <<"Connect",A,B>>
    [] pc = 11 -> /\ FLEWaitNewNotmsg(C) /\ edge' = <<"Wait",C,C>>
    [] pc = 12 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 13 -> /\ ConnectAndFollowerSendFOLLOWERINFO(A,C) /\ edge' = <<"Connect",A,C>>
    [] pc = 14 -> /\ LeaderProcessFOLLOWERINFO(A,C) /\ edge' = <<"FollowerInfo",A,C>>
    [] pc = 15 -> /\ FLEReceiveNotmsg(C,B) /\ edge' = <<"Receive",C,B>>
    [] pc = 16 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 17 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 18 -> /\ LeaderProcessFOLLOWERINFO(A,B) /\ edge' = <<"FollowerInfo",A,B>>
    [] pc = 19 -> /\ FLEReceiveNotmsg(C,B) /\ edge' = <<"Receive",C,B>>
    [] pc = 20 -> /\ FLEReceiveNotmsg(C,A) /\ edge' = <<"Receive",C,A>>
    [] pc = 21 -> /\ FollowerProcessLEADERINFO(C,A) /\ edge' = <<"LeaderInfo",C,A>>
    [] pc = 22 -> /\ FollowerProcessLEADERINFO(B,A) /\ edge' = <<"LeaderInfo",B,A>>
    [] pc = 23 -> /\ LeaderProcessACKEPOCH(A,B) /\ edge' = <<"AckEpoch",A,B>>
    [] pc = 24 -> /\ LeaderSyncFollower(A,B) /\ edge' = <<"Sync",A,B>>
    [] pc = 25 -> /\ LeaderProcessACKEPOCH(A,C) /\ edge' = <<"AckEpoch",A,C>>
    [] pc = 26 -> /\ LeaderSyncFollower(A,C) /\ edge' = <<"Sync",A,C>>
    [] pc = 27 -> /\ FollowerProcessSyncMessage(B,A) /\ edge' = <<"SyncMessage",B,A>>
    [] pc = 28 -> /\ FollowerProcessSyncMessage(C,A) /\ edge' = <<"SyncMessage",C,A>>
    [] pc = 29 -> /\ FollowerProcessNEWLEADER(C,A) /\ edge' = <<"NewLeader",C,A>>
    [] pc = 30 -> /\ FollowerProcessNEWLEADER(B,A) /\ edge' = <<"NewLeader",B,A>>
    [] pc = 31 -> /\ LeaderProcessACKLD(A,B) /\ edge' = <<"AckLd",A,B>>
    [] pc = 32 -> /\ FollowerProcessUPTODATE(B,A) /\ edge' = <<"UpToDate",B,A>>
    [] pc = 33 -> /\ LeaderProcessACKLD(A,C) /\ edge' = <<"AckLd",A,C>>
    [] pc = 34 -> /\ FollowerProcessUPTODATE(C,A) /\ edge' = <<"UpToDate",C,A>>
    [] pc = 35 -> /\ LeaderProcessRequest(A) /\ edge' = <<"Request",A,A>>
    [] pc = 36 -> /\ LeaderProcessRequest(A) /\ edge' = <<"Request",A,A>>
    [] pc = 37 -> /\ LeaderProcessRequest(A) /\ edge' = <<"Request",A,A>>
    [] pc = 38 -> /\ NodeCrash(A) /\ edge' = <<"Crash",A,A>>
    [] pc = 39 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 40 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 41 -> /\ FLEReceiveNotmsg(C,B) /\ edge' = <<"Receive",C,B>>
    [] pc = 42 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 43 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 44 -> /\ FLENotmsgTimeout(B) /\ edge' = <<"Timeout",B,B>>
    [] pc = 45 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 46 -> /\ FLENotmsgTimeout(C) /\ edge' = <<"Timeout",C,C>>
    [] pc = 47 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 48 -> /\ FLEReceiveNotmsg(C,B) /\ edge' = <<"Receive",C,B>>
    [] pc = 49 -> /\ FLEWaitNewNotmsg(C) /\ edge' = <<"Wait",C,C>>
    [] pc = 50 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 51 -> /\ FLEWaitNewNotmsg(C) /\ edge' = <<"Wait",C,C>>
    [] pc = 52 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 53 -> /\ FLENotmsgTimeout(B) /\ edge' = <<"Timeout",B,B>>
    [] pc = 54 -> /\ FLEWaitNewNotmsg(B) /\ edge' = <<"Wait",B,B>>
    [] pc = 55 -> /\ ConnectAndFollowerSendFOLLOWERINFO(B,C) /\ edge' = <<"Connect",B,C>>
    [] pc = 56 -> /\ LeaderProcessFOLLOWERINFO(B,C) /\ edge' = <<"FollowerInfo",B,C>>
    [] pc = 57 -> /\ FollowerProcessLEADERINFO(C,B) /\ edge' = <<"LeaderInfo",C,B>>
    [] pc = 58 -> /\ LeaderProcessACKEPOCH(B,C) /\ edge' = <<"AckEpoch",B,C>>
    [] pc = 59 -> /\ NodeCrash(B) /\ edge' = <<"Crash",B,B>>
    [] pc = 60 -> /\ NodeStart(A) /\ edge' = <<"Start",A,A>>
    [] pc = 61 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 62 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 63 -> /\ FLEReceiveNotmsg(A,B) /\ edge' = <<"Receive",A,B>>
    [] pc = 64 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 65 -> /\ FLENotmsgTimeout(C) /\ edge' = <<"Timeout",C,C>>
    [] pc = 66 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 67 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 68 -> /\ FLEReceiveNotmsg(A,B) /\ edge' = <<"Receive",A,B>>
    [] pc = 69 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 70 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 71 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 72 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 73 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 74 -> /\ FLEReceiveNotmsg(C,A) /\ edge' = <<"Receive",C,A>>
    [] pc = 75 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 76 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 77 -> /\ FLENotmsgTimeout(C) /\ edge' = <<"Timeout",C,C>>
    [] pc = 78 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 79 -> /\ FLEWaitNewNotmsg(C) /\ edge' = <<"Wait",C,C>>
    [] pc = 80 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 81 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 82 -> /\ FLENotmsgTimeout(A) /\ edge' = <<"Timeout",A,A>>
    [] pc = 83 -> /\ FLEWaitNewNotmsg(A) /\ edge' = <<"Wait",A,A>>
    [] pc = 84 -> /\ ConnectAndFollowerSendFOLLOWERINFO(A,C) /\ edge' = <<"Connect",A,C>>
    [] pc = 85 -> /\ LeaderProcessFOLLOWERINFO(A,C) /\ edge' = <<"FollowerInfo",A,C>>
    [] pc = 86 -> /\ FollowerProcessLEADERINFO(C,A) /\ edge' = <<"LeaderInfo",C,A>>
    [] pc = 87 -> /\ LeaderProcessACKEPOCH(A,C) /\ edge' = <<"AckEpoch",A,C>>
    [] pc = 88 -> /\ LeaderSyncFollower(A,C) /\ edge' = <<"Sync",A,C>>
    [] pc = 89 -> /\ FollowerProcessSyncMessage(C,A) /\ edge' = <<"SyncMessage",C,A>>
    [] pc = 90 -> /\ NodeCrash(A) /\ edge' = <<"Crash",A,A>>
    [] pc = 91 -> /\ NodeStart(B) /\ edge' = <<"Start",B,B>>
    [] pc = 92 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 93 -> /\ FLEReceiveNotmsg(B,A) /\ edge' = <<"Receive",B,A>>
    [] pc = 94 -> /\ FLENotmsgTimeout(C) /\ edge' = <<"Timeout",C,C>>
    [] pc = 95 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 96 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 97 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 98 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 99 -> /\ FLENotmsgTimeout(C) /\ edge' = <<"Timeout",C,C>>
    [] pc = 100 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 101 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 102 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 103 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 104 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 105 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 106 -> /\ FLENotmsgTimeout(C) /\ edge' = <<"Timeout",C,C>>
    [] pc = 107 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 108 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 109 -> /\ FLENotmsgTimeout(C) /\ edge' = <<"Timeout",C,C>>
    [] pc = 110 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 111 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 112 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 113 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 114 -> /\ FLEReceiveNotmsg(C,B) /\ edge' = <<"Receive",C,B>>
    [] pc = 115 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 116 -> /\ FLEHandleNotmsg(C) /\ edge' = <<"Handle",C,C>>
    [] pc = 117 -> /\ FLEWaitNewNotmsg(C) /\ edge' = <<"Wait",C,C>>
    [] pc = 118 -> /\ FLEReceiveNotmsg(B,C) /\ edge' = <<"Receive",B,C>>
    [] pc = 119 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 120 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 121 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 122 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 123 -> /\ FLEHandleNotmsg(B) /\ edge' = <<"Handle",B,B>>
    [] pc = 124 -> /\ FLEWaitNewNotmsg(B) /\ edge' = <<"Wait",B,B>>
    [] pc = 125 -> /\ ConnectAndFollowerSendFOLLOWERINFO(B,C) /\ edge' = <<"Connect",B,C>>
    [] pc = 126 -> /\ LeaderProcessFOLLOWERINFO(B,C) /\ edge' = <<"FollowerInfo",B,C>>
    [] pc = 127 -> /\ FollowerProcessLEADERINFO(C,B) /\ edge' = <<"LeaderInfo",C,B>>
    [] pc = 128 -> /\ LeaderProcessACKEPOCH(B,C) /\ edge' = <<"AckEpoch",B,C>>
    [] pc = 129 -> /\ LeaderSyncFollower(B,C) /\ edge' = <<"Sync",B,C>>
    [] pc = 130 -> /\ FollowerProcessSyncMessage(C,B) /\ edge' = <<"SyncMessage",C,B>>
    [] pc = 131 -> /\ FollowerProcessNEWLEADER(C,B) /\ edge' = <<"NewLeader",C,B>>
    [] pc = 132 -> /\ LeaderProcessACKLD(B,C) /\ edge' = <<"AckLd",B,C>>
    [] pc = 133 -> /\ FollowerProcessUPTODATE(C,B) /\ edge' = <<"UpToDate",C,B>>
    [] pc = 134 -> /\ LeaderProcessRequest(B) /\ edge' = <<"Request",B,B>>
    [] pc = 135 -> /\ FollowerProcessPROPOSAL(C,B) /\ edge' = <<"Proposal",C,B>>
    [] pc = 136 -> /\ LeaderProcessACK(B,C) /\ edge' = <<"Ack",B,C>>
    [] pc = 137 -> /\ NodeStart(A) /\ edge' = <<"Start",A,A>>
    [] pc = 138 -> /\ FLEReceiveNotmsg(A,B) /\ edge' = <<"Receive",A,B>>
    [] pc = 139 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 140 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 141 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 142 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 143 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 144 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 145 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 146 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 147 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 148 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 149 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 150 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 151 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 152 -> /\ FLENotmsgTimeout(A) /\ edge' = <<"Timeout",A,A>>
    [] pc = 153 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 154 -> /\ FLEReceiveNotmsg(B,A) /\ edge' = <<"Receive",B,A>>
    [] pc = 155 -> /\ FLEReceiveNotmsg(C,A) /\ edge' = <<"Receive",C,A>>
    [] pc = 156 -> /\ FLEReceiveNotmsg(A,B) /\ edge' = <<"Receive",A,B>>
    [] pc = 157 -> /\ FLEReceiveNotmsg(A,C) /\ edge' = <<"Receive",A,C>>
    [] pc = 158 -> /\ FLEHandleNotmsg(A) /\ edge' = <<"Handle",A,A>>
    [] pc = 159 -> /\ ConnectAndFollowerSendFOLLOWERINFO(B,A) /\ edge' = <<"Connect",B,A>>
    [] pc = 160 -> /\ LeaderProcessFOLLOWERINFO(B,A) /\ edge' = <<"FollowerInfo",B,A>>
    [] pc = 161 -> /\ FollowerProcessLEADERINFO(A,B) /\ edge' = <<"LeaderInfo",A,B>>
    [] pc = 162 -> /\ LeaderProcessACKEPOCH(B,A) /\ edge' = <<"AckEpoch",B,A>>
    [] pc = 163 -> /\ LeaderSyncFollower(B,A) /\ edge' = <<"Sync",B,A>>
    [] pc = 164 -> /\ FollowerProcessSyncMessage(A,B) /\ edge' = <<"SyncMessage",A,B>>
    [] pc = 165 -> /\ FollowerProcessNEWLEADER(A,B) /\ edge' = <<"NewLeader",A,B>>
    [] pc = 166 -> /\ LeaderProcessACKLD(B,A) /\ edge' = <<"AckLd",B,A>>
    [] pc = 167 -> /\ FollowerProcessUPTODATE(A,B) /\ edge' = <<"UpToDate",A,B>>
    [] pc = 168 -> /\ FollowerProcessCOMMIT(C,B) /\ edge' = <<"Commit",C,B>>
    [] pc = 169 -> /\ NodeCrash(C) /\ edge' = <<"Crash",C,C>>
    [] pc = 170 -> /\ LeaderProcessRequest(B) /\ edge' = <<"Request",B,B>>
    [] pc = 171 -> /\ FollowerProcessPROPOSAL(A,B) /\ edge' = <<"Proposal",A,B>>
    [] pc = 172 -> /\ LeaderProcessACK(B,A) /\ edge' = <<"Ack",B,A>>
    [] pc = 173 -> /\ FollowerProcessCOMMIT(A,B) /\ edge' = <<"Commit",A,B>>
    [] pc = 174 -> /\ LeaderProcessRequest(B) /\ edge' = <<"Request",B,B>>
    [] pc = 175 -> /\ NodeStart(C) /\ edge' = <<"Start",C,C>>
    [] OTHER -> FALSE
GuidedInit == Init /\ pc = 0 /\ edge = <<"Stutter",A,A>>
GuidedNext == IF pc < 176 THEN /\ FixedAction /\ pc' = pc+1 ELSE /\ HealthyNext /\ lastCommitted'[B].index = lastCommitted[B].index /\ UNCHANGED pc
GuidedSpec == GuidedInit /\ [][GuidedNext]_<<vars,pc,edge>>
IndicesBounded == \A i \in Server: /\ lastCommitted[i].index <= Len(history[i]) /\ lastSnapshot[i].index <= Len(history[i])
====
