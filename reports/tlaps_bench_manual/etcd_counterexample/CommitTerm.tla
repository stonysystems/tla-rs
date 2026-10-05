---- MODULE CommitTerm ----
EXTENDS etcd_raftDefs
VARIABLE pc
Step(n, A) == pc = n /\ pc' = n+1 /\ A
Recv(src,dst,ty) == \E m \in DOMAIN messages :
    /\ m.msource = src /\ m.mdest = dst /\ m.mtype = ty /\ Receive(m)
ReplyRecv(src,dst,ty) == \E m \in DOMAIN messages :
    /\ m.msource = src /\ m.mdest = dst /\ m.mtype = ty /\ Receive(m)
    /\ pendingMessages' # pendingMessages
SInit == Init /\ pc = 0
SNext ==
  \/ Step(0, Timeout(1))
  \/ Step(1, RequestVote(1,1))
  \/ Step(2, RequestVote(1,3))
  \/ Step(3, Ready(1))
  \/ Step(4, Recv(1,1,RequestVoteResponse))
  \/ Step(5, Recv(1,3,RequestVoteRequest))
  \/ Step(6, Recv(1,3,RequestVoteRequest))
  \/ Step(7, Ready(3))
  \/ Step(8, Recv(3,1,RequestVoteResponse))
  \/ Step(9, BecomeLeader(1))
  \/ Step(10, ClientRequest(1,0))
  \/ Step(11, Ready(1))
  \/ Step(12, Timeout(2))
  \/ Step(13, Timeout(2))
  \/ Step(14, RequestVote(2,2))
  \/ Step(15, RequestVote(2,3))
  \/ Step(16, Ready(2))
  \/ Step(17, Recv(2,2,RequestVoteResponse))
  \/ Step(18, Recv(2,3,RequestVoteRequest))
  \/ Step(19, Recv(2,3,RequestVoteRequest))
  \/ Step(20, Ready(3))
  \/ Step(21, Recv(3,2,RequestVoteResponse))
  \/ Step(22, BecomeLeader(2))
  \/ Step(23, ClientRequest(2,0))
  \/ Step(24, Ready(2))
  \/ Step(25, StepDownToFollower(1))
  \/ Step(26, Timeout(1))
  \/ Step(27, Timeout(1))
  \/ Step(28, RequestVote(1,1))
  \/ Step(29, RequestVote(1,3))
  \/ Step(30, Ready(1))
  \/ Step(31, Recv(1,1,RequestVoteResponse))
  \/ Step(32, Recv(1,3,RequestVoteRequest))
  \/ Step(33, Recv(1,3,RequestVoteRequest))
  \/ Step(34, Ready(3))
  \/ Step(35, Recv(3,1,RequestVoteResponse))
  \/ Step(36, BecomeLeader(1))
  \/ Step(37, ClientRequest(1,0))
  \/ Step(38, AppendEntriesToSelf(1))
  \/ Step(39, AppendEntries(1,3,<<1,3>>))
  \/ Step(40, Ready(1))
  \/ Step(41, Recv(1,1,AppendEntriesResponse))
  \/ Step(42, Recv(1,3,AppendEntriesRequest))
  \/ Step(43, ReplyRecv(1,3,AppendEntriesRequest))
  \/ Step(44, Ready(3))
  \/ Step(45, Recv(3,1,AppendEntriesResponse))
  \/ Step(46, AdvanceCommitIndex(1))
  \/ (pc = 47 /\ UNCHANGED <<pc,vars>>)
SSpec == SInit /\ [][SNext]_<<pc,vars>> /\ WF_<<pc,vars>>(SNext)
Reached == <>(pc = 47)
FinalWitness == pc = 47 =>
    /\ currentTerm[1] = 3 /\ state[1] = Leader /\ commitIndex[1] = 2
    /\ log[1][1].term = 1 /\ log[1][2].term = 3
    /\ currentTerm[2] = 2 /\ state[2] = Leader /\ log[2][1].term = 2
    /\ ~LeaderCompletenessInv
====
