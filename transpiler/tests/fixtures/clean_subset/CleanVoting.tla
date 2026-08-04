------------------------------ MODULE CleanVoting ----------------------------
(* A clean-subset reference spec (Phase 52.M0).

   Every rule of the contract is satisfied:
     C1  state / votes are per-node arrays; messages is the network.
     C2  every action reads only self's copy and the received message.
     C3  no write-only ghost state, no aggregation over Node.
     C4  messages is manipulated only by `\cup` (send) and `\` (discard),
         and every message carries src/dst.
     C5  Next is a disjunction of `\E self \in Node : Action(self)` plus one
         network-only environment action.

   Deliberately written without bulleted /\ lists so that it parses with the
   tla-rs TLA+ front-end. *)

EXTENDS Naturals, FiniteSets

CONSTANT Node

VARIABLE state, votes, messages

RequestVote(self) ==
    state[self] = "idle"
    /\ state' = [state EXCEPT ![self] = "candidate"]
    /\ messages' = messages \cup {[type |-> "req", src |-> self, dst |-> self]}
    /\ votes' = votes

GrantVote(self, m) ==
    m.dst = self
    /\ m.type = "req"
    /\ state[self] = "idle"
    /\ messages' = (messages \ {m}) \cup {[type |-> "vote", src |-> self, dst |-> m.src]}
    /\ state' = [state EXCEPT ![self] = "voted"]
    /\ votes' = votes

CountVote(self, m) ==
    m.dst = self
    /\ m.type = "vote"
    /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {m.src}]
    /\ messages' = messages \ {m}
    /\ state' = state

BecomeLeader(self) ==
    state[self] = "candidate"
    /\ Cardinality(votes[self]) * 2 > Cardinality(Node)
    /\ state' = [state EXCEPT ![self] = "leader"]
    /\ votes' = votes
    /\ messages' = messages

DropMessage(m) ==
    messages' = messages \ {m}
    /\ state' = state
    /\ votes' = votes

Init ==
    state = [i \in Node |-> "idle"]
    /\ votes = [i \in Node |-> {}]
    /\ messages = {}

Next ==
    (\E self \in Node : RequestVote(self))
    \/ (\E self \in Node : BecomeLeader(self))
    \/ (\E self \in Node : \E m \in messages : GrantVote(self, m))
    \/ (\E self \in Node : \E m \in messages : CountVote(self, m))
    \/ (\E m \in messages : DropMessage(m))

==============================================================================
