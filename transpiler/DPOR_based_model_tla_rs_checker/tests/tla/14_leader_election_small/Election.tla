---- MODULE Election ----
\* Hand-written single-node Bully leader-election spec for DPOR case 14.
\* Replaces the prior verus2tla-emitted parameterized Init/Next that TLC
\* could not enumerate without a wrapper. This version uses TLC-native
\* VARIABLES + Init/Next so the case runs directly under TLC.
\*
\* Models one node's local view during a Bully election. Other nodes are
\* abstracted as nondeterministic event sources via existential
\* quantification over Nodes in Next.

EXTENDS Naturals, FiniteSets

VARIABLE electing, has_leader, leader, alive,
         has_highest, highest_heard,
         waiting_answer, waiting_node

Nodes == {1, 2}

Init ==
    /\ electing = {}
    /\ has_leader = FALSE
    /\ leader = 0
    /\ alive = Nodes
    /\ has_highest = FALSE
    /\ highest_heard = 0
    /\ waiting_answer = FALSE
    /\ waiting_node = 0

DetectFailure(node) ==
    /\ node \in alive
    /\ has_leader = TRUE
    /\ leader \notin alive
    /\ electing' = electing \cup {node}
    /\ waiting_answer' = TRUE
    /\ waiting_node' = node
    /\ has_leader' = has_leader
    /\ leader' = leader
    /\ alive' = alive
    /\ has_highest' = has_highest
    /\ highest_heard' = highest_heard

StartElection(node) ==
    /\ node \in alive
    /\ electing' = electing \cup {node}
    /\ has_leader' = FALSE
    /\ leader' = 0
    /\ waiting_answer' = TRUE
    /\ waiting_node' = node
    /\ alive' = alive
    /\ has_highest' = has_highest
    /\ highest_heard' = highest_heard

SendAnswer(node, sender) ==
    /\ node \in alive
    /\ node > sender
    /\ electing' = electing \cup {node}
    /\ has_highest' = TRUE
    /\ highest_heard' = IF (~has_highest) \/ (node > highest_heard)
                        THEN node ELSE highest_heard
    /\ has_leader' = has_leader
    /\ leader' = leader
    /\ alive' = alive
    /\ waiting_answer' = waiting_answer
    /\ waiting_node' = waiting_node

ReceiveAnswer(node) ==
    /\ node \in alive
    /\ waiting_answer = TRUE
    /\ waiting_node = node
    /\ waiting_answer' = FALSE
    /\ waiting_node' = 0
    /\ electing' = electing \ {node}
    /\ has_leader' = has_leader
    /\ leader' = leader
    /\ alive' = alive
    /\ has_highest' = has_highest
    /\ highest_heard' = highest_heard

SendCoordinator(node) ==
    /\ node \in alive
    /\ node \in electing
    /\ waiting_answer = TRUE
    /\ waiting_node = node
    /\ has_leader' = TRUE
    /\ leader' = node
    /\ electing' = electing \ {node}
    /\ waiting_answer' = FALSE
    /\ waiting_node' = 0
    /\ alive' = alive
    /\ has_highest' = has_highest
    /\ highest_heard' = highest_heard

ReceiveCoordinator(node, new_leader) ==
    /\ node \in alive
    /\ has_leader' = TRUE
    /\ leader' = new_leader
    /\ electing' = electing \ {node}
    /\ alive' = alive
    /\ has_highest' = has_highest
    /\ highest_heard' = highest_heard
    /\ waiting_answer' = waiting_answer
    /\ waiting_node' = waiting_node

NodeFail(node) ==
    /\ node \in alive
    /\ alive' = alive \ {node}
    /\ electing' = electing \ {node}
    /\ has_leader' = IF has_leader /\ leader = node THEN FALSE ELSE has_leader
    /\ leader'     = IF has_leader /\ leader = node THEN 0 ELSE leader
    /\ waiting_answer' = IF waiting_answer /\ waiting_node = node
                         THEN FALSE ELSE waiting_answer
    /\ waiting_node'   = IF waiting_answer /\ waiting_node = node
                         THEN 0 ELSE waiting_node
    /\ has_highest' = has_highest
    /\ highest_heard' = highest_heard

Next ==
    \E n \in Nodes :
        \/ DetectFailure(n)
        \/ StartElection(n)
        \/ \E sndr \in Nodes : SendAnswer(n, sndr)
        \/ ReceiveAnswer(n)
        \/ SendCoordinator(n)
        \/ \E ldr \in Nodes : ReceiveCoordinator(n, ldr)
        \/ NodeFail(n)

SafetyElectingSubsetAlive ==
    \A n \in Nodes : n \in electing => n \in alive

SafetyWaitingNodeAliveWhenWaiting ==
    waiting_answer => waiting_node \in alive

SafetyNoWaitingImpliesClearedWaitingNode ==
    ~waiting_answer => waiting_node = 0

TypeOK ==
    /\ electing \subseteq Nodes
    /\ has_leader \in BOOLEAN
    /\ leader \in (Nodes \cup {0})
    /\ alive \subseteq Nodes
    /\ has_highest \in BOOLEAN
    /\ highest_heard \in (Nodes \cup {0})
    /\ waiting_answer \in BOOLEAN
    /\ waiting_node \in (Nodes \cup {0})

================================================================================
