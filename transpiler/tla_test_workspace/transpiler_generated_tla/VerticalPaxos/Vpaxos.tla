---- MODULE Vpaxos ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants, VPMessage

Init(s, c) ==
    /\ s.config_num = 0
    /\ s.max_bal = 0
    /\ s.max_v_bal = 0
    /\ s.max_val = 0
    /\ s.has_voted = FALSE
    /\ s.is_active = TRUE
    /\ s.promises_rcvd = {}
    /\ s.accepts_rcvd = {}
    /\ s.committed = FALSE
    /\ s.committed_val = 0
    /\ s.witness_val = 0
    /\ s.has_witness = FALSE
    /\ c.quorum_size >= 1
    /\ c.num_nodes >= c.quorum_size

Prepare(s, s_, c, b, sent_packets) ==
    /\ s.is_active = TRUE
    /\ b > s.max_bal
    /\ s_.max_bal = b
    /\ sent_packets = <<[bal |-> b]>>
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = s.has_voted
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

SendPromise(s, s_, c, prepare_bal, sent_packets) ==
    /\ s.is_active = TRUE
    /\ prepare_bal > s.max_bal
    /\ s_.max_bal = prepare_bal
    /\ sent_packets = <<[bal |-> prepare_bal, v_bal |-> s.max_v_bal, val |-> s.max_val]>>
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = s.has_voted
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

ReceivePromise(s, s_, c, sender, promise_bal, promise_v_bal, promise_val, sent_packets) ==
    /\ s.is_active = TRUE
    /\ promise_bal = s.max_bal
    /\ ~sender \in s.promises_rcvd
    /\ s_.promises_rcvd = s.promises_rcvd \cup {sender}
    /\ s_.max_v_bal = IF promise_v_bal > s.max_v_bal THEN promise_v_bal ELSE s.max_v_bal
    /\ s_.max_val = IF promise_v_bal > s.max_v_bal THEN promise_val ELSE s.max_val
    /\ sent_packets = <<>>
    /\ s_.max_bal = s.max_bal
    /\ s_.has_voted = s.has_voted
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

Accept(s, s_, c, b, v, sent_packets) ==
    /\ s.is_active = TRUE
    /\ b = s.max_bal
    /\ b > s.max_v_bal
    /\ s_.max_v_bal = b
    /\ s_.max_val = v
    /\ s_.has_voted = TRUE
    /\ sent_packets = <<[bal |-> b, val |-> v]>>
    /\ s_.max_bal = s.max_bal
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

ReceiveAccepted(s, s_, c, sender, accept_bal, sent_packets) ==
    /\ s.is_active = TRUE
    /\ accept_bal = s.max_bal
    /\ ~sender \in s.accepts_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd \cup {sender}
    /\ sent_packets = <<>>
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = s.has_voted
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

Commit(s, s_, c, sent_packets) ==
    /\ s.is_active = TRUE
    /\ s.committed = FALSE
    /\ Len(s.accepts_rcvd) >= c.quorum_size
    /\ s_.committed = TRUE
    /\ s_.committed_val = s.max_val
    /\ sent_packets = <<>>
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = s.has_voted
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

Reconfigure(s, s_, c, sent_packets) ==
    /\ s.is_active = TRUE
    /\ s_.config_num = s.config_num + 1
    /\ s_.max_bal = 0
    /\ s_.max_v_bal = 0
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = FALSE
    /\ s_.is_active = TRUE
    /\ s_.promises_rcvd = {}
    /\ s_.accepts_rcvd = {}
    /\ sent_packets = <<>>
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

WitnessSync(s, s_, c, witness_val, sent_packets) ==
    /\ s.is_active = TRUE
    /\ s_.has_witness = TRUE
    /\ s_.witness_val = witness_val
    /\ s_.max_val = IF ~s.has_voted THEN witness_val ELSE s.max_val
    /\ sent_packets = <<>>
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.has_voted = s.has_voted
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val

Sync(s, s_, c, new_config, val, sent_packets) ==
    /\ s.is_active = FALSE
    /\ new_config > s.config_num
    /\ s_.config_num = new_config
    /\ s_.max_bal = 0
    /\ s_.max_v_bal = 0
    /\ s_.max_val = val
    /\ s_.has_voted = FALSE
    /\ s_.is_active = TRUE
    /\ s_.promises_rcvd = {}
    /\ s_.accepts_rcvd = {}
    /\ s_.committed = FALSE
    /\ s_.committed_val = 0
    /\ s_.witness_val = 0
    /\ s_.has_witness = FALSE
    /\ sent_packets = <<>>

Deactivate(s, s_, c, sent_packets) ==
    /\ s.is_active = TRUE
    /\ s_.is_active = FALSE
    /\ sent_packets = <<>>
    /\ s_.config_num = s.config_num
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = s.has_voted
    /\ s_.promises_rcvd = s.promises_rcvd
    /\ s_.accepts_rcvd = s.accepts_rcvd
    /\ s_.committed = s.committed
    /\ s_.committed_val = s.committed_val
    /\ s_.witness_val = s.witness_val
    /\ s_.has_witness = s.has_witness

Next(s, s_, c) ==
    \/ \E b \in Int, sent_packets \in Seq(VPMessage) : Prepare(s, s_, c, b, sent_packets)
    \/ \E prepare_bal \in Int, sent_packets \in Seq(VPMessage) : SendPromise(s, s_, c, prepare_bal, sent_packets)
    \/ \E sender \in Int, promise_bal \in Int, promise_v_bal \in Int, promise_val \in Int, sent_packets \in Seq(VPMessage) : ReceivePromise(s, s_, c, sender, promise_bal, promise_v_bal, promise_val, sent_packets)
    \/ \E b \in Int, v \in Int, sent_packets \in Seq(VPMessage) : Accept(s, s_, c, b, v, sent_packets)
    \/ \E sender \in Int, accept_bal \in Int, sent_packets \in Seq(VPMessage) : ReceiveAccepted(s, s_, c, sender, accept_bal, sent_packets)
    \/ \E sent_packets \in Seq(VPMessage) : Commit(s, s_, c, sent_packets)
    \/ \E sent_packets \in Seq(VPMessage) : Reconfigure(s, s_, c, sent_packets)
    \/ \E witness_val \in Int, sent_packets \in Seq(VPMessage) : WitnessSync(s, s_, c, witness_val, sent_packets)
    \/ \E new_config \in Int, val \in Int, sent_packets \in Seq(VPMessage) : Sync(s, s_, c, new_config, val, sent_packets)
    \/ \E sent_packets \in Seq(VPMessage) : Deactivate(s, s_, c, sent_packets)

====
