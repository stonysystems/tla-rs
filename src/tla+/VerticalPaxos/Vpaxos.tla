---- MODULE Vpaxos ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS State, Constants

Init(s, c) ==
    /\ s.config_num = 0
    /\ s.max_bal = 0
    /\ s.max_v_bal = 0
    /\ s.max_val = 0
    /\ s.has_voted = FALSE
    /\ s.is_active = TRUE
    /\ c.quorum_size >= 1
    /\ c.num_nodes >= c.quorum_size

Prepare(s, s_, c, b) ==
    /\ s.is_active = TRUE
    /\ b > s.max_bal
    /\ s_.max_bal = b
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = s.has_voted
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active

Accept(s, s_, c, b, v) ==
    /\ s.is_active = TRUE
    /\ b = s.max_bal
    /\ b > s.max_v_bal
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = b
    /\ s_.max_val = v
    /\ s_.has_voted = TRUE
    /\ s_.config_num = s.config_num
    /\ s_.is_active = s.is_active

Reconfigure(s, s_, c) ==
    /\ s.is_active = TRUE
    /\ s_.config_num = s.config_num + 1
    /\ s_.max_bal = 0
    /\ s_.max_v_bal = 0
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = FALSE
    /\ s_.is_active = TRUE

Sync(s, s_, c, new_config, val) ==
    /\ s.is_active = FALSE
    /\ new_config > s.config_num
    /\ s_.config_num = new_config
    /\ s_.max_bal = 0
    /\ s_.max_v_bal = 0
    /\ s_.max_val = val
    /\ s_.has_voted = FALSE
    /\ s_.is_active = TRUE

Deactivate(s, s_, c) ==
    /\ s.is_active = TRUE
    /\ s_.config_num = s.config_num
    /\ s_.max_bal = s.max_bal
    /\ s_.max_v_bal = s.max_v_bal
    /\ s_.max_val = s.max_val
    /\ s_.has_voted = s.has_voted
    /\ s_.is_active = FALSE

Next(s, s_, c) ==
    \/ \E b \in Int : Prepare(s, s_, c, b)
    \/ \E b \in Int, v \in Int : Accept(s, s_, c, b, v)
    \/ Reconfigure(s, s_, c)
    \/ \E new_config \in Int, val \in Int : Sync(s, s_, c, new_config, val)
    \/ Deactivate(s, s_, c)

====
