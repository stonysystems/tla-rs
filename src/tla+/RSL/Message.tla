---- MODULE Message ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

RslMessage ==
    {RslMessageInvalid, RslMessageRequest, RslMessage1a, RslMessage1b, RslMessage2a, RslMessage2b, RslMessageHeartbeat, RslMessageReply, RslMessageAppStateRequest, RslMessageAppStateSupply, RslMessageStartingPhase2}

====
