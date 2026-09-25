impl CState {
    pub open spec fn valid(&self) -> bool {
        &&& self.role.valid()
        &&& match self.election_membership_phase {
            Some(phase) => phase.valid(),
            None => true,
        }
    }
}

/// Verified deep clone for the executable membership vector.
fn clone_membership_servers(
    servers: &Vec<u64>,
) -> (result: Vec<u64>)
    ensures
        result@ == servers@,
{
    let mut result = Vec::<u64>::new();
    let mut index: usize = 0;
    while index < servers.len()
        invariant
            index <= servers.len(),
            result@ == servers@.subrange(0, index as int),
        decreases servers.len() - index,
    {
        result.push(servers[index]);
        index += 1;
    }
    result
}

impl Clone for CMembershipConfig {
    fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        CMembershipConfig {
            servers: clone_membership_servers(&self.servers),
        }
    }
}

pub fn clone_membership_config(
    input: &CMembershipConfig,
) -> (result: CMembershipConfig)
    ensures
        result@ == input@,
{
    input.clone()
}

pub fn clone_membership_phase(
    input: &CMembershipPhase,
) -> (result: CMembershipPhase)
    ensures
        result@ == input@,
{
    input.clone()
}

pub fn clone_optional_membership_phase(
    input: &Option<CMembershipPhase>,
) -> (result: Option<CMembershipPhase>)
    ensures
        match result {
            Some(phase) => Some(membership_phase_view(phase@)),
            None => None,
        } == match input {
            Some(phase) => Some(membership_phase_view(phase@)),
            None => None,
        },
{
    match input {
        Some(phase) => Some(phase.clone()),
        None => None,
    }
}

impl Clone for CMembershipPhase {
    fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        match self {
            CMembershipPhase::Stable { config } => {
                CMembershipPhase::Stable {
                    config: config.clone(),
                }
            },
            CMembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                CMembershipPhase::Joint {
                    old_config: old_config.clone(),
                    new_config: new_config.clone(),
                }
            },
        }
    }
}

impl Clone for CLogValue {
    fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        match self {
            CLogValue::Data { value } => {
                CLogValue::Data {
                    value: *value,
                }
            },
            CLogValue::Configuration { phase } => {
                CLogValue::Configuration {
                    phase: phase.clone(),
                }
            },
        }
    }
}

impl Clone for CLogEntry {
    fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        CLogEntry {
            term: self.term,
            value: self.value,
            payload: self.payload.clone(),
        }
    }
}

impl Clone for CRaftMessage {
    fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        match self {
            CRaftMessage::RequestVote {
                term,
                candidate,
                last_log_index,
                last_log_term,
            } => CRaftMessage::RequestVote {
                term: *term,
                candidate: *candidate,
                last_log_index: *last_log_index,
                last_log_term: *last_log_term,
            },
            CRaftMessage::VoteResponse {
                term,
                granted,
                voter,
                voter_last_log_index,
                voter_last_log_term,
            } => CRaftMessage::VoteResponse {
                term: *term,
                granted: *granted,
                voter: *voter,
                voter_last_log_index: *voter_last_log_index,
                voter_last_log_term: *voter_last_log_term,
            },
            CRaftMessage::AppendEntries {
                term,
                leader,
                prev_index,
                prev_term,
                value,
                payload,
                has_entry,
                leader_commit,
            } => CRaftMessage::AppendEntries {
                term: *term,
                leader: *leader,
                prev_index: *prev_index,
                prev_term: *prev_term,
                value: *value,
                payload: payload.clone(),
                has_entry: *has_entry,
                leader_commit: *leader_commit,
            },
            CRaftMessage::AppendResponse {
                term,
                success,
                match_index,
                follower,
            } => CRaftMessage::AppendResponse {
                term: *term,
                success: *success,
                match_index: *match_index,
                follower: *follower,
            },
        }
    }
}

impl Clone for CRaftPacket {
    fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        CRaftPacket {
            src: self.src,
            dst: self.dst,
            msg: self.msg.clone(),
        }
    }
}
