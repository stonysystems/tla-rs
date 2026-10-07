#!/usr/bin/env python3
"""Check that intentional protocol faults break the handwritten Verus proofs."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = [
    ("early_completion", "open_addressing.rs",
     "if c.fps.difference(s.history).is_empty() { LWriter { pc: Pc::Done, ..t } }",
     "if true { LWriter { pc: Pc::Done, ..t } }", "open_addressing_proof"),
    ("unsorted_flush", "open_addressing.rs",
     "newexternal: (s.newexternal + smaller(s.external, s.newexternal, x)).push(x)",
     "newexternal: (s.newexternal + smaller(s.external, s.newexternal, x)).push(-x)", "open_addressing_proof"),
    ("undefined_writeback", "flash.rs", "mem: s.wb.data, ..s", "mem: -1, ..s", "flash_proof"),
    ("nak_not_cleared", "flash.rs", "Action::ClearNak => LState { nakc: false,", "Action::ClearNak => LState { nakc: true,", "flash_liveness"),
    ("responder_ignores_pmap_lock", "tlb.rs",
     "t.pc == Pc::ResponderLockAction && !s.plock[t.userpmap]",
     "t.pc == Pc::ResponderLockAction", "tlb_proof"),
    ("release_votes_without_persisting", "etcd.rs",
     "disk: Disk { term: n.term, voted_for: n.voted_for, log: n.log, commit: n.commit }",
     "disk: n.disk", "etcd_election"),
    ("overlapping_configuration_changes", "hashicorp.rs",
     "n.committed_config_index == n.latest_config_index && n.commit > 0",
     "n.commit > 0", "hashicorp_config"),
    ("duplicate_exclusive_owner", "flash.rs",
     "if exclusive { invalid(s.procs[dst], false) } else { Proc { cache: Cache::S, ..s.procs[dst] } }",
     "if exclusive { s.procs[dst] } else { Proc { cache: Cache::S, ..s.procs[dst] } }", "flash_coherence"),
    ("stale_writeback", "flash.rs", "mem: s.wb.data, ..s", "mem: s.previous, ..s", "flash_coherence"),
    ("unlocked_forwarding", "flash.rs",
     "Action::LocalRelay { src, exclusive } => LState { dir: Dir { pending: true, ..d }",
     "Action::LocalRelay { src, exclusive } => LState { dir: Dir { pending: false, ..d }", "flash_control"),
    ("acknowledge_without_invalidating", "flash.rs",
     "Action::Invalidate { dst } => LState { inv: s.inv.insert(dst, Inv::Ack), procs: s.procs.insert(dst, invalid(s.procs[dst], true)), ..s }",
     "Action::Invalidate { dst } => LState { inv: s.inv.insert(dst, Inv::Ack), ..s }", "flash_shared"),
    ("invalidation_not_acknowledged", "flash.rs",
     "Action::Invalidate { dst } => LState { inv: s.inv.insert(dst, Inv::Ack)",
     "Action::Invalidate { dst } => LState { inv: s.inv.insert(dst, Inv::Inv)", "flash_invalidation"),
    ("reply_not_consumed", "flash.rs",
     "Action::ReceiveNak { dst } => LState { uni: s.uni.insert(dst, no_uni())",
     "Action::ReceiveNak { dst } => LState { uni: s.uni", "flash_requests"),
    ("directory_lock_not_released", "flash.rs",
     "dir: if remaining.is_empty() { Dir { invalidating: remaining, pending: false",
     "dir: if remaining.is_empty() { Dir { invalidating: remaining, pending: true", "flash_directory"),
    ("invent_log_entry_term", "etcd.rs",
     "log: n.log + sub(entries, n.log.len()-index+2, entries.len() as int)",
     "log: n.log.push(n.term+1)", "etcd_origins"),
    ("quiescence_keeps_work", "tlb.rs",
     "Step::WaitQuiescence(q) => replace(s, p, LProcessor { todo: t.todo.remove(q), ..t })",
     "Step::WaitQuiescence(q) => replace(s, p, LProcessor { todo: t.todo, ..t })", "tlb_quiescence"),
    ("pmap_lock_not_released", "tlb.rs",
     "Step::UnlockPmap => LState { plock: s.plock.insert(t.writepmap, false)",
     "Step::UnlockPmap => LState { plock: s.plock.insert(t.writepmap, true)", "tlb_progress"),
    ("append_ignores_previous_term", "etcd.rs",
     "n.role == Role::Follower && log_ok(n, prev, prev_term) && match how",
     "n.role == Role::Follower && match how", "etcd_logs"),
    ("overwrite_positive_entry", "open_addressing.rs",
     "Pc::Cas => if s.table[idx(c, t.fp, t.index)] == t.expected {",
     "Pc::Cas => if true {", "open_addressing_contains"),
    ("skip_matching_fingerprint", "open_addressing.rs",
     "Pc::IsMth => if matches(s.table[idx(c, t.fp, t.index)], t.fp)",
     "Pc::IsMth => if false", "open_addressing_scanning"),
    ("flush_without_marking", "open_addressing.rs",
     "table: s.table.insert(wrap(t.ei, c.k), Cell::Value(-x))",
     "table: s.table.insert(wrap(t.ei, c.k), Cell::Value(x))", "open_addressing_consistency"),
    ("release_append_without_log_persistence", "etcd.rs",
     "disk: Disk { term: n.term, voted_for: n.voted_for, log: n.log, commit: n.commit }",
     "disk: Disk { term: n.term, voted_for: n.voted_for, log: n.disk.log, commit: n.commit }", "etcd_acknowledgments"),
    ("commit_without_acknowledgment_quorum", "etcd.rs",
     "filter(|index: int| quorum(c.voters.filter(|k: int| n.matched[k] >= index), c))",
     "filter(|index: int| true)", "etcd_commit_history"),
    ("vote_without_log_comparison", "etcd.rs",
     "m.term == n.term && up_to_date(n, term, len) && (n.voted_for == None || n.voted_for == Some(m.source))",
     "m.term == n.term && (n.voted_for == None || n.voted_for == Some(m.source))", "etcd_vote_witness"),
    ("truncate_two_entries_on_conflict", "etcd.rs",
     "log: sub(n.log, 1, n.log.len()-1)", "log: sub(n.log, 1, n.log.len()-2)", "etcd_retention"),
    ("heartbeat_commit_without_match", "etcd.rs",
     "commit: if mode == Mode::Heartbeat { min(n.commit, n.matched[j]) }",
     "commit: if mode == Mode::Heartbeat { n.commit }", "etcd_leader_trace"),
    ("hashicorp_vote_without_persistence", "hashicorp.rs",
     "LServer { voted_for: Some(m.source), persisted_vote_term: m.term, persisted_voted_for: Some(m.source), ..n }",
     "LServer { voted_for: Some(m.source), ..n }", "hashicorp_votes"),
    ("hashicorp_double_vote", "hashicorp.rs",
     "up_to_date(n.log, term, len) && (m.term > n.term || m.term == n.term && (n.voted_for == None || n.voted_for == Some(m.source)))",
     "up_to_date(n.log, term, len) && m.term >= n.term", "hashicorp_votes"),
    ("hashicorp_append_without_previous_term", "hashicorp.rs",
     "Receive::AcceptAppend => m.term >= n.term && log_ok(n,prev,prev_term)",
     "Receive::AcceptAppend => m.term >= n.term", "hashicorp_prefixes"),
    ("hashicorp_acknowledge_unstored_suffix", "hashicorp.rs",
     "matched: prev+entries.len() })",
     "matched: prev+entries.len()+1 })", "hashicorp_replication"),
    ("hashicorp_vote_without_log_comparison", "hashicorp.rs",
     "up_to_date(n.log, term, len) && (m.term > n.term || m.term == n.term && (n.voted_for == None || n.voted_for == Some(m.source)))",
     "m.term > n.term || m.term == n.term && (n.voted_for == None || n.voted_for == Some(m.source))", "hashicorp_vote_witness"),
    ("hashicorp_config_without_current_term_commit", "hashicorp.rs",
     "n.commit > 0 && n.log[n.commit-1].term == n.term",
     "n.commit > 0", "hashicorp_commit_trace"),
    ("hashicorp_premature_config_commit", "hashicorp.rs",
     "let cc=if n.latest_config_index <= ci { n.latest_config_index } else { n.committed_config_index };",
     "let cc=n.latest_config_index;", "hashicorp_config_commit"),
    ("zab_shutdown_retains_messages", "zab.rs",
     "if q.contains(p.1) { Seq::empty() } else { s.msgs[p] }",
     "s.msgs[p]", "zab_connections"),
    ("zab_accepts_stale_epoch", "zab.rs",
     "if e < n.accepted { clean(remove_learner(shut_follower(s,i),j,i),i,j) }",
     "if false { clean(remove_learner(shut_follower(s,i),j,i),i,j) }", "zab_epochs"),
    ("zab_old_leader_reconnects", "zab.rs",
     "&& s.nodes[j].leader == None && s.oracle == Some(i)",
     "&& s.nodes[j].leader == None", "zab_sessions"),
    ("zab_broadcast_before_sync", "zab.rs",
     "i,ae_connected(n.ae),Message::Propose(t.zxid,t.value)",
     "i,ce_connected(n.ce),Message::Propose(t.zxid,t.value)", "zab_sync"),
    ("zab_follower_changes_value", "zab.rs",
     "history: n.history.push(Txn { zxid: z,value: v,ack: Set::empty(),epoch: n.current })",
     "history: n.history.push(Txn { zxid: z,value: v+1,ack: Set::empty(),epoch: n.current })", "zab_current_logs"),
    ("zab_ack_without_storage", "zab.rs",
     "reply(replace(s,i,LServer { history: n.history.push(Txn { zxid: z,value: v,ack: Set::empty(),epoch: n.current }),..n }),i,j,Message::Ack(z))",
     "reply(s,i,j,Message::Ack(z))", "zab_ack_messages"),
    ("zab_omit_sync_ack", "zab.rs",
     "Txn { ack: h[k].ack.insert(i),..h[k] }",
     "Txn { ack: h[k].ack,..h[k] }", "zab_log_math"),
    ("zab_commit_names_missing_entry", "zab.rs",
     "if first { discard_broadcast(t,i,j,al_connected(al),Message::CommitLd(last(n.history))) }",
     "if first { discard_broadcast(t,i,j,al_connected(al),Message::CommitLd(Zxid { epoch: n.current,counter: n.sent+1 })) }", "zab_commit_delivery"),
    ("zab_skips_inherited_commit", "zab.rs",
     "committed: if first { Commit { index: n.history.len() as int,zxid: last(n.history) } }",
     "committed: if first { Commit { index: n.history.len() as int-1,zxid: last(n.history) } }", "zab_primary_barrier"),
    ("zab_broadcast_omits_proposal_record", "zab.rs",
     "proposals: s.proposals.insert(Proposal { source: i,epoch: n.current,zxid: t.zxid,value: t.value })",
     "proposals: s.proposals", "zab_proposal_records"),
    ("zab_proposal_records_wrong_epoch", "zab.rs",
     "proposals: s.proposals.insert(Proposal { source: i,epoch: n.current,zxid: t.zxid,value: t.value })",
     "proposals: s.proposals.insert(Proposal { source: i,epoch: n.current+1,zxid: t.zxid,value: t.value })", "zab_proposal_order"),
    ("cahill_abort_keeps_waiter", "cahill.rs",
     "if q.contains(r) { blank() } else if r == t",
     "if q.contains(r) { LTxn { waiting: s.txns[r].waiting,..blank() } } else if r == t", "cahill_support"),
    ("cahill_keeps_deadlock_cycle", "cahill.rs",
     "else if !deadlocked(s,c,t,k) { LState { txns: s.txns.insert(t,LTxn { waiting: Some(k),..s.txns[t] }),..s } }",
     "else if true { LState { txns: s.txns.insert(t,LTxn { waiting: Some(k),..s.txns[t] }),..s } }", "cahill_deadlocks"),
    ("cahill_acquires_owned_lock", "cahill.rs",
     "else if !locked(s,c,k) { acquire(s,c,t,k) }",
     "else if true { acquire(s,c,t,k) }", "cahill_locks"),
    ("cahill_commits_with_both_flags", "cahill.rs",
     "if s.txns[t].incoming && s.txns[t].outgoing { abort(s,t,Reason::CommitConflict) } else {",
     "if false { abort(s,t,Reason::CommitConflict) } else {", "cahill_conflicts"),
    ("cahill_read_omits_newer_writer_flag", "cahill.rs",
     "incoming: s.txns[r].incoming || newer.contains(r) || others.contains(r)",
     "incoming: s.txns[r].incoming || others.contains(r)", "cahill_overlap_access"),
    ("cahill_write_omits_reader_flag", "cahill.rs",
     "outgoing: s.txns[r].outgoing || readers.contains(r)",
     "outgoing: s.txns[r].outgoing", "cahill_overlap_access"),
    ("cahill_ignores_prior_committed_writer", "cahill.rs",
     "if !writers_since(s,t,k).is_empty() {",
     "if false {", "cahill_first_committer"),
    ("mongodb_changes_request_read_timestamp", "mongodb.rs",
     "read_ts: rtx.read_ts };",
     "read_ts: rtx.read_ts+1 };", "mongodb_read_time"),
    ("mongodb_ignores_prepare_blocking", "mongodb.rs",
     "kind == Kind::Read && !prepare_conflict(s.shards[i],c,t,k) &&",
     "kind == Kind::Read && true &&", "mongodb_prepare_barrier"),
    ("mongodb_ignores_write_conflicts", "mongodb.rs",
     "let conflict=write_conflict(s.shards[i],c,t,k);",
     "let conflict=false;", "mongodb_write_conflicts"),
    ("mongodb_changes_participants_after_commit_starts", "mongodb.rs",
     "&& !any_aborted(s,c,t) && !s.routers[r][t].committing && s.routers[r][t].read_ts != c.no_value",
     "&& !any_aborted(s,c,t) && s.routers[r][t].read_ts != c.no_value", "mongodb_participants"),
    ("mongodb_vote_changes_prepare_timestamp", "mongodb.rs",
     "Vote { shard: m.shard,txn: m.txn,to: m.coordinator,ts }",
     "Vote { shard: m.shard,txn: m.txn,to: m.coordinator,ts: ts+1 }", "mongodb_votes"),
    ("zk_notification_forges_sender", "zk_election.rs",
     "Notification { source: i,role: n.role,round: n.clock,vote: n.vote }",
     "Notification { source: i+1,role: n.role,round: n.clock,vote: n.vote }", "zk_election_types"),
    ("zookeeper_receipt_changes_server_id", "zookeeper.rs",
     "else { q.insert(Electing { sid: j,zxid,quorum: yes }) }",
     "else { q.insert(Electing { sid: j+1,zxid,quorum: yes }) }", "zookeeper_receipt_sets"),
    ("zookeeper_records_wrong_leader", "zookeeper.rs",
     "s.epoch_leader[n.accepted].insert(i)",
     "s.epoch_leader[n.accepted].insert(i+1)", "zookeeper_leadership"),
    ("zookeeper_forgets_positive_epoch_receipt", "zookeeper.rs",
     "quorum: yes || old.quorum", "quorum: yes", "zookeeper_quorum_receipts"),
    ("zookeeper_omits_sync_mode_header", "zookeeper.rs",
     "Mode::Diff => Message::Diff(zxid)",
     "Mode::Diff => Message::Proposal(zxid,0)", "zookeeper_pending_mode"),
    ("zookeeper_sync_rewrites_history", "zookeeper.rs",
     "Txn { ack: h[k].ack.insert(j),..h[k] }",
     "Txn { value: h[k].value+1,ack: h[k].ack.insert(j),..h[k] }", "zookeeper_leader_logs"),
    ("zookeeper_reuses_transaction_counter", "zookeeper.rs",
     "counter: if old.epoch == e.current { old.counter+1 } else { 1 }",
     "counter: if old.epoch == e.current { old.counter } else { 1 }", "zookeeper_log_order"),
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--verus", default=os.environ.get("VERUS_PATH", "verus"))
    ap.add_argument("--output", type=Path, default=ROOT / "reports/tlaps_bench_manual/controls")
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--only", action="append", help="Run only the named control; repeat to select several.")
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, filename, before, after, module in CONTROLS:
        if args.only and name not in args.only:
            continue
        with tempfile.TemporaryDirectory(prefix="tlaps-manual-control-") as temp:
            root = Path(temp)
            target = root / "src/protocol/TLAPSBench"
            shutil.copytree(ROOT / "src/protocol/TLAPSBench", target)
            shutil.copy2(ROOT / "src/protocol/tlaps_bench_harness.rs", target.parent)
            common = root / "src/common/logic"
            common.mkdir(parents=True)
            shutil.copy2(ROOT / "src/common/logic/temporal_s.rs", common)
            path = target / filename
            text = path.read_text()
            if text.count(before) != 1:
                raise RuntimeError(f"{name}: expected exactly one mutation location")
            path.write_text(text.replace(before, after))
            command = [args.verus, "--crate-type=lib", "--no-cheating", "--triggers-mode", "silent",
                       "--rlimit", "30", "--num-threads", "4", "-V", "spinoff-all",
                       "--verify-only-module", f"TLAPSBench::{module}",
                       str(root / "src/protocol/tlaps_bench_harness.rs")]
            try:
                run = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, timeout=args.timeout)
                output = run.stdout
                # A timeout, parse failure, or resource limit alone is not a successful control.
                rejected = run.returncode != 0 and bool(re.search(
                    r"error: (?:assertion failed|postcondition not satisfied|precondition not satisfied)", output))
                result = {"control": name, "rejected_by_proof": rejected, "exit_code": run.returncode}
            except subprocess.TimeoutExpired as exc:
                output = (exc.stdout or b"").decode() if isinstance(exc.stdout, bytes) else exc.stdout or ""
                result = {"control": name, "rejected_by_proof": False, "timed_out": True}
            (args.output / f"{name}.log").write_text(output)
            results.append(result)
            print(json.dumps(result), flush=True)
    (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    return 0 if all(r["rejected_by_proof"] for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
