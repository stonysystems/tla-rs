# Coverage and scope decisions

The catalog is provisional. A search result, a fetched proceedings page and a
completed paper-level screening decision are different kinds of evidence.
The [coverage ledger](coverage.json) records the work actually performed.

| Venue | Work performed | Remaining census work |
|---|---|---|
| OSDI | Retrieved and keyword-screened the 11 technical programs from 2012 through 2026; checked selected earlier papers | Enumerate 1996, 1999, 2000, 2002, 2004, 2006, 2008 and 2010; inspect abstracts beyond title matches |
| NSDI | Retrieved and keyword-screened all 15 technical programs from 2012 through 2026; checked selected 2004 and 2011 papers | Enumerate 2004 through 2011; complete abstract screening |
| SOSP | Targeted paper discovery; retrieved 2023 and 2025 program pages | All editions need a complete census. The attempted 2024 program URL returned 404 and proves no absence of relevant papers |
| SIGMOD | Targeted discovery, primary paper checks, and the official 2021 accepted-paper list for PigPaxos | Enumerate 1997 through 2026 research and full industry papers, including PACMMOD since 2023 |
| VLDB | Retrieved PVLDB volumes 1 through 19, spanning conference editions 2008 through 2026; keyword-screened 5,211 paginated records and obtained 197 candidates | Screen all relevant abstracts and protocol sections, classify the remaining candidates, and enumerate 1997 through 2007 proceedings |

The September 26, 1996 cutoff requires checking exact dates for boundary-year
editions. [OSDI 1996](https://www.usenix.org/legacy/publications/library/proceedings/osdi96/)
ran October 28–31 and falls after the cutoff. Earlier 1996 SIGMOD/VLDB editions
fall before it. NSDI began in 2004.
[SOSP 2026](https://sigops.org/s/conferences/sosp/2026/) starts September 29,
after this ledger's cutoff; no forthcoming papers were included here.

The PVLDB title count includes paginated material of different publication
types. It is not a count of eligible research papers. Title screening cannot
establish completeness: for example, a system paper can introduce a consensus
variant without mentioning consensus in its title. The JSON ledger's keywords
describe the PVLDB pass. The USENIX pass used a related, narrower filter for
consensus, replication, Paxos, Raft, shared logs, fault tolerance and commitment.

The source snapshots are outside the repository. [sources.json](sources.json)
records retrieved URLs, formats, dates and digests for all 52 included records.
Retrieval does not mean that every section was read. The per-paper `source_review`
field distinguishes abstract/selected-section screening from the detailed
review used for a formalization. PDFs were fetched from publishers or authors.
The linked arXiv versions must be reconciled with the final versions before
modeling. No copyrighted paper PDFs are checked into the repository.

## Common venue mistakes

These related works are outside the five requested venues. They may supply
proof dependencies, but they must not inflate the catalog.

| Work | Actual venue |
|---|---|
| [Raft](https://www.usenix.org/conference/atc14/technical-sessions/presentation/ongaro) | USENIX ATC 2014 |
| [The Part-Time Parliament](https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf) | TOCS 1998 |
| [Flexible Paxos](https://arxiv.org/abs/1608.06696) | OPODIS 2016 |
| [Omni-Paxos](https://2023.eurosys.org/program.html) | EuroSys 2023 |
| [ZooKeeper](https://www.usenix.org/legacy/events/atc10/tech/full_papers/Hunt.pdf) | USENIX ATC 2010 |
| [FlexiRaft](https://vldb.org/cidrdb/2023/flexiraft-flexible-quorums-with-raft.html) | CIDR 2023; hosting under vldb.org does not make it VLDB |

Byzantine and hybrid arbitrary-fault protocols are excluded under the current
benign-fault scope. An implementation or verification paper about an unchanged
consensus algorithm also fails the user's protocol-contribution criterion.
The catalog separately records disputed cases and specific exclusions with
their sources. Those decisions can change after a fuller paper review.

## Completion criterion for the census

Before changing `exhaustive` to true, enumerate every eligible proceedings
edition and every full paper, retain a stable identifier for each screened
record, and assign an inclusion or exclusion reason. Check references and
subsequent corrections of included protocols. Resolve all pending cases and
review title-negative candidates by abstract. Finally audit venue, edition,
publication type and version. This pass has not completed those steps.
