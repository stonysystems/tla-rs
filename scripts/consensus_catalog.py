#!/usr/bin/env python3
"""Validate the research ledger and render its human-readable catalog.

Use --check in review to reject stale output or broken local evidence links.
Bibliographic screening and paper/model correspondence still require review.
"""
import argparse
import json
from collections import Counter
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "docs/non-bft-consensus"
VENUES = {"OSDI", "SOSP", "NSDI", "SIGMOD", "VLDB"}


def render(data):
    papers = data["papers"]
    identifiers = [p["id"] for p in papers]
    assert len(identifiers) == len(set(identifiers)), "duplicate paper IDs"
    assert data["exhaustive"] is False, "exhaustiveness needs a completed census"
    assert data["paper_level_proofs_complete"] is False, "paper proofs remain open"
    for paper in papers:
        assert paper["venue"] in VENUES, paper["id"]
        assert 1996 <= paper["conference_year"] <= 2026, paper["id"]
        assert urlparse(paper["source_url"]).scheme == "https", paper["id"]
        for field in ("model_paths", "evidence_paths"):
            for name in paper[field]:
                path = (ROOT / name).resolve()
                assert path.is_relative_to(ROOT), name
                assert path.exists(), f"missing {paper['id']} evidence: {name}"
        for related in paper.get("related_ids", []):
            assert related in identifiers, related

    counts = Counter(p["venue"] for p in papers)
    lines = [
        "# Non-BFT consensus paper catalog", "",
        "Generated from [catalog.json](catalog.json) by "
        "`python3 scripts/consensus_catalog.py`.", "",
        f"As of {data['as_of']}: {len(papers)} included records, "
        f"{len(data['pending_screening'])} unresolved candidates. "
        "This is a provisional catalog, not an exhaustive census or a claim "
        "that the listed protocols have been proved.", "",
        data["publication_policy"], "", data["scope"], "",
        "Only properties formally proved with Verus count toward proof progress. "
        "Historical model-checking results do not discharge proof obligations.", "",
        "Counts: " + "; ".join(f"{v} {counts[v]}" for v in sorted(VENUES)) + ".", "",
        "The 2021 PAC/G-PAC erratum is a separate correction record. "
        "The year column uses conference editions, which can differ from "
        "PVLDB/PACMMOD publication dates.", "",
        "| Year | Venue | Paper | Protocol change | Local verification status |",
        "|---|---|---|---|---|",
    ]
    def esc(s):
        return s.replace("|", "\\|").replace("\n", " ")
    for p in papers:
        lines.append(f"| {p['conference_year']} | {p['venue']} | "
                     f"[{esc(p['title'])}]({p['source_url']}) | "
                     f"{esc(p['contribution'])} | {p['proof_status']} |")
    lines += ["", "## Proof obligations and evidence", "",
              "These are targets for formalization. An obligation listed here "
              "is not a proved theorem. Existing repository evidence has not "
              "been rerun unless its report explicitly says so.", ""]
    for p in papers:
        lines += [f"### {p['id']}", "", f"{p['protocol']}. {p['obligations']}.", "",
                  f"Model status: `{p['model_status']}`. "
                  f"Source review: `{p['source_review']}`.", ""]
        for key in ("publication_note", "scope_note", "safety_note"):
            if p.get(key):
                lines += [p[key], ""]
        links = [f"[{name}](../../{name})"
                 for field in ("model_paths", "evidence_paths") for name in p[field]]
        if links:
            lines += ["Local files: " + ", ".join(links) + ".", ""]
    for key, title in [("pending_screening", "Unresolved candidates"),
                       ("screened_exclusions", "Screened exclusions")]:
        lines += [f"## {title}", "", "| Paper | Venue/year | Reason |",
                  "|---|---|---|"]
        for p in data[key]:
            lines.append(f"| [{esc(p['title'])}]({p['source_url']}) | "
                         f"{p['venue']} {p['year']} | {esc(p['reason'])} |")
        lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = json.loads((DIRECTORY / "catalog.json").read_text())
    expected = render(data)
    output = DIRECTORY / "catalog.md"
    if args.check:
        if not output.exists() or output.read_text() != expected:
            raise SystemExit("Catalog is stale; run python3 scripts/consensus_catalog.py")
        print(f"Catalog checked: {len(data['papers'])} records; local links exist.")
    else:
        output.write_text(expected)
        print(f"Wrote {output}")


if __name__ == "__main__":
    main()
