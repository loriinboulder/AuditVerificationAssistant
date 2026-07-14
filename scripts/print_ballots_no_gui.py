#!/usr/bin/env python3
"""
Print ballot content for a list of ImprintedIds, with no tkinter
dependency at all -- unlike scripts/run_headless.py, this never
constructs a Tk() root, so nothing can pop up on screen.

Replicates RLAAuditHelper.py's _parse_cvr / _format_contest_name /
_generate_ballot_output logic directly (not imported, since importing
RLAAuditHelper.py pulls in tkinter at module load time).

Usage:
    python3 scripts/print_ballots_no_gui.py <cvr_file> <imprinted_ids_file> [audit_board_label]

<imprinted_ids_file> is a plain text file, one ImprintedId per line
(blank lines and lines starting with '#' are ignored).
"""
import csv
import re
import sys

_CONTEST_NAME_SHORTENINGS = [
    (
        re.compile(r"^Representative to the \d+\w+ United States Congress - District (\d+)(.*)$"),
        r"US Rep - CD\1\2",
    ),
    (
        re.compile(r"^Regent of the University of Colorado - Congressional District (\d+)(.*)$"),
        r"CU Regent - CD\1\2",
    ),
    (
        re.compile(r"^State Board of Education Member - Congressional District (\d+)(.*)$"),
        r"State BOE - CD\1\2",
    ),
]


def format_contest_name(contest_name):
    m = re.search(r"\s*\(Vote For=(\d+)\)\s*$", contest_name)
    if m and m.group(1) == "1":
        contest_name = contest_name[: m.start()].strip()
    contest_name = re.sub(
        r"\s*\((?:statutory|constitutional)\)\s*", " ", contest_name, flags=re.IGNORECASE
    ).strip()
    for pattern, replacement in _CONTEST_NAME_SHORTENINGS:
        contest_name = pattern.sub(replacement, contest_name)
    return contest_name


def parse_cvr(cvr_filepath):
    with open(cvr_filepath, "r", newline="", encoding="utf-8") as f:
        rows = list(csv.reader(f))
    if len(rows) < 5:
        raise ValueError("CVR file must have at least 5 rows.")

    row2, row3, row4 = rows[1], rows[2], rows[3]

    id_column_count = 0
    imprinted_id_col = None
    for i, header in enumerate(row4):
        if header.strip():
            id_column_count = i + 1
            if header.strip() == "ImprintedId":
                imprinted_id_col = i
            if header.strip() == "BallotType":
                break
    if imprinted_id_col is None:
        raise ValueError("Could not find 'ImprintedId' column in the CVR header.")

    contests = []
    current_contest = None
    contest_start = None
    for i in range(id_column_count, len(row2)):
        cell = row2[i].strip() if i < len(row2) else ""
        if cell and cell != current_contest:
            if current_contest is not None:
                contests.append((current_contest, contest_start, i - 1))
            current_contest = cell
            contest_start = i
    if current_contest is not None:
        contests.append((current_contest, contest_start, len(row2) - 1))

    return {
        "row3": row3,
        "ballots": rows[4:],
        "contests": contests,
        "imprinted_id_col": imprinted_id_col,
    }


def find_ballot(cvr_data, imprinted_id):
    col = cvr_data["imprinted_id_col"]
    for ballot in cvr_data["ballots"]:
        if len(ballot) > col and ballot[col].strip() == imprinted_id:
            return ballot
    return None


def generate_ballot_output(cvr_data, imprinted_id, ballot):
    iid_label = f" ImprintedId {imprinted_id} "
    if ballot is None:
        return ["", iid_label.center(80, "-"), "Missing"]

    row3 = cvr_data["row3"]
    entries = []
    for contest_name, start_col, end_col in cvr_data["contests"]:
        if not any(
            col < len(ballot) and ballot[col].strip() != "" for col in range(start_col, end_col + 1)
        ):
            continue
        display_name = format_contest_name(contest_name)
        selected = [
            row3[col].strip()
            for col in range(start_col, end_col + 1)
            if col < len(ballot) and ballot[col].strip() == "1" and col < len(row3) and row3[col].strip()
        ]
        vote_str = ", ".join(selected) if selected else "NO VOTE"
        entries.append((display_name, vote_str))

    width = max((len(name) for name, _ in entries), default=0)
    lines = ["", iid_label.center(80, "-")]
    for name, vote_str in entries:
        lines.append(f"{name:>{width}} __ {vote_str}")
    return lines


def main():
    if len(sys.argv) not in (3, 4):
        print(__doc__)
        sys.exit(1)
    cvr_file, ids_file = sys.argv[1], sys.argv[2]
    label = sys.argv[3] if len(sys.argv) == 4 else "Audit Board 1"

    with open(ids_file) as f:
        imprinted_ids = [
            ln.strip() for ln in f if ln.strip() and not ln.strip().startswith("#")
        ]

    cvr_data = parse_cvr(cvr_file)
    print(label)
    for iid in imprinted_ids:
        ballot = find_ballot(cvr_data, iid)
        for line in generate_ballot_output(cvr_data, iid, ballot):
            print(line)


if __name__ == "__main__":
    main()
