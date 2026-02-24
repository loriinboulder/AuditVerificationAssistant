import csv
import hashlib
import os
import re
import shutil
import tempfile
import zipfile
import tkinter as tk
from tkinter import filedialog, messagebox
from dataclasses import dataclass, field
from typing import List, Tuple


# ---------------------------------------------------------------------------
# Ballot selection algorithm (from the Colorado RLA system).
#
# Replicates the logic in:
#   BallotSelection.java, BallotManifestInfo.java,
#   ColoradoBallotManifestParser.java, PseudoRandomNumberGenerator.java
#
# The manifest CSV is expected to have exactly these columns in order
# (header row is skipped; column names are ignored):
#   0: County ID
#   1: Scanner / Tabulator ID
#   2: Batch ID
#   3: Number of ballots in batch
#   4: Storage location (ignored)
#
# The PRNG is Philip Stark's SHA-256-based generator:
#   For counter = 1, 2, ..., count:
#     rand = 1 + SHA-256(seed + "," + str(counter)) as unsigned int % domain_size
# ---------------------------------------------------------------------------

@dataclass
class _Batch:
    county_id: str
    scanner_id: str
    batch_id: str
    sequence_start: int
    sequence_end: int
    ultimate_start: int = field(default=0, init=False)
    ultimate_end: int = field(default=0, init=False)


def select_ballots(
    manifest_path: str,
    seed: str,
    count: int,
) -> List[Tuple[str, str, int]]:
    """
    Select ballots for audit.

    Args:
        manifest_path: Path to the ballot manifest CSV file.
        seed:          PRNG seed (digits only, at least 20 characters).
        count:         Number of ballots to select.

    Returns:
        List of (scanner_id, batch_id, ballot_position) tuples.
        ballot_position is 1-based within the batch.
        Duplicates are possible (sampling is with replacement).
    """

    # --- Step 1: Parse manifest by column position; assign per-county
    #             sequence numbers in CSV row order. ---
    batches: List[_Batch] = []
    county_ballot_count: dict[str, int] = {}

    with open(manifest_path, newline="", encoding="utf-8-sig") as f:
        reader = csv.reader(f)
        next(reader)  # skip header row regardless of column names
        for row in reader:
            if not any(cell.strip() for cell in row):
                continue  # skip blank lines
            county      = row[0].strip()
            scanner_id  = row[1].strip()
            batch_id    = row[2].strip()
            num_ballots = int(row[3].strip())

            prev = county_ballot_count.get(county, 0)
            sequence_start = 1 if prev == 0 else prev + 1
            sequence_end   = sequence_start + num_ballots - 1
            county_ballot_count[county] = sequence_end

            batches.append(_Batch(
                county_id=county,
                scanner_id=scanner_id,
                batch_id=batch_id,
                sequence_start=sequence_start,
                sequence_end=sequence_end,
            ))

    # --- Step 2: Sort by (county_id, sequence_end).
    #             Within a county this preserves CSV row order. ---
    batches.sort(key=lambda b: (b.county_id, b.sequence_end))

    # --- Step 3: Domain size = sum of max(sequence_end) per county. ---
    county_ids = {b.county_id for b in batches}
    domain_size = sum(
        max(b.sequence_end for b in batches if b.county_id == c)
        for c in county_ids
    )

    # --- Step 4: Assign global ultimate sequence positions. ---
    last = 0
    for b in batches:
        b.ultimate_start = last + 1
        b.ultimate_end   = b.ultimate_start + (b.sequence_end - b.sequence_start)
        last = b.ultimate_end

    # --- Step 5 & 6: Generate random numbers and map to ballots. ---
    results: List[Tuple[str, str, int]] = []

    for counter in range(1, count + 1):
        data   = (seed + "," + str(counter)).encode("utf-8")
        digest = hashlib.sha256(data).digest()
        rand   = 1 + (int.from_bytes(digest, byteorder="big") % domain_size)

        batch = next(
            (b for b in batches if b.ultimate_start <= rand <= b.ultimate_end),
            None,
        )
        if batch is None:
            raise ValueError(
                f"No batch holds random position {rand} "
                f"(domain_size={domain_size}, counter={counter})"
            )

        ballot_position = rand - batch.ultimate_start + 1
        results.append((batch.scanner_id, batch.batch_id, ballot_position))

    return results


class RLAAuditHelperApp:
    def __init__(self, root):
        self.root = root
        self.root.title("RLA Audit Helper")
        self.root.geometry("720x520")
        self.root.resizable(True, True)

        # Input data state
        self.input_path = None       # zip file or directory chosen by user
        self.data_dir = None         # directory where data files live
        self.temp_dir = None         # temp dir created when unpacking a zip

        # File paths resolved from CONTENTS
        self.cvr_filepath = None
        self.manifest_filepath = None
        self.contest_results_filepath = None
        self.ballot_list_files = []  # list of (auditboard_n: int, filepath: str), sorted by n

        # Parsed CVR state (cached across menu options until input changes)
        self.cvr_data = None
        self.imprinted_id_col = None
        self.id_column_count = None
        self.contests = []           # list of (contest_name, start_col, end_col)

        self.show_file_screen()

    # ------------------------------------------------------------------
    # Utilities
    # ------------------------------------------------------------------
    def clear_screen(self):
        for widget in self.root.winfo_children():
            widget.destroy()

    def compute_sha256(self, filepath):
        sha256_hash = hashlib.sha256()
        with open(filepath, "rb") as f:
            for chunk in iter(lambda: f.read(8192), b""):
                sha256_hash.update(chunk)
        return sha256_hash.hexdigest()

    def update_status(self, message):
        self.status_text.config(state=tk.NORMAL)
        self.status_text.insert(tk.END, message + "\n")
        self.status_text.see(tk.END)
        self.status_text.config(state=tk.DISABLED)
        self.root.update()

    # ------------------------------------------------------------------
    # Screen 1: Input Data File Selection
    # ------------------------------------------------------------------
    def show_file_screen(self):
        self.clear_screen()

        tk.Label(self.root, text="RLA Audit Helper",
                 font=("TkDefaultFont", 14, "bold")).pack(pady=20)

        file_frame = tk.Frame(self.root, padx=10, pady=5)
        file_frame.pack(fill=tk.X)

        tk.Label(file_frame, text="Input Data:").pack(side=tk.LEFT)
        self.file_entry = tk.Entry(file_frame, width=50)
        self.file_entry.pack(side=tk.LEFT, padx=(5, 5), fill=tk.X, expand=True)

        btn_sub = tk.Frame(file_frame)
        btn_sub.pack(side=tk.LEFT)
        tk.Button(btn_sub, text="Browse Folder...", command=self.browse_folder).pack(side=tk.LEFT, padx=2)
        tk.Button(btn_sub, text="Browse Zip...", command=self.browse_zip).pack(side=tk.LEFT, padx=2)

        if self.input_path:
            self.file_entry.insert(0, self.input_path)

        tk.Label(self.root,
                 text="Select a folder or zip file that contains a CONTENTS file.",
                 font=("TkDefaultFont", 9), fg="gray").pack(pady=(2, 10))

        tk.Button(self.root, text="Continue", command=self.load_input_data, width=15).pack(pady=5)

    def browse_folder(self):
        path = filedialog.askdirectory(title="Select input data folder")
        if path:
            self.file_entry.delete(0, tk.END)
            self.file_entry.insert(0, path)

    def browse_zip(self):
        path = filedialog.askopenfilename(
            title="Select input zip file",
            filetypes=[("Zip files", "*.zip"), ("All files", "*.*")]
        )
        if path:
            self.file_entry.delete(0, tk.END)
            self.file_entry.insert(0, path)

    def load_input_data(self):
        path = self.file_entry.get().strip()
        if not path:
            messagebox.showerror("Error", "Please select an input data folder or zip file.")
            return

        # Clean up any previous temp directory
        if self.temp_dir and os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
            self.temp_dir = None

        try:
            if os.path.isdir(path):
                self.data_dir = path
            elif zipfile.is_zipfile(path):
                self.temp_dir = tempfile.mkdtemp()
                with zipfile.ZipFile(path, 'r') as zf:
                    zf.extractall(self.temp_dir)
                # If the zip contained a single top-level directory, step into it
                items = os.listdir(self.temp_dir)
                if len(items) == 1 and os.path.isdir(os.path.join(self.temp_dir, items[0])):
                    self.data_dir = os.path.join(self.temp_dir, items[0])
                else:
                    self.data_dir = self.temp_dir
            else:
                messagebox.showerror("Error", "The selected path is not a folder or a zip file.")
                return

            # Locate and parse CONTENTS
            contents_path = os.path.join(self.data_dir, "CONTENTS")
            if not os.path.exists(contents_path):
                messagebox.showerror("Error", "The input data does not contain a CONTENTS file.")
                return

            raw_contents = {}
            with open(contents_path, 'r', encoding='utf-8') as f:
                for lineno, line in enumerate(f, 1):
                    line = line.strip()
                    if not line:
                        continue
                    if ':' not in line:
                        messagebox.showerror("Error", f"CONTENTS line {lineno} has no colon: '{line}'")
                        return
                    file_type, filename = line.split(':', 1)
                    file_type = file_type.strip()
                    filename = filename.strip()
                    raw_contents.setdefault(file_type, []).append(filename)

            # Resolve paths and validate files exist
            self.cvr_filepath = None
            self.manifest_filepath = None
            self.contest_results_filepath = None
            self.ballot_list_files = []

            if 'CVRfile' in raw_contents:
                self.cvr_filepath = os.path.join(self.data_dir, raw_contents['CVRfile'][0])
            if 'ballotmanifest' in raw_contents:
                self.manifest_filepath = os.path.join(self.data_dir, raw_contents['ballotmanifest'][0])
            if 'contestresults' in raw_contents:
                self.contest_results_filepath = os.path.join(
                    self.data_dir, raw_contents['contestresults'][0])

            for filename in raw_contents.get('ballotlist', []):
                filepath = os.path.join(self.data_dir, filename)
                if not os.path.exists(filepath):
                    messagebox.showerror("Error", f"Ballot list file not found: {filename}")
                    return
                with open(filepath, 'r', encoding='utf-8') as f:
                    first_line = f.readline().strip()
                m = re.match(r'^auditboard:(\d+)$', first_line)
                if not m:
                    messagebox.showerror(
                        "Error",
                        f"Ballot list file '{filename}': first line must be 'auditboard:n' "
                        f"(found: '{first_line}')"
                    )
                    return
                self.ballot_list_files.append((int(m.group(1)), filepath))

            self.ballot_list_files.sort(key=lambda x: x[0])

            # Reset cached CVR parse
            self.cvr_data = None
            self.input_path = path
            self.show_main_menu()

        except Exception as e:
            messagebox.showerror("Error", f"Error loading input data: {e}")

    # ------------------------------------------------------------------
    # Screen 2: Main Menu
    # ------------------------------------------------------------------
    def show_main_menu(self):
        self.clear_screen()

        tk.Label(self.root, text="RLA Audit Helper",
                 font=("TkDefaultFont", 14, "bold")).pack(pady=10)

        short_path = self.input_path
        if len(short_path) > 70:
            short_path = "..." + short_path[-67:]
        tk.Label(self.root, text=f"Data: {short_path}",
                 font=("TkDefaultFont", 9), fg="gray").pack(pady=(0, 10))

        tk.Label(self.root, text="Select an option:",
                 font=("TkDefaultFont", 11)).pack(pady=5)

        btn_frame = tk.Frame(self.root, padx=10, pady=5)
        btn_frame.pack()

        options = [
            ("(1) Verify the CVR",                   self.show_verify_cvr_screen),
            ("(2) Verify the Ballot List",            self.show_verify_ballot_list_screen),
            ("(3) Verify Contest Results",            self.show_verify_contest_results_screen),
            ("(4) Print Lists of Ballot Contents",    self.show_print_ballot_lists_screen),
            ("(5) Print Specific Ballot Contents",    self.show_print_specific_ballot_screen),
            ("(6) Exit",                              self.root.quit),
        ]
        for text, cmd in options:
            tk.Button(btn_frame, text=text, command=cmd, width=42).pack(pady=3)

        tk.Button(self.root, text="Change Input Data",
                  command=self.show_file_screen, width=20).pack(pady=10)

    # ------------------------------------------------------------------
    # Option 1: Verify the CVR
    # ------------------------------------------------------------------
    def show_verify_cvr_screen(self):
        if not self.cvr_filepath:
            messagebox.showerror("Error", "No CVR file was specified in CONTENTS.")
            return

        self.clear_screen()
        tk.Label(self.root, text="Verify the CVR",
                 font=("TkDefaultFont", 14, "bold")).pack(pady=10)
        tk.Label(self.root, text=f"File: {os.path.basename(self.cvr_filepath)}",
                 font=("TkDefaultFont", 9), fg="gray").pack(pady=(0, 10))

        hash_frame = tk.Frame(self.root, padx=10, pady=5)
        hash_frame.pack(fill=tk.X)
        tk.Label(hash_frame, text="Expected SHA256 Hash:").pack(anchor=tk.W)
        self.hash_entry = tk.Entry(hash_frame, width=70)
        self.hash_entry.pack(fill=tk.X, pady=(5, 0))

        tk.Button(self.root, text="Verify Hash",
                  command=self.verify_cvr_hash, width=15).pack(pady=10)

        result_frame = tk.Frame(self.root, padx=10, pady=5)
        result_frame.pack(fill=tk.BOTH, expand=True)
        tk.Label(result_frame, text="Result:").pack(anchor=tk.W)
        self.result_text = tk.Text(result_frame, height=6, state=tk.DISABLED)
        self.result_text.pack(fill=tk.BOTH, expand=True, pady=(5, 10))
        self.result_text.tag_configure("match", foreground="green",
                                       font=("TkDefaultFont", 12, "bold"))
        self.result_text.tag_configure("nomatch", foreground="red",
                                       font=("TkDefaultFont", 12, "bold"))

        tk.Button(self.root, text="Back to Main Menu",
                  command=self.show_main_menu, width=20).pack(pady=5)

    def verify_cvr_hash(self):
        expected = self.hash_entry.get().strip().lower()
        if not expected:
            messagebox.showerror("Error", "Please enter a SHA256 hash.")
            return
        if len(expected) != 64:
            messagebox.showerror("Error", "SHA256 hash must be 64 hexadecimal characters.")
            return
        try:
            computed = self.compute_sha256(self.cvr_filepath)
        except Exception as e:
            messagebox.showerror("Error", f"Error reading file: {e}")
            return

        self.result_text.config(state=tk.NORMAL)
        self.result_text.delete(1.0, tk.END)
        if computed == expected:
            self.result_text.insert(tk.END, "MATCH\n\n", "match")
            self.result_text.insert(tk.END, "The file hash matches the provided hash.\n\n")
        else:
            self.result_text.insert(tk.END, "NO MATCH\n\n", "nomatch")
            self.result_text.insert(tk.END, "The hashes do not match.\n\n")
        self.result_text.insert(tk.END, f"Expected:  {expected}\n")
        self.result_text.insert(tk.END, f"Computed:  {computed}")
        self.result_text.config(state=tk.DISABLED)

    # ------------------------------------------------------------------
    # Option 2: Verify the Ballot List
    # ------------------------------------------------------------------
    def show_verify_ballot_list_screen(self):
        if not self.manifest_filepath:
            messagebox.showerror("Error", "No ballot manifest file was specified in CONTENTS.")
            return
        if not self.ballot_list_files:
            messagebox.showerror("Error", "No ballot list files were specified in CONTENTS.")
            return

        self.clear_screen()
        tk.Label(self.root, text="Verify the Ballot List",
                 font=("TkDefaultFont", 14, "bold")).pack(pady=10)

        seed_frame = tk.Frame(self.root, padx=10, pady=5)
        seed_frame.pack(fill=tk.X)
        tk.Label(seed_frame, text="Random Seed:").pack(side=tk.LEFT)
        self.seed_entry = tk.Entry(seed_frame, width=30)
        self.seed_entry.pack(side=tk.LEFT, padx=(5, 0))

        tk.Button(self.root, text="Verify Ballot List",
                  command=self.verify_ballot_list, width=20).pack(pady=10)

        status_frame = tk.Frame(self.root, padx=10, pady=5)
        status_frame.pack(fill=tk.BOTH, expand=True)
        tk.Label(status_frame, text="Status:").pack(anchor=tk.W)
        self.status_text = tk.Text(status_frame, height=10, state=tk.DISABLED)
        self.status_text.pack(fill=tk.BOTH, expand=True, pady=(5, 10))
        self.status_text.tag_configure("success", foreground="green",
                                       font=("TkDefaultFont", 10, "bold"))
        self.status_text.tag_configure("error", foreground="red")

        tk.Button(self.root, text="Back to Main Menu",
                  command=self.show_main_menu, width=20).pack(pady=5)

    def verify_ballot_list(self):
        seed = self.seed_entry.get().strip()
        if not seed:
            messagebox.showerror("Error", "Please enter the random seed.")
            return

        self.status_text.config(state=tk.NORMAL)
        self.status_text.delete(1.0, tk.END)
        self.status_text.config(state=tk.DISABLED)

        try:
            # Collect all ImprintedIds from all ballot list files
            self.update_status("Reading ballot list files...")
            imprinted_ids = []
            for ab_n, filepath in self.ballot_list_files:
                with open(filepath, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                ids_in_file = [ln.strip() for ln in lines[1:] if ln.strip()]
                self.update_status(f"  Audit Board {ab_n}: {len(ids_in_file)} ballot(s)")
                imprinted_ids.extend(ids_in_file)

            total = len(imprinted_ids)
            self.update_status(f"Total ballots in ballot list files: {total}")

            # Parse ImprintedIds -> (scanner, batch, position) integer tuples
            ballot_list_tuples = []
            for iid in imprinted_ids:
                parts = iid.split('-')
                if len(parts) != 3:
                    self.update_status(f"  Warning: skipping invalid ImprintedId '{iid}'")
                    continue
                try:
                    ballot_list_tuples.append((int(parts[0]), int(parts[1]), int(parts[2])))
                except ValueError:
                    self.update_status(f"  Warning: skipping non-numeric ImprintedId '{iid}'")

            # Run ballot selection algorithm
            self.update_status(f"\nRunning ballot selection (seed='{seed}', count={total})...")
            selected_raw = select_ballots(self.manifest_filepath, seed, total)

            selected_tuples = []
            for scanner_id, batch_id, ballot_position in selected_raw:
                selected_tuples.append((int(scanner_id), int(batch_id), int(ballot_position)))

            # Compare as sorted multisets
            ballot_list_sorted = sorted(ballot_list_tuples)
            selected_sorted = sorted(selected_tuples)

            if ballot_list_sorted == selected_sorted:
                self.status_text.config(state=tk.NORMAL)
                self.status_text.insert(tk.END,
                    "\nBALLOT LIST VERIFIED SUCCESSFULLY!\n", "success")
                self.status_text.config(state=tk.DISABLED)
                messagebox.showinfo("Success",
                    "The ballot list matches the expected selection.")
            else:
                self.status_text.config(state=tk.NORMAL)
                self.status_text.insert(tk.END,
                    "\nBALLOT LIST DOES NOT MATCH.\n", "error")
                self.status_text.config(state=tk.DISABLED)

                from collections import Counter
                list_ctr = Counter(ballot_list_sorted)
                sel_ctr  = Counter(selected_sorted)
                in_list_not_sel = list_ctr - sel_ctr
                in_sel_not_list = sel_ctr - list_ctr

                if in_list_not_sel:
                    self.update_status(
                        f"\nIn ballot list but NOT in expected selection "
                        f"({sum(in_list_not_sel.values())} ballot(s)):")
                    for (sc, ba, po), cnt in sorted(in_list_not_sel.items()):
                        self.status_text.config(state=tk.NORMAL)
                        suffix = f" (x{cnt})" if cnt > 1 else ""
                        self.status_text.insert(
                            tk.END, f"  {sc}-{ba}-{po}{suffix}\n", "error")
                        self.status_text.config(state=tk.DISABLED)

                if in_sel_not_list:
                    self.update_status(
                        f"\nIn expected selection but NOT in ballot list "
                        f"({sum(in_sel_not_list.values())} ballot(s)):")
                    for (sc, ba, po), cnt in sorted(in_sel_not_list.items()):
                        self.status_text.config(state=tk.NORMAL)
                        suffix = f" (x{cnt})" if cnt > 1 else ""
                        self.status_text.insert(
                            tk.END, f"  {sc}-{ba}-{po}{suffix}\n", "error")
                        self.status_text.config(state=tk.DISABLED)

                messagebox.showwarning("Verification Failed",
                    "The ballot list does not match the expected selection.\n"
                    "See status window for details.")

        except Exception as e:
            messagebox.showerror("Error", f"Error verifying ballot list: {e}")
            self.update_status(f"Error: {e}")

    # ------------------------------------------------------------------
    # Option 3: Verify Contest Results
    # ------------------------------------------------------------------
    def show_verify_contest_results_screen(self):
        if not self.cvr_filepath:
            messagebox.showerror("Error", "No CVR file was specified in CONTENTS.")
            return
        if not self.contest_results_filepath:
            messagebox.showerror("Error", "No contest results file was specified in CONTENTS.")
            return

        self.clear_screen()
        tk.Label(self.root, text="Verify Contest Results",
                 font=("TkDefaultFont", 14, "bold")).pack(pady=10)
        tk.Label(self.root,
                 text=(f"CVR: {os.path.basename(self.cvr_filepath)}"
                       f"   Results: {os.path.basename(self.contest_results_filepath)}"),
                 font=("TkDefaultFont", 9), fg="gray").pack(pady=(0, 5))

        tk.Button(self.root, text="Verify Results",
                  command=self.run_verify_contest_results, width=20).pack(pady=10)

        status_frame = tk.Frame(self.root, padx=10, pady=5)
        status_frame.pack(fill=tk.BOTH, expand=True)
        tk.Label(status_frame, text="Status:").pack(anchor=tk.W)
        self.status_text = tk.Text(status_frame, height=12, state=tk.DISABLED)
        self.status_text.pack(fill=tk.BOTH, expand=True, pady=(5, 10))
        self.status_text.tag_configure("success", foreground="green",
                                       font=("TkDefaultFont", 10, "bold"))
        self.status_text.tag_configure("error", foreground="red")

        tk.Button(self.root, text="Back to Main Menu",
                  command=self.show_main_menu, width=20).pack(pady=5)

    def run_verify_contest_results(self):
        self.status_text.config(state=tk.NORMAL)
        self.status_text.delete(1.0, tk.END)
        self.status_text.config(state=tk.DISABLED)

        try:
            self.update_status("Parsing CVR file...")
            self._parse_cvr()
            self.update_status(
                f"Parsed CVR: {len(self.cvr_data['ballots'])} ballots, "
                f"{len(self.contests)} contest(s).")

            self.update_status("Reading contest results file...")
            try:
                reported = self._parse_results_file(self.contest_results_filepath)
            except ValueError as e:
                self.update_status(f"Error in results file: {e}")
                messagebox.showerror("Error", f"Invalid results file:\n{e}")
                return
            self.update_status(
                f"Found {len(reported)} contest/choice entries in results file.")

            self.update_status("Computing results from CVR...")
            cvr_results = self._compute_cvr_results()
            self.update_status(
                f"Found {len(cvr_results)} contest/choice entries in CVR.")

            # Build contest -> choice sets
            cvr_contests = {}
            for contest, choice in cvr_results:
                cvr_contests.setdefault(contest, set()).add(choice)
            rep_contests = {}
            for contest, choice in reported:
                rep_contests.setdefault(contest, set()).add(choice)

            self.update_status("\nVerifying results...")
            errors = []

            for key in cvr_results:
                if key not in reported:
                    errors.append(f"Missing from results: {key[0]} / {key[1]}")

            for contest in cvr_contests:
                if contest in rep_contests:
                    for choice in cvr_contests[contest] - rep_contests[contest]:
                        if (contest, choice) not in cvr_results or (contest, choice) not in reported:
                            errors.append(
                                f"Choice missing from results: {contest} / {choice}")
                    for choice in rep_contests[contest] - cvr_contests[contest]:
                        errors.append(
                            f"Extra choice in results (not in CVR): {contest} / {choice}")

            vote_mismatches = []
            for key, cvr_votes in cvr_results.items():
                if key in reported and cvr_votes != reported[key]:
                    vote_mismatches.append(
                        f"{key[0]} / {key[1]}: CVR={cvr_votes}, Reported={reported[key]}"
                    )

            if errors:
                self.update_status("\nStructure errors found:")
                for error in errors:
                    self.status_text.config(state=tk.NORMAL)
                    self.status_text.insert(tk.END, f"  {error}\n", "error")
                    self.status_text.config(state=tk.DISABLED)

            if vote_mismatches:
                self.update_status("\nVote count mismatches:")
                for mismatch in vote_mismatches:
                    self.status_text.config(state=tk.NORMAL)
                    self.status_text.insert(tk.END, f"  {mismatch}\n", "error")
                    self.status_text.config(state=tk.DISABLED)

            if not errors and not vote_mismatches:
                self.status_text.config(state=tk.NORMAL)
                self.status_text.insert(tk.END,
                    "\nALL RESULTS VERIFIED SUCCESSFULLY!\n", "success")
                self.status_text.config(state=tk.DISABLED)
                messagebox.showinfo("Success", "All contest results match!")
            else:
                total = len(errors) + len(vote_mismatches)
                self.update_status(f"\nTotal issues found: {total}")
                messagebox.showwarning("Verification Failed",
                    f"Found {total} issue(s).\nSee status window for details.")

        except Exception as e:
            messagebox.showerror("Error", f"Error: {e}")
            self.update_status(f"Error: {e}")

    # ------------------------------------------------------------------
    # Option 4: Print Lists of Ballot Contents
    # ------------------------------------------------------------------
    def show_print_ballot_lists_screen(self):
        if not self.cvr_filepath:
            messagebox.showerror("Error", "No CVR file was specified in CONTENTS.")
            return
        if not self.ballot_list_files:
            messagebox.showerror("Error", "No ballot list files were specified in CONTENTS.")
            return

        self.clear_screen()
        tk.Label(self.root, text="Print Lists of Ballot Contents",
                 font=("TkDefaultFont", 14, "bold")).pack(pady=10)

        # Output folder
        folder_frame = tk.Frame(self.root, padx=10, pady=5)
        folder_frame.pack(fill=tk.X)
        tk.Label(folder_frame, text="Output Folder:").pack(side=tk.LEFT)
        self.output_folder_entry = tk.Entry(folder_frame, width=45)
        self.output_folder_entry.pack(side=tk.LEFT, padx=(5, 5), fill=tk.X, expand=True)
        tk.Button(folder_frame, text="Browse...",
                  command=self.browse_output_folder).pack(side=tk.LEFT)

        # Audit board selection
        ab_frame = tk.LabelFrame(self.root, text="Audit Board", padx=10, pady=5)
        ab_frame.pack(fill=tk.X, padx=10, pady=5)

        self.ab_var = tk.StringVar(value="all")
        tk.Radiobutton(ab_frame, text="All Audit Boards",
                       variable=self.ab_var, value="all").pack(anchor=tk.W)
        for ab_n, _ in self.ballot_list_files:
            tk.Radiobutton(ab_frame, text=f"Audit Board #{ab_n}",
                           variable=self.ab_var, value=str(ab_n)).pack(anchor=tk.W)

        tk.Button(self.root, text="Print Audit Board List",
                  command=self.print_ballot_lists, width=22).pack(pady=(5, 8))

        # Specified list section
        sl_frame = tk.LabelFrame(self.root, text="Specified Ballot List", padx=10, pady=5)
        sl_frame.pack(fill=tk.X, padx=10, pady=5)

        sl_file_row = tk.Frame(sl_frame)
        sl_file_row.pack(fill=tk.X)
        tk.Label(sl_file_row, text="List File:").pack(side=tk.LEFT)
        self.spec_list_entry = tk.Entry(sl_file_row, width=40)
        self.spec_list_entry.pack(side=tk.LEFT, padx=(5, 5), fill=tk.X, expand=True)
        tk.Button(sl_file_row, text="Browse...",
                  command=self.browse_specified_list_file).pack(side=tk.LEFT)

        tk.Button(sl_frame, text="Print Specified List",
                  command=self.print_specified_ballot_list, width=22).pack(pady=(5, 2))

        status_frame = tk.Frame(self.root, padx=10, pady=5)
        status_frame.pack(fill=tk.BOTH, expand=True)
        tk.Label(status_frame, text="Status:").pack(anchor=tk.W)
        self.status_text = tk.Text(status_frame, height=4, state=tk.DISABLED)
        self.status_text.pack(fill=tk.BOTH, expand=True, pady=(5, 5))

        tk.Button(self.root, text="Back to Main Menu",
                  command=self.show_main_menu, width=20).pack(pady=5)

    def browse_output_folder(self):
        folder = filedialog.askdirectory(title="Select output folder")
        if folder:
            self.output_folder_entry.delete(0, tk.END)
            self.output_folder_entry.insert(0, folder)

    def print_ballot_lists(self):
        folder = self.output_folder_entry.get().strip()
        if not folder:
            messagebox.showerror("Error", "Please select an output folder.")
            return
        if not os.path.isdir(folder):
            messagebox.showerror("Error", "The selected output folder does not exist.")
            return

        selection = self.ab_var.get()
        if selection == "all":
            to_print = self.ballot_list_files
        else:
            ab_n = int(selection)
            to_print = [(n, p) for n, p in self.ballot_list_files if n == ab_n]

        self.status_text.config(state=tk.NORMAL)
        self.status_text.delete(1.0, tk.END)
        self.status_text.config(state=tk.DISABLED)

        try:
            self.update_status("Parsing CVR file...")
            if self.cvr_data is None:
                self._parse_cvr()
            self.update_status(
                f"CVR: {len(self.cvr_data['ballots'])} ballots, "
                f"{len(self.contests)} contest(s).")

            locations = self._load_manifest_locations()

            separator = "-" * 60
            ballot_location_lines = []

            for ab_n, filepath in to_print:
                self.update_status(f"Processing Audit Board {ab_n}...")
                with open(filepath, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                imprinted_ids = [ln.strip() for ln in lines[1:] if ln.strip()]

                output_lines = [f"Audit Board {ab_n}", separator]
                for iid in imprinted_ids:
                    output_lines.extend(self._generate_ballot_output(iid,
                        self._find_ballot(iid)))
                    output_lines.append(separator)
                    parts = iid.split('-')
                    loc = locations.get((parts[0], parts[1]), "") if len(parts) == 3 else ""
                    ballot_location_lines.append(f"{iid}, {loc}")

                out_path = os.path.join(folder, f"BallotContents_AuditBoard_{ab_n}.txt")
                with open(out_path, 'w', encoding='utf-8') as f:
                    f.write("\n".join(output_lines))
                self.update_status(f"  Written: {os.path.basename(out_path)}")

            loc_path = os.path.join(folder, "BallotList_selectedBallots.txt")
            with open(loc_path, 'w', encoding='utf-8') as f:
                f.write("\n".join(ballot_location_lines))
            self.update_status(f"  Written: BallotList_selectedBallots.txt")

            self.update_status("Done.")
            messagebox.showinfo("Success", f"Ballot contents written to:\n{folder}")

        except Exception as e:
            messagebox.showerror("Error", f"Error: {e}")
            self.update_status(f"Error: {e}")

    def browse_specified_list_file(self):
        filepath = filedialog.askopenfilename(
            title="Select ImprintedId list file",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        if filepath:
            self.spec_list_entry.delete(0, tk.END)
            self.spec_list_entry.insert(0, filepath)

    def print_specified_ballot_list(self):
        list_path = self.spec_list_entry.get().strip()
        if not list_path:
            messagebox.showerror("Error", "Please select a ballot list file.")
            return
        if not os.path.isfile(list_path):
            messagebox.showerror("Error", f"File not found: {list_path}")
            return

        folder = self.output_folder_entry.get().strip()
        if not folder:
            messagebox.showerror("Error", "Please select an output folder.")
            return
        if not os.path.isdir(folder):
            messagebox.showerror("Error", "The selected output folder does not exist.")
            return

        self.status_text.config(state=tk.NORMAL)
        self.status_text.delete(1.0, tk.END)
        self.status_text.config(state=tk.DISABLED)

        try:
            if self.cvr_data is None:
                self.update_status("Parsing CVR file...")
                self._parse_cvr()
                self.update_status(
                    f"CVR: {len(self.cvr_data['ballots'])} ballots, "
                    f"{len(self.contests)} contest(s).")

            with open(list_path, 'r', encoding='utf-8') as f:
                imprinted_ids = [ln.strip() for ln in f if ln.strip()]
            self.update_status(f"Read {len(imprinted_ids)} ImprintedId(s) from list.")

            locations = self._load_manifest_locations()

            separator = "-" * 60
            input_stem = os.path.splitext(os.path.basename(list_path))[0]
            output_lines = [input_stem, separator]
            ballot_location_lines = []
            for iid in imprinted_ids:
                output_lines.extend(self._generate_ballot_output(iid, self._find_ballot(iid)))
                output_lines.append(separator)
                parts = iid.split('-')
                loc = locations.get((parts[0], parts[1]), "") if len(parts) == 3 else ""
                ballot_location_lines.append(f"{iid}, {loc}")

            out_path = os.path.join(folder, f"BallotContents_{input_stem}.txt")
            with open(out_path, 'w', encoding='utf-8') as f:
                f.write("\n".join(output_lines))
            self.update_status(f"Written: {os.path.basename(out_path)}")

            loc_path = os.path.join(folder, f"BallotList_{input_stem}.txt")
            with open(loc_path, 'w', encoding='utf-8') as f:
                f.write("\n".join(ballot_location_lines))
            self.update_status(f"Written: {os.path.basename(loc_path)}")

            messagebox.showinfo("Success", f"Ballot contents written to:\n{folder}")

        except Exception as e:
            messagebox.showerror("Error", f"Error: {e}")
            self.update_status(f"Error: {e}")

    # ------------------------------------------------------------------
    # Option 5: Print Specific Ballot Contents
    # ------------------------------------------------------------------
    def show_print_specific_ballot_screen(self):
        if not self.cvr_filepath:
            messagebox.showerror("Error", "No CVR file was specified in CONTENTS.")
            return

        self.clear_screen()
        tk.Label(self.root, text="Print Specific Ballot Contents",
                 font=("TkDefaultFont", 14, "bold")).pack(pady=10)

        entry_frame = tk.Frame(self.root, padx=10, pady=5)
        entry_frame.pack()

        tk.Label(entry_frame, text="Tabulator:").grid(
            row=0, column=0, sticky=tk.E, padx=5, pady=3)
        self.tab_entry = tk.Entry(entry_frame, width=12)
        self.tab_entry.grid(row=0, column=1, sticky=tk.W)

        tk.Label(entry_frame, text="Batch:").grid(
            row=1, column=0, sticky=tk.E, padx=5, pady=3)
        self.batch_entry = tk.Entry(entry_frame, width=12)
        self.batch_entry.grid(row=1, column=1, sticky=tk.W)

        tk.Label(entry_frame, text="Ballot Number:").grid(
            row=2, column=0, sticky=tk.E, padx=5, pady=3)
        self.ballot_num_entry = tk.Entry(entry_frame, width=12)
        self.ballot_num_entry.grid(row=2, column=1, sticky=tk.W)

        tk.Button(self.root, text="Look Up Ballot",
                  command=self.print_specific_ballot, width=15).pack(pady=8)

        result_frame = tk.Frame(self.root, padx=10, pady=5)
        result_frame.pack(fill=tk.BOTH, expand=True)
        tk.Label(result_frame, text="Ballot Contents:").pack(anchor=tk.W)
        self.ballot_result_text = tk.Text(result_frame, height=12, state=tk.DISABLED)
        self.ballot_result_text.pack(fill=tk.BOTH, expand=True, pady=(5, 5))

        tk.Button(self.root, text="Back to Main Menu",
                  command=self.show_main_menu, width=20).pack(pady=5)

    def print_specific_ballot(self):
        tabulator  = self.tab_entry.get().strip()
        batch      = self.batch_entry.get().strip()
        ballot_num = self.ballot_num_entry.get().strip()

        if not tabulator or not batch or not ballot_num:
            messagebox.showerror("Error",
                "Please enter the tabulator, batch, and ballot number.")
            return

        imprinted_id = f"{tabulator}-{batch}-{ballot_num}"

        try:
            if self.cvr_data is None:
                self._parse_cvr()

            ballot = self._find_ballot(imprinted_id)
            lines  = self._generate_ballot_output(imprinted_id, ballot)

            self.ballot_result_text.config(state=tk.NORMAL)
            self.ballot_result_text.delete(1.0, tk.END)
            self.ballot_result_text.insert(tk.END, "\n".join(lines))
            self.ballot_result_text.config(state=tk.DISABLED)

        except Exception as e:
            messagebox.showerror("Error", f"Error looking up ballot: {e}")

    # ------------------------------------------------------------------
    # CVR parsing and ballot helpers
    # ------------------------------------------------------------------
    def _parse_cvr(self):
        """Parse self.cvr_filepath and populate self.cvr_data / self.contests."""
        with open(self.cvr_filepath, 'r', newline='', encoding='utf-8') as f:
            rows = list(csv.reader(f))

        if len(rows) < 5:
            raise ValueError("CVR file must have at least 5 rows.")

        row2 = rows[1]   # contest names
        row3 = rows[2]   # choice names
        row4 = rows[3]   # column headers

        # Count ID columns (up to and including "BallotType")
        self.id_column_count = 0
        self.imprinted_id_col = None
        for i, header in enumerate(row4):
            if header.strip():
                self.id_column_count = i + 1
                if header.strip() == "ImprintedId":
                    self.imprinted_id_col = i
                if header.strip() == "BallotType":
                    break

        if self.imprinted_id_col is None:
            raise ValueError("Could not find 'ImprintedId' column in the CVR header.")

        # Build contest list from row 2
        self.contests = []
        current_contest = None
        contest_start = None
        for i in range(self.id_column_count, len(row2)):
            cell = row2[i].strip() if i < len(row2) else ""
            if cell and cell != current_contest:
                if current_contest is not None:
                    self.contests.append((current_contest, contest_start, i - 1))
                current_contest = cell
                contest_start = i
        if current_contest is not None:
            self.contests.append((current_contest, contest_start, len(row2) - 1))

        self.cvr_data = {
            'row2': row2,
            'row3': row3,
            'row4': row4,
            'ballots': rows[4:]
        }

    def _find_ballot(self, imprinted_id):
        """Return the ballot row for an ImprintedId, or None if not found."""
        for ballot in self.cvr_data['ballots']:
            if (len(ballot) > self.imprinted_id_col and
                    ballot[self.imprinted_id_col].strip() == imprinted_id):
                return ballot
        return None

    def _format_contest_name(self, contest_name):
        """Strip '(Vote For=1)' suffix; keep other suffixes."""
        m = re.search(r'\s*\(Vote For=(\d+)\)\s*$', contest_name)
        if m and m.group(1) == '1':
            return contest_name[:m.start()].strip()
        return contest_name

    def _generate_ballot_output(self, imprinted_id, ballot):
        """Return a list of text lines describing a single ballot."""
        lines = [f"ImprintedId {imprinted_id}"]
        if ballot is None:
            lines.append("Missing")
            return lines

        row3 = self.cvr_data['row3']
        for contest_name, start_col, end_col in self.contests:
            # Skip contests not on this ballot (all cells blank)
            if not any(col < len(ballot) and ballot[col].strip() != ""
                       for col in range(start_col, end_col + 1)):
                continue

            display_name = self._format_contest_name(contest_name)
            selected = [
                row3[col].strip()
                for col in range(start_col, end_col + 1)
                if col < len(ballot) and ballot[col].strip() == "1"
                and col < len(row3) and row3[col].strip()
            ]

            vote_str = ", ".join(selected) if selected else "NO VOTE"
            combined = f"{display_name} - {vote_str}"
            if len(combined) < 84:
                lines.append(combined)
            else:
                lines.append(display_name)
                for v in (selected if selected else ["NO VOTE"]):
                    lines.append("        " + v)

        return lines

    # ------------------------------------------------------------------
    # Manifest helpers
    # ------------------------------------------------------------------
    def _load_manifest_locations(self):
        """Return {(tabulator_id, batch_id): location} from the ballot manifest.
        Both keys are stripped strings. Returns empty dict if no manifest available."""
        if not self.manifest_filepath:
            return {}
        locations = {}
        with open(self.manifest_filepath, newline='', encoding='utf-8-sig') as f:
            reader = csv.reader(f)
            next(reader)  # skip header
            for row in reader:
                if not any(cell.strip() for cell in row):
                    continue
                tabulator = row[1].strip()
                batch     = row[2].strip()
                location  = row[4].strip() if len(row) > 4 else ""
                locations[(tabulator, batch)] = location
        return locations

    # ------------------------------------------------------------------
    # Contest results helpers
    # ------------------------------------------------------------------
    def _parse_results_file(self, filepath):
        """Return {(contest, choice): vote_count} from a 3-column CSV."""
        results = {}
        with open(filepath, 'r', newline='', encoding='utf-8') as f:
            for lineno, row in enumerate(csv.reader(f), 1):
                if len(row) != 3:
                    raise ValueError(f"Line {lineno}: expected 3 columns, got {len(row)}")
                contest = row[0].strip()
                choice  = row[1].strip()
                try:
                    votes = int(row[2].strip())
                except ValueError:
                    raise ValueError(
                        f"Line {lineno}: vote count '{row[2]}' is not an integer")
                results[(contest, choice)] = votes
        return results

    def _compute_cvr_results(self):
        """Return {(contest, choice): vote_count} tallied from self.cvr_data."""
        results = {}
        row3 = self.cvr_data['row3']
        for contest_name, start_col, end_col in self.contests:
            cn = contest_name.strip()
            for col in range(start_col, end_col + 1):
                choice = row3[col].strip() if col < len(row3) else ""
                if choice:
                    results[(cn, choice)] = 0
        for ballot in self.cvr_data['ballots']:
            for contest_name, start_col, end_col in self.contests:
                cn = contest_name.strip()
                for col in range(start_col, end_col + 1):
                    if col < len(ballot) and ballot[col].strip() == "1":
                        choice = row3[col].strip() if col < len(row3) else ""
                        if choice:
                            results[(cn, choice)] = results.get((cn, choice), 0) + 1
        return results


# Run the application
if __name__ == "__main__":
    root = tk.Tk()
    app = RLAAuditHelperApp(root)
    root.mainloop()
