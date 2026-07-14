#!/usr/bin/env python3
"""
Headless runner for RLAAuditHelperApp, for scripting/testing without
clicking through the GUI (there's currently no CLI mode upstream).

Usage:
    python3 scripts/run_headless.py <data_dir> <output_dir>

<data_dir> must contain a CONTENTS file plus whatever it references
(CVRfile, ballotmanifest, ballotlist). Zips the directory in memory (the
app's loader expects a zip), loads it, and prints ballot contents for all
audit boards into <output_dir>.
"""
import os
import sys
import zipfile
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))
import tkinter as tk
import RLAAuditHelper as mod


def run(data_dir: str, output_dir: str) -> None:
    os.makedirs(output_dir, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmpdir:
        zip_path = os.path.join(tmpdir, "data.zip")
        with zipfile.ZipFile(zip_path, "w") as zf:
            for name in os.listdir(data_dir):
                path = os.path.join(data_dir, name)
                if os.path.isfile(path):
                    zf.write(path, name)

        root = tk.Tk()
        root.withdraw()
        app = mod.RLAAuditHelperApp(root)
        try:
            app.show_file_screen()
            app.file_entry.insert(0, zip_path)
            app.load_input_data()

            if not app.cvr_filepath:
                raise SystemExit("No CVR file loaded -- check CONTENTS/CVRfile.")
            if not app.manifest_filepath:
                raise SystemExit("No manifest loaded -- check CONTENTS/ballotmanifest.")
            if not app.ballot_lists:
                raise SystemExit("No ballot list loaded -- check CONTENTS/ballotlist.")

            print(f"CVR: {app.cvr_filepath}")
            print(f"Manifest: {app.manifest_filepath}")
            for n, ids in app.ballot_lists:
                print(f"Audit Board {n}: {len(ids)} ballot(s)")

            app.show_print_ballot_lists_screen()
            app.output_folder_entry.insert(0, output_dir)
            app.ab_var.set("all")
            app.print_ballot_lists()

            print(f"\nWrote to {output_dir}:")
            for fn in sorted(os.listdir(output_dir)):
                print(f"  {fn}")
        finally:
            root.destroy()


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    run(sys.argv[1], sys.argv[2])
