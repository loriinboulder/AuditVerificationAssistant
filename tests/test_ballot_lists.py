"""Tests for loading the combined-CSV ballot list format (CONTENTS: ballotlist:...)."""

import os
import zipfile
from unittest.mock import patch

import pytest

tk = pytest.importorskip("tkinter")

import RLAAuditHelper as mod

TESTDATA_DEMO = os.path.join(os.path.dirname(__file__), "..", "testdata-demo")


def _zip_dir(src_dir, dest_zip):
    with zipfile.ZipFile(dest_zip, "w") as zf:
        for name in os.listdir(src_dir):
            path = os.path.join(src_dir, name)
            if os.path.isfile(path):
                zf.write(path, name)


def _make_app():
    try:
        root = tk.Tk()
    except tk.TclError:
        pytest.skip("no display available for Tk")
    root.withdraw()
    return root, mod.RLAAuditHelperApp(root)


def _load_zip(app, zip_path):
    app.show_file_screen()
    app.file_entry.insert(0, str(zip_path))
    app.load_input_data()


def test_combined_ballot_list_is_split_by_audit_board(tmp_path):
    zip_path = tmp_path / "demo.zip"
    _zip_dir(TESTDATA_DEMO, zip_path)

    root, app = _make_app()
    try:
        _load_zip(app, zip_path)

        boards = dict(app.ballot_lists)
        assert set(boards) == {1, 2}
        assert len(boards[1]) == 81
        assert len(boards[2]) == 90
        assert boards[1][0] == "102-1-7"
    finally:
        root.destroy()


def test_print_ballot_lists_writes_one_file_per_board(tmp_path):
    zip_path = tmp_path / "demo.zip"
    _zip_dir(TESTDATA_DEMO, zip_path)

    root, app = _make_app()
    try:
        _load_zip(app, zip_path)

        app.show_print_ballot_lists_screen()
        outdir = tmp_path / "out"
        outdir.mkdir()
        app.output_folder_entry.insert(0, str(outdir))
        app.ab_var.set("all")
        app.print_ballot_lists()

        written = sorted(os.listdir(outdir))
        assert written == [
            "BallotContents_AuditBoard_1.txt",
            "BallotContents_AuditBoard_2.txt",
        ]
    finally:
        root.destroy()


def test_extra_and_reordered_columns_are_ignored(tmp_path):
    data_dir = tmp_path / "gooddata"
    data_dir.mkdir()
    (data_dir / "CONTENTS").write_text("ballotlist:ballotlist.csv\n")
    (data_dir / "ballotlist.csv").write_text(
        "audit_board,extra,imprinted_id\n"
        "Audit board 1,foo,102-1-7\n"
        "Audit board 2,bar,105-36-7\n"
    )
    zip_path = tmp_path / "good.zip"
    _zip_dir(data_dir, zip_path)

    root, app = _make_app()
    try:
        _load_zip(app, zip_path)

        boards = dict(app.ballot_lists)
        assert boards[1] == ["102-1-7"]
        assert boards[2] == ["105-36-7"]
    finally:
        root.destroy()


def test_missing_required_columns_reports_error(tmp_path):
    data_dir = tmp_path / "baddata"
    data_dir.mkdir()
    (data_dir / "CONTENTS").write_text("ballotlist:ballotlist.csv\n")
    (data_dir / "ballotlist.csv").write_text("imprinted_id,board\n102-1-7,Audit board 1\n")
    zip_path = tmp_path / "bad.zip"
    _zip_dir(data_dir, zip_path)

    root, app = _make_app()
    try:
        with patch("RLAAuditHelper.messagebox.showerror") as mock_err:
            _load_zip(app, zip_path)
        assert mock_err.called
        assert app.ballot_lists == []
    finally:
        root.destroy()
