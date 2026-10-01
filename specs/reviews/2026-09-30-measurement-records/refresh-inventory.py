"""Recompute freshness of the archived prior ledger; does not grant review credit."""
import importlib.util
from pathlib import Path

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("inventory", here / "corpus_review_snapshot.py")
inventory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inventory)
inventory.ROOT = here.parents[2]
inventory.LEDGER = str(here / "prior-ledger.tsv")
inventory.report(inventory.reconcile(inventory.read_ledger(), inventory.inventory()))
