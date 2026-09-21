"""Behaviour checks for coverage invalidation; no Lean/network dependency."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("corpus_review", Path(__file__).with_name("corpus_review.py"))
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        review.ROOT = self.root
        subprocess.run(["git", "init", "-q", str(self.root)], check=True, capture_output=True)
        (self.root / "CsdLean4").mkdir()
        self.write("CsdLean4/A.lean", "module\n/- nested /- import Missing -/ comment -/\ndef a := 1\n")
        self.write("CsdLean4/B.lean", "module\npublic import all CsdLean4.A\ndef b := a\n")
        self.write("CsdLean4/C.lean", 'module\n/-\nimport CsdLean4.Missing\n-/\ndef c := "import CsdLean4.Missing"\n')
        self.write("lean-toolchain", "example:v1\n")
        review.git("add", ".")
        self.rows = review.reconcile({}, review.inventory())
        for row in self.rows.values():
            row.update(review_scope="full", reviewed_blob=row["blob"],
                       reviewed_context=row["context_hash"], validation_status="passed",
                       evidence="specs/reviews/example.md", issues="CR-EXAMPLE")
            row["status"] = review.effective(row)

    def write(self, path, content):
        (self.root / path).write_text(content, encoding="utf-8")

    def test_changed_dependency_invalidates_consumers_not_unrelated_files(self):
        self.write("CsdLean4/A.lean", "module\ndef a := 2\n")
        rows = review.reconcile(self.rows, review.inventory())
        self.assertEqual(rows["CsdLean4/A.lean"]["status"], "stale-source")
        self.assertEqual(rows["CsdLean4/B.lean"]["status"], "stale-dependency")
        self.assertEqual(rows["CsdLean4/C.lean"]["status"], "reviewed")
        self.assertEqual(rows["CsdLean4/B.lean"]["issues"], "CR-EXAMPLE")

    def test_toolchain_change_invalidates_every_review(self):
        self.write("lean-toolchain", "example:v2\n")
        rows = review.reconcile(self.rows, review.inventory())
        self.assertEqual({r["status"] for r in rows.values()}, {"stale-dependency"})

    def test_added_and_retired_files_keep_historical_evidence(self):
        self.write("CsdLean4/D.lean", "module\ndef d := 0\n")
        review.git("add", "CsdLean4/D.lean")
        review.git("update-index", "--force-remove", "CsdLean4/C.lean")
        rows = review.reconcile(self.rows, review.inventory())
        self.assertEqual(rows["CsdLean4/D.lean"]["status"], "unreviewed")
        self.assertEqual(rows["CsdLean4/C.lean"]["status"], "retired")
        self.assertEqual(rows["CsdLean4/C.lean"]["evidence"], "specs/reviews/example.md")

    def test_partial_and_historical_reviews_never_count_as_complete(self):
        row = self.rows["CsdLean4/A.lean"].copy()
        row["review_scope"] = "partial"
        self.assertEqual(review.effective(row), "partial")
        row.update(review_scope="full", validation_status="pending")
        self.assertEqual(review.effective(row), "source-reviewed")
        row.update(reviewed_blob="", prior_evidence="older-review.md")
        self.assertEqual(review.effective(row), "historical")

    def test_import_parser_fails_closed_on_unknown_import_syntax(self):
        self.write("CsdLean4/B.lean", "module\nimport CsdLean4.A CsdLean4.C\n")
        with self.assertRaisesRegex(ValueError, "Unsupported import syntax"):
            review.inventory()


if __name__ == "__main__":
    unittest.main()
