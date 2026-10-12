"""End-to-end parser/runner regressions; no third-party Python dependencies."""
import pathlib
import subprocess
import sys
import unittest

BINARY = str(pathlib.Path(sys.argv.pop(1)).resolve())
ROOT = pathlib.Path(__file__).resolve().parent.parent


class FrontendTests(unittest.TestCase):
    def run_source(self, source, status=0, output=None, error=None):
        result = subprocess.run(
            [BINARY, "-"], input=source, text=True, capture_output=True, timeout=20
        )
        self.assertEqual(result.returncode, status, result.stdout + result.stderr)
        if output is not None:
            self.assertEqual(result.stdout, "-: " + output + "\n")
        if error is not None:
            self.assertIn(error, result.stderr)
        return result

    def test_examples(self):
        pair = "forall a0. (Int -> Bool -> a0) -> a0"
        auto = "(forall a0. a0 -> a0) -> forall a0. a0 -> a0"
        expected = {
            "A1": "?m0 -> ?m1 -> ?m1",
            "A2": "(?m0 -> ?m0) -> ?m0 -> ?m0",
            "A4": "(forall a0. a0 -> a0) -> ?m0 -> ?m0",
            "A5": auto,
            "A6": "(forall a0. a0 -> a0) -> ?m0 -> ?m0",
            "A7": auto,
            "A10a": pair, "A10b": pair, "A10c": pair,
            "C2": "Int",
            "E2b": "(forall a0. a0 -> a0) -> " + pair,
            "E3b": "(Int -> Bool -> ?m0) -> ?m0",
        }
        files = sorted((ROOT / "examples").glob("*.fresco"))
        self.assertEqual({p.stem for p in files}, set(expected))
        for path in files:
            with self.subTest(example=path.name):
                result = subprocess.run([BINARY, str(path)], capture_output=True, text=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, f"{path}: {expected[path.stem]}\n")

    def test_term_shadowing(self):
        self.run_source("fun (x : unit -> unit) (x : unit) -> x",
                        output="(unit -> unit) -> unit -> unit")

    def test_outer_term_index(self):
        self.run_source("fun (x : unit -> unit) (y : unit) -> x",
                        output="(unit -> unit) -> unit -> unit -> unit")

    def test_type_shadowing(self):
        self.run_source("(fun x y -> y) : forall a. a -> (forall a. a -> a)",
                        output="forall a0. a0 -> forall a1. a1 -> a1")

    def test_application_associates_left(self):
        self.run_source("(fun (f : unit -> unit) x -> f x) (fun x -> x) ()", output="unit")

    def test_context_and_shadowing(self):
        self.run_source("type Int; val x : Int; fun (x : unit) -> x",
                        output="unit -> unit")
        self.run_source("type a0; val f : forall a. a0 -> a; f",
                        output="forall a1. a0 -> a1")
        self.run_source("type Int; val f : Int -> Int; fun x -> f x",
                        output="Int -> Int")

    def test_paper_rejections(self):
        files = sorted((ROOT / "examples" / "rejected").glob("*.fresco"))
        self.assertEqual({p.stem for p in files}, {"A8", "E2a", "E3b-unfrozen"})
        for path in files:
            with self.subTest(example=path.name):
                result = subprocess.run([BINARY, str(path)], capture_output=True, text=True, timeout=20)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("type error", result.stderr)

    def test_comments_and_whitespace(self):
        self.run_source("-- header\n( \n ) -- no final newline", output="unit")

    def test_wildcard(self):
        self.run_source("(fun _ -> ()) ()", output="unit")
        self.run_source("fun _ -> _", 2, error="wildcard")

    def test_rejections(self):
        for source, message in [
            ("", "expected an expression"),
            ("fun x ->", "expected an expression"),
            ("(fun x -> x", "expected ')'"),
            ("{| ()", "expected '|}'"),
            ("() )", "expected end of file"),
            ("() @ unit", "unexpected character"),
            ("fun -> ()", "expected a function parameter"),
            ("() : forall . unit", "expected a binder name"),
            ("x", "unbound term variable x"),
            ("fun (x : a) -> x", "unbound type variable a"),
            ("let x = () in x", "unexpected character"),
            ("type Int; type Int; ()", "duplicate declaration Int"),
            ("val x : unit; val x : unit; x", "duplicate declaration x"),
            ("val x : Int; type Int; x", "unbound type variable Int"),
            ("type Int ()", "expected ';'"),
            ("(fun x -> x) : forall a. b -> a", "unbound type variable b"),
        ]:
            with self.subTest(source=source):
                self.run_source(source, 2, error=message)

    def test_location(self):
        self.run_source("-- comment\nfun x ->\n  missing", 2,
                        error="-:3:3: unbound term variable missing")

    def test_type_errors(self):
        for source in ["() ()", "() : unit -> unit", "{| () |}"]:
            with self.subTest(source=source):
                self.run_source(source, 1, error="type error")

    def test_missing_file_and_usage(self):
        for args in [[], [str(ROOT / "examples" / "does-not-exist.fresco")]]:
            result = subprocess.run([BINARY] + args, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertTrue(result.stderr)

    def test_multiple_files_continue_after_error(self):
        path = ROOT / "examples" / "A1.fresco"
        result = subprocess.run([BINARY, str(path) + ".missing", str(path)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, f"{path}: ?m0 -> ?m1 -> ?m1\n")


if __name__ == "__main__":
    unittest.main()
