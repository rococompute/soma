#!/usr/bin/env python3
"""Check insert against Kykeon's actual allocator helpers and inventory the app.
Does not edit/build/run Kykeon's unikernel, agents, brokers, or native C code.
Only the allocator module is executed on the host, with native calls disabled.
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kykeon", type=Path, default=ROOT.parent / "kykeon")
    parser.add_argument("--report", type=Path, help="Preserve the complete app inventory at a new path")
    args = parser.parse_args()
    source = args.kykeon.resolve() / "unikernel"
    soma = os.environ.get("SOMA", str(ROOT / "_build/install/default/bin/soma"))

    def run(command, cwd, codes=(0,)):
        p = subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=300)
        if p.returncode not in codes:
            raise RuntimeError(f"{command}: exit {p.returncode}\n{p.stdout}\n{p.stderr}")
        return p

    with tempfile.TemporaryDirectory(prefix="soma-insert-kykeon-") as work:
        work = Path(work)
        # Compile the whole original allocator, with fail-fast native fixtures.
        # None of these native operations is needed by round_up/round_down.
        (work / "guest.ml").write_text('''let user_memory () = failwith "native operation in pure allocator test"
let set_bounds _ _ = failwith "native operation in pure allocator test"
let raw_memset _ _ _ = failwith "native operation in pure allocator test"
''')
        shutil.copyfile(source / "lx/mem.ml", work / "mem.ml")
        cases = [0, 1, 4095, 4096, 4097, -1, -(1 << 62), (1 << 62) - 1]
        (work / "reference.ml").write_text("let () = List.iter (fun x -> Printf.printf \"%d %d\\n\" (Mem.round_up x) (Mem.round_down x)) ["
                                           + ";".join(map(str, cases)) + "]\n")
        run(["ocamlc", "-o", "reference", "guest.ml", "mem.ml", "reference.ml"], work)
        expected = [tuple(map(int, line.split())) for line in run([str(work / "reference")], work).stdout.splitlines()]
        out = work / "translated"
        result = run([soma, "insert", str(source / "lx/mem.ml"), "-I", str(work),
                      "--partial", "--out", str(out), "--json"], work, codes=(1,))
        report = json.loads(result.stdout)
        assert any(d["code"] == "mutation" for f in report["files"] for d in f["diagnostics"])
        literal = lambda n: f"{n & ((1 << 63) - 1)}%uint63"
        expectations = []
        for i, (value, (up, down)) in enumerate(zip(cases, expected)):
            for suffix, target, answer in [("up", "oc_round_5fup", up), ("down", "oc_round_5fdown", down)]:
                expectations.append(f"Example allocator_{suffix}_{i} : {target} {literal(value)} = {literal(answer)}. Proof. reflexivity. Qed.\n")
        (out / "mem.exp").write_text("".join(expectations))
        run([soma, "check", str(out / "mem.soma")], work)
        print("PASS Kykeon allocator: 16 OCaml/Soma comparisons, including negative and overflowing values")

        command = [soma, "insert", str(source), "--partial", "--report-only", "--json"]
        if args.report:
            command += ["--report", str(args.report.resolve())]
        result = run(command, work, codes=(0, 1))
        report = json.loads(result.stdout)
        files = report["files"]
        print(f"Kykeon inventory: {len(files)} files; {sum(f['translated_items'] for f in files)}/{sum(f['source_items'] for f in files)} checked top-level items")
        counts = Counter(d["code"] for f in files for d in f["diagnostics"])
        print("Remaining diagnostics: " + ", ".join(f"{key}={value}" for key, value in counts.most_common()))


if __name__ == "__main__":
    main()
