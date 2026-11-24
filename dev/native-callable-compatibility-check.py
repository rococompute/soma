#!/usr/bin/env python3
"""Retain a cold-cache, byte-exact baseline/candidate callable ABI comparison.

Run under the caller's build lock. The output directory must be empty; each
compiler gets its own fresh project/cache and retained native products.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("output directory must be empty (retained evidence is never overwritten)")
    fixture = Path(__file__).resolve().parents[1] / "examples/example_projects/native_callables"
    source_files = sorted(path for path in fixture.iterdir() if path.is_file())
    receipt = {
        "format": "soma-native-callable-cold-compatibility-v1",
        "cold_independent_caches": True,
        "source": {path.name: digest(path) for path in source_files},
        "compilers": {},
        "products": {},
    }
    for name, compiler in (("baseline", args.baseline), ("candidate", args.candidate)):
        # Keep the installed entry-point path: Soma locates its libraries
        # relative to argv[0], even when that entry point is a symlink.
        compiler = compiler.absolute()
        compiler.resolve(strict=True)
        root = output / name
        project = root / "project"
        project.mkdir(parents=True)
        for source in source_files:
            shutil.copyfile(source, project / source.name)
        native = root / "native"
        with (root / "extract.log").open("w") as log:
            subprocess.run([str(compiler), "extract", "main.soma", "-o", str(native)],
                           cwd=project, stdout=log, stderr=subprocess.STDOUT, check=True)
        with (root / "main.hashes.txt").open("w") as hashes:
            subprocess.run([str(compiler), "hash", "main.soma"], cwd=project,
                           stdout=hashes, check=True)
        receipt["compilers"][name] = {
            "invocation": str(compiler),
            "executable": str(compiler.resolve(strict=True)),
            "sha256": digest(compiler),
            "source": str(project.relative_to(output)),
            "cache": str((project / ".soma-cache").relative_to(output)),
        }
    baseline = output / "baseline"
    candidate = output / "candidate"
    names = sorted(path.name for path in (baseline / "native").glob("soma_callable_*.ml"))
    if not names:
        raise RuntimeError("baseline did not emit callable schemas")
    candidate_names = sorted(path.name for path in (candidate / "native").glob("soma_callable_*.ml"))
    if names != candidate_names:
        raise RuntimeError("emitted callable schema filenames differ")
    relative_products = ["native/" + name for name in names] + [
        "native/soma_bindings.ml", "native/prog.ml", "native/prog.mli",
        "native/native_abi.manifest", "native/native_callables.manifest", "main.hashes.txt",
    ]
    failures = []
    for relative in relative_products:
        old = baseline / relative
        new = candidate / relative
        equal = old.read_bytes() == new.read_bytes()
        receipt["products"][relative] = {
            "baseline": str(old.relative_to(output)),
            "candidate": str(new.relative_to(output)),
            "baseline_sha256": digest(old),
            "candidate_sha256": digest(new),
            "equal": equal,
        }
        if not equal:
            failures.append(relative)
    receipt["equal"] = not failures
    receipt_path = output / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if failures:
        raise RuntimeError("callable compatibility differs: " + ", ".join(failures))
    print(f"PASS: {len(relative_products)} cold-cache callable products/hash reports byte-identical")
    print(f"Retained evidence: {receipt_path}")
    print(f"Receipt SHA256: {digest(receipt_path)}")


if __name__ == "__main__":
    main()

