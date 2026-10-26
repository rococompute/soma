#!/usr/bin/env python3
"""Graduality lattice: make the type annotations of typed Rocq programs less
precise, and check that the programs still compile and compute the same.

For each file of the corpus (ordinary typed Rocq, compiled with gradual
typing on), every type annotation is a site: binders `(x : T)` (also in
`fun` and constructors) and return types `: T :=`. A mutant replaces one
site by `Dyn`, or one base type inside it (`list nat` -> `list Dyn`); there
are also mutants with every site of a definition, or of the whole file, set
to `Dyn`. Each mutant is the whole file with that change, so the uses of a
mutated definition must keep compiling too.

Graduality (Lennon-Bertrand et al., GCIC) predicts, for these programs:
  - static: every mutant compiles (making a type less precise never
    turns an accepted program into a rejected one);
  - dynamic: every observation (`Definition obs_... : T := ...`, at a fixed
    type) has the same value as in the original, since a well-typed
    program has no source of `unk` or `raise`.

Outcomes of a mutant: compiled, rejected (with the error), out of steps
(Gradual Steps), or timeout. Outcomes of an observation: same, less
precise (`unk` where the original has a value), raise, or different.

Usage: lattice.py [--rocq PATH] [--jobs N] [--out DIR] [corpus files...]
"""

import argparse, concurrent.futures, json, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
DEFAULT_ROCQ = os.path.join(ROOT, "_build", "install", "default", "bin", "rocq")
TIMEOUT = 120
SORTS = {"Type", "Set", "Prop", "SProp"}

# ---------------------------------------------------------------- parsing

def comment_mask(text):
    """The text with comments replaced by spaces (same length)."""
    out, i, depth = list(text), 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1; out[i] = out[i + 1] = " "; i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1; out[i] = out[i + 1] = " "; i += 2
        else:
            if depth and text[i] != "\n": out[i] = " "
            i += 1
    return "".join(out)

def sentences(text):
    """(start, end) of the sentences: a '.' followed by a blank or the end."""
    masked, res, start = comment_mask(text), [], 0
    for m in re.finditer(r"\.(\s|$)", masked):
        res.append((start, m.start() + 1)); start = m.end()
    return res

def match_close(s, i):
    """Index of the parenthesis closing the one at s[i]."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] in "([{": depth += 1
        elif s[j] in ")]}":
            depth -= 1
            if depth == 0: return j
    return -1

IDENT = r"[A-Za-z_][A-Za-z0-9_']*"

def sites(text, start, end):
    """Type annotations in a sentence, as (start, end, kind) of the type."""
    masked = comment_mask(text)[start:end]
    head = re.match(r"\s*(Definition|Fixpoint|Inductive)\s+(" + IDENT + ")", masked)
    if not head or head.group(2).startswith("obs_"): return []
    found = []
    # binders and ascriptions: ( idents : T )
    for m in re.finditer(r"\(\s*(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*:(?!=)", masked):
        close = match_close(masked, m.start())
        if close < 0: continue
        t0 = m.end()
        typ = masked[t0:close]
        if typ.strip() in SORTS or not typ.strip(): continue
        found.append((start + t0, start + close, "binder"))
    # return type: ':' at depth 0 before ':=' (Definition, Fixpoint)
    if head.group(1) in ("Definition", "Fixpoint"):
        depth, i = 0, head.end()
        while i < len(masked):
            c = masked[i]
            if c in "([{": depth += 1
            elif c in ")]}": depth -= 1
            elif depth == 0 and masked.startswith(":=", i): break
            elif depth == 0 and c == ":":
                stop = masked.find(":=", i)
                typ = masked[i + 1:stop]
                if typ.strip() and typ.strip() not in SORTS and "{struct" not in typ:
                    found.append((start + i + 1, start + stop, "return"))
                break
            i += 1
    return found

def base_types(text):
    """Types without arguments, which an inner mutation may replace by Dyn
    (an applied type constructor cannot be: [Dyn A] is not a type)."""
    names = {"nat", "bool", "unit"}
    names |= set(re.findall(r"(?:Inductive|Record)\s+(" + IDENT + r")\s*:?=", text))
    return names

def variants(text, site, types):
    """Less precise replacements of the type at [site]: Dyn, and each base
    type occurrence inside it replaced by Dyn."""
    s, e, _ = site
    typ = text[s:e]
    res = [(" Dyn ", "whole")]
    toks = list(re.finditer(IDENT, typ))
    if len(toks) > 1:
        for t in toks:
            if t.group(0) in types:
                res.append((typ[:t.start()] + "Dyn" + typ[t.end():], "inner " + t.group(0)))
    return res

# ---------------------------------------------------------------- running

def observations(text):
    return re.findall(r"Definition\s+(obs_[A-Za-z0-9_']*)", text)

def run_rocq(rocq, name, text, obs):
    """Compile [text] with gradual typing on; return (status, detail, values)."""
    d = tempfile.mkdtemp(prefix="lattice")
    try:
        body = text + "\nSet Printing All.\n" + "".join(
            "Eval lazy in %s.\n" % o for o in obs)
        path = os.path.join(d, name)
        with open(path, "w") as f: f.write(body)
        try:
            p = subprocess.run([rocq, "c", "-q", "-ri", "Corelib.Gradual.Gradual", name],
                               cwd=d, capture_output=True, text=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return "timeout", "", {}
        out = p.stdout + p.stderr
        if p.returncode != 0:
            err = " ".join(out[out.find("Error"):].split())[:300] if "Error" in out else out[-300:]
            if "Gradual reduction exceeded" in out: return "out_of_steps", err, {}
            return "rejected", err, {}
        vals = re.findall(r"^\s*= (.*?)\n\s*: ", out, re.S | re.M)
        vals = [" ".join(v.split()) for v in vals]
        return "compiled", "", dict(zip(obs, vals))
    finally:
        shutil.rmtree(d, ignore_errors=True)

# ------------------------------------------------------------- comparing

def tree(s):
    """Printed term as nested lists of atoms."""
    stack, cur = [], []
    for tok in re.findall(r"\(|\)|[^\s()]+", s):
        if tok == "(": stack.append(cur); cur = []
        elif tok == ")": sub, cur = cur, stack.pop(); cur.append(sub)
        else: cur.append(tok)
    return cur

def less_precise(m, o):
    """[m] is [o] with some subterms replaced by unknown."""
    if isinstance(m, list) and m and m[0] == "@unknown": return True
    if isinstance(m, str) or isinstance(o, str): return m == o
    return len(m) == len(o) and all(less_precise(a, b) for a, b in zip(m, o))

def compare(mv, ov):
    if mv == ov: return "same"
    if "@err" in mv.split() or "(@err" in mv: return "raise"
    if less_precise(tree(mv), tree(ov)): return "less_precise"
    return "different"

# ------------------------------------------------------------------ main

def mutants(text):
    """(description, mutated text) for the single-site, per-definition and
    whole-file mutants."""
    types = base_types(text)
    per_sentence = [(s, e, sites(text, s, e)) for s, e in sentences(text)]
    res = []
    for s, e, ss in per_sentence:
        name = re.match(r"\s*\w+\s+(" + IDENT + ")", comment_mask(text)[s:e]).group(1) if ss else None
        for site in ss:
            for rep, how in variants(text, site, types):
                line = text.count("\n", 0, site[0]) + 1
                desc = "%s: %s %s (line %d) %s -> %s" % (
                    name, site[2], how, line, " ".join(text[site[0]:site[1]].split()), rep.strip())
                res.append(("single", desc, text[:site[0]] + rep + text[site[1]:]))
        if len(ss) > 1:
            t = text
            for site in sorted(ss, reverse=True):
                t = t[:site[0]] + " Dyn " + t[site[1]:]
            res.append(("definition", "%s: all %d annotations -> Dyn" % (name, len(ss)), t))
    all_sites = sorted([x for _, _, ss in per_sentence for x in ss], reverse=True)
    t = text
    for site in all_sites:
        t = t[:site[0]] + " Dyn " + t[site[1]:]
    res.append(("file", "all %d annotations of the file -> Dyn" % len(all_sites), t))
    return res

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rocq", default=DEFAULT_ROCQ)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--out", default=os.path.join(HERE, "results"))
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    files = a.files or sorted(os.path.join(HERE, "corpus", f)
                              for f in os.listdir(os.path.join(HERE, "corpus")) if f.endswith(".v"))
    os.makedirs(a.out, exist_ok=True)
    results = []
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for path in files:
            name = os.path.basename(path)
            text = open(path).read()
            obs = observations(text)
            base = run_rocq(a.rocq, name, text, obs)
            if base[0] != "compiled":
                print("baseline of %s does not compile: %s" % (name, base[1]), file=sys.stderr)
                sys.exit(2)
            ms = mutants(text)
            futs = [pool.submit(run_rocq, a.rocq, name, mt, obs) for _, _, mt in ms]
            for (kind, desc, _), fut in zip(ms, futs):
                status, err, vals = fut.result()
                cmp = {o: compare(vals[o], base[2][o]) for o in vals}
                results.append({"file": name, "kind": kind, "mutant": desc, "status": status,
                                "error": err, "observations": cmp,
                                "values": {o: vals[o] for o in vals if cmp[o] != "same"},
                                "expected": {o: base[2][o] for o in vals if cmp[o] != "same"}})
            print("%s: %d mutants" % (name, len(ms)), file=sys.stderr)
    with open(os.path.join(a.out, "results.json"), "w") as f:
        json.dump(results, f, indent=1)
    report(results, os.path.join(a.out, "report.md"))
    print(open(os.path.join(a.out, "report.md")).read())

# Why a mutant is rejected, from the error message.
CAUSES = [
    ("structural recursion on a Dyn argument",
     r'Recursive definition on "Dyn"|Cannot guess decreasing argument'),
    ("recursive call on a cast (a constructor field made Dyn)",
     r"principal argument equal to \"cast"),
    ("an implicit argument that nothing determines (no argument or expected type fixes it)",
     r"unresolved implicit arguments|Cannot infer the implicit parameter"),
    ("an argument of an inductive type left undetermined",
     r"Cannot infer the \w+ argument of the inductive type"),
    ("match or if on a scrutinee of type Dyn",
     r"which is not a \(co-\)inductive type"),
    ("dependent match on a cast to an indexed family (index or return type not inferred)",
     r"match cast Dyn|cast Dyn \w+ \?u|The term \"vnil\" has type"),
]

def cause(err):
    for name, rx in CAUSES:
        if re.search(rx, err): return name
    return "other"

def report(results, path):
    from collections import Counter
    st = Counter(r["status"] for r in results)
    obs = Counter(v for r in results for v in r["observations"].values())
    lines = ["# Graduality lattice", "",
             "%d mutants of %d files." % (len(results), len({r["file"] for r in results})), "",
             "| Static: mutant | count |", "|---|---|"]
    lines += ["| %s | %d |" % (k, st[k]) for k in ("compiled", "rejected", "out_of_steps", "timeout")]
    lines += ["", "| Dynamic: observation of a compiled mutant | count |", "|---|---|"]
    lines += ["| %s | %d |" % (k, obs[k]) for k in ("same", "less_precise", "raise", "different")]
    by_kind = Counter((r["kind"], r["status"]) for r in results)
    lines += ["", "| Mutants by kind | compiled | rejected | out of steps | timeout |", "|---|---|---|---|---|"]
    for k in ("single", "definition", "file"):
        lines.append("| %s | %d | %d | %d | %d |" % (k, by_kind[(k, "compiled")], by_kind[(k, "rejected")],
                                                     by_kind[(k, "out_of_steps")], by_kind[(k, "timeout")]))
    bad = [r for r in results if r["status"] != "compiled"]
    causes = Counter(cause(r["error"]) for r in bad)
    if bad:
        lines += ["", "| Why mutants are rejected | count |", "|---|---|"]
        lines += ["| %s | %d |" % (k, n) for k, n in causes.most_common()]
    if bad:
        lines += ["", "## Mutants that do not compile", ""]
        for r in bad:
            lines.append("- `%s` %s: **%s** (%s) — %s" % (r["file"], r["mutant"], r["status"],
                                                         cause(r["error"]), r["error"]))
    diff = [r for r in results if any(v != "same" for v in r["observations"].values())]
    if diff:
        lines += ["", "## Observations that changed", ""]
        for r in diff:
            for o, v in r["observations"].items():
                if v != "same":
                    lines.append("- `%s` %s: `%s` is **%s**: `%s` (original `%s`)" % (
                        r["file"], r["mutant"], o, v, r["values"][o], r["expected"][o]))
    with open(path, "w") as f: f.write("\n".join(lines) + "\n")

if __name__ == "__main__":
    main()
