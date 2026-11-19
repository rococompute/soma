#!/usr/bin/env bash
# Use the complete production parser, independently of the compiler build.
set -euo pipefail
source_root="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
cp "$source_root/clib/somaToml.ml" "$fixture/somaToml.ml"
cat > "$fixture/check.ml" <<'ML'
let repeat text count = String.concat "" (List.init count (fun _ -> text))
let parsed text = ignore (SomaToml.parse text)
let limited label text =
  match SomaToml.parse text with
  | _ -> failwith (label ^ ": accepted excessive nesting")
  | exception SomaToml.Error (line, message) ->
      assert (line >= 1);
      let needle = "nesting exceeds the limit" in
      let rec contains i =
        i + String.length needle <= String.length message &&
        (String.sub message i (String.length needle) = needle || contains (i + 1)) in
      if not (contains 0) then failwith (label ^ ": " ^ message)
let () =
  List.iter (fun depth ->
      parsed ("x = " ^ repeat "[" depth ^ "0" ^ repeat "]" depth);
      parsed ("x = " ^ repeat "{ a = " depth ^ "0" ^ repeat "}" depth);
      parsed ("x = " ^ repeat "[{ a = " (depth / 2) ^ "0" ^ repeat "}]" (depth / 2));
      parsed (String.concat "." (List.init depth (fun _ -> "a")) ^ " = 0")) [1; 16; 128];
  List.iter (fun depth ->
      limited "array" ("x = " ^ repeat "[" depth ^ "0" ^ repeat "]" depth);
      limited "inline table" ("x = " ^ repeat "{ a = " depth ^ "0" ^ repeat "}" depth);
      limited "mixed" ("x = " ^ repeat "[{ a = " depth ^ "0" ^ repeat "}]" depth);
      limited "dotted key" (String.concat "." (List.init depth (fun _ -> "a")) ^ " = 0");
      limited "header" ("[" ^ String.concat "." (List.init depth (fun _ -> "a")) ^ "]\nx = 0"))
    [129; 100000];
  (* Nesting state belongs to a parse, not a process-global counter. *)
  parsed "[project]\nname = 'fine'\nvalues = [1, { a = [true, false] }]";
  print_endline "TOML nesting is bounded with contextual parser errors: passed"
ML
(cd "$fixture" && ocamlc -o check somaToml.ml check.ml && ./check)
