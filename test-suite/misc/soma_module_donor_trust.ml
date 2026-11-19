let write f text = Out_channel.with_open_bin f (fun oc -> output_string oc text)
let read f = In_channel.with_open_bin f In_channel.input_all
let mkdir f = Unix.mkdir f 0o700
let exists f = Sys.file_exists f
let context = SomaMerkle.string "test-context"
let () =
  mkdir "stage"; write "stage/whole" "complete bytes";
  mkdir "live";
  assert (not (SomaModuleStore.rename_absent "stage" "live"));
  assert (exists "stage/whole"); assert (Array.length (Sys.readdir "live") = 0);
  write "live/protected" "live bytes";
  assert (not (SomaModuleStore.rename_absent "stage" "live"));
  assert (read "live/protected" = "live bytes");
  (* Actual concurrent creator, including an empty live destination. *)
  let pid = Unix.fork () in
  if pid = 0 then (mkdir "concurrent"; exit 0);
  assert (snd (Unix.waitpid [] pid) = Unix.WEXITED 0);
  assert (not (SomaModuleStore.rename_absent "stage" "concurrent"));
  assert (exists "stage/whole");
  assert (SomaModuleStore.rename_absent "stage" "published");
  assert (not (exists "stage")); assert (read "published/whole" = "complete bytes");
  mkdir "racer-one"; mkdir "racer-two";
  write "racer-one/winner" "one"; write "racer-two/winner" "two";
  let child = Unix.fork () in
  if child = 0 then exit (if SomaModuleStore.rename_absent "racer-one" "race" then 0 else 3);
  let won = SomaModuleStore.rename_absent "racer-two" "race" in
  let child_won = snd (Unix.waitpid [] child) = Unix.WEXITED 0 in
  assert (won <> child_won);
  assert (read "race/winner" = (if won then "two" else "one"));
  assert (exists (if won then "racer-one/winner" else "racer-two/winner"));
  mkdir "nul-stage";
  let rejects source destination =
    try ignore (SomaModuleStore.rename_absent source destination); false
    with Unix.Unix_error _ | Invalid_argument _ -> true in
  assert (rejects "nul-stage\000suffix" "nul-target");
  assert (rejects "nul-stage" "nul-target\000suffix");
  assert (exists "nul-stage" && not (exists "nul-target"));
  print_endline "atomic success/existing-empty/live/concurrent no-replace: passed";
  mkdir "root"; mkdir "cache";
  write "root/a.soma" "value : nat := 1.\n";
  write "root/b.soma" "value : nat := 1.\n";
  let source = SomaModuleStore.source_hash "root/a.soma" in
  write "cache/a.vo" "producer object A bytes";
  write "cache/a.stamp" ("soma-stamp 4\nsource " ^ source ^ "\n");
  SomaCache.record "cache/a.vo"; SomaCache.record "cache/a.stamp";
  SomaModuleStore.record ~root:"root" ~cache:"cache" ~prefix:"" ~source:"root/a.soma"
    ~vo:"cache/a.vo" ~stamp:"cache/a.stamp" ~expected:source;
  assert (SomaCache.trusted "cache/a.donor");
  (* A legitimate pair moved to another unit cannot acquire that unit's
     producer descriptor, even when both source files have identical bytes. *)
  write "cache/b.vo" (read "cache/a.vo"); write "cache/b.stamp" (read "cache/a.stamp");
  assert (SomaCache.trusted "cache/b.vo");
  write "cache/b.donor" (read "cache/a.donor");
  SomaModuleStore.record ~root:"root" ~cache:"cache" ~prefix:"" ~source:"root/a.soma"
    ~vo:"cache/b.vo" ~stamp:"cache/b.stamp" ~expected:source;
  SomaModuleStore.publish ~store:"store" ~context ~root:"root" ~cache:"cache";
  mkdir "fresh"; write "fresh/a.soma" (read "root/a.soma"); write "fresh/b.soma" (read "root/b.soma");
  SomaModuleStore.restore ~store:"store" ~context ~root:"fresh" ~cache:"fresh/.soma-cache";
  assert (exists "fresh/.soma-cache/a.vo"); assert (not (exists "fresh/.soma-cache/b.vo"));
  assert (SomaCache.trusted "fresh/.soma-cache/a.vo");
  (* Never overwrite even an already-created empty cache directory. *)
  mkdir "occupied"; write "occupied/a.soma" (read "root/a.soma"); mkdir "occupied/.soma-cache";
  SomaModuleStore.restore ~store:"store" ~context ~root:"occupied" ~cache:"occupied/.soma-cache";
  assert (Array.length (Sys.readdir "occupied/.soma-cache") = 0);
  (* Trusted exact descriptor does not authorize altered object bytes. *)
  let rec corrupt dir = Array.iter (fun n -> let f = Filename.concat dir n in
      if Sys.is_directory f then corrupt f else if n = "object.vo" then write f "altered") (Sys.readdir dir) in
  corrupt "store";
  mkdir "tampered"; write "tampered/a.soma" (read "root/a.soma");
  SomaModuleStore.restore ~store:"store" ~context ~root:"tampered" ~cache:"tampered/.soma-cache";
  assert (not (exists "tampered/.soma-cache"));
  (* Re-labeling the producer descriptor is not certified. *)
  let descriptor = read "cache/a.donor" in
  let rows = String.split_on_char '\n' descriptor |> List.map (fun row ->
      if String.starts_with ~prefix:"unit " row then "unit \"b\"" else row) in
  Sys.remove "cache/a.donor";
  write "cache/b.donor" (String.concat "\n" rows);
  SomaModuleStore.publish ~store:"forged-store" ~context ~root:"root" ~cache:"cache";
  assert (not (exists "forged-store"));
  print_endline "producer path/pair provenance, changed bytes, existing cache and malformed descriptors: passed"
