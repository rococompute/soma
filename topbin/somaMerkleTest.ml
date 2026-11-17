let require b message = if not b then failwith message
let write p s = Out_channel.with_open_bin p (fun oc -> output_string oc s)
let rec remove p =
  match (Unix.lstat p).Unix.st_kind with
  | Unix.S_DIR -> Array.iter (fun n -> remove (Filename.concat p n)) (Sys.readdir p); Unix.rmdir p
  | _ -> Sys.remove p

let () =
  let dir = Filename.temp_file "soma-merkle-test-" "" in
  Sys.remove dir; Unix.mkdir dir 0o700;
  Fun.protect ~finally:(fun () -> remove dir) (fun () ->
      let root = Filename.concat dir "source" and cache = Filename.concat dir "cache" in
      Unix.mkdir root 0o700;
      let path p = Filename.concat root p in
      Unix.mkdir (path "a") 0o700; Unix.mkdir (path "b") 0o700;
      write (path "a/one") "abc"; write (path "b/two") "other";
      Unix.sleepf 2.1;
      let scan () = SomaMerkle.scan ~cache root in
      let first = scan () in
      require (List.assoc "a/one" first.files =
          "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") "SHA-256 known vector";
      require (first.hashed_files = 2) "cold scan reads both files";
      let warm = scan () in
      require (warm.digest = first.digest && warm.hashed_files = 0 && warm.reused_files = 2)
        "warm scan reuses bytes from the persistent cache";
      (* A separate process reads exactly the same cache, without process-local memoization. *)
      let pid = Unix.fork () in
      if pid = 0 then begin
        let again = scan () in
        exit (if again.digest = first.digest && again.hashed_files = 0 then 0 else 1)
      end;
      require (snd (Unix.waitpid [] pid) = Unix.WEXITED 0) "cache survives process boundaries";
      let old = Unix.stat (path "a/one") in
      write (path "a/one") "xyz";
      Unix.utimes (path "a/one") old.st_atime old.st_mtime;
      let edited = scan () in
      require (edited.digest <> first.digest) "same-size edit with restored mtime changes root";
      require (List.assoc "b" edited.directories = List.assoc "b" first.directories)
        "unaffected sibling keeps its Merkle address";
      require (List.assoc "a" edited.directories <> List.assoc "a" first.directories)
        "changed leaf changes ancestor address";
      Unix.rename (path "b/two") (path "b/renamed");
      let renamed = scan () in
      require (renamed.digest <> edited.digest) "rename changes directory hash";
      Sys.remove (path "b/renamed");
      require ((scan ()).digest <> renamed.digest) "deletion changes directory hash";
      write (path "new") "added";
      let added = scan () in
      Unix.chmod (path "new") 0o700;
      require ((scan ()).digest <> added.digest) "permission change changes fingerprint";
      Unix.symlink "a/one" (path "link");
      require (List.mem_assoc "link" (scan ()).files) "follow installation symlinks";
      Unix.symlink "." (path "cycle");
      require (try ignore (scan ()); false with Failure _ -> true) "reject directory cycles";
      Sys.remove (path "cycle");
      let indices = Filename.concat cache "indices" in
      Array.iter (fun n -> write (Filename.concat indices n) "corrupt\n") (Sys.readdir indices);
      require ((scan ()).hashed_files = 3) "corrupt cache falls back to hashing";
      let no_write = Filename.concat dir "not-created" in
      ignore (SomaMerkle.scan ~cache:no_write ~write:false root);
      require (not (Sys.file_exists no_write)) "read-only scan writes nothing";
      Unix.putenv "SOMA_FINGERPRINT_CACHE" "0";
      require ((scan ()).hashed_files = 3) "strict mode re-reads all content";
      Unix.putenv "SOMA_FINGERPRINT_CACHE" "";
      print_endline "Merkle fingerprints: passed")
