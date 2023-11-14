(* Generated block-backed named files for Sandbox. The device is dedicated
   to Soma. Two alternating snapshots leave the previous committed bank
   intact until the new payload and its final header have been written. *)
let source = {soma|open Lwt.Infix

module Make (B : Mirage_block.S) = struct
  type t = { disk : B.t; sector : int; bank : int; writable : bool; lock : Lwt_mutex.t;
             mutable generation : int64; mutable active : int;
             mutable files : (string, string) Hashtbl.t }
  let magic = "SOMAKV01"
  let fail msg = failwith ("Sandbox storage: " ^ msg)
  let u32 b off =
    let n = ref 0L in
    for i = 0 to 3 do n := Int64.logor (Int64.shift_left !n 8) (Int64.of_int (Char.code b.[off+i])) done;
    if !n > Int64.of_int max_int then fail "length overflow";
    Int64.to_int !n
  let put32 b off n =
    let n = Int64.of_int n in
    for i = 0 to 3 do Bytes.set b (off+i) (Char.chr (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical n (8*(3-i)))))) done
  let get64 s off =
    let n = ref 0L in
    for i = 0 to 7 do n := Int64.logor (Int64.shift_left !n 8) (Int64.of_int (Char.code s.[off+i])) done; !n
  let put64 b off n =
    for i = 0 to 7 do Bytes.set b (off+i) (Char.chr (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical n (8*(7-i)))))) done
  let read_sector disk sector offset =
    let b = Cstruct.create sector in
    B.read disk (Int64.of_int offset) [b] >|= function
    | Ok () -> Cstruct.to_string b | Error _ -> fail "device read failed"
  let write_sector disk offset bytes =
    B.write disk (Int64.of_int offset) [Cstruct.of_string bytes] >|= function
    | Ok () -> () | Error _ -> fail "device write failed"
  let read_bytes disk sector start len =
    let out = Buffer.create len in
    let rec loop off left =
      if left = 0 then Lwt.return (Buffer.contents out)
      else read_sector disk sector off >>= fun s ->
        let n = min left sector in Buffer.add_substring out s 0 n;
        loop (off+1) (left-n)
    in loop start len
  let decode body =
    let pos = ref 4 and fs = Hashtbl.create 17 in
    let count = u32 body 0 in
    if count > (String.length body - 4) / 8 then fail "bad entry count";
    let take () =
      if !pos > String.length body - 4 then fail "short length";
      let len = u32 body !pos in pos := !pos + 4;
      if len > String.length body - !pos then fail "short value";
      let s = String.sub body !pos len in pos := !pos + len; s in
    for _ = 1 to count do
      let name = take () in let data = take () in
      if Hashtbl.mem fs name then fail "duplicate name";
      Hashtbl.add fs name data
    done;
    if !pos <> String.length body then fail "trailing bytes";
    fs
  (* Torn: an invalid header that is a cut-short first header (generation
     1): nonzero bytes only before its checksum ends, beginning with the
     magic and generation 1 as far as they go. *)
  type bank = Empty | Bad | Torn | Valid of int64 * (string, string) Hashtbl.t
  let torn_first header =
    let k = ref (String.length header) in
    while !k > 0 && header.[!k-1] = '\000' do decr k done;
    let k = !k in
    let ok = ref (k < 56) in
    for i = 0 to min k 8 - 1 do if header.[i] <> magic.[i] then ok := false done;
    for i = 8 to 14 do if header.[i] <> '\000' then ok := false done;
    if Char.code header.[15] > 1 then ok := false;
    !ok
  let load disk sector bank index =
    read_sector disk sector (index*bank) >>= fun header ->
    if header = String.make sector '\000' then Lwt.return Empty
    else if String.sub header 0 8 <> magic || Digest.string (String.sub header 0 40) <> String.sub header 40 16 then
      Lwt.return (if torn_first header then Torn else Bad)
    else
      let generation = get64 header 8 and len64 = get64 header 16 in
      if generation <= 0L || len64 < 4L || len64 > Int64.of_int ((bank-1)*sector)
      then Lwt.return Bad
      else read_bytes disk sector (index*bank+1) (Int64.to_int len64) >|= fun body ->
        if Digest.string body <> String.sub header 24 16 then Bad
        else try Valid (generation, decode body) with Failure _ | Invalid_argument _ -> Bad
  let connect disk =
    B.get_info disk >>= fun info ->
    let sector = info.Mirage_block.sector_size in
    if sector < 64 || sector > 65536 then fail "unsupported sector size";
    let banks = Int64.min (Int64.div info.Mirage_block.size_sectors 2L)
        (Int64.of_int (16*1024*1024/sector)) in
    if banks < 2L then fail "disk needs at least four sectors";
    let bank = Int64.to_int banks in
    load disk sector bank 0 >>= fun first ->
    load disk sector bank 1 >|= fun second ->
    let generation, active, files = match first, second with
      | Empty, Empty -> 0L, 1, Hashtbl.create 17
      (* the first commit goes to bank 0; cut short in its header, nothing
         was ever committed, and the next commit rewrites bank 0 *)
      | Torn, Empty -> 0L, 1, Hashtbl.create 17
      | Valid (a, fs), Valid (b, gs) -> if a >= b then a, 0, fs else b, 1, gs
      | Valid (a, fs), _ -> a, 0, fs
      | _, Valid (b, fs) -> b, 1, fs
      | _ -> fail "no valid snapshot; refusing to overwrite disk"
    in {disk; sector; bank; writable=info.Mirage_block.read_write;
        lock=Lwt_mutex.create (); generation; active; files}
  let encode fs capacity =
    let entries = List.sort compare (Hashtbl.fold (fun k v xs -> (k,v)::xs) fs []) in
    let size = List.fold_left (fun n (k,v) ->
        if String.length k > capacity-n-8 || String.length v > capacity-n-8-String.length k
        then fail "disk full";
        n+8+String.length k+String.length v) 4 entries in
    let out = Bytes.create size in put32 out 0 (List.length entries);
    let pos = ref 4 in
    let put s = put32 out !pos (String.length s); pos := !pos+4;
      Bytes.blit_string s 0 out !pos (String.length s); pos := !pos+String.length s in
    List.iter (fun (k,v) -> put k; put v) entries;
    Bytes.to_string out
  let commit t fs =
    if not t.writable then fail "device is read-only";
    if t.generation = Int64.max_int then fail "generation exhausted";
    let payload = encode fs ((t.bank-1)*t.sector) in
    let index = 1-t.active and generation = Int64.succ t.generation in
    let rec payload_sectors pos offset =
      if pos = String.length payload then Lwt.return_unit
      else let n = min t.sector (String.length payload-pos) in
        let bytes = Bytes.make t.sector '\000' in
        Bytes.blit_string payload pos bytes 0 n;
        write_sector t.disk offset (Bytes.to_string bytes) >>= fun () ->
        payload_sectors (pos+n) (offset+1)
    in
    payload_sectors 0 (index*t.bank+1) >>= fun () ->
    let header = Bytes.make t.sector '\000' in
    Bytes.blit_string magic 0 header 0 8;
    put64 header 8 generation; put64 header 16 (Int64.of_int (String.length payload));
    Bytes.blit_string (Digest.string payload) 0 header 24 16;
    Bytes.blit_string (Digest.string (Bytes.sub_string header 0 40)) 0 header 40 16;
    write_sector t.disk (index*t.bank) (Bytes.to_string header) >>= fun () ->
    (* A first-header prefix can be recovered as an uncommitted empty store.
       Acknowledge generation 1 only after recording a byte beyond that
       prefix. A torn receipt rewrite still leaves a complete valid header. *)
    (if generation = 1L then begin
       Bytes.set header 56 '\001';
       write_sector t.disk (index*t.bank) (Bytes.to_string header)
     end else Lwt.return_unit) >|= fun () ->
    t.files <- fs; t.active <- index; t.generation <- generation
  let read t name = Lwt_mutex.with_lock t.lock (fun () -> Lwt.return (Hashtbl.find_opt t.files name))
  let update t name data append = Lwt_mutex.with_lock t.lock (fun () ->
      let fs = Hashtbl.copy t.files in
      let old = if append then match Hashtbl.find_opt fs name with Some s -> s | None -> "" else "" in
      if String.length data > (t.bank-1)*t.sector-String.length old then fail "disk full";
      Hashtbl.replace fs name (old ^ data); commit t fs)
  let write t name data = update t name data false
  let append t name data = update t name data true
end
|soma}
