(** SHA-256 directory fingerprints. Directory nodes contain sorted names,
    kinds, permissions and child hashes. Every scan enumerates directories and
    stats files; a directory's mtime alone never certifies its descendants.
    Stable file digests can be reused from a private, content-addressed cache.
    Set SOMA_FINGERPRINT_CACHE=0 to read all bytes on every scan. *)
type snapshot = {
  digest : string;
  files : (string * string) list;
  directories : (string * string) list;
  hashed_files : int;
  reused_files : int;
  hashed_bytes : int64;
}

val string : string -> string
val file_hash : string -> string
val valid_hash : string -> bool
val scan : ?cache:string -> ?write:bool -> ?skip:string list -> string -> snapshot
