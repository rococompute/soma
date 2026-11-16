(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val magic_number : int32

type 'a segment = private {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
}

type 'a id = private { id : string }
(** Private to ensure the phantom tag is injective *)

type in_handle
type out_handle

val make_id : string -> 'a id

val open_in : file:string -> in_handle
val close_in : in_handle -> unit
val marshal_in_segment : in_handle -> segment:'a id -> 'a * Digest.t
val get_segment : in_handle -> segment:'a id -> 'a segment
val segments : in_handle -> Obj.t segment CString.Map.t

(** Soma: [library_hash ch], the hash of the "library" segment of [ch], if it
    has one: what a library is, without its proofs. *)
val library_hash : in_handle -> Digest.t option

(** Soma: [replaced_segment ~file ~library name] is the position and hash of
    the segment [name] of [file] as it is now, when its "library" segment
    still hashes to [library]. A library whose proofs are checked beside the
    build is loaded first without them, and its file then replaced by the
    same library with them (vernac/somaImport.ml): what was read of it
    lazily (its proofs, its VM code) is read again from the new file. *)
val replaced_segment : file:string -> library:Digest.t -> string -> (int64 * Digest.t) option

val open_out : file:string -> out_handle
val close_out : out_handle -> unit
val marshal_out_segment : out_handle -> segment:'a id -> 'a -> unit
val marshal_out_binary : out_handle -> segment:'a id -> out_channel * (unit -> unit)
(** [marshal_out_binary oh segment] is a low level, stateful, API returning
    [oc, stop]. Once called no other API can be used on the same [oh] and only
    [Stdlib.output_*] APIs should be used on [oc]. [stop ()] must be invoked in
    order to signal that all data was written to [oc] (which should not be used
    afterwards). Only after calling [stop] the other API can be used on [oh]. *)
