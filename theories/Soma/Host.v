(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The machine's host, [Soma.Host]

    Not part of the prelude: [Require Soma.Host.], then [Host.clock tt].
    What a program built for the machine (an executable, not a Sandbox
    unikernel) asks of the system it runs on: the clock, its arguments
    and output, files, paths, processes and TCP sockets. Soma carries
    each out (toplevel/somaHost.ml, which a build that uses them gets
    as soma_host.ml) and decides nothing: a program decides what to ask
    and what each answer means.

    Each is a primitive that Soma never computes: to the kernel and when
    Soma evaluates a term it is a parameter, so that no proof holds by
    running the machine, and [soma explore] lists the ones a program
    uses. A program whose [main] uses one is built, as one that uses an
    OCaml module is (see [Soma.OCaml]).

    Most answer with an [answer]: whether it was carried out (or the
    boolean it reads), a number, and data, each a string. An effect's is
    [(true, (0, []))]; one that failed and says why is [(false, (0,
    [why]))]. Numbers given as arguments are decimal text (a mode, octal).
    Descriptors (sockets, and the pipes a process writes its output on)
    are known by names the host gives them. *)

From Stdlib Require Import Strings.String Lists.List.
Require Import Soma.OCaml.

(** ** The program's own *)

(** its arguments, without the executable's name *)
Parameter argv : unit -> list string.
(** each string on a line of its own on standard output *)
Parameter print_lines : list string -> unit.
(** [f] applied to the state, again and again: the program runs until
    something ends it (an [exit], a signal) *)
Parameter forever : forall {A : Type}, (A -> A) -> A -> unit.

(** ** The clock, the log and the program's output *)

(** the clock: [(true, (now, []))], seconds since 1970 *)
Parameter clock : unit -> bool * (float * list string).
(** TEXT on standard output, after the time it is, on a line *)
Parameter log : string -> bool * (float * list string).
(** STAMP (seconds since 1970, as text) as the local [HH:MM] *)
Parameter local_time : string -> bool * (float * list string).
(** refusing to go on: "error: MESSAGE" on standard error, and exit 1 *)
Parameter fail : string -> bool * (float * list string).
(** TEXT on standard output, as it is *)
Parameter print : string -> bool * (float * list string).
(** the program ends with the status CODE *)
Parameter exit : string -> bool * (float * list string).
(** the directory it runs in: [[it]] *)
Parameter cwd : unit -> bool * (float * list string).
(** COUNT bytes of the system's randomness: [[them]] *)
Parameter random_bytes : string -> bool * (float * list string).

(** ** Files *)

(** a file read whole: [[its text]], or not found *)
Parameter read_text : string -> bool * (float * list string).
(** whether a path is there *)
Parameter file_exists : string -> bool * (float * list string).
(** a directory's entries (none when it isn't there) *)
Parameter dir_entries : string -> bool * (float * list string).
(** PATH's mode set to MODE (octal): whether it was *)
Parameter chmod : string -> string -> bool * (float * list string).
(** TEXT appended to PATH (created when it isn't there) in one write, and
    then on disk: what was appended survives a crash whole *)
Parameter append_synced : string -> string -> bool * (float * list string).
(** TEXT put in PATH, created or emptied first; SYNC "true": on disk
    before the answer *)
Parameter file_put : string -> string -> string -> bool * (float * list string).
(** TEXT replaces PATH atomically using a fresh exclusive sibling file.
    A final symlink/non-regular destination is refused; existing permissions
    are kept. SYNC "true" syncs contents before rename and parent afterwards. *)
Parameter file_replace : string -> string -> string -> bool * (float * list string).
(** A file relative to a trusted ROOT replaced atomically, making missing
    parents. Relative components cannot be empty, . or .., and no descendant
    symlink is followed, including concurrent replacements. *)
Parameter path_replace : string -> string -> string -> bool * (float * list string).
(** A regular file relative to trusted ROOT unlinked without following
    descendant symlinks; the same relative-component rules apply. *)
Parameter path_remove : string -> string -> bool * (float * list string).
(** a file's mode: [[octal]], found when it's there *)
Parameter file_mode : string -> bool * (float * list string).
(** SRC renamed DST *)
Parameter rename : string -> string -> bool * (float * list string).
(** a directory's entries on disk *)
Parameter sync_dir : string -> bool * (float * list string).
(** one directory made *)
Parameter make_dir : string -> bool * (float * list string).
(** one file removed *)
Parameter remove_file : string -> bool * (float * list string).
(** a new private temporary file, PREFIX SUFFIX: [[its path]] *)
Parameter temp_new : string -> string -> bool * (float * list string).
(** a new temporary directory, PREFIX: [[its path]] *)
Parameter temp_dir : string -> bool * (float * list string).

(** ** Paths and the environment *)

(** a path, its last part not followed: [[kind, exec]], its kind "file",
    "dir", "symlink", "other" or "none", and whether its owner may run it *)
Parameter path_stat : string -> bool * (float * list string).
(** the program's own executable, as an absolute path fixed when it
    started: [[it]] *)
Parameter self_exe : unit -> bool * (float * list string).
(** the environment's entries, NAME=VALUE *)
Parameter env_entries : unit -> bool * (float * list string).

(** ** Processes *)

(** PROG ARGS run from CWD ("" for where the program is) with the
    environment ENV, its standard input the file STDIN ("" for none), its
    output on a pipe named among the descriptors and its errors
    discarded: [[its pid, the pipe's name]], or not found and why *)
Parameter spawn : string -> string -> string -> list string -> list string -> bool * (float * list string).
(** a process's end, waited for: [[how, value]], how "exit", "signal" or
    "stop", and its number *)
Parameter wait_pid : string -> bool * (float * list string).
(** A positive process id sent SIGKILL. An already absent process is
    idempotent success; invalid ids or permission/OS errors return failure.
    The caller must not mark a job stopped after a failed request. *)
Parameter kill_pid : string -> bool * (float * list string).
(** from now on, a broken pipe doesn't end the program *)
Parameter no_sigpipe : unit -> bool * (float * list string).
(** PROG ARGS started on its own and not waited for, its parent the
    system's, its input and output /dev/null *)
Parameter start_detached : string -> list string -> bool * (float * list string).
(** PROG ARGS started with its output and errors appended to LOG, its
    input the program's: [[its pid]] *)
Parameter start_logged : string -> string -> list string -> bool * (float * list string).
(** from now on, an interrupt or a terminate terminates PIDS and ends the
    program with 0 *)
Parameter stop_on_signal : list string -> bool * (float * list string).

(** ** TCP sockets *)

(** a listener on HOST PORT, with BACKLOG: [[its name]], or not found and
    why *)
Parameter sock_listen : string -> string -> string -> bool * (float * list string).
(** a dial that doesn't wait: [[its name, "connected" or "connecting"]] *)
Parameter sock_dial : string -> string -> bool * (float * list string).
(** one wait of MS milliseconds over the descriptors named to read and to
    write: [(true, (those ready to read, those ready to write))], none when
    it was interrupted, or [(false, ([why], []))] *)
Parameter sock_select : string -> list string -> list string -> bool * (list string * list string).
(** a connection a listener has (NONBLOCK "true": it doesn't block):
    [[its name, the peer's address]] *)
Parameter sock_accept : string -> string -> bool * (float * list string).
(** what a descriptor has, 64 KiB at most: [["bytes", DATA]], [["again"]]
    (nothing yet) or [["closed"]] *)
Parameter sock_read : string -> bool * (float * list string).
(** DATA written, as much as fits: [["wrote", COUNT]], [["again"]] or
    [["failed"]] *)
Parameter sock_write : string -> string -> bool * (float * list string).
(** found when a dial failed *)
Parameter sock_error : string -> bool * (float * list string).
(** a descriptor closed, and its name forgotten *)
Parameter sock_close : string -> bool * (float * list string).

(** Soma's host runtime carries them out, with OCaml's unix library,
    which comes with the compiler *)
OCaml Library "unix".
OCaml Bind Module "Soma_host".
