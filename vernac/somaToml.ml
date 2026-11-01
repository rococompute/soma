(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: TOML 1.0 (https://toml.io/en/v1.0.0), which soma.toml is written
   in: comments, tables ([a.b]) and arrays of tables ([[a]]), bare,
   quoted and dotted keys, strings of the four kinds, integers (decimal,
   0x, 0o, 0b), floats, booleans, arrays and inline tables. Dates and times
   are refused, as soma.toml has none. A key is defined once, and a table
   once: inline tables and arrays are closed. *)

type value =
  | String of string
  | Int of int
  | Float of float
  | Bool of bool
  | Array of value list
  | Table of table

and table = (string * entry) list

and entry = { line : int; value : value }

exception Error of int * string

let describe = function
  | String _ -> "a string"
  | Int _ -> "an integer"
  | Float _ -> "a float"
  | Bool _ -> "a boolean"
  | Array _ -> "an array"
  | Table _ -> "a table"

(* * The tables being read *)

(* A table made by a header ([a]), or on the way to one ([a] of [a.b]),
   or by dotted keys (a.b = 1) *)
type how = Header | Implicit | Dotted

type node =
  | Leaf of value               (* closed: a value, an inline table, an array *)
  | Node of tbl
  | Tables of tbl list ref      (* [[a]], the last first *)

and tbl = { mutable keys : (string * (int * node)) list; (* the last first *)
            mutable how : how }

let new_tbl how = { keys = []; how }

let find t k = List.assoc_opt k t.keys

let add t k line n = t.keys <- (k, (line, n)) :: t.keys

let rec freeze t =
  List.rev_map (fun (k, (line, n)) ->
      k, { line; value = match n with
          | Leaf v -> v
          | Node t -> Table (freeze t)
          | Tables l -> Array (List.rev_map (fun t -> Table (freeze t)) !l) }) t.keys

(* * Reading *)

type st = { s : string; mutable i : int; mutable line : int }

let fail_at line fmt = Printf.ksprintf (fun m -> raise (Error (line, m))) fmt
let fail st fmt = fail_at st.line fmt

let peek st = if st.i < String.length st.s then Some st.s.[st.i] else None
let peek_at st k = if st.i + k < String.length st.s then Some st.s.[st.i + k] else None

let advance st =
  if st.s.[st.i] = '\n' then st.line <- st.line + 1;
  st.i <- st.i + 1

let skip st n = for _ = 1 to n do advance st done

let looking_at st p =
  let n = String.length p in
  st.i + n <= String.length st.s && String.sub st.s st.i n = p

let expect st p what =
  if looking_at st p then skip st (String.length p) else fail st "expected %s" what

let shown = function
  | None -> "the end of the file"
  | Some '\n' | Some '\r' -> "the end of the line"
  | Some c -> Printf.sprintf "%C" c

(* control characters other than tab are not allowed in comments and strings *)
let control c = (c < ' ' && c <> '\t') || c = '\127'

let skip_ws st = while (match peek st with Some (' ' | '\t') -> true | _ -> false) do advance st done

let skip_comment st =
  if peek st = Some '#' then
    let rec go () = match peek st with
      | None | Some '\n' -> ()
      | Some '\r' when peek_at st 1 = Some '\n' -> ()
      | Some c when control c -> fail st "a comment has the control character %C" c
      | Some _ -> advance st; go () in
    go ()

let newline st = match peek st with
  | Some '\n' -> advance st; true
  | Some '\r' when peek_at st 1 = Some '\n' -> skip st 2; true
  | _ -> false

(* the rest of a line: whitespace and a comment *)
let end_line st =
  skip_ws st;
  skip_comment st;
  if peek st <> None && not (newline st) then
    fail st "expected the end of the line, found %s" (shown (peek st))

(* whitespace, comments and newlines, as between an array's values *)
let rec skip_blank st =
  skip_ws st;
  skip_comment st;
  if newline st then skip_blank st

(* ** Strings *)

let is_hex = function '0'..'9' | 'a'..'f' | 'A'..'F' -> true | _ -> false

(* after a backslash *)
let escape st buf =
  let c = match peek st with Some c -> c | None -> fail st "unterminated string" in
  advance st;
  match c with
  | 'b' -> Buffer.add_char buf '\b'
  | 't' -> Buffer.add_char buf '\t'
  | 'n' -> Buffer.add_char buf '\n'
  | 'f' -> Buffer.add_char buf '\012'
  | 'r' -> Buffer.add_char buf '\r'
  | '"' -> Buffer.add_char buf '"'
  | '\\' -> Buffer.add_char buf '\\'
  | 'u' | 'U' ->
    let n = if c = 'u' then 4 else 8 in
    if st.i + n > String.length st.s || not (String.for_all is_hex (String.sub st.s st.i n)) then
      fail st "\\%c is followed by %d hexadecimal digits" c n;
    let code = int_of_string ("0x" ^ String.sub st.s st.i n) in
    skip st n;
    if code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF) then
      fail st "\\%c%0*X is no Unicode scalar value" c n code;
    Buffer.add_utf_8_uchar buf (Uchar.of_int code)
  | c -> fail st "\\%c is no escape sequence: \\b \\t \\n \\f \\r \\\" \\\\ \\uXXXX \\UXXXXXXXX are" c

let string_char st buf c =
  if control c then fail st "a string has the control character %C: write it escaped" c;
  Buffer.add_char buf c;
  advance st

(* "...", at its opening quote *)
let basic_string st =
  advance st;
  let buf = Buffer.create 16 in
  let rec go () = match peek st with
    | None | Some '\n' | Some '\r' -> fail st "unterminated string: a string in \"...\" is on one line (\"\"\"...\"\"\" spans lines)"
    | Some '"' -> advance st
    | Some '\\' -> advance st; escape st buf; go ()
    | Some c -> string_char st buf c; go () in
  go ();
  Buffer.contents buf

(* '...', at its opening quote *)
let literal_string st =
  advance st;
  let buf = Buffer.create 16 in
  let rec go () = match peek st with
    | None | Some '\n' | Some '\r' -> fail st "unterminated string: a string in '...' is on one line ('''...''' spans lines)"
    | Some '\'' -> advance st
    | Some c -> string_char st buf c; go () in
  go ();
  Buffer.contents buf

(* """...""" or '''...''', at its opening delimiter: a newline right after
   it is not part of the string, nor one or two quotes right before its
   closing one *)
let multiline_string st ~quote =
  let delim = String.make 3 quote in
  let line = st.line in
  skip st 3;
  ignore (newline st);
  let buf = Buffer.create 64 in
  let rec go () =
    if looking_at st delim then begin
      skip st 3;
      for _ = 1 to 2 do if peek st = Some quote then (Buffer.add_char buf quote; advance st) done
    end else match peek st with
      | None -> fail_at line "unterminated string: %s is not closed" delim
      | Some '\\' when quote = '"' ->
        advance st;
        (* a backslash at the end of a line: the whitespace and newlines that
           follow are not part of the string *)
        let i = st.i in
        skip_ws st;
        if newline st then begin
          let rec blank () = skip_ws st; if newline st then blank () in
          blank ()
        end else begin
          st.i <- i;
          escape st buf
        end;
        go ()
      | Some '\n' -> Buffer.add_char buf '\n'; advance st; go ()
      | Some '\r' when peek_at st 1 = Some '\n' -> Buffer.add_string buf "\r\n"; skip st 2; go ()
      | Some c -> string_char st buf c; go () in
  go ();
  Buffer.contents buf

(* ** Keys *)

let is_bare = function 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '-' -> true | _ -> false

let simple_key st = match peek st with
  | Some '"' when looking_at st "\"\"\"" -> fail st "a key cannot be a multi-line string"
  | Some '\'' when looking_at st "'''" -> fail st "a key cannot be a multi-line string"
  | Some '"' -> basic_string st
  | Some '\'' -> literal_string st
  | Some c when is_bare c ->
    let start = st.i in
    while (match peek st with Some c -> is_bare c | None -> false) do advance st done;
    String.sub st.s start (st.i - start)
  | c -> fail st "expected a key (letters, digits, _ and -, or a string in quotes), found %s" (shown c)

(* a.b."c d" *)
let key st =
  let rec go acc =
    skip_ws st;
    let k = simple_key st in
    skip_ws st;
    if peek st = Some '.' then (advance st; go (k :: acc)) else List.rev (k :: acc) in
  go []

let dotted keys =
  String.concat "." (List.map (fun k ->
      if k <> "" && String.for_all is_bare k then k else Printf.sprintf "%S" k) keys)

(* ** Numbers *)

(* [s] is [ok] characters, with each _ between two of them *)
let well_formed ok s =
  let n = String.length s in
  n > 0 &&
  (let rec go i = i >= n ||
                  (if s.[i] = '_' then i > 0 && i < n - 1 && ok s.[i - 1] && ok s.[i + 1]
                   else ok s.[i]) && go (i + 1) in
   go 0)

let is_digit = function '0'..'9' -> true | _ -> false

let without_underscores s = String.concat "" (String.split_on_char '_' s)

let number st =
  let line = st.line in
  let start = st.i in
  while (match peek st with
      | Some ('0'..'9' | 'a'..'z' | 'A'..'Z' | '_' | '+' | '-' | '.' | ':') -> true
      | _ -> false) do advance st done;
  let t = String.sub st.s start (st.i - start) in
  let bad () =
    fail_at line "%s is no value: a value is a number, a string in quotes, true or false, \
                  an array [...] or an inline table {...}" t in
  let n = String.length t in
  if String.contains t ':' ||
     (n >= 10 && t.[4] = '-' && t.[7] = '-' && is_digit t.[0] && is_digit t.[5] && is_digit t.[8]) then
    fail_at line "%s: dates and times are not supported in soma.toml; write it as a string in quotes" t;
  let sign, body = match t.[0] with
    | '+' | '-' -> String.make 1 t.[0], String.sub t 1 (n - 1)
    | _ -> "", t in
  match body with
  | "inf" -> Float (if sign = "-" then Float.neg_infinity else Float.infinity)
  | "nan" -> Float Float.nan
  | _ ->
    let m = String.length body in
    if m > 2 && body.[0] = '0' && (body.[1] = 'x' || body.[1] = 'o' || body.[1] = 'b') then begin
      let ok = match body.[1] with
        | 'x' -> is_hex
        | 'o' -> (function '0'..'7' -> true | _ -> false)
        | _ -> (function '0' | '1' -> true | _ -> false) in
      let digits = String.sub body 2 (m - 2) in
      if sign <> "" || not (well_formed ok digits) then bad ();
      match int_of_string_opt ("0" ^ String.make 1 body.[1] ^ without_underscores digits) with
      | Some i -> Int i
      | None -> fail_at line "%s is too large an integer" t
    end else begin
      (* digits, then .digits, then e[+-]digits *)
      let upto stop i = let rec go j = if j < m && not (stop body.[j]) then go (j + 1) else j in go i in
      let int_end = upto (fun c -> c = '.' || c = 'e' || c = 'E') 0 in
      let int_part = String.sub body 0 int_end in
      if not (well_formed is_digit int_part) then bad ();
      if String.length (without_underscores int_part) > 1 && int_part.[0] = '0' then
        fail_at line "%s: an integer does not begin with 0" t;
      if int_end = m then
        match int_of_string_opt (sign ^ without_underscores int_part) with
        | Some i -> Int i
        | None -> fail_at line "%s is too large an integer" t
      else begin
        let frac_end =
          if body.[int_end] = '.' then begin
            let e = upto (fun c -> c = 'e' || c = 'E') (int_end + 1) in
            if not (well_formed is_digit (String.sub body (int_end + 1) (e - int_end - 1))) then bad ();
            e
          end else int_end in
        if frac_end < m then begin
          let e = frac_end + 1 in
          let e = if e < m && (body.[e] = '+' || body.[e] = '-') then e + 1 else e in
          if not (well_formed is_digit (String.sub body e (m - e))) then bad ()
        end;
        Float (float_of_string (sign ^ without_underscores body))
      end
    end

(* ** Values *)

(* the tables of a dotted key's prefix, from [t], made when missing *)
let rec descend st line t seen = function
  | [] -> t
  | k :: rest ->
    let seen = seen @ [k] in
    let t' = match find t k with
      | None -> let t' = new_tbl Dotted in add t k line (Node t'); t'
      | Some (_, Node ({ how = Dotted; _ } as t')) -> t'
      | Some (l, Node _) ->
        fail_at line "%s is a table defined on line %d, by a header: its keys go under it" (dotted seen) l
      | Some (l, _) -> fail_at line "%s is already defined, on line %d, as no table" (dotted seen) l in
    descend st line t' seen rest

let rec value st = match peek st with
  | Some '"' when looking_at st "\"\"\"" -> String (multiline_string st ~quote:'"')
  | Some '\'' when looking_at st "'''" -> String (multiline_string st ~quote:'\'')
  | Some '"' -> String (basic_string st)
  | Some '\'' -> String (literal_string st)
  | Some '[' -> advance st; array st
  | Some '{' -> advance st; inline_table st
  | Some 't' when looking_at st "true" -> skip st 4; Bool true
  | Some 'f' when looking_at st "false" -> skip st 5; Bool false
  | Some ('+' | '-' | '0'..'9' | 'i' | 'n') -> number st
  | c -> fail st "expected a value, found %s" (shown c)

and array st =
  let rec go acc =
    skip_blank st;
    if peek st = Some ']' then (advance st; List.rev acc)
    else begin
      let v = value st in
      skip_blank st;
      match peek st with
      | Some ',' -> advance st; go (v :: acc)
      | Some ']' -> advance st; List.rev (v :: acc)
      | c -> fail st "expected , or ] in an array, found %s" (shown c)
    end in
  Array (go [])

and inline_table st =
  let t = new_tbl Header in
  skip_ws st;
  if peek st = Some '}' then advance st
  else begin
    let rec go () =
      keyval st t;
      skip_ws st;
      match peek st with
      | Some ',' -> advance st; go ()
      | Some '}' -> advance st
      | c -> fail st "expected , or } in an inline table, which is on one line, found %s" (shown c) in
    go ()
  end;
  Table (freeze t)

(* key = value, into [t] *)
and keyval st t =
  let line = st.line in
  let keys = key st in
  if peek st <> Some '=' then fail st "expected = after the key %s, found %s" (dotted keys) (shown (peek st));
  advance st;
  skip_ws st;
  let v = value st in
  let rec split = function [k] -> [], k | k :: r -> let p, l = split r in k :: p, l | [] -> assert false in
  let prefix, last = split keys in
  let t = descend st line t [] prefix in
  match find t last with
  | Some (l, _) -> fail_at line "%s is already defined, on line %d" (dotted keys) l
  | None -> add t last line (Leaf v)

(* [a.b.c] and [[a.b.c]]: the table they begin *)
let header st root keys ~array =
  let line = st.line in
  let rec go t seen = function
    | [] -> assert false
    | [k] ->
      let seen = seen @ [k] in
      if array then match find t k with
        | None -> let n = new_tbl Header in add t k line (Tables (ref [n])); n
        | Some (_, Tables l) -> let n = new_tbl Header in l := n :: !l; n
        | Some (l, _) -> fail_at line "%s is already defined, on line %d, as no array of tables" (dotted seen) l
      else begin match find t k with
        | None -> let n = new_tbl Header in add t k line (Node n); n
        | Some (_, Node ({ how = Implicit; _ } as n)) -> n.how <- Header; n
        | Some (l, _) -> fail_at line "[%s] is already defined, on line %d" (dotted seen) l
      end
    | k :: rest ->
      let seen = seen @ [k] in
      let n = match find t k with
        | None -> let n = new_tbl Implicit in add t k line (Node n); n
        | Some (_, Node n) -> n
        | Some (_, Tables l) -> List.hd !l
        | Some (l, Leaf _) -> fail_at line "%s is already defined, on line %d, as no table" (dotted seen) l in
      go n seen rest in
  go root [] keys

let parse s =
  let st = { s; i = 0; line = 1 } in
  if looking_at st "\xEF\xBB\xBF" then st.i <- 3;
  let root = new_tbl Header in
  let rec go cur =
    skip_ws st;
    match peek st with
    | None -> ()
    | Some ('\n' | '\r' | '#') -> end_line st; go cur
    | Some '[' ->
      let array = looking_at st "[[" in
      skip st (if array then 2 else 1);
      let keys = key st in
      if array then expect st "]]" "]] to close [[" else expect st "]" "] to close [";
      let cur = header st root keys ~array in
      end_line st;
      go cur
    | Some _ -> keyval st cur; end_line st; go cur in
  go root;
  freeze root
