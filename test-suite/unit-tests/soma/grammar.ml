(* Soma's changes to the grammar: definitions without [Definition],
   bare terms, and the tokens of JSX *)

open Utest
open Vernacexpr

let log_out_ch = open_log_out_ch __FILE__

(* The commands of [text], as the main entry parses them *)
let parse text =
  let pa = Procq.Parsable.make (Gramlib.Stream.of_string text) in
  let rec loop acc =
    match Procq.Entry.parse Pvernac.Vernac_.main_entry pa with
    | None -> List.rev acc
    | Some { CAst.v = { expr; _ }; _ } -> loop (expr :: acc)
  in
  loop []

let kind = function
  | VernacSynPure (VernacDefinition ((_, Decls.Definition), ({ CAst.v = Names.Name id; _ }, _), _)) ->
    "definition " ^ Names.Id.to_string id
  | VernacSynPure (VernacCheckMayEval (Some _, None, _)) -> "evaluation"
  | VernacSynPure (VernacCheckMayEval (None, None, _)) -> "check"
  | _ -> "other"

(* the unit tests load no library, hence no notation: the terms are
   applications *)
let kinds text =
  try List.map kind (parse text)
  with Gramlib.Grammar.ParseError msg -> ["parse error: " ^ msg]

let implicit_definition = mk_eq_test "soma-implicit-definition"
    "[f x := t.] is a Definition"
    ["definition f"] (kinds "f x := x.")

let typed_implicit_definition = mk_eq_test "soma-typed-implicit-definition"
    "[f (x : nat) : nat := t.] is a Definition"
    ["definition f"] (kinds "f (x : nat) : nat := x.")

let explicit_definition = mk_eq_test "soma-explicit-definition"
    "[Definition f := t.] is still a Definition"
    ["definition f"] (kinds "Definition f := 1.")

let bare_term = mk_eq_test "soma-bare-term"
    "a bare term is evaluated"
    ["evaluation"; "evaluation"] (kinds "f 1. g x y.")

let check_stays = mk_eq_test "soma-check"
    "Check is not an evaluation"
    ["check"] (kinds "Check f.")

let program = mk_eq_test "soma-program"
    "a program mixes definitions and bare terms"
    ["definition double"; "evaluation"; "definition answer"; "evaluation"]
    (kinds "double n := add n n.\ndouble 21.\nanswer := double 21.\nanswer.")

(* The tokens of [text] *)
let tokens text =
  let kw = Procq.get_keyword_state () in
  let s = CLexer.Lexer.tok_func (Gramlib.Stream.of_string text) in
  let rec loop acc =
    match Gramlib.LStream.peek kw s with
    | None | Some Tok.EOI -> List.rev acc
    | Some t -> Gramlib.LStream.junk kw s; loop (Tok.extract_string false t :: acc)
  in
  loop []

(* Setting an option adds an object to the current library *)
let () =
  Lib.init ();
  let dp = Names.DirPath.make [Names.Id.of_string "SomaGrammar"] in
  Lib.start_compilation dp (Names.ModPath.MPfile dp)

let with_jsx b f =
  Goptions.set_bool_option_value ["JSX"; "Syntax"] b;
  Fun.protect f ~finally:(fun () -> Goptions.set_bool_option_value ["JSX"; "Syntax"] false)

let less_than = mk_eq_test "soma-jsx-off"
    "without JSX, [x<y] is a comparison"
    ["x"; "<"; "y"] (tokens "x<y")

let tag = mk_eq_test "soma-jsx-tag"
    "with JSX, [<] followed by a letter opens a tag"
    [CLexer.jsx_tag_open; "p"; ">"; CLexer.jsx_tag_close; "p"; ">"]
    (with_jsx true (fun () -> tokens "<p></p>"))

let fragment = mk_eq_test "soma-jsx-fragment"
    "with JSX, [<>] and [</>] are a fragment"
    [CLexer.jsx_fragment_open; CLexer.jsx_fragment_close]
    (with_jsx true (fun () -> tokens "<></>"))

let spaced_less_than = mk_eq_test "soma-jsx-comparison"
    "with JSX, [x < y] is still a comparison"
    ["x"; "<"; "y"] (with_jsx true (fun () -> tokens "x < y"))

let tests = [ implicit_definition; typed_implicit_definition; explicit_definition;
              bare_term; check_stays; program;
              less_than; tag; fragment; spaced_less_than ]

let _ = run_tests __FILE__ log_out_ch tests
