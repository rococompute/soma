(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * React components with JSX, [Soma.JSX]

    Not part of the prelude. A program that requires it writes JSX, as in
    ReasonReact, for elements and components:

        Greeting {name : string} := <div className="greeting"> "Hello, " name </div>.
        page := <main> <Greeting name="world" /> <Greeting name="Soma" /> </main>.

    - [<tag attr=value ...> children </tag>] and [<tag ... />], for a tag
      in lowercase, are an HTML element ([node]). Its attributes are
      strings, except [onClick=action] and the other [on...], events, whose
      value is an action of the app.
    - [<Component prop=value ...> children </Component>] and
      [<Component ... />] are [Component (prop := value) ...
      (children := [...])]: a component is a function whose props are
      implicit arguments, [Greeting {name : string} := ...]. A prop
      missing or unknown is an error when the program is checked; a prop
      of type [Any] takes any value, checked when the element is evaluated.
    - [<> children </>] is a fragment.
    - An attribute value or a child is an atom ([name], ["text"], [42],
      [(f x)]) or any term in braces ([{to_string count}]). A string child
      is a text element.

    JSX changes how [<] is read, in this file and the ones that require it:
    [<] directly followed by a letter opens a tag, so a comparison is
    written [x < y] (not [x<y]); [<>] opens a fragment, so "not equal" is
    [!=].

    An app has a state, actions that change it ([update]) and a [view] of
    it, whose events produce actions; [replay] is the state after a
    sequence of actions, what a theorem about the app's behavior is about. *)

From Stdlib Require Strings.String Strings.Ascii Lists.List.
Require Import Soma.Strings Soma.Lists Soma.Show.

(** An attribute of an element whose events produce actions of type [A] *)
Inductive attribute (A : Type) : Type :=
| attr (name value : string)
| on (event : string) (action : A).

(* nested in [list]: no [All] scheme is needed *)
#[warnings="-register-all"]
Inductive element (A : Type) : Type :=
| text (s : string)
| node (tag : string) (attributes : list (attribute A)) (children : list (element A))
| fragment (children : list (element A)).

Arguments attr {A} name value.
Arguments on {A} event action.
Arguments text {A} s.
Arguments node {A} tag attributes children.
Arguments fragment {A} children.

(** a string where an element is expected is a text element *)
(* [A] is the element's, from where it is expected: not uniform *)
#[warnings="-uniform-inheritance"]
Coercion text : string >-> element.

(** The lists of JSX: [jsx_cons] checks each child at type [element A],
    so that a string child becomes a text element *)
Definition jsx_cons {A} (e : element A) (l : list (element A)) : list (element A) := cons e l.
Definition attr_cons {A} (a : attribute A) (l : list (attribute A)) : list (attribute A) := cons a l.

(** * HTML *)

Definition char (n : nat) : string := String.String (Ascii.ascii_of_nat n) String.EmptyString.

(** ampersands, angle brackets and double quotes as HTML entities *)
Fixpoint escape (s : string) : string :=
  match s with
  | String.EmptyString => String.EmptyString
  | String.String c rest =>
    let n := Ascii.nat_of_ascii c in
    (if Nat.eqb n 38 then "&amp;"
     else if Nat.eqb n 60 then "&lt;"
     else if Nat.eqb n 62 then "&gt;"
     else if Nat.eqb n 34 then "&quot;"
     else String.String c String.EmptyString) ++ escape rest
  end.

Definition render_attribute {A} (a : attribute A) : string :=
  match a with
  | attr name value => (" " ++ name ++ "=" ++ char 34 ++ escape value ++ char 34)%str
  | on _ _ => String.EmptyString
  end.

(** an element as HTML; events are left out *)
Fixpoint render {A} (e : element A) : string :=
  match e with
  | text s => escape s
  | node tag attributes children =>
    ("<" ++ tag ++ String.concat "" (List.map render_attribute attributes) ++ ">" ++
     String.concat "" (List.map render children) ++
     "</" ++ tag ++ ">")%str
  | fragment children => String.concat "" (List.map render children)
  end.

(** * Apps: state, actions and a view *)

(** An app whose state has type [S] and whose actions have type [A]: it
    starts at [init], each action changes the state with [update], and
    [view] shows the state, its events producing actions. *)
Record app (S A : Type) : Type := {
  init : S;
  update : A -> S -> S;
  view : S -> element A
}.

Arguments init {S A} a.
Arguments update {S A} a action state.
Arguments view {S A} a state.

(** [make_app init update view]: the app, by position, so that a program
    can name its own functions [update] and [view] *)
Definition make_app {S A} (init : S) (update : A -> S -> S) (view : S -> element A) : app S A :=
  Build_app S A init update view.

(** the state after [actions], in order, starting from [state] *)
Definition replay {S A} (update : A -> S -> S) (state : S) (actions : list A) : S :=
  List.fold_left (fun s action => update action s) actions state.

(** an app's state after [actions], from its initial state *)
Definition state_after {S A} (a : app S A) (actions : list A) : S :=
  replay (update a) (init a) actions.

#[export] Set JSX Syntax.
