(* Soma's JSX library: JSX under [Set JSX Syntax] *)

(* Without JSX, [<] directly followed by a letter is a comparison *)
Check (fun x y : nat => x<y).

(* as in a Soma program: the prelude, then JSX *)
From Soma Require Import Soma JSX.

(* With JSX: a comparison needs a space, or a non-letter, after [<] *)
Check (fun x y : nat => x < y).
Check (fun x : nat => x<10).
Check (fun x y : nat => x <= y <-> y >= x).

Definition hello : element unit := <div className="greeting"> "Hello" </div>.
Example hello_html : render hello = "<div className=""greeting"">Hello</div>" := eq_refl.

(* a component's props are named implicit arguments *)
Definition Greeting {A} {name : string} : element A := <p> "Hello, " name "!" </p>.
Definition page : element unit := <main> <Greeting name="world" /> <Greeting name="you" /> </main>.
Example page_html :
  render page = "<main><p>Hello, world!</p><p>Hello, you!</p></main>" := eq_refl.

(* a missing or mistyped prop is an error *)
Fail Definition missing : element unit := <Greeting />.
Fail Definition mistyped : element unit := <Greeting name=42 />.

(* children, braces, fragments *)
Definition Box {A} {children : list (element A)} : element A := node "section" [] children.
Definition boxed : element unit := <Box> <p> "a" </p> {text "b"} </Box>.
Example boxed_html : render boxed = "<section><p>a</p>b</section>" := eq_refl.
Definition both : element unit := <> <i> "x" </i> <b> "y" </b> </>.
Example both_html : render both = "<i>x</i><b>y</b>" := eq_refl.

(* the tags must match: <p> ... </div> is a parse error, which Fail cannot
   catch *)

(* events are actions, which type the element *)
Inductive action := Go.
Definition button := <button onClick=Go> "go" </button>.
Check button : element action.

(* escaping *)
Example escaped : render (text (A := unit) "a<b&c") = "a&lt;b&amp;c" := eq_refl.

(* a prop of type Any takes any value, checked when evaluated *)
Definition Loose {A} {n : Any} : element A := <span> (n : string) </span>.
Example loose_ok : render (A := unit) (<Loose n="x" />) = "<span>x</span>" := eq_refl.

(* An implicit argument that is not a type is not made [?] by GCIC: a
   prop left out above, and Program's proofs *)
Require Import Stdlib.Program.Wf Stdlib.micromega.Lia.
Program Fixpoint countdown (n : nat) {measure n} : nat :=
  match n with 0 => 0 | _ => countdown (n - 1) end.
Next Obligation. lia. Qed.

(* the app model *)
Definition step (a : action) (n : nat) := S n.
Definition app1 := make_app 0 step (fun n => <p> "x" </p>).
Example after_two : state_after app1 [Go, Go] = 2 := eq_refl.
