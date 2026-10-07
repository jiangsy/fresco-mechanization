(** ext_algo — the runner for [guess^N], the SORT WRAPPER.

    Two rows, and both are decided by the mode, so this needs no domain
    predicate of its own: [guess^SK] is the identity and [guess^TY] is M1.7's
    runner read back into [pskl].  It is here because [a_extract]'s third
    stage is a [guess^N], so this is the piece that makes the pipeline's LAST
    stage runnable rather than merely specified.

    ⚙ A SECOND RESULT RECORD rather than a reuse of [guess_result]: the
    wrapper returns a SKELETON where [e_guess_mono] returns a TYPE, and the
    tree's rule is that a record's fields say what sort they carry.  Both
    extract to a plain OCaml triple. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_guess_impl.

(* ⚠️ NO [Set Implicit Arguments] in an implementation file — see
   def_guess_impl.v's header. *)

Record guess_sk_result : Type := mk_guess_sk_result {
  gs_supply : supply;      (* the supply the run leaves behind *)
  gs_block  : aenv;        (* Ξ' — the invented flexibles *)
  gs_skel   : pskl         (* Q' — the guessed skeleton *)
}.

(** ⭐ THE RUNNER.  [lc_pskl Q] is the same honest precondition M1.7's runner
    carries: it says the caller handed us a skeleton and not a dangling
    index.  It is NOT a termination certificate — the recursion is entirely
    inside [e_guess_mono_run]. *)
Definition e_guess_run (S0 : supply) (NM : a_sub_mode) (Q : pskl)
    (H : lc_pskl Q) : guess_sk_result :=
  match NM with
  | a_sub_mode_sk => mk_guess_sk_result S0 nil Q
  | a_sub_mode_ty =>
      let r := e_guess_mono_run S0 Q H in
      mk_guess_sk_result (gr_supply r) (gr_block r) (ptyp_to_pskl (gr_type r))
  end.

(** Runner soundness: what it returns is a real [guess^N] run.  Composed with
    [e_guess_sound] (prop_guess.v) this reaches [a_guess], i.e. the encoding
    the four flagship theorems are stated over. *)
Lemma e_guess_run_sound : forall S0 NM Q (H : lc_pskl Q),
  e_guess S0 NM Q
    (gs_supply (e_guess_run S0 NM Q H))
    (gs_block  (e_guess_run S0 NM Q H))
    (gs_skel   (e_guess_run S0 NM Q H)).
Proof.
  intros S0 NM Q H; destruct NM; simpl.
  - apply e_guess__ty. apply e_guess_mono_run_sound.
  - apply e_guess__sk.
Qed.
