(** Frost — Ltac utilities. *)

Require Import Coq.Program.Equality.
Require Export Metalib.Metatheory.

Require Import src.frost.notations.

(* Specialise a cofinite-quantified hypothesis to a fresh atom x. *)
Ltac inst_cofinite_impl H x :=
  match type of H with
  | forall x0, x0 `notin` ?L -> _ =>
      let Fr := fresh "Fr" in
      assert (x `notin` L) as Fr by auto;
      specialize (H x Fr); clear Fr
  end.

Ltac inst_cofinites_with x :=
  repeat
    match goal with
    | H : forall x0, x0 `notin` ?L -> _ |- _ =>
        inst_cofinite_impl H x
    end.

Tactic Notation "inst_cofinites_with" ident(x) :=
  inst_cofinites_with x.

(** Override Metalib's [gather_atoms] to include every atom-bearing
    source in our context: name-sets [atoms], single atoms, term
    contexts ([list (atom * dbind)]), tag / Ψ-scope contexts
    ([list atom]), and free-variable functions on all current type
    categories / [exp].

    Pairs with [pick fresh] (already metalib) and with
    [inst_cofinites_for], defined below, which applies a cofinite
    rule [R] using all gathered atoms as [L].

    Conventions follow the public reference at
      jiangsy/proof_worklist_remechnization/systemdk/ltac_utils.v.
*)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * dbind) => dom x) in
  let D := gather_atoms_with (fun x : list atom => List.fold_right add empty x) in
  let E := gather_atoms_with (fun x : exp => fvar_in_exp x) in
  let F := gather_atoms_with (fun x : exp => ftvar_in_exp x) in
  let G := gather_atoms_with (fun x : ptyp => ftvar_in_ptyp x) in
  let H := gather_atoms_with (fun x : btyp => ftvar_in_btyp x) in
  let I := gather_atoms_with (fun x : utyp => ftvar_in_utyp x) in
  let J := gather_atoms_with (fun x : pskl => ftvar_in_pskl x) in
  let K := gather_atoms_with (fun x : bskl => ftvar_in_bskl x) in
  let L := gather_atoms_with (fun x : uskl => ftvar_in_uskl x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union`
          G `union` H `union` I `union` J `union` K `union` L).

(** Apply a cofinite-quantified rule [R] using [gather_atoms] as the
    freshness set. Replaces [apply R with (L := L `union` ... `union` dom Γ)]. *)
Tactic Notation "inst_cofinites_for" constr(R) :=
  let _L := gather_atoms in
  apply R with (L := _L).

Tactic Notation "inst_cofinites_for" constr(R) ident(name) ":=" constr(val) :=
  let _L := gather_atoms in
  apply R with (L := _L) (name := val).

(* Destruct the (boolean / decidable-equality) condition of an
   [if _ then _ else _] appearing in the goal.  Replaces the ubiquitous
     [match goal with |- context [ if ?e then _ else _ ] => destruct e end]
   idiom, optionally taking an intro pattern for the two branches. *)
Tactic Notation "destruct_if" :=
  match goal with |- context [ if ?e then _ else _ ] => destruct e end.
Tactic Notation "destruct_if" "as" simple_intropattern(pat) :=
  match goal with |- context [ if ?e then _ else _ ] => destruct e as pat end.

(* Close a set goal from a single [_ [=] empty] hypothesis, scoping fsetdec to
   just that hypothesis (per the `clear -` discipline).  Backtracks over the
   candidate hypotheses. *)
Ltac fsetdec_empty :=
  match goal with H : _ [=] empty |- _ => clear - H; fsetdec end.

(* Discharge an absurd [guarded_pskl pskl_hole] hypothesis. *)
Ltac inv_guarded_hole :=
  match goal with H : guarded_pskl pskl_hole |- _ => inversion H end.

(* ===================================================================== *)
(*  ⭐ THE [∉] KIT — use these instead of a bare or `clear -`-scoped       *)
(*  [fsetdec] on a [x ∉ S] goal.  Measured 2026-08-09; between them they  *)
(*  took the tree's two worst proofs from 426 s and 248 s to 0.09 s and   *)
(*  0.9 s.                                                               *)
(*                                                                       *)
(*  WHY [fsetdec] IS THE WRONG DEFAULT HERE.  It calls [tauto], which is  *)
(*  exponential in the propositional structure it can see — and a set     *)
(*  hypothesis contributes one leaf per atom.  Past roughly a DOZEN       *)
(*  leaves it falls off a cliff (the 2026-08-06 pass recorded the same    *)
(*  threshold).  There are two independent ways to get there, and they    *)
(*  need different fixes:                                                *)
(*                                                                       *)
(*    (a) MANY hypotheses, each small — e.g. four [atom_fresh] results    *)
(*        in scope at a nested binder.  Fix: [keep_only_subject], which   *)
(*        keeps only the one about the goal's own subject.  ⚠️ A generic   *)
(*        `clear` of non-set hypotheses does NOT help, and neither does   *)
(*        `clear - H1 H2 H3 H4` naming the relevant ones: those keep      *)
(*        every leaf.  The scoping has to be BY SUBJECT.                  *)
(*                                                                       *)
(*    (b) ONE hypothesis that is itself huge — typically a rule's [L]     *)
(*        avoid-set, a union of a dozen [dom]/[ftvar_in_aenv] terms.      *)
(*        [clear -] cannot help; the hypothesis IS the problem.  Fix:     *)
(*        split it into atomic facts FIRST ([destruct_notin]) so [tauto]  *)
(*        sees a flat context, or avoid [tauto] altogether                *)
(*        ([solve_notin]).                                               *)
(*                                                                       *)
(*  ⭐ USE [solve_notin_auto] (bottom of this section).  It DISPATCHES on  *)
(*  the shape and then applies the matching order — the two cannot be     *)
(*  merged into one cascade, see the ⚠️ note there.  [solve_notin_fast]    *)
(*  (a) and [solve_notin_flat] (b) are the explicit single-shape entry    *)
(*  points, for a site whose shape you have measured.                     *)
(* ===================================================================== *)

(** Keep only the freshness hypothesis about THIS goal's subject — case (a). *)
Ltac keep_only_subject :=
  match goal with
  | |- ?v `notin` _ =>
      repeat match goal with
             | H : ?w `notin` _ |- _ =>
                 tryif constr_eq w v then fail else clear H
             end
  end.

(** ⭐ Case (a) — MANY hypotheses.  The default for a [x ∉ S] goal proved in
    an ambient context (typical inside a proof body).  [test_examples.v]:
    467 s -> 23.8 s. *)
Ltac solve_notin_fast :=
  first [ assumption
        | solve [ keep_only_subject; fsetdec ]
        | solve [ destruct_notin; fsetdec ]
        | solve [ solve_notin ]
        | fsetdec ].

(** ⭐ Case (b) — ONE huge hypothesis.  The default for the [ltac:(…)] side
    conditions of the swap / rename kit, which are already [clear -]-scoped to
    a single hypothesis that is a rule's [L] avoid-set.
    [a_pat_complete_abs_anno]: 248 s -> 0.9 s. *)
Ltac solve_notin_flat :=
  first [ assumption
        | solve [ destruct_notin; fsetdec ]
        | solve [ solve_notin ]
        | fsetdec ].

(** ⚠️ WHY THE ORDER CANNOT SIMPLY BE MERGED — measured, twice, the hard way.
    Cases (a) and (b) want OPPOSITE first stages, and a plain [first] cascade
    does not work, because in each case the WRONG stage still SUCCEEDS — just
    slowly — so [first] commits to it and never reaches the right one:

      · [keep_only_subject; fsetdec] first  → (a) 23.8 s, but (b) stays 248 s
        (the single big hypothesis survives the scoping, so this IS the
        original slow [fsetdec]);
      · [destruct_notin; fsetdec] first     → (b) 0.9 s, but (a) becomes 142 s
        ([destruct_notin] duplicates hypotheses per union node);
      · both combined                        → (a) 130 s.

    Hence [solve_notin_auto] below, which DISPATCHES on the shape instead of
    guessing an order. *)

(** Is this shape (a)?  I.e. does the context hold TWO freshness hypotheses
    about atoms OTHER than the goal's subject?  That is exactly the condition
    under which [keep_only_subject] has something to remove — one foreign
    hypothesis is shape (b), where the cost is the hypothesis itself. *)
Ltac two_foreign_notin :=
  match goal with
  | |- ?v `notin` _ =>
      match goal with
      | H1 : ?w1 `notin` _, H2 : ?w2 `notin` _ |- _ =>
          tryif constr_eq H1 H2 then fail else
          tryif constr_eq w1 v  then fail else
          tryif constr_eq w2 v  then fail else idtac
      end
  end.

(** ⭐⭐ THE ONE TO USE — prefer this to [fsetdec] on any [x ∉ S] goal.
    Picks the order by shape, then falls back.  Measured: it matches
    hand-picking the right tactic at every site (full build 9:44 either way,
    vs 13:04 before the sweep and ~20.5 min before the kit), and it keeps
    [test_examples.v] on the fast branch (30.8 s, vs 130-142 s when the order
    is wrong).  [solve_notin_fast] / [solve_notin_flat] are kept below as the
    explicit single-shape entry points, for a site you have measured. *)
Ltac solve_notin_auto :=
  first [ assumption
        | tryif two_foreign_notin
          then first [ solve [ keep_only_subject; fsetdec ]
                     | solve [ destruct_notin; fsetdec ] ]
          else first [ solve [ destruct_notin; fsetdec ]
                     | solve [ keep_only_subject; fsetdec ] ]
        | solve [ solve_notin ]
        | fsetdec ].
