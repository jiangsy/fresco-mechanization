(** Appendix B (consistency-proofs.tex), "Lemmas for Subtyping" — decoration
    of the ordinary algorithmic judgments.

    First target: Lemma [Decorating algorithmic consistency]
    (lemma:decorating-algorithmic-consistency): an ordinary algorithmic
    consistency run is a decorated run with the empty tag context, reading
    the plain skeleton [P] as an (untagged) unresolved skeleton. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Plain skeletons as (untagged) unresolved skeletons                    *)
(* ===================================================================== *)

Lemma pskl_to_uskl_open_rec : forall P P' k,
  pskl_to_uskl (open_pskl_wrt_pskl_rec k P' P)
  = open_uskl_wrt_uskl_rec k (pskl_to_uskl P') (pskl_to_uskl P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma pskl_to_uskl_open : forall P Q,
  pskl_to_uskl (open_pskl_wrt_pskl P Q)
  = open_uskl_wrt_uskl (pskl_to_uskl P) (pskl_to_uskl Q).
Proof.
  intros; unfold open_pskl_wrt_pskl, open_uskl_wrt_uskl;
    apply pskl_to_uskl_open_rec.
Qed.

Lemma pskl_to_uskl_open_var : forall P α,
  pskl_to_uskl (open_pskl_wrt_pskl P (pskl_var_f α))
  = open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α).
Proof. intros; apply pskl_to_uskl_open. Qed.

(** Erasure is a retraction of the embedding. *)
Lemma uskl_to_pskl_pskl_to_uskl : forall P,
  uskl_to_pskl (pskl_to_uskl P) = P.
Proof. induction P; simpl; f_equal; auto. Qed.

Lemma pskl_to_uskl_lc : forall P,
  lc_pskl P -> lc_uskl (pskl_to_uskl P).
Proof.
  intros P H; induction H; simpl; auto.
  apply lc_uskl_all_syn; intros α.
  rewrite <- pskl_to_uskl_open_var; auto.
Qed.

Lemma pskl_to_uskl_guarded : forall P,
  guarded_pskl P -> guarded_uskl (pskl_to_uskl P).
Proof.
  intros P H; inversion H; subst; simpl; constructor; auto using pskl_to_uskl_lc.
Qed.

(* ===================================================================== *)

(* [a_consis_decorate_gen] / [a_consis_decorate] (Lemma [Decorating
   algorithmic consistency], consistency-proofs.tex) live in
   prop_consis_rename.v §10, not here.

   Why: cluster 4 made [a_consis]'s three ∀ rows EXISTS-FRESH, while the
   decorated [a_consistag] rows are (rightly) still cofinite — so a ∀ row of
   this lemma must now rebuild a whole FAMILY from the algorithmic run's ONE
   binder.  That means MOVING the binder with
   [a_assign_unify_consis_rename_tvar], and the moved premise is no
   sub-derivation, so the proof became a SIZE induction on
   [size_pskl P + size_pskl P0] (cluster 3's shape (1); the worked precedent
   is [a_consistag_decoration_size], prop_decorate_sub.v §7).  The rename
   lemma lives downstream of this file — prop_flex.v imports this one — so
   the lemma had to move rather than the asset.

   Consumer-visible: the lemma gained a [uniq Θ0] premise (the rename needs
   it), and consumers must now [Require] prop_consis_rename. *)
