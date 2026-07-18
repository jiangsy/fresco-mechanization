(** DECORATION OF ALGORITHMIC SUBTYPING (lemma:decorating-algorithmic-
    subtyping, subtyping-proofs.tex:32-58) — the R-B enabler of
    thm:sound-subtyping (docs/DESIGN-subtyping.md §2.2, phase P4).

    An algorithmic subtyping run [Θ0 ⊢ₐ[N|M|P0] P ⊑ Q ⊣ Θ1] can be
    replayed as a DECORATED run [Θ0 ⊢ᵗ[N|M|P0|∅] ⌊P⌋ᵘ ⊑ Q ⊣ Θ1] whose
    ForallL instantiations use decorated skeletons whose tags the run
    solves.  This file builds the auxiliary lemmas bottom-up. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_pat_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Erasure commutes with close                                       *)
(* ===================================================================== *)

Lemma uskl_to_pskl_close_rec : forall ψ X k,
  uskl_to_pskl (close_uskl_wrt_uskl_rec k X ψ)
  = close_pskl_wrt_pskl_rec k X (uskl_to_pskl ψ).
Proof.
  induction ψ; intros X k; simpl; try (f_equal; auto; fail).
  - destruct (lt_ge_dec n k); reflexivity.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      reflexivity.
Qed.

Lemma uskl_to_pskl_close : forall ψ X,
  ⌊ close_uskl_wrt_uskl X ψ ⌋ˢ = close_pskl_wrt_pskl X ⌊ ψ ⌋ˢ.
Proof.
  intros. unfold close_uskl_wrt_uskl, close_pskl_wrt_pskl.
  apply uskl_to_pskl_close_rec.
Qed.

(* ===================================================================== *)
(*  §2  Look decoration (lemma:look-decoration)                           *)
(*                                                                        *)
(*  Every locally-closed skeleton [Q] admits a decoration [ψ]: a fresh    *)
(*  tag on every quantifier, ghosts turned dotted.  Stated with an        *)
(*  avoid-set [L] so sibling subtrees get disjoint tags (the arrow rule   *)
(*  of [d_tags_skl] needs [Ψ1 ∩ Ψ2 = ∅]).                                 *)
(* ===================================================================== *)

Lemma pskl_decorate_exists : forall Q,
  lc_pskl Q ->
  forall L, exists Ψ ψ,
    AtomSetImpl.inter Ψ L [=] empty /\
    is_tskl ψ /\
    d_tags_skl Ψ ψ /\
    ⌊ ψ ⌋ˢ = Q /\
    (pskl_ghost_free Q -> uskl_ghost_free ψ).
Proof.
  intros Q Hlc; induction Hlc; intros L.
  - (* unit *)
    exists empty, uskl_unit. repeat apply conj;
      [ fsetdec | apply is_tskl__unit | apply d_tags_skl__unit; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__unit ].
  - (* var *)
    exists empty, (uskl_var_f Xps). repeat apply conj;
      [ fsetdec | apply is_tskl__var | apply d_tags_skl__var; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__var ].
  - (* arrow *)
    destruct (IHHlc1 L) as [Ψ1 [ψ1 [Hd1 [Ht1 [Hg1 [He1 Hgf1]]]]]].
    destruct (IHHlc2 (L `union` Ψ1))
      as [Ψ2 [ψ2 [Hd2 [Ht2 [Hg2 [He2 Hgf2]]]]]].
    exists (Ψ1 `union` Ψ2), (uskl_arrow ψ1 ψ2). repeat apply conj.
    + clear - Hd1 Hd2. fsetdec.
    + apply is_tskl__arrow; assumption.
    + apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
        [ assumption | assumption | clear - Hd2; fsetdec | fsetdec ].
    + simpl. rewrite He1, He2. reflexivity.
    + intros Hg. simpl in Hg. destruct Hg as [Hga Hgb].
      apply uskl_ghost_free__arrow; [ apply Hgf1; auto | apply Hgf2; auto ].
  - (* all_syn → all_etag ε *)
    destruct (atom_fresh (L `union` ftvar_in_pskl P1)) as [X0 FrX].
    destruct (H0 X0 (L `union` singleton X0))
      as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    destruct (atom_fresh (L `union` Ψ0)) as [ε Frε].
    exists (add ε Ψ0), (uskl_all_etag ε (close_uskl_wrt_uskl X0 ψ0)).
    repeat apply conj.
    + clear - Hd0 Frε. fsetdec.
    + apply is_tskl__all_etag with (L := singleton X0).
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply is_tskl_subst_mono; [ exact Ht0 | apply mono_ptyp__var ].
    + apply d_tags_skl__all_etag with (L := singleton X0) (Ψ0 := Ψ0);
        [ | clear - Frε; fsetdec | fsetdec ].
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply d_tags_skl_subst_mono; [ exact Hg0 | apply mono_ptyp__var ].
    + simpl. rewrite uskl_to_pskl_close. rewrite He0.
      rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        [ reflexivity | clear - FrX; fsetdec ].
    + intros Hg. simpl in Hg.
      apply uskl_ghost_free__all_etag with (L := singleton X0).
      intros Y HY.
      rewrite <- subst_bskl_in_uskl_spec.
      change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply uskl_ghost_free_subst_mono; [ | apply mono_ptyp__var ].
      apply Hgf0. unfold open_pskl_wrt_pskl. apply pskl_ghost_free_open_rec.
      exact Hg.
  - (* hole → holeg *)
    exists empty, uskl_holeg. repeat apply conj;
      [ fsetdec | apply is_tskl__holeg | apply d_tags_skl__holeg; fsetdec
      | reflexivity | intros Hg; simpl in Hg; contradiction ].
  - (* tophole → topholeg *)
    destruct (IHHlc L) as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    exists Ψ0, (uskl_topholeg ψ0). repeat apply conj.
    + exact Hd0.
    + apply is_tskl__topholeg; assumption.
    + apply d_tags_skl__topholeg; assumption.
    + simpl. rewrite He0. reflexivity.
    + intros Hg. simpl in Hg. contradiction.
Qed.
