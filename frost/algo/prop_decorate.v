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
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Plain skeletons as (untagged) unresolved skeletons                    *)
(* ===================================================================== *)

Lemma pskl_to_uskl_open_rec : forall P Q k,
  pskl_to_uskl (open_pskl_wrt_pskl_rec k Q P)
  = open_uskl_wrt_uskl_rec k (pskl_to_uskl Q) (pskl_to_uskl P).
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

Lemma pskl_to_uskl_open_var : forall P X,
  pskl_to_uskl (open_pskl_wrt_pskl P (pskl_var_f X))
  = open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f X).
Proof. intros; apply pskl_to_uskl_open. Qed.

(** Erasure is a retraction of the embedding. *)
Lemma uskl_to_pskl_pskl_to_uskl : forall P,
  uskl_to_pskl (pskl_to_uskl P) = P.
Proof. induction P; simpl; f_equal; auto. Qed.

Lemma pskl_to_uskl_lc : forall P,
  lc_pskl P -> lc_uskl (pskl_to_uskl P).
Proof.
  intros P H; induction H; simpl; auto.
  apply lc_uskl_all_syn; intros X.
  rewrite <- pskl_to_uskl_open_var; auto.
Qed.

Lemma pskl_to_uskl_guarded : forall P,
  guarded_pskl P -> guarded_uskl (pskl_to_uskl P).
Proof.
  intros P H; inversion H; subst; simpl; constructor; auto using pskl_to_uskl_lc.
Qed.

(* ===================================================================== *)
(*  Lemma [Decorating algorithmic consistency]                            *)
(*  If  aconsis[Δ1|Δ2][P0]{Θ0}{P}{Q}{Θ1}                                  *)
(*  then aconsistag[Δ1|Δ2][P0][·]{Θ0}{P}{Q}{Θ1}.                          *)
(* ===================================================================== *)

(* Generalized over the used-name set [F] so the induction's indices stay
   VARIABLES (a bare [induction] on the [F = ∅] instance would capture the
   goal's [Ψ = ∅] literal).  [a_consis]'s own premises all share the root's
   [F], and the decorated rules store the paper-shaped [F = ∅] premises, so
   Leibniz [F = empty] transports through every case. *)
Lemma a_consis_decorate_gen : forall F Δ1 Δ2 Θ0 P0 P Q Θ1,
  Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ≈ Q ⊣ Θ1 ->
  F = empty ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ≈ Q ⊣ Θ1.
Proof.
  intros * Hc; induction Hc; intros HF; subst; simpl.
  - (* Ghost *)
    apply a_consistag__ghost; auto. fsetdec.
  - (* Unit *)
    apply a_consistag__unit. fsetdec.
  - (* Rigid *)
    apply a_consistag__rigid; auto. fsetdec.
  - (* Arrow *)
    eapply a_consistag__arrow; eauto. fsetdec.
  - (* ForallInh (untagged) *)
    eapply a_consistag__forall_inh_untagged with (L := L).
    intros α Hα. rewrite <- pskl_to_uskl_open_var. auto.
  - (* ForallSyn (untagged) *)
    eapply a_consistag__forall_syn_untagged with (L := L).
    intros α Hα. rewrite <- pskl_to_uskl_open_var. auto.
  - (* UnivGhost *)
    apply a_consistag__univ_ghost; auto.
  - (* UnivGhost1 *)
    eapply a_consistag__univ_ghost1 with (L := L).
    intros α Hα. auto.
  - (* UnivGhost2 *)
    apply a_consistag__univ_ghost2; auto.
  - (* Flex *)
    apply a_consistag__flex; auto. fsetdec.
  - (* FlexL *)
    eapply a_consistag__flex_l; eauto. fsetdec.
  - (* FlexR *)
    apply a_consistag__flex_r;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto; try fsetdec.
  - (* GhostR *)
    replace P with (uskl_to_pskl (pskl_to_uskl P)) at 2
      by apply uskl_to_pskl_pskl_to_uskl.
    apply a_consistag__ghost_r;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto; try fsetdec.
  - (* UnivGhostR *)
    apply a_consistag__univ_ghost_r; auto using pskl_to_uskl_guarded;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto.
Qed.

(** The paper-shaped instance (no used names at the root). *)
Lemma a_consis_decorate : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  Θ0 ⊢ₐ[ Δ1 | Δ2 | P0 ] P ≈ Q ⊣ Θ1 ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ≈ Q ⊣ Θ1.
Proof.
  intros * Hc; eapply a_consis_decorate_gen; eauto.
Qed.
