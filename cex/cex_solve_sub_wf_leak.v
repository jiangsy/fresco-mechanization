(** ⚠️ SUB-SOLVING DOES NOT PRESERVE WELL-FORMEDNESS once SS-ForallR is
    faithful — so the paper's [Θ_0 ⊢ P_a] cannot be recovered from the solve
    alone, and must be a CONCLUSION of P6-Sv, which is where the paper puts
    it (subtyping-proofs.tex:1737).

    prop_look_complete_sub_cstr.v used to carry a lemma [a_solve_sub_wf]
    claiming the opposite (modulo a rigid prefix Ξ the proof itself grew for
    SolS-ForallR):

      Θ ⊢ₛ P ≼[M] P0 ⤳ P'  ->  all_tvar Ξ ->
      (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P -> (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P0 ->
      Δ ∩ ftv P0 [=] ∅ ->
      (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P'

    Under the COFINITE encoding of SS-ForallR that was true: the rule's
    single output P' had to serve every fresh binder, hence was binder-free,
    and [a_wf_pskl_strip_tvar] could remove the binder the proof had put into
    the context.  The freshness campaign (DESIGN.md §4.3) made the rule
    faithful to the paper and to the reference implementation
    (type.ml:517-520 opens the RHS and DISCARDS the binder name), so the
    binder now LEGITIMATELY ESCAPES into the result — and an escaped binder
    is exactly a free variable the conclusion's context does not bind.

    THE WITNESS is as small as it gets — no flexibles, no ghosts beyond the
    ◇ the rule needs, and an EMPTY Δ:

        ◇  ≼[TC]  ∀a. a   ⤳   ∀◇ b

    SolS-ForallR opens the target at a fresh rigid [b] and recurses on
    [◇ ≼[TC] b]; SolS-GhostL — the rule for a ◇ subject against a GUARDED
    target — closes that with [∀◇ b], COPYING the target into the output,
    [b] and all.  Both inputs are well-formed at [Θ ⨟ ∅] (a ◇ is wf
    anywhere; [∀a. a] is wf because its body is checked at [add a ∅]), and
    [∅ ∩ ftv (∀a. a) = ∅].  But [∀◇ b] is NOT wf at [Θ ⨟ ∅]: it needs
    [b ∈ ∅] or [b] bound in Θ, and [b] is fresh for both.

    WHAT THIS DOES *NOT* SAY.  Neither the paper nor the rule is wrong.
    DESIGN §4.3 already records that ill-scoped solve outputs are filtered
    DOWNSTREAM by the wf side conditions that consume them
    ([a_sub__forall_l]'s [(Ξ ++ Θ0) ⨟ ∅ ⊢ₚₛᵃ P1]); what is refuted is the
    idea that the filter can be DERIVED from the solve.  The paper never
    tries: its P6-Sv states [Θ_0 ⊢ P_a] among its own conclusions and proves
    it inside the induction, carrying it as [Θ_0,β ⊢ P_a] through the
    SolS-ForallR row and discharging β there from [β ∉ ftv ψ_a] and the
    PRECISION conclusion (:1897-1900).  [a_solve_sub_complete_var] now does
    exactly that, and [a_solve_sub_wf] is gone (RESTART NOTE at
    prop_look_complete_sub_cstr.v:323). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

Set Implicit Arguments.

(** The claim's rigid prefix predicate, copied from
    prop_look_complete_sub_cstr.v (which this file must not depend on — it
    is the file whose lemma is being refuted). *)
Fixpoint all_tvar (Ξ : aenv) : Prop :=
  match Ξ with
  | nil => True
  | (_, b) :: Ξ' => b = abind_tvar /\ all_tvar Ξ'
  end.

(* ===================================================================== *)
(*  The run:  ◇ ≼[TC] ∀a. a  ⤳  ∀◇ b                                     *)
(* ===================================================================== *)

(* ⚙️ [ftvar_in_aenv], not [dom] (2026-08-04): the solve's five binder rows
   were strengthened to the avoid-set [a_guess_mono] and the look rules
   already use, since SE-FlexR now calls [guess^TY].  The refutation is
   untouched — it only has to CHOOSE its escaping binder, and a fresher
   choice is still a choice. *)
Lemma cex_leak_run : forall Θ b,
  b `notin` ftvar_in_aenv Θ ->
  Θ ⊢ₛ pskl_hole ≼[ mode_tc ] (pskl_all_syn (pskl_var_b 0))
     ⤳ nil ⨾ (pskl_tophole (pskl_var_f b)).
Proof.
  intros Θ b Hb.
  apply a_solve_sub__forall_r with (β := b);
    [ exact I | cbn; clear - Hb; fsetdec | ].
  (* [open (var_b 0) (var_f b) = var_f b] *)
  unfold open_pskl_wrt_pskl; cbn.
  apply a_solve_sub__ghost_l; [ exact I | apply guarded_pskl__var ].
Qed.

(* ===================================================================== *)
(*  Both inputs are well-formed at the EMPTY Δ, and the Δ-side condition   *)
(*  holds vacuously.                                                      *)
(* ===================================================================== *)

Lemma cex_wf_subject : forall Θ, Θ ⨟ empty ⊢ₚₛᵃ pskl_hole.
Proof. intros Θ. apply a_wf_pskl__hole. Qed.

Lemma cex_wf_target : forall Θ,
  Θ ⨟ empty ⊢ₚₛᵃ (pskl_all_syn (pskl_var_b 0)).
Proof.
  intros Θ. apply a_wf_pskl__all with (L := empty). intros α Hα.
  unfold open_pskl_wrt_pskl; cbn.
  apply a_wf_pskl__var. left. clear; fsetdec.
Qed.

(* ===================================================================== *)
(*  … but the output is NOT well-formed there.                            *)
(* ===================================================================== *)

Lemma cex_output_not_wf : forall Θ b,
  b `notin` dom Θ ->
  ~ (Θ ⨟ empty ⊢ₚₛᵃ (pskl_tophole (pskl_var_f b))).
Proof.
  intros Θ b Hb Hwf.
  inversion Hwf as [ | | | | | ? ? ? Hg Hbody ]; subst.
  inversion Hbody as [ | ? ? ? Hin | | | | ]; subst.
  destruct Hin as [Habs | Hbt].
  - clear - Habs; fsetdec.
  - destruct Hbt as [Hbd | [Hbd | [τ Hbd]]];
      apply binds_In in Hbd; contradiction.
Qed.

(** THE REFUTATION.  Instantiated at [Ξ := nil] and [Δ := ∅] — the very
    configuration the (former) single call site used
    (prop_look_complete_sub_cstr.v's α-stack row). *)
Theorem solve_sub_preserves_wf_is_false :
  ~ (forall Θ M P P0 Ξ0 P',
       Θ ⊢ₛ P ≼[ M ] P0 ⤳ Ξ0 ⨾ P' ->
       forall Ξ Δ, all_tvar Ξ ->
       (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P ->
       (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P0 ->
       Δ ∩ ftvar_in_pskl P0 [=] empty ->
       (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P').
Proof.
  intros Hclaim.
  (* one rigid entry in Θ, and a DIFFERENT atom for the escaping binder *)
  destruct (atom_fresh empty) as [α Hα].
  destruct (atom_fresh (singleton α)) as [b Hb].
  pose (Θ := (α ~ abind_tvar)).
  assert (HbΘ : b `notin` ftvar_in_aenv Θ)
    by (subst Θ; cbn; clear - Hb; fsetdec).
  assert (HbΘd : b `notin` dom Θ) by (subst Θ; cbn; clear - Hb; fsetdec).
  apply (@cex_output_not_wf Θ b HbΘd).
  change Θ with (nil ++ Θ) at 1.
  apply (Hclaim Θ mode_tc pskl_hole (pskl_all_syn (pskl_var_b 0)) nil
                (pskl_tophole (pskl_var_f b))
                (@cex_leak_run Θ b HbΘ) nil empty I);
    [ apply cex_wf_subject | apply cex_wf_target | clear; fsetdec ].
Qed.

