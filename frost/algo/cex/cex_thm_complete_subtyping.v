(** ⚠️⚠️⚠️ THEOREM 4.6 (`thm:complete-subtyping`, "Completeness and optimality
    of subtyping", algorithmic.tex:1447) IS FALSE — machine-checked, one
    self-contained instance, Qed + axiom-free.

    Also refuted, one lemma lower and by the same instance: LEMMA E.17
    (`lemma:complete-look`, "Look completeness", subtyping-proofs.tex:2730) —
    see [p6l_look_completeness_fails] in probe_double_occ_run.v.

    ⭐ WHY THIS FILE EXISTS SEPARATELY.  probe_double_occ_run.v refutes the
    MECH's motive ([main_forall]), whose subject [R] carries the derivation's
    ε-TAGS; the paper's Definition of a solution writes the subject as
    [syn{θ₁P}], the plain painting of the ALGORITHM's input.  So the tagged
    witness does not literally instantiate Theorem 4.6.  It does not need to:
    the same configuration works with the UNTAGGED ForallL row, and the
    statement here is the paper's Definition verbatim.  ⭐ It quotes the
    PAPER's declarative subtyping [Ψ ⨟ Θ ⊢ₛᵃ[N|M] R ⩽ Q] ([ad_pat_sub],
    fig:decl-subtyping-all) — NOT the mech-invented hygienic mirror
    [ad_pat_sub_gv], which is used only as a construction device and
    immediately projected ([ad_pat_sub_gv_forget] then [ad_pat_sub_g_of]).
    No source program, no typing, no prose declarative claim — the
    declarative solution is a Coq term.

    THE INSTANCE.  Θ0 holds ONE undefined flexible:

        Θ0 = f̂            N = TY            M = FN(TC)
        P0 = (∀γ.γ→γ) → f̂                   P  = ∀β.β→β

      · [(Θ0;N;M;P0;P)] IS a subtyping problem: Θ0 well-formed, P0 and P
        well-formed in Θ0, and skmod[TY]{P0}{FN(TC)} — the payload's spine
        ends in the TYPE f̂, which is what skmod[TY] asks for at TC.
      · It HAS a solution [(κ : Θ0 ⊑ Θ0 ; Q)] with

            κ = f̂ ↦ 1→1        Q = inh(∀β.β→β) → (1→1)

        The declarative derivation ([solution_d]) is ForallL — untagged
        subject, instantiation ψa = ∀^ε β.β→β — then Sub-Arrow splitting the
        tag index as {ε} ∪ ·:
          – DOMAIN, at index {ε}: consistency [ψa ∼ inh(∀β.β→β)] by
            ForallInh-TAGGED, which is where the guess's tag ε is PAID (the
            counterpart is an INHERITED ∀ — the "never guess polymorphism out
            of thin air" obligation, discharged, not assumed);
          – CODOMAIN, at index · and mode TC: [ψa ⩽ 1→1] by ForallL with the
            MONOTYPE instantiation 1, so no tag is owed, then Check.
        The fill [Θ0 ⊢ inh{κP0} ⊳ Q] is [fill_d].
      · YET NO ALGORITHMIC RUN EXISTS ([probe_no_run]).

    WHY THE ALGORITHM FAILS — the marker occurs TWICE.  Algorithmic ForallL
    opens the subject's binder with a fresh MARKER α and hands [α→α] to the
    extract, which is indexed by α and collects one constraint per occurrence
    of it.  Walking [α→α] against [(∀γ.γ→γ) → f̂] in lockstep:

        the DOMAIN occurrence faces (∀γ.γ→γ) — an arrow-LEFT, a CONSISTENCY
          position — so LE-Var emits   eq(∀γ.γ→γ)
        the CODOMAIN occurrence faces f̂ — a SUBTYPING position — so LS-Var
          emits                        sub_tc(f̂)

    ([probe_look_det]: that list, deterministically).  One marker, two
    constraints, so the solve must COMBINE them — and that is where the
    information is destroyed: [a_solve_cstr__eq] threads the eq's yield
    ∀γ.γ→γ into the sub-constraint, SS-ForallL opens β, SS-Check hands
    [β→β ∼ f̂] to SE-FlexR, whose output IS the flexible, and the close then
    re-binds a VACUOUS binder ∀_.f̂ ([probe_solve_det]).  With a single
    occurrence there would be one constraint and nothing to lose.

    ⭐ AND THE LOSS IS THE WHOLE DEFECT: cex/probe_solve_flexr.v shows that
    handing ForallL the RIGHT instantiation ∀β.β→β makes the run exist.
    docs/PAPER-GAPS.md; DESIGN §14.10a. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_sub_complete.   (* ad_pat_sub_g_of *)
Require Import src.frost.algo.cex.cex_p7_shield_double_occ.
Require Import src.frost.algo.cex.probe_double_occ_run.

Set Implicit Arguments.

(** The algorithm's input skeleton [P = ∀β.β→β] — [Pd] with the tag erased,
    and [pskl_to_tskl] paints it back to the UNTAGGED [syn{P}]. *)
Definition Pcex : pskl :=
  pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).

(** The declarative solution, at the UNTAGGED ForallL row — the only change
    from [join_d], and it drops that lemma's [e <> t] hypothesis with it
    (an untagged subject carries no tag for the guess's ε to clash with).

    ⚙ Built in [ad_pat_sub_gv] only because that is the shape the cex file's
    leaf lemmas already have; [solution_d] immediately projects it to the
    PAPER's judgment [Ψ ⨟ Θ ⊢ₛᵃ[N|M] R ⩽ Q] ([ad_pat_sub],
    fig:decl-subtyping-all), and the refutation below quotes only that.  The
    projection is the right way round: [_gv] carries EXTRA side conditions
    (tag hygiene, fuel), so a [_gv] derivation is a plain one, never the
    reverse. *)
Lemma join_untagged_gv : forall f,
  ad_pat_sub_gv 3 a_sub_mode_ty (mode_fn mode_tc) empty (Θ0d f)
    (pskl_to_tskl (msubst_pskl (κd f) Pcex)) Qd.
Proof.
  intros f. destruct (atom_fresh empty) as [e _].
  unfold Pcex, κd; simpl. unfold Qd.
  apply ad_pat_sub_gv__forall_l_untagged
    with (Ψ' := singleton e) (ψ := ψd e).
  - discriminate.
  - clear; fsetdec.
  - simpl; clear; fsetdec.
  - apply ψd_tags.
  - apply ψd_erase_wf.
  - unfold open_uskl_wrt_uskl; simpl.
    apply ad_pat_sub_gv__arrow with (Ψ1 := singleton e) (Ψ2 := empty).
    + apply consis_d.       (* the guess's tag ε is PAID here *)
    + apply refine_dom_d.
    + apply join_cod_d.     (* mode TC; instantiation 1, so no tag owed *)
    + clear; fsetdec.
Qed.

(** …and the same derivation in the PAPER's judgment. *)
Lemma solution_d : forall f,
  empty ⨟ (Θ0d f) ⊢ₛᵃ[ a_sub_mode_ty | (mode_fn mode_tc) ]
    (pskl_to_tskl (msubst_pskl (κd f) Pcex)) ⩽ Qd.
Proof.
  intros f. eapply ad_pat_sub_g_of. apply ad_pat_sub_gv_forget.
  apply join_untagged_gv.
Qed.

(** The premise LEMMA E.17 needs, likewise in the paper's judgment: the
    declarative subtyping of the subject with the guess substituted, at the
    ambient tag index [Ψ, Ψa] = [·, {ε}]. *)
Lemma look_premise_d : forall f e,
  (empty `union` singleton e) ⨟ (Θ0d f) ⊢ₛᵃ[ a_sub_mode_ty | (mode_fn mode_tc) ]
    (open_uskl_wrt_uskl Rjd (ψd e)) ⩽ Qd.
Proof.
  intros f e. eapply ad_pat_sub_g_of. apply ad_pat_sub_gv_forget.
  apply join_premise_d.
Qed.

(** ⚠️⚠️⚠️ Theorem 4.6, refuted.  The three blocks are exactly the paper's
    Definition (Problems and solutions of subtyping, algorithmic.tex:1423)
    and the theorem's conclusion. *)
Theorem thm_complete_subtyping_false : forall f,
  (* (1) [(Θ0; TY; FN TC; P0; P)] IS a subtyping problem *)
  a_wf_aenv (Θ0d f)
  /\ (Θ0d f) ⨟ empty ⊢ₚₛᵃ (P0d f)
  /\ (Θ0d f) ⨟ empty ⊢ₚₛᵃ Pcex
  /\ a_ty_mode_compat (mode_fn mode_tc) (P0d f)
  (* (2) it HAS a solution [(κ : Θ0 ⊑ Θ0 ; Q)] *)
  /\ (κd f) ∷ (Θ0d f) ⊑ (Θ0d f)
  /\ empty ⨟ (Θ0d f) ⊢ₛᵃ[ a_sub_mode_ty | (mode_fn mode_tc) ]
       (pskl_to_tskl (msubst_pskl (κd f) Pcex)) ⩽ Qd
  /\ prop_consis_sound.ad_refine_syn_f empty (Θ0d f) empty
       (pskl_to_bskl_inh (msubst_pskl (κd f) (P0d f))) Qd
  (* (3) yet the ALGORITHM has NO run — a fortiori no optimal solution *)
  /\ (forall P1 Θ1,
        ~ a_sub a_sub_mode_ty (mode_fn mode_tc) (P0d f) (Θ0d f) Pcex P1 Θ1).
Proof.
  intros f.
  destruct (atom_fresh empty) as [t _].
  repeat split.
  - apply Θ0d_wf.
  - apply P0d_wf.
  - exact (Pd_wf f t).       (* [Pd t] IS [Pcex] — the tag erases away *)
  - apply P0d_mode.
  - apply inc_d.
  - apply solution_d.
  - apply fill_d.
  - intros P1 Θ1. apply probe_no_run.
Qed.

Print Assumptions thm_complete_subtyping_false.
Print Assumptions look_premise_d.
