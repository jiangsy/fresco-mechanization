(** DECORATION OF ALGORITHMIC SUBTYPING (lemma:decorating-algorithmic-
    subtyping, subtyping-proofs.tex:32-58) — the R-B enabler of
    thm:sound-subtyping (docs/DESIGN-subtyping.md §2.2, phase P4).

    An algorithmic subtyping run [Θ0 ⊢ₐ[N|M|P0] P ⩽ Q ⊣ Θ1] can be
    replayed as a DECORATED run [Θ0 ⊢ᵗ[N|M|P0|∅] ⌊P⌋ᵘ ⩽˙ Q ⊣ Θ1] whose
    ForallL instantiations use decorated skeletons whose tags the run
    solves.  This file builds the auxiliary lemmas bottom-up. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
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
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_sub_sound.

Set Implicit Arguments.

(* §1-§2 (uskl_to_pskl_close, pskl_decorate_exists, is_tskl_lc) moved to
   prop_pat_sub.v §7 so prop_sub_sound can pick decorations when
   instantiating the cofinite ForallL tag premise. *)

(* ===================================================================== *)
(*  §3  Constraint-solving concatenation (lemma:solvetag-concat)          *)
(*                                                                        *)
(*  Solvable constraint lists are eq-prefixed with at most a single sub   *)
(*  at the tail; splitting/joining a solve at a list append splits/joins  *)
(*  the solved tag set.                                                   *)
(* ===================================================================== *)

Lemma a_solvetag_split : forall C1 C2 ψ Ψ,
  (C1 ++ C2) ⊩ᵗ ψ ⤳ Ψ ->
  exists Ψ1 Ψ2,
    C1 ⊩ᵗ ψ ⤳ Ψ1 /\ C2 ⊩ᵗ ψ ⤳ Ψ2 /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  induction C1 as [ | c C1' IH ]; intros C2 ψ Ψ Hs; simpl in Hs.
  - exists empty, Ψ. repeat apply conj;
      [ apply a_solvetag__empty; fsetdec | exact Hs | fsetdec ].
  - destruct c as [ M Q | Q ].
    + (* sub head : inversion unifies C1' ++ C2 = nil *)
      inversion Hs as [ | M0 Q0 ψ0 Ψ0 Hsub Hnil | ]; subst.
      symmetry in H0. apply app_eq_nil in H0. destruct H0 as [-> ->].
      exists Ψ, empty. repeat apply conj;
        [ apply a_solvetag__sub; exact Hsub
        | apply a_solvetag__empty; fsetdec | fsetdec ].
    + (* eq head *)
      inversion Hs as [ | | Q0 C0 ψ0 Ψall Ψa Ψb Heqp Hrest HΨ ]; subst.
      destruct (IH C2 ψ Ψb Hrest) as [Ψ1 [Ψ2 [Hs1 [Hs2 HΨe]]]].
      exists (Ψa `union` Ψ1), Ψ2. repeat apply conj.
      * eapply a_solvetag__eq; [ exact Heqp | exact Hs1 | fsetdec ].
      * exact Hs2.
      * clear - HΨ HΨe. fsetdec.
Qed.

Scheme a_solvetag_sub_mut := Induction for a_solvetag_sub Sort Prop
  with a_solvetag_eq_mut := Induction for a_solvetag_eq Sort Prop.
Combined Scheme a_solvetag_sub_eq_mutind
  from a_solvetag_sub_mut, a_solvetag_eq_mut.

Lemma a_solvetag_sub_eq_psi_cong :
  (forall ψ M P Ψ, ψ ≼ᵗ[ M ] P ⤳ Ψ ->
     forall Ψ', Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] P ⤳ Ψ') /\
  (forall ψ P Ψ, ψ ∼ᵗ P ⤳ Ψ ->
     forall Ψ', Ψ [=] Ψ' -> ψ ∼ᵗ P ⤳ Ψ').
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M P Ψ _ => forall Ψ', Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] P ⤳ Ψ')
           (fun ψ P Ψ _ => forall Ψ', Ψ [=] Ψ' -> ψ ∼ᵗ P ⤳ Ψ'));
    intros; try (econstructor; eauto; fsetdec).
Qed.

Lemma a_solvetag_sub_psi_cong : forall ψ M P Ψ Ψ',
  ψ ≼ᵗ[ M ] P ⤳ Ψ -> Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] P ⤳ Ψ'.
Proof. intros; eapply (proj1 a_solvetag_sub_eq_psi_cong); eauto. Qed.

Lemma a_solvetag_eq_psi_cong : forall ψ P Ψ Ψ',
  ψ ∼ᵗ P ⤳ Ψ -> Ψ [=] Ψ' -> ψ ∼ᵗ P ⤳ Ψ'.
Proof. intros; eapply (proj2 a_solvetag_sub_eq_psi_cong); eauto. Qed.

Lemma a_solvetag_psi_cong : forall 𝒞 ψ Ψ Ψ',
  𝒞 ⊩ᵗ ψ ⤳ Ψ -> Ψ [=] Ψ' -> 𝒞 ⊩ᵗ ψ ⤳ Ψ'.
Proof.
  intros 𝒞 ψ Ψ Ψ' Hs; revert Ψ'; induction Hs; intros Ψ' Heq.
  - apply a_solvetag__empty. fsetdec.
  - apply a_solvetag__sub. eapply a_solvetag_sub_psi_cong; eauto.
  - eapply a_solvetag__eq; [ exact H | exact Hs | clear - Heq H0; fsetdec ].
Qed.

(* NB: the paper's converse (join) direction is only sound when the
   left list is eq-only — a sub constraint solves only as a singleton
   list.  The forward split above is what the main decoration proof
   consumes; the join is deferred until a call site fixes its shape. *)


(* ===================================================================== *)
(*  §4  Erasure commutes with decorated substitution                     *)
(* ===================================================================== *)

Lemma uskl_to_pskl_subst : forall ψ ψg β,
  ⌊ subst_bskl_in_uskl ψg β ψ ⌋ˢ
  = subst_pskl_in_pskl ⌊ ψg ⌋ˢ β ⌊ ψ ⌋ˢ.
Proof.
  induction ψ; intros ψg β; simpl; try (f_equal; auto; fail).
  destruct_if;
    reflexivity.
Qed.

(* ===================================================================== *)
(*  §5  The ρ metasubstitution (rigid vars → decorated skeletons)         *)
(*                                                                        *)
(*  The paper's ρ, applied to a decorated skeleton, and its erased        *)
(*  counterpart applied to the plain erasure.  Represented as iterated    *)
(*  single substitutions; freshness of the domain against the range is    *)
(*  maintained at every use so iterated = simultaneous.                   *)
(* ===================================================================== *)

Fixpoint msubst_uskl (ρ : list (atom * uskl)) (T : uskl) : uskl :=
  match ρ with
  | nil => T
  | (β, ψg) :: ρ' => subst_bskl_in_uskl ψg β (msubst_uskl ρ' T)
  end.

Fixpoint msubst_pskl_named (ρ : list (atom * pskl)) (P : pskl) : pskl :=
  match ρ with
  | nil => P
  | (β, Pg) :: ρ' => subst_pskl_in_pskl Pg β (msubst_pskl_named ρ' P)
  end.

Definition erase_msubst (ρ : list (atom * uskl)) : list (atom * pskl) :=
  map (fun ψg => uskl_to_pskl ψg) ρ.

(** Erasure commutes with the metasubstitution. *)
Lemma uskl_to_pskl_msubst : forall ρ R,
  ⌊ msubst_uskl ρ R ⌋ˢ = msubst_pskl_named (erase_msubst ρ) ⌊ R ⌋ˢ.
Proof.
  induction ρ as [ | [β ψg] ρ' IH ]; intros R; simpl; [ reflexivity | ].
  rewrite uskl_to_pskl_subst. rewrite IH. reflexivity.
Qed.

(** A variable outside the domain is untouched. *)
Lemma msubst_uskl_var_notin : forall ρ β,
  β `notin` dom ρ ->
  msubst_uskl ρ (uskl_var_f β) = uskl_var_f β.
Proof.
  induction ρ as [ | [α1 ψg] ρ' IH ]; intros β Hβ; simpl; [ reflexivity | ].
  rewrite IH; [ | simpl in Hβ; clear - Hβ; fsetdec ].
  simpl.
  destruct_if as [-> | Hne];
    [ simpl in Hβ; exfalso; clear - Hβ; fsetdec | reflexivity ].
Qed.

(** Local closure of every range skeleton lets ρ commute with opening. *)
Definition msubst_lc (ρ : list (atom * uskl)) : Prop :=
  forall β ψg, binds β ψg ρ -> lc_uskl ψg.

Lemma msubst_uskl_open_comm : forall ρ R α,
  msubst_lc ρ ->
  α `notin` dom ρ ->
  (forall β ψg, binds β ψg ρ -> α `notin` ftvar_in_uskl ψg) ->
  msubst_uskl ρ (open_uskl_wrt_uskl R (uskl_var_f α))
  = open_uskl_wrt_uskl (msubst_uskl ρ R) (uskl_var_f α).
Proof.
  induction ρ as [ | [α1 ψg] ρ' IH ]; intros R α Hlc Hdom Hftv;
    simpl; [ reflexivity | ].
  assert (Hlcγ : lc_uskl ψg)
    by (eapply Hlc; unfold binds; simpl; left; reflexivity).
  assert (Hlc' : msubst_lc ρ')
    by (intros b p Hb; eapply Hlc; unfold binds; simpl; right; exact Hb).
  assert (Hdom' : α `notin` dom ρ')
    by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (Hftv' : forall b p, binds b p ρ' -> α `notin` ftvar_in_uskl p)
    by (intros b p Hb; eapply Hftv; unfold binds; simpl; right; exact Hb).
  rewrite (IH R α Hlc' Hdom' Hftv').
  rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcγ ].
  f_equal.
  assert (Hαγ : α <> α1) by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (HXf : α `notin` ftvar_in_uskl ψg)
    by (eapply Hftv; unfold binds; simpl; left; reflexivity).
  simpl.
  destruct_if as [-> | _];
    [ contradiction | reflexivity ].
Qed.
(* general erasure/open commute (open with an arbitrary skeleton) *)
Lemma uskl_to_pskl_open_gen : forall R ψg,
  ⌊ open_uskl_wrt_uskl R ψg ⌋ˢ
  = open_pskl_wrt_pskl ⌊ R ⌋ˢ ⌊ ψg ⌋ˢ.
Proof.
  intros. unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl.
  generalize 0. induction R; intros k; simpl; try (f_equal; auto; fail).
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

(* ===================================================================== *)
(*  §6  Vacuous subtyping decoration (lemma:vacuous-subtyping-decoration) *)
(*                                                                        *)
(*  With input skeleton [◇] the run solves no tags and is determined by   *)
(*  the source's ERASURE alone: any two lc sources with equal erasure     *)
(*  give the same run.  Stronger than (and directly implies) the paper's  *)
(*  ρ-threaded statement, since both sides erase equally.                 *)
(* ===================================================================== *)

Lemma a_subtag_vacuous_erasure : forall NM M P0 Ψ Θ0 R1' P Θ1,
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] R1' ⩽˙ P ⊣ Θ1 ->
  P0 = pskl_hole ->
  forall R2', lc_uskl R2' -> ⌊ R2' ⌋ˢ = ⌊ R1' ⌋ˢ ->
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] R2' ⩽˙ P ⊣ Θ1.
Proof.
  intros NM M P0 Ψ Θ0 R1' P Θ1 H.
  induction H; intros HP0 R2' HlcT2 Herase; subst; try discriminate HP0.
  - (* Infer : output is ⌊R⌋ = ⌊R2'⌋ *)
    rewrite <- Herase. apply a_subtag__infer; assumption.
  - (* Check : P0 = B = ◇, but guarded_pskl ◇ is absurd *)
    inv_guarded_hole.
  - (* UnivGhostR : source guarded, output tophole ⌊R⌋ *)
    (* ⌊R2'⌋ = ⌊R⌋ guarded ⇒ R2' top ∈ {unit,var,arrow} ⇒ R2' guarded *)
    assert (HgT2 : guarded_uskl R2').
    { inversion H; subst; simpl in Herase;
        destruct R2'; simpl in Herase; inversion Herase; subst;
        inversion HlcT2; subst; constructor; assumption. }
    rewrite <- Herase. apply a_subtag__univ_ghost_r; assumption.
  - (* ForallL tagged : reconstruct on R2' (shape decides tagged/untagged);
       the cofinite tag family maps through the family IH pointwise. *)
    destruct R2'; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + eapply a_subtag__forall_l_untagged with (L := L) (Ξ := Ξ) (P1 := P1);
        [ exact H | right; reflexivity | | exact H2 | exact H3 | ].
      * intros α Hα.
        match goal with
        | Hb : ⌊ ?T2b ⌋ˢ = ⌊ ?Rb ⌋ˢ
          |- a_extract _ _ _ _ ⌊ open_uskl_wrt_uskl ?T2b _ ⌋ˢ _ _ _ =>
            replace (⌊ open_uskl_wrt_uskl T2b (uskl_var_f α) ⌋ˢ)
              with (⌊ open_uskl_wrt_uskl Rb (uskl_var_f α) ⌋ˢ)
              by (rewrite ! uskl_to_pskl_open; rewrite Hb; reflexivity)
        end.
        apply H1; exact Hα.
      * intros Ψg ψg Hfr Hsort Hera.
        match goal with
        | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
            eapply (IHfam Ψg ψg Hfr Hsort Hera eq_refl)
        end.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion Hsort; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen.
           match goal with Hb : ⌊ _ ⌋ˢ = ⌊ _ ⌋ˢ |- _ => rewrite Hb end.
           reflexivity.
    + eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
        [ exact H | right; reflexivity | | exact H2 | exact H3 | ].
      * intros α Hα.
        match goal with
        | Hb : ⌊ ?T2b ⌋ˢ = ⌊ ?Rb ⌋ˢ
          |- a_extract _ _ _ _ ⌊ open_uskl_wrt_uskl ?T2b _ ⌋ˢ _ _ _ =>
            replace (⌊ open_uskl_wrt_uskl T2b (uskl_var_f α) ⌋ˢ)
              with (⌊ open_uskl_wrt_uskl Rb (uskl_var_f α) ⌋ˢ)
              by (rewrite ! uskl_to_pskl_open; rewrite Hb; reflexivity)
        end.
        apply H1; exact Hα.
      * intros Ψg ψg Hfr Hsort Hera.
        match goal with
        | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
            eapply (IHfam Ψg ψg Hfr Hsort Hera eq_refl)
        end.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion Hsort; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen.
           match goal with Hb : ⌊ _ ⌋ˢ = ⌊ _ ⌋ˢ |- _ => rewrite Hb end.
           reflexivity.
  - (* ForallL untagged : identical reconstruction *)
    destruct R2'; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + eapply a_subtag__forall_l_untagged with (L := L) (Ξ := Ξ) (P1 := P1);
        [ exact H | right; reflexivity | | exact H2 | exact H3 | ].
      * intros α Hα.
        match goal with
        | Hb : ⌊ ?T2b ⌋ˢ = ⌊ ?Rb ⌋ˢ
          |- a_extract _ _ _ _ ⌊ open_uskl_wrt_uskl ?T2b _ ⌋ˢ _ _ _ =>
            replace (⌊ open_uskl_wrt_uskl T2b (uskl_var_f α) ⌋ˢ)
              with (⌊ open_uskl_wrt_uskl Rb (uskl_var_f α) ⌋ˢ)
              by (rewrite ! uskl_to_pskl_open; rewrite Hb; reflexivity)
        end.
        apply H1; exact Hα.
      * intros Ψg ψg Hfr Hsort Hera.
        match goal with
        | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
            eapply (IHfam Ψg ψg Hfr Hsort Hera eq_refl)
        end.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion Hsort; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen.
           match goal with Hb : ⌊ _ ⌋ˢ = ⌊ _ ⌋ˢ |- _ => rewrite Hb end.
           reflexivity.
    + eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
        [ exact H | right; reflexivity | | exact H2 | exact H3 | ].
      * intros α Hα.
        match goal with
        | Hb : ⌊ ?T2b ⌋ˢ = ⌊ ?Rb ⌋ˢ
          |- a_extract _ _ _ _ ⌊ open_uskl_wrt_uskl ?T2b _ ⌋ˢ _ _ _ =>
            replace (⌊ open_uskl_wrt_uskl T2b (uskl_var_f α) ⌋ˢ)
              with (⌊ open_uskl_wrt_uskl Rb (uskl_var_f α) ⌋ˢ)
              by (rewrite ! uskl_to_pskl_open; rewrite Hb; reflexivity)
        end.
        apply H1; exact Hα.
      * intros Ψg ψg Hfr Hsort Hera.
        match goal with
        | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
            eapply (IHfam Ψg ψg Hfr Hsort Hera eq_refl)
        end.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion Hsort; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen.
           match goal with Hb : ⌊ _ ⌋ˢ = ⌊ _ ⌋ˢ |- _ => rewrite Hb end.
           reflexivity.
  - (* Ghost : source hole, output P0=hole *)
    destruct R2'; simpl in Herase; inversion Herase; subst.
    + apply a_subtag__ghost; assumption.
    + apply a_subtag__ghostg; assumption.
  - (* GhostG : source holeg, output hole *)
    destruct R2'; simpl in Herase; inversion Herase; subst.
    + apply a_subtag__ghost; [ assumption ].
    + apply a_subtag__ghostg; assumption.
  - (* UnivGhostL : source tophole R *)
    destruct R2'; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + apply a_subtag__univ_ghost_l; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
    + apply a_subtag__univ_ghost_lg; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
  - (* UnivGhostLG : source topholeg R *)
    destruct R2'; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + apply a_subtag__univ_ghost_l; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
    + apply a_subtag__univ_ghost_lg; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
  - (* FlexMono : source var α ⇒ R2' = var α *)
    destruct R2'; simpl in Herase; inversion Herase; subst.
    apply a_subtag__flex_mono; assumption.
Qed.

(* ===================================================================== *)
(*  §7  Ψ-congruence for decorated consistency and subtyping             *)
(*                                                                        *)
(*  The tag context threads through every rule via [=]-premises, so it    *)
(*  respects set equality.  Needed by the decoration-var lemmas (their    *)
(*  var/unit cases produce Ψ ∪ ∅).                                        *)
(* ===================================================================== *)

Lemma a_consistag_psi_cong : forall Δ1 Δ2 P0 Ψ Θ0 R P Θ1,
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ P ⊣ Θ1 ->
  forall Ψ', Ψ [=] Ψ' ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ' ] R ∼˙ P ⊣ Θ1.
Proof.
  intros Δ1 Δ2 P0 Ψ Θ0 R P Θ1 H; induction H; intros Ψ' Heq; econstructor;
    solve
      [ eassumption
      | (match goal with
         | IH : forall Ψ0 : atoms, _ [=] Ψ0 -> _ |- _ =>
             eapply IH; eassumption
         end)
      | (intros;
         match goal with
         | IH : forall α : atom, α `notin` _ ->
                  forall Ψ0, _ [=] Ψ0 -> _ |- _ =>
             eapply IH; [ eassumption | eassumption ]
         end)
      | fsetdec ].
Qed.







(* a_subtag/a_subtag_flex Ψ-congruence deferred until the subtyping-
   decoration-var lemma needs it (the mutual solve tactic needs per-case
   handling for flex_mono/forall_l; built when consumed). *)

(* ===================================================================== *)
(*  §8  Consistency decoration for variables (lemma:consistency-          *)
(*  decoration-var, consistency-proofs.tex:606)                          *)
(*                                                                        *)
(*  Induction on the decorated constraint-solving (EQ) derivation.  The   *)
(*  ∀-cases open a FRESH RIGID on both sides, so ρ is NOT extended — it    *)
(*  just commutes with the opening (msubst_uskl_open_comm).               *)
(*                                                                        *)
(*  WIP bundle — easy cases (unit/var) Qed via psi_cong; the structural   *)
(*  ∀/arrow/ghost/flex cases are honest admits (true, unfinished).        *)
(* ===================================================================== *)

(** The free type variables of ρ's range (a finite avoid-set). *)
Definition msubst_ftv (ρ : list (atom * uskl)) : atoms :=
  fold_right (fun p acc => ftvar_in_uskl (snd p) `union` acc) empty ρ.

Lemma msubst_ftv_binds : forall ρ β ψg,
  binds β ψg ρ -> ftvar_in_uskl ψg [<=] msubst_ftv ρ.
Proof.
  induction ρ as [ | [α1 g] ρ' IH ]; intros β ψg Hb; simpl in *;
    [ inversion Hb | ].
  destruct Hb as [Heq | Hb].
  - inversion Heq; subst. clear; fsetdec.
  - specialize (IH _ _ Hb). clear - IH; fsetdec.
Qed.

(** ρ distributes over every skeleton constructor (iterated subst). *)
Lemma msubst_uskl_arrow : forall ρ R R',
  msubst_uskl ρ (uskl_arrow R R')
  = uskl_arrow (msubst_uskl ρ R) (msubst_uskl ρ R').
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_tophole : forall ρ R,
  msubst_uskl ρ (uskl_tophole R) = uskl_tophole (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_topholeg : forall ρ R,
  msubst_uskl ρ (uskl_topholeg R) = uskl_topholeg (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_all_syn : forall ρ R,
  msubst_uskl ρ (uskl_all_syn R) = uskl_all_syn (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_all_etag : forall ρ ε R,
  msubst_uskl ρ (uskl_all_etag ε R) = uskl_all_etag ε (msubst_uskl ρ R).
Proof. induction ρ as [|[α1 g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

(** strip = pskl_to_uskl ∘ uskl_to_pskl commutes with opening. *)
Lemma strip_open : forall ψ β,
  pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψ (uskl_var_f β)))
  = open_uskl_wrt_uskl (pskl_to_uskl (uskl_to_pskl ψ)) (uskl_var_f β).
Proof.
  intros. rewrite uskl_to_pskl_open. rewrite pskl_to_uskl_open_var. reflexivity.
Qed.

Lemma lc_uskl_to_pskl_local : forall R, lc_uskl R -> lc_pskl (uskl_to_pskl R).
Proof.
  intros R H; induction H; simpl;
    try (constructor; auto; fail);
    constructor; intros α; rewrite <- uskl_to_pskl_open; auto.
Qed.

(** Reflection of local closure / guardedness through the erasure. *)
Lemma degree_uskl_of_pskl : forall R' k,
  degree_pskl_wrt_pskl k (uskl_to_pskl R') -> degree_uskl_wrt_uskl k R'.
Proof.
  induction R'; intros k Hd; simpl in Hd; inversion Hd; subst;
    constructor; auto.
Qed.

Lemma lc_uskl_of_pskl : forall T,
  lc_pskl (uskl_to_pskl T) -> lc_uskl T.
Proof.
  intros T H. apply lc_uskl_of_degree. apply degree_uskl_of_pskl.
  apply degree_pskl_wrt_pskl_of_lc_pskl. exact H.
Qed.

Lemma guarded_uskl_to_pskl_fwd : forall R,
  guarded_uskl R -> guarded_pskl (uskl_to_pskl R).
Proof.
  intros R H; inversion H; simpl; constructor;
    apply lc_uskl_to_pskl_local; assumption.
Qed.

Lemma guarded_uskl_of_pskl : forall T,
  guarded_pskl (uskl_to_pskl T) -> guarded_uskl T.
Proof.
  destruct T; simpl; intros H; inversion H; subst;
    try (constructor; apply lc_uskl_of_pskl; assumption).
Qed.

(** ρ preserves local closure. *)
Lemma msubst_uskl_lc : forall ρ R,
  msubst_lc ρ -> lc_uskl R -> lc_uskl (msubst_uskl ρ R).
Proof.
  induction ρ as [ | [β ψg] ρ' IH ]; intros R Hlc HT; simpl; [ exact HT | ].
  apply subst_bskl_in_uskl_lc_uskl.
  - apply IH; [ | exact HT ].
    intros b p Hb; eapply Hlc; unfold binds; simpl; right; exact Hb.
  - eapply Hlc; unfold binds; simpl; left; reflexivity.
Qed.

(** A unit/variable-headed EQ run solves no tags. *)
Lemma a_solvetag_eq_atom_empty : forall ψ P0 Ψ,
  ψ ∼ᵗ P0 ⤳ Ψ ->
  (ψ = uskl_unit \/ exists α, ψ = uskl_var_f α) ->
  Ψ [=] empty.
Proof.
  intros ψ P0 Ψ H; induction H; intros Hshape;
    try (destruct Hshape as [Hd | [α0 Hd]]; discriminate Hd);
    try assumption.
  - (* UnivGhostR : same subject, recurse *)
    apply IHa_solvetag_eq; exact Hshape.
Qed.

(** With input ◇ the consistency run is determined by the source's erasure
    (analogue of a_subtag_vacuous_erasure). *)
Lemma a_consistag_vacuous_erasure : forall Δ1 Δ2 P0 Ψ Θ0 R1 P Θ1,
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R1 ∼˙ P ⊣ Θ1 ->
  P0 = pskl_hole ->
  forall T2, uskl_to_pskl T2 = uskl_to_pskl R1 ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] T2 ∼˙ P ⊣ Θ1.
Proof.
  intros Δ1 Δ2 P0 Ψ Θ0 R1 P Θ1 H;
    induction H; intros HP0 T2 Herase; subst; try discriminate HP0.
  - (* Ghost : R1 = ◇, output ◇ *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      [ apply a_consistag__ghost; [ simpl; clear; fsetdec | assumption ]
      | apply a_consistag__ghostg; assumption ].
  - (* FlexL : R1 = var α, so T2 = var α *)
    destruct T2; simpl in Herase; inversion Herase; subst.
    eapply a_consistag__flex_l; eassumption.
  - (* GhostG : R1 = holeg, output ◇ *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      [ apply a_consistag__ghost; [ simpl; clear; fsetdec | assumption ]
      | apply a_consistag__ghostg; assumption ].
  - (* UnivGhost2 : guarded_pskl ◇ is absurd *)
    inv_guarded_hole.
  - (* GhostR : output ⌊R⌋; reconstruct with T2 (same erasure) *)
    rewrite <- Herase.
    apply a_consistag__ghost_r; [ rewrite Herase; assumption | assumption ].
Qed.

(* ===================================================================== *)
(*  §8.5  Monotype-shape lemmas for the SEq-FlexR decoration case         *)
(*                                                                        *)
(*  FlexR decorates a run whose RHS is a flexible (monotype) variable α̂.  *)
(*  The subject's erasure is assigned to α̂, so it must be a monotype — in  *)
(*  particular quantifier-free.  Every [abind_flex_mono_def τ] carries a   *)
(*  monotype [τ] BY WELL-FORMEDNESS (def_extra.v:147; Assign-SolveM's     *)
(*  guess is checked mono — type.ml:351), so the monotype fact is a wf     *)
(*  lookup, not consistency reasoning; the existing [a_assign_sound] gives *)
(*  a decorated pattern-consistency against α̂ that we read off below.      *)
(* ===================================================================== *)

Inductive no_all_syn_pskl : pskl -> Prop :=
| nas_pskl__unit    : no_all_syn_pskl pskl_unit
| nas_pskl__var_b   : forall n, no_all_syn_pskl (pskl_var_b n)
| nas_pskl__var_f   : forall α, no_all_syn_pskl (pskl_var_f α)
| nas_pskl__arrow   : forall P1 P2,
    no_all_syn_pskl P1 -> no_all_syn_pskl P2 -> no_all_syn_pskl (pskl_arrow P1 P2)
| nas_pskl__hole    : no_all_syn_pskl pskl_hole
| nas_pskl__tophole : forall P, no_all_syn_pskl P -> no_all_syn_pskl (pskl_tophole P).

Inductive no_all_syn_uskl : uskl -> Prop :=
| nas_uskl__unit     : no_all_syn_uskl uskl_unit
| nas_uskl__var_b    : forall n, no_all_syn_uskl (uskl_var_b n)
| nas_uskl__var_f    : forall α, no_all_syn_uskl (uskl_var_f α)
| nas_uskl__arrow    : forall R1 R2,
    no_all_syn_uskl R1 -> no_all_syn_uskl R2 -> no_all_syn_uskl (uskl_arrow R1 R2)
| nas_uskl__hole     : no_all_syn_uskl uskl_hole
| nas_uskl__holeg    : no_all_syn_uskl uskl_holeg
| nas_uskl__tophole  : forall R, no_all_syn_uskl R -> no_all_syn_uskl (uskl_tophole R)
| nas_uskl__topholeg : forall R, no_all_syn_uskl R -> no_all_syn_uskl (uskl_topholeg R).

Lemma no_all_syn_pskl_to_uskl : forall P,
  no_all_syn_pskl P -> no_all_syn_uskl (pskl_to_uskl P).
Proof. induction 1; simpl; constructor; auto. Qed.

(** A pattern-consistency run against a monotype RHS reads a quantifier-free
    subject: erasure of a flex-var assignment can only remove tags that are
    not there.  Def-variable lookups use [a_wf_aenv_binds_def_mono]. *)
Lemma ad_pat_consis_mono_no_all_syn : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  no_all_syn_uskl R.
Proof.
  intros Ψ Θ R Q H; induction H; intros Hwf Hmono;
    try solve [ inversion Hmono ];
    try solve [ constructor ].
  - (* arrow *)
    inversion Hmono; subst.
    constructor; [ apply IHad_pat_consis1 | apply IHad_pat_consis2 ]; auto.
  - (* tophole_drop *)
    constructor. apply IHad_pat_consis; auto.
  - (* flex_r : RHS is a def variable; its def is a monotype (wf) *)
    apply IHad_pat_consis; [ exact Hwf | ].
    apply mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; [ exact Hwf | eassumption ].
Qed.

(** Canonical form: a ghost-free [ψ] whose stripped image (under [ρ]) carries
    no [all_syn] has no ε-tags either, so [ρ] applied to [ψ] and to its strip
    coincide.  (The tags live only on quantifiers; no quantifier survives.) *)
Lemma msubst_ghostfree_eq_strip : forall ρ ψ,
  uskl_ghost_free ψ ->
  no_all_syn_uskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ->
  msubst_uskl ρ ψ = msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)).
Proof.
  intros ρ ψ H; induction H; intros Hnas.
  - (* unit *) reflexivity.
  - (* var *) reflexivity.
  - (* arrow *)
    simpl. rewrite ! msubst_uskl_arrow.
    simpl in Hnas. rewrite msubst_uskl_arrow in Hnas. inversion Hnas; subst.
    erewrite IHuskl_ghost_free1 by eassumption.
    erewrite IHuskl_ghost_free2 by eassumption.
    reflexivity.
  - (* all_etag : strip is an all_syn, contradicting no_all_syn *)
    simpl in Hnas. rewrite msubst_uskl_all_syn in Hnas. inversion Hnas.
  - (* all_syn : likewise *)
    simpl in Hnas. rewrite msubst_uskl_all_syn in Hnas. inversion Hnas.
Qed.

(** A decorated-consistency run against a flexible-variable input reads a
    quantifier-free subject.  The flex-var rules that fire (rigid/flex/flexl/
    ghost) leave a variable or hole; FlexR assigns the subject's erasure to
    α̂, so [a_assign_sound] exposes it as pattern-consistent with the monotype
    α̂ — quantifier-free by the previous lemma. *)
Lemma a_consistag_flexvar_subject_no_all_syn : forall Δ1 Δ2 α Ψ Θ0 R P Θ1,
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | (pskl_var_f α) | Ψ ] R ∼˙ P ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl R) ->
  no_all_syn_uskl R.
Proof.
  intros Δ1 Δ2 α Ψ Θ0 R P Θ1 H.
  remember (pskl_var_f α) as P0 eqn:HP0. revert HP0.
  induction H; intros HP0 Hwf HwfS;
    try discriminate HP0; try solve [ constructor ].
  - (* flex_r : subject is [pskl_to_uskl P], with P assigned to α̂ *)
    rewrite uskl_to_pskl_pskl_to_uskl in HwfS.
    match goal with
    | Hass : a_assign _ _ _ _ _ _ |- _ =>
        eapply ad_pat_consis_mono_no_all_syn;
          [ eapply (proj2 (a_assign_sound Hass ltac:(constructor) Hwf HwfS))
          | eapply (a_assign_preserves_wf Hass ltac:(constructor) Hwf HwfS)
          | constructor ]
    end.
  - (* univ_ghost2 : subject ⫯R; recurse on the inner R (same var input) *)
    constructor.
    simpl in HwfS. inversion HwfS; subst.
    eapply IHa_consistag;
      [ first [ eassumption | reflexivity ] | exact Hwf | eassumption ].
Qed.

Lemma lc_uskl_arrow_inv : forall R R',
  lc_uskl (uskl_arrow R R') -> lc_uskl R /\ lc_uskl R'.
Proof. intros R R' H; inversion H; auto. Qed.

Lemma a_wf_pskl_arrow_inv : forall Θ Δ P1 P2,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_arrow P1 P2) -> Θ ⨟ Δ ⊢ₚₛᵃ P1 /\ Θ ⨟ Δ ⊢ₚₛᵃ P2.
Proof. intros * H; inversion H; auto. Qed.

Lemma a_wf_pskl_tophole_inv : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_tophole P) -> Θ ⨟ empty ⊢ₚₛᵃ P.
Proof. intros * H; inversion H; auto. Qed.

Lemma lc_uskl_tophole_inv : forall R,
  lc_uskl (uskl_tophole R) -> lc_uskl R.
Proof. intros R H; inversion H; auto. Qed.

Lemma lc_uskl_topholeg_inv : forall R,
  lc_uskl (uskl_topholeg R) -> lc_uskl R.
Proof. intros R H; inversion H; auto. Qed.

Lemma a_consistag_decoration_var : forall ψ P0 Ψa,
  ψ ∼ᵗ P0 ⤳ Ψa ->
  forall Δ1 Δ2 Ψ Θ0 P Θ1 ρ,
    msubst_lc ρ ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ]
      (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ∼˙ P ⊣ Θ1 ->
    (* external well-formedness (paper's prose side conditions): only the
       FlexR leaf consumes them, threaded through the induction — the arrow
       case gets its mid-context invariants from [a_consistag_sound_aux] and
       weakens the right run's wf across [Θ0 ⊴ Θm] ([a_wf_pskl_isub],
       [a_isub_binds_tvar]); the ∀-cases extend Δ/Θ by a fresh rigid. *)
    a_wf_aenv Θ0 ->
    lc_uskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)))) ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | (Ψ `union` Ψa) ]
      (msubst_uskl ρ ψ) ∼˙ P ⊣ Θ1.
Proof.
  intros ψ P0 Ψa H; induction H;
    intros Δ1 Δ2 Ψc Θ0 Qc Θ1 ρ Hlcρ Hcons Hwf HlcS HwfP0 HwfS Hrig Hnfd Hfaf.
  - (* SEq-Unit : ψ = unit, strip = unit, sources identical *)
    simpl in Hcons |- *.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H; fsetdec ].
  - (* SEq-Var : ψ = var α, strip = var α, sources identical *)
    simpl in Hcons |- *.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H; fsetdec ].
  - (* SEq-Vacuous : P0 = ◇, both sources erase equally *)
    eapply a_consistag_psi_cong;
      [ eapply a_consistag_vacuous_erasure;
          [ exact Hcons | reflexivity | ]
      | clear - H; fsetdec ].
    rewrite ! uskl_to_pskl_msubst. f_equal.
    rewrite uskl_to_pskl_pskl_to_uskl. reflexivity.
  - (* SEq-Arrow : invert the consistency arrow, IH each part; thread wf
       (mid-context Θm's invariants from a_consistag_sound_aux on the left run). *)
    simpl in HlcS. rewrite msubst_uskl_arrow in HlcS.
    apply lc_uskl_arrow_inv in HlcS as [HlcS1 HlcS2].
    simpl in HwfS. rewrite msubst_uskl_arrow in HwfS. simpl in HwfS.
    apply a_wf_pskl_arrow_inv in HwfS as [HwfS1 HwfS2].
    apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP1 HwfP2].
    rewrite msubst_uskl_arrow.
    simpl in Hcons. rewrite msubst_uskl_arrow in Hcons.
    inversion Hcons; subst. clear Hcons.
    lazymatch goal with
    | Hc1 : _ ⊢ᵗ[ _ | _ | _ | ?Ψi1 ] _ ∼˙ _ ⊣ ?Θm,
      Hc2 : ?Θm ⊢ᵗ[ _ | _ | _ | ?Ψi2 ] _ ∼˙ _ ⊣ _,
      HΨi : _ [=] union ?Ψi1 ?Ψi2 |- _ =>
        destruct (a_consistag_sound_aux Hc1 Hwf HlcS1 HwfP1 HwfS1 Hrig Hnfd Hfaf)
          as [Hle [HwfΘm [HnfdΘm [HfafΘm _]]]];
        eapply a_consistag__arrow with
          (Ψ1 := Ψi1 `union` Ψ1) (Ψ2 := Ψi2 `union` Ψ2) (Θ1 := Θm);
        [ eapply IHa_solvetag_eq1;
            [ exact Hlcρ | exact Hc1 | exact Hwf | exact HlcS1 | exact HwfP1
            | exact HwfS1 | exact Hrig | exact Hnfd | exact Hfaf ]
        | eapply IHa_solvetag_eq2;
            [ exact Hlcρ | exact Hc2 | exact HwfΘm | exact HlcS2
            | eapply a_wf_pskl_isub; [ exact HwfP2 | exact Hle ]
            | eapply a_wf_pskl_isub; [ exact HwfS2 | exact Hle ]
            | intros α Hα; eapply a_isub_binds_tvar; [ exact Hle | apply Hrig; exact Hα ]
            | exact HnfdΘm | exact HfafΘm ]
        | clear - HΨi H1; fsetdec ]
    end.
  - (* SEq-ForallInh : open a fresh rigid; build the extended wf hyps as in
       a_consistag_sound_aux's ForallInh case, then IH the opened body. *)
    rewrite msubst_uskl_all_etag.
    simpl in Hcons. rewrite msubst_uskl_all_syn in Hcons.
    inversion Hcons; subst.
    match goal with
    | Hc : forall a, a `notin` _ -> _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
        rename Hc into Hcbody
    end.
    simpl in HlcS. rewrite msubst_uskl_all_syn in HlcS. inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    inversion HwfP0 as [ | | | LP Θa Δa P0a Hbody0 Heqa | | ]; subst.
    simpl in HwfS. rewrite msubst_uskl_all_syn in HwfS. simpl in HwfS.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    eapply a_consistag__forall_inh_tagged
      with (Ψ0 := Ψc `union` Ψ0) (ε := ε)
           (L := LP `union` LS `union` L `union` L0 `union` dom ρ
                 `union` msubst_ftv ρ `union` dom Θ0);
      [ intros β Hβ | clear - H1; fsetdec ].
    assert (Hβρ : β `notin` dom ρ) by (clear - Hβ; fsetdec).
    assert (Hβf : forall α1 ψg, binds α1 ψg ρ -> β `notin` ftvar_in_uskl ψg).
    { intros α1 ψg Hb. pose proof (msubst_ftv_binds _ _ _ Hb) as Hsc.
      clear - Hβ Hsc. fsetdec. }
    assert (HβΘ : β `notin` dom Θ0) by (clear - Hβ; fsetdec).
    rewrite <- (@msubst_uskl_open_comm ρ ψ β Hlcρ Hβρ Hβf).
    eapply (H0 β ltac:(clear - Hβ; fsetdec));
      [ exact Hlcρ
      | (* consistency premise *)
        rewrite strip_open;
        pose proof (Hcbody β ltac:(clear - Hβ; fsetdec)) as Hcβ;
        rewrite <- (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                      Hlcρ Hβρ Hβf) in Hcβ;
        exact Hcβ
      | apply a_wf_aenv__tvar; [ exact HβΘ | exact Hwf ]
      | (* lc of opened subject *)
        rewrite strip_open;
        rewrite (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                   Hlcρ Hβρ Hβf);
        apply HlcSbody
      | (* wf of opened input *)
        eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc (Hbody0 β ltac:(clear - Hβ; fsetdec)) β)
          | clear; fsetdec ]
      | (* wf of opened subject-erasure *)
        rewrite strip_open;
        rewrite (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                   Hlcρ Hβρ Hβf);
        rewrite uskl_to_pskl_open;
        eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc (HbodyS β ltac:(clear - Hβ; fsetdec)) β)
          | clear; fsetdec ]
      | (* Hrig *)
        intros α Hα; destruct (α == β) as [ -> | Hne ];
          [ unfold binds; left; reflexivity
          | unfold binds; right; apply Hrig; clear - Hα Hne; fsetdec ]
      | (* Hnfd *)
        apply no_flex_dep_cong with (Δ := add β (Δ1 `union` Δ2));
          [ clear; fsetdec
          | apply no_flex_dep_open_tvar; [ exact Hwf | exact Hnfd | exact HβΘ ] ]
      | (* Hfaf *)
        apply faf_cong with (Δ := add β (Δ1 `union` Δ2));
          [ clear; fsetdec | apply faf_open_tvar; [ exact Hfaf | exact HβΘ ] ] ].
  - (* SEq-UnivGhostG : invert UnivGhost, IH the inner (same context) *)
    rewrite msubst_uskl_topholeg.
    simpl in HlcS. rewrite msubst_uskl_tophole in HlcS.
    apply lc_uskl_tophole_inv in HlcS.
    simpl in HwfS. rewrite msubst_uskl_tophole in HwfS. simpl in HwfS.
    apply a_wf_pskl_tophole_inv in HwfS.
    apply a_wf_pskl_tophole_inv in HwfP0.
    simpl in Hcons. rewrite msubst_uskl_tophole in Hcons.
    inversion Hcons; subst;
      try (match goal with Hg : guarded_pskl (pskl_tophole _) |- _ =>
             solve [ inversion Hg ] end);
      try (match goal with Hg : guarded_uskl (uskl_tophole _) |- _ =>
             solve [ inversion Hg ] end).
    match goal with
    | Hc : _ ⊢ᵗ[ _ | _ | _ | _ ]
             (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ∼˙ _ ⊣ _ |- _ =>
        apply a_consistag__univ_ghostg;
        eapply IHa_solvetag_eq;
          [ exact Hlcρ | exact Hc | exact Hwf | exact HlcS | exact HwfP0
          | exact HwfS | exact Hrig | exact Hnfd | exact Hfaf ]
    end.
  - (* SEq-ForallSyn : as ForallInh but input ∀◇ (unchanged across opening,
       so its wf reassociates directly), tag pass-through. *)
    rewrite msubst_uskl_all_etag.
    simpl in Hcons. rewrite msubst_uskl_all_syn in Hcons.
    inversion Hcons; subst;
      try (match goal with Hg : guarded_uskl (uskl_all_syn _) |- _ =>
             solve [ inversion Hg ] end).
    match goal with
    | Hc : forall a, a `notin` _ -> _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
        rename Hc into Hcbody
    end.
    simpl in HlcS. rewrite msubst_uskl_all_syn in HlcS. inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    simpl in HwfS. rewrite msubst_uskl_all_syn in HwfS. simpl in HwfS.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    eapply a_consistag__forall_syn_tagged
      with (ε := ε) (L := LS `union` L `union` L0 `union` dom ρ
                          `union` msubst_ftv ρ `union` dom Θ0);
      intros β Hβ.
    assert (Hβρ : β `notin` dom ρ) by (clear - Hβ; fsetdec).
    assert (Hβf : forall α1 ψg, binds α1 ψg ρ -> β `notin` ftvar_in_uskl ψg).
    { intros α1 ψg Hb. pose proof (msubst_ftv_binds _ _ _ Hb) as Hsc.
      clear - Hβ Hsc. fsetdec. }
    assert (HβΘ : β `notin` dom Θ0) by (clear - Hβ; fsetdec).
    rewrite <- (@msubst_uskl_open_comm ρ ψ β Hlcρ Hβρ Hβf).
    eapply (H0 β ltac:(clear - Hβ; fsetdec));
      [ exact Hlcρ
      | rewrite strip_open;
        pose proof (Hcbody β ltac:(clear - Hβ; fsetdec)) as Hcβ;
        rewrite <- (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                      Hlcρ Hβρ Hβf) in Hcβ;
        exact Hcβ
      | apply a_wf_aenv__tvar; [ exact HβΘ | exact Hwf ]
      | rewrite strip_open;
        rewrite (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                   Hlcρ Hβρ Hβf);
        apply HlcSbody
      | (* input ∀◇ is unchanged: reassociate its wf under the fresh rigid *)
        eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc HwfP0 β) | clear; fsetdec ]
      | rewrite strip_open;
        rewrite (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                   Hlcρ Hβρ Hβf);
        rewrite uskl_to_pskl_open;
        eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc (HbodyS β ltac:(clear - Hβ; fsetdec)) β)
          | clear; fsetdec ]
      | intros α Hα; destruct (α == β) as [ -> | Hne ];
          [ unfold binds; left; reflexivity
          | unfold binds; right; apply Hrig; clear - Hα Hne; fsetdec ]
      | apply no_flex_dep_cong with (Δ := add β (Δ1 `union` Δ2));
          [ clear; fsetdec
          | apply no_flex_dep_open_tvar; [ exact Hwf | exact Hnfd | exact HβΘ ] ]
      | apply faf_cong with (Δ := add β (Δ1 `union` Δ2));
          [ clear; fsetdec | apply faf_open_tvar; [ exact Hfaf | exact HβΘ ] ] ].
  - (* SEq-UnivGhostR : ψ is guarded (unit/var/arrow).  For unit/var the
       source is unchanged (Ψa=∅, psi_cong); for arrow, peel the ⫯ off the
       input (invert with UnivGhostR), IH the arrow, then re-attach ⫯. *)
    destruct ψ; simpl in H; try solve [ inversion H ]; simpl in Hcons.
    + (* unit *)
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      assert (Hemp : Ψ [=] empty)
        by (eapply a_solvetag_eq_atom_empty; [ exact H0 | left; reflexivity ]).
      clear - Hemp; fsetdec.
    + (* var_f α *)
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      assert (Hemp : Ψ [=] empty)
        by (eapply a_solvetag_eq_atom_empty; [ exact H0 | right; eauto ]).
      clear - Hemp; fsetdec.
    + (* arrow *)
      inversion H; subst.
      assert (Hml1 : lc_uskl (msubst_uskl ρ ψ1))
        by (apply msubst_uskl_lc; [ exact Hlcρ | apply lc_uskl_of_pskl; assumption ]).
      assert (Hml2 : lc_uskl (msubst_uskl ρ ψ2))
        by (apply msubst_uskl_lc; [ exact Hlcρ | apply lc_uskl_of_pskl; assumption ]).
      apply a_wf_pskl_tophole_inv in HwfP0.
      rewrite msubst_uskl_arrow in Hcons.
      inversion Hcons; subst.
      apply a_consistag__univ_ghost_r.
      * rewrite msubst_uskl_arrow. constructor; assumption.
      * rewrite msubst_uskl_arrow; unfold a_non_flex; simpl; split;
          [ constructor; apply lc_uskl_to_pskl_local; assumption
          | intro Hf; inversion Hf ].
      * eapply IHa_solvetag_eq;
          [ exact Hlcρ
          | simpl; rewrite msubst_uskl_arrow; eassumption
          | exact Hwf | exact HlcS | exact HwfP0 | exact HwfS
          | exact Hrig | exact Hnfd | exact Hfaf ].
  - (* SEq-FlexR : P0 = var α̂, ghost-free ψ, Ψa = ∅.  Paper (consistency-
       proofs.tex:893-915): α̂ is a monotype, so erasure removes tags that are
       not there and ρ(ψ) = ρ(erase ψ).  The subject of [Hcons] carries no
       [all_syn] (a_consistag_flexvar_subject_no_all_syn, via a_assign_sound),
       so ρ(ψ) coincides with ρ(erase ψ) (msubst_ghostfree_eq_strip); then
       psi_cong absorbs the empty Ψa. *)
    (* CRUX (paper: "α̂ is a monotype"): the subject of Hcons carries no
       [all_syn] (a_consistag_flexvar_subject_no_all_syn via a_assign_sound;
       def is mono BY well-formedness), so ρ(ψ) = ρ(erase ψ) and psi_cong
       absorbs the empty Ψa. *)
    assert (Hnas : no_all_syn_uskl
                     (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))))
      by (eapply a_consistag_flexvar_subject_no_all_syn;
            [ exact Hcons | exact Hwf | exact HwfS ]).
    assert (Heq : msubst_uskl ρ ψ
                  = msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)))
      by (apply msubst_ghostfree_eq_strip; [ exact H | exact Hnas ]).
    rewrite Heq.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H0; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §9  Ψ-congruence for decorated subtyping (prerequisite for            *)
(*  subtyping-decoration-var).  The tag context threads through every     *)
(*  a_subtag rule via [=]-premises, so it respects set equality.  The     *)
(*  flex-walk (a_subtag_flex) carries no Ψ, so a single induction on      *)
(*  a_subtag suffices; the Check case defers to a_consistag_psi_cong.     *)
(* ===================================================================== *)

Lemma a_subtag_psi_cong : forall NM M P0 Ψ Θ0 R P Θ1,
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] R ⩽˙ P ⊣ Θ1 ->
  forall Ψ', Ψ [=] Ψ' ->
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ' ] R ⩽˙ P ⊣ Θ1.
Proof.
  intros NM M P0 Ψ Θ0 R P Θ1 H; induction H; intros Ψ' Heq.
  - (* Infer *) apply a_subtag__infer; clear - H Heq; fsetdec.
  - (* Check *) eapply a_subtag__check; try assumption.
    eapply a_consistag_psi_cong; [ eassumption | exact Heq ].
  - (* ForallR *) eapply a_subtag__forall_r; try eassumption.
    match goal with
    | IH : forall Ψ0, _ |- _ => eapply IH; exact Heq
    end.
  - (* UnivGhostR *) apply a_subtag__univ_ghost_r; [ assumption | clear - H0 Heq; fsetdec ].
  - (* Arrow *) eapply a_subtag__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ eassumption | eassumption
      | match goal with Ho : _ [=] union Ψ1 Ψ2 |- _ => clear - Ho Heq; fsetdec end ].
  - (* ForallL, β1=ε : the family maps through the family IH pointwise *)
    eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
      try eassumption.
    intros Ψg ψg Hfr Hsort Hera.
    match goal with
    | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
        eapply (IHfam Ψg ψg Hfr Hsort Hera); clear - Heq; fsetdec
    end.
  - (* ForallL, β1=· *)
    eapply a_subtag__forall_l_untagged with (L := L) (Ξ := Ξ) (P1 := P1);
      try eassumption.
    intros Ψg ψg Hfr Hsort Hera.
    match goal with
    | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
        eapply (IHfam Ψg ψg Hfr Hsort Hera); clear - Heq; fsetdec
    end.
  - (* Ghost *) apply a_subtag__ghost; clear - H Heq; fsetdec.
  - (* GhostG *) apply a_subtag__ghostg; clear - H Heq; fsetdec.
  - (* UnivGhostL *) apply a_subtag__univ_ghost_l; [ assumption | ].
    match goal with IH : forall Ψ0, _ |- _ => eapply IH; exact Heq end.
  - (* UnivGhostLG *) apply a_subtag__univ_ghost_lg; [ assumption | ].
    match goal with IH : forall Ψ0, _ |- _ => eapply IH; exact Heq end.
  - (* FlexMono *) apply a_subtag__flex_mono; [ eassumption | clear - H0 Heq; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §10  Solvetag toolbox for subtyping-decoration-var                    *)
(*                                                                        *)
(*  (a) tags-origin: a solvetag run only solves tags syntactically        *)
(*      present on its subject — so tag-free subjects solve nothing;      *)
(*  (b) hole-target runs solve nothing (the paper: with input skeleton ◇  *)
(*      we can never solve tags, subtyping-proofs.tex:499-501);           *)
(*  (c) target-variable renaming and the ∀-target opening commutation —   *)
(*      the mechanized form of the paper's WLOG rule-reordering           *)
(*      (subtyping-proofs.tex:155-173) for the ForallR/ForallL overlap.   *)
(* ===================================================================== *)

Fixpoint utags_uskl (R : uskl) : atoms :=
  match R with
  | uskl_unit => empty
  | uskl_var_b _ => empty
  | uskl_var_f _ => empty
  | uskl_arrow R1 R2 => utags_uskl R1 `union` utags_uskl R2
  | uskl_all_syn R0 => utags_uskl R0
  | uskl_all_etag ε R0 => add ε (utags_uskl R0)
  | uskl_hole => empty
  | uskl_tophole R0 => utags_uskl R0
  | uskl_holeg => empty
  | uskl_topholeg R0 => utags_uskl R0
  end.

Lemma utags_open_rec : forall R' β k,
  utags_uskl (open_uskl_wrt_uskl_rec k (uskl_var_f β) R') [=] utags_uskl R'.
Proof.
  induction R'; intros β k; simpl;
    try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]); simpl;
    try rewrite IHR'1; try rewrite IHR'2; try rewrite IHR'; fsetdec.
Qed.

Lemma utags_open_var : forall R β,
  utags_uskl (open_uskl_wrt_uskl R (uskl_var_f β)) [=] utags_uskl R.
Proof. intros. apply utags_open_rec. Qed.

(** (a) Tags-origin bound. *)
Lemma a_solvetag_sub_eq_tags_bound :
  (forall ψ M P Ψ, ψ ≼ᵗ[ M ] P ⤳ Ψ -> Ψ [<=] utags_uskl ψ) /\
  (forall ψ P Ψ, ψ ∼ᵗ P ⤳ Ψ -> Ψ [<=] utags_uskl ψ).
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M P Ψ _ => Ψ [<=] utags_uskl ψ)
           (fun ψ P Ψ _ => Ψ [<=] utags_uskl ψ));
    intros; simpl;
    try solve [ clear - e; fsetdec ];
    try solve [ assumption ];
    try solve [ match goal with HΨ : _ [=] union _ _ |- _ =>
                  clear - HΨ H H0; fsetdec end ];
    try match goal with
        | H : forall β, β `notin` ?L -> _ [<=] utags_uskl _ |- _ =>
            destruct (atom_fresh L) as [β Hβ];
            pose proof (H β Hβ) as Hb;
            try rewrite (utags_open_var _ β) in Hb;
            try (clear - Hb; fsetdec)
        end.
  (* forall_inh : Ψ [=] add ε Ψ0, Ψ0 ⊆ utags(open ψ β) = utags ψ *)
  match goal with HΨ : _ [=] add _ _ |- _ => clear - HΨ Hb; fsetdec end.
Qed.

Lemma a_solvetag_sub_tags_bound : forall ψ M P Ψ,
  ψ ≼ᵗ[ M ] P ⤳ Ψ -> Ψ [<=] utags_uskl ψ.
Proof. intros; eapply (proj1 a_solvetag_sub_eq_tags_bound); eauto. Qed.

(** (b) A hole-target run solves nothing. *)
Lemma a_solvetag_sub_eq_hole_empty :
  (forall ψ M P Ψ, ψ ≼ᵗ[ M ] P ⤳ Ψ -> P = pskl_hole -> Ψ [=] empty) /\
  (forall ψ P Ψ, ψ ∼ᵗ P ⤳ Ψ -> P = pskl_hole -> Ψ [=] empty).
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M P Ψ _ => P = pskl_hole -> Ψ [=] empty)
           (fun ψ P Ψ _ => P = pskl_hole -> Ψ [=] empty));
    intros; subst; try discriminate;
    try solve [ assumption ];
    try solve [ auto ];
    try solve [ inv_guarded_hole ];
    try match goal with
        | H : forall β, β `notin` ?L -> pskl_hole = pskl_hole -> _ |- _ =>
            destruct (atom_fresh L) as [β Hβ]; exact (H β Hβ eq_refl)
        end.
Qed.

Lemma a_solvetag_sub_hole_empty : forall ψ M Ψ,
  ψ ≼ᵗ[ M ] pskl_hole ⤳ Ψ -> Ψ [=] empty.
Proof. intros; eapply (proj1 a_solvetag_sub_eq_hole_empty); eauto. Qed.

(** (c) Target-variable renaming: solvetag is insensitive to the names of
    rigid variables in the target (tags live on the subject). *)
Lemma guarded_pskl_subst_var : forall P α β,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros P α β Hg; inversion Hg; subst; simpl.
  - constructor.
  - destruct_if;
      constructor.
  - constructor; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

Lemma a_solvetag_sub_eq_target_rename :
  (forall ψ M P Ψ, ψ ≼ᵗ[ M ] P ⤳ Ψ ->
     forall α β0, ψ ≼ᵗ[ M ] (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ) /\
  (forall ψ P Ψ, ψ ∼ᵗ P ⤳ Ψ ->
     forall α β0, ψ ∼ᵗ (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ).
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M P Ψ _ =>
              forall α β0, ψ ≼ᵗ[ M ] (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ)
           (fun ψ P Ψ _ =>
              forall α β0, ψ ∼ᵗ (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ));
    intros; simpl;
    (* target-shape-preserving rules whose premises close by auto *)
    try solve [ constructor; auto ];
    (* subject-driven cofinite rules with untouched target *)
    try solve [ apply a_solvetag_sub__forall_l with (L := L);
                intros β Hβ; auto ];
    try solve [ apply a_solvetag_eq__forall_syn with (L := L);
                intros β Hβ;
                match goal with
                | IH : forall b : atom, _ |- _ =>
                    solve [ specialize (IH β Hβ α β0); simpl in IH; exact IH ]
                end ];
    (* Check: guardedness of the target survives a variable rename *)
    try solve [ apply a_solvetag_sub__check;
                [ assumption | apply guarded_pskl_subst_var; assumption
                | auto ] ];
    (* arrows *)
    try solve [ eapply a_solvetag_sub__arrow; eauto ];
    try solve [ eapply a_solvetag_eq__arrow; eauto ];
    (* FlexR: the target variable itself may be renamed *)
    try solve [ destruct_if;
                apply a_solvetag_eq__flex_r; assumption ];
    (* ∀-targets: push the rename under the target binder *)
    try solve [ apply a_solvetag_sub__forall_r
                  with (L := L `union` singleton α);
                intros β Hβ;
                rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
                  [ | clear - Hβ; fsetdec | constructor ];
                match goal with
                | IH : forall b : atom, _ |- _ =>
                    solve [ apply IH; clear - Hβ; fsetdec ]
                end ];
    try solve [ eapply a_solvetag_eq__forall_inh
                  with (L := L `union` singleton α);
                [ intros β Hβ;
                  rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
                    [ | clear - Hβ; fsetdec | constructor ];
                  match goal with
                  | IH : forall b : atom, _ |- _ =>
                      solve [ apply IH; clear - Hβ; fsetdec ]
                  end
                | eassumption ] ];
    (* UnivGhostR *)
    try solve [ apply a_solvetag_eq__univ_ghost_r; [ assumption | auto ] ].
Qed.

(** ∀-target opening: a run against [∀β.B] runs against any instance
    [B^β] with the same solved tags — pushing the subtyping side's
    ForallR under the solvetag derivation (the paper's WLOG). *)
Lemma a_solvetag_sub_all_syn_open : forall ψ P Ψ,
  ψ ≼ᵗ[ mode_tc ] (pskl_all_syn P) ⤳ Ψ ->
  forall β, ψ ≼ᵗ[ mode_tc ] (open_pskl_wrt_pskl P (pskl_var_f β)) ⤳ Ψ.
Proof.
  intros ψ P Ψ H.
  remember (pskl_all_syn P) as Q0 eqn:HQ.
  remember mode_tc as M0 eqn:HM.
  revert P HQ. induction H; intros B0 HQ β0; subst; try discriminate HQ.
  - (* SSub-Var *)
    apply a_solvetag_sub__var; assumption.
  - (* SSub-ForallL *)
    apply a_solvetag_sub__forall_l with (L := L). intros β Hβ.
    apply H0; auto.
  - (* SSub-UnivGhostLG *)
    apply a_solvetag_sub__univ_ghost_lg. apply IHa_solvetag_sub; auto.
  - (* SSub-Check : guarded (all_syn P) is absurd *)
    match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
      inversion Hg end.
  - (* SSub-ForallR : instantiate a fresh β', rename to β0 *)
    inversion HQ; subst.
    destruct (atom_fresh (L `union` ftvar_in_pskl B0 `union` singleton β0))
      as [β' Hβ'].
    pose proof (H β' ltac:(clear - Hβ'; fsetdec)) as Hinst.
    pose proof (proj1 a_solvetag_sub_eq_target_rename _ _ _ _ Hinst β' β0)
      as Hren.
    rewrite <- subst_pskl_in_pskl_intro in Hren;
      [ exact Hren | clear - Hβ'; fsetdec ].
Qed.

(** Erasures of ρ-images of a decoration and of its strip coincide. *)
Lemma uskl_to_pskl_msubst_strip : forall ρ ψ,
  ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)) ⌋ˢ = ⌊ msubst_uskl ρ ψ ⌋ˢ.
Proof.
  intros. rewrite ! uskl_to_pskl_msubst.
  rewrite uskl_to_pskl_pskl_to_uskl. reflexivity.
Qed.

(** Remaining msubst distribution laws. *)
Lemma msubst_uskl_unit : forall ρ, msubst_uskl ρ uskl_unit = uskl_unit.
Proof. induction ρ as [|[α1 g] ρ' IH]; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_hole : forall ρ, msubst_uskl ρ uskl_hole = uskl_hole.
Proof. induction ρ as [|[α1 g] ρ' IH]; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_holeg : forall ρ, msubst_uskl ρ uskl_holeg = uskl_holeg.
Proof. induction ρ as [|[α1 g] ρ' IH]; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

(* ===================================================================== *)
(*  §11  Subtyping decoration for variables                               *)
(*  (lemma:subtyping-decoration-var, subtyping-proofs.tex:176-483)        *)
(*                                                                        *)
(*  Design notes (deviations register):                                   *)
(*  - induction on the DECORATED SUBTYPING premise (not on decorated      *)
(*    constraint solving as in the paper), generalizing ψ/ρ/the solvetag  *)
(*    run: the paper's WLOG rule-reordering (tex:155-173) becomes the     *)
(*    solvetag target-opening lemma [a_solvetag_sub_all_syn_open] in the  *)
(*    ForallR case, and the subject-shape overlaps resolve by inversion.  *)
(*  - the prose mode discipline [mod_comp_sk (inh P0) M] is threaded for  *)
(*    NM = SK: without it the Ghost/UnivGhostL cases meet solvetag        *)
(*    ForallR on a ∀-headed P0 (e.g. P0 = ∀α.◇, ψ = ◈) where the          *)
(*    decorated subject has no rule — the paper's ssub-ForallR case       *)
(*    silently assumes N = TY (tex:394).  The discipline forecloses SK    *)
(*    ∀-targets at TC ([is_sskl] rejects the inherited painting of a ∀).  *)
(* ===================================================================== *)

(** Guardedness of a decorated source follows from guardedness of its
    stripped ρ-image (the head shapes coincide except at variables, where
    the two sources are the same term). *)
Lemma guarded_msubst_decorate : forall ρ ψ,
  msubst_lc ρ ->
  lc_uskl ψ ->
  guarded_uskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ->
  guarded_uskl (msubst_uskl ρ ψ).
Proof.
  intros ρ ψ Hlcρ Hlc Hg. destruct ψ; simpl in Hg |- *.
  - rewrite msubst_uskl_unit in *. exact Hg.
  - inversion Hlc.
  - exact Hg.
  - rewrite msubst_uskl_arrow in *. inversion Hlc; subst.
    constructor; apply msubst_uskl_lc; assumption.
  - rewrite msubst_uskl_all_syn in Hg. inversion Hg.
  - rewrite msubst_uskl_all_syn in Hg. inversion Hg.
  - rewrite msubst_uskl_hole in Hg. inversion Hg.
  - rewrite msubst_uskl_tophole in Hg. inversion Hg.
  - rewrite msubst_uskl_hole in Hg. inversion Hg.
  - rewrite msubst_uskl_tophole in Hg. inversion Hg.
Qed.

(** Free-variable bound for the metasubstitution. *)
Lemma msubst_uskl_ftv_upper : forall ρ R,
  ftvar_in_uskl (msubst_uskl ρ R)
  [<=] ftvar_in_uskl R `union` msubst_ftv ρ.
Proof.
  induction ρ as [ | [α1 ψg] ρ' IH ]; intros R; simpl; [ fsetdec | ].
  pose proof (ftvar_in_uskl_subst_bskl_in_uskl_upper
                (msubst_uskl ρ' R) ψg α1) as Hup.
  pose proof (IH R) as Hr. clear - Hup Hr. fsetdec.
Qed.

(** The trivial Δ-side conditions of consistency decoration at Δ = ∅. *)
Lemma rig_empty : forall Θ : aenv,
  forall α, α `in` (empty `union` empty) -> binds α abind_tvar Θ.
Proof. intros Θ α Hα. exfalso. clear - Hα. fsetdec. Qed.

Lemma no_flex_dep_empty : forall Θ, no_flex_dep (empty `union` empty) Θ.
Proof. intros Θ β τ Hb. clear. fsetdec. Qed.

Lemma faf_empty : forall Θ, flex_above_free (empty `union` empty) Θ.
Proof. intros Θ Θ1 β b Θ2 Heq Hne. clear. fsetdec. Qed.

Lemma lc_msubst_strip : forall ρ ψ,
  msubst_lc ρ -> lc_uskl ψ ->
  lc_uskl (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))).
Proof.
  intros. apply msubst_uskl_lc; [ assumption | ].
  apply pskl_to_uskl_lc. apply lc_uskl_to_pskl_local. assumption.
Qed.

(** The erasure-swap obligation of [a_subtag_vacuous_erasure]: the
    decorated ρ-image erases like anything erasure-equal to the strip's. *)
Lemma erase_swap : forall ρ (ψ : uskl) R,
  ⌊ R ⌋ˢ = ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)) ⌋ˢ ->
  ⌊ msubst_uskl ρ ψ ⌋ˢ = ⌊ R ⌋ˢ.
Proof.
  intros ρ ψ R H. rewrite H. symmetry. apply uskl_to_pskl_msubst_strip.
Qed.

Lemma a_subtag_decoration_var : forall NM M P0 Ψ Θ0 R P Θ1,
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] R ⩽˙ P ⊣ Θ1 ->
  forall ψ Ψa ρ,
    R = msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ)) ->
    ψ ≼ᵗ[ M ] P0 ⤳ Ψa ->
    msubst_lc ρ ->
    lc_uskl ψ ->
    a_wf_aenv Θ0 ->
    lc_uskl R ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ R ⌋ˢ ->
    (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
    Θ0 ⊢ᵗ[ NM | M | P0 | (Ψ `union` Ψa) ] (msubst_uskl ρ ψ) ⩽˙ P ⊣ Θ1.
Proof.
  intros NM M P0 Ψ Θ0 R P Θ1 Hsub.
  induction Hsub;
    intros ψf Ψa ρ HeqT Hst Hlcρ Hlcψ Hwf HlcT HwfP0 HwfT Hmod.
  - (* Infer : P0 = ◇ solves nothing; rebuild at the decorated subject *)
    assert (Hemp : Ψa [=] empty)
      by (eapply a_solvetag_sub_hole_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite uskl_to_pskl_msubst_strip.
    apply a_subtag__infer; assumption.
  - (* Check : dispatch on the solvetag run *)
    inversion Hst; subst; simpl in *.
    + (* solvetag Var : ψf is a variable; the two sources coincide *)
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ eapply a_subtag__check; eassumption
        | fsetdec_empty ].
    + (* solvetag ForallL : the stripped subject is ∀-headed, not guarded *)
      match goal with Hg : guarded_uskl (msubst_uskl _ _) |- _ =>
        rewrite msubst_uskl_all_syn in Hg; inversion Hg end.
    + (* solvetag UnivGhostLG : the stripped subject is ∀◇-headed *)
      match goal with Hg : guarded_uskl (msubst_uskl _ _) |- _ =>
        rewrite msubst_uskl_tophole in Hg; inversion Hg end.
    + (* solvetag Vacuous : P0 = ◇, but the Check target is guarded *)
      inv_guarded_hole.
    + (* solvetag Check : decorate the consistency premise *)
      eapply a_subtag__check.
      * apply guarded_msubst_decorate;
          [ exact Hlcρ | exact Hlcψ | assumption ].
      * assumption.
      * eapply a_consistag_decoration_var;
          [ eassumption | exact Hlcρ | eassumption
          | exact Hwf | exact HlcT | exact HwfP0 | exact HwfT
          | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ].
    + (* solvetag ForallR : the Check target is guarded, not a ∀ *)
      match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
        inversion Hg end.
  - (* ForallR : open the target; commute the solvetag run under the ∀.
       Exists-fresh (2026-07-31): the rule's own binder α serves directly. *)
    match goal with
    | Hfr : ?a `notin` union (dom (?Ξx ++ ?Θx)) _ |- _ =>
        rewrite dom_app in Hfr
    end.
    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ assumption | assumption | | ].
    { (* freshness at the ρ-decorated subject: its erasure is R's *)
      assert (Heqf : ⌊ msubst_uskl ρ ψf ⌋ˢ = ⌊ R ⌋ˢ)
        by (apply erase_swap; rewrite HeqT; reflexivity).
      pose proof (ftvar_in_pskl_uskl_to_pskl (msubst_uskl ρ ψf)) as Hf1.
      pose proof (ftvar_in_pskl_uskl_to_pskl R) as Hf2.
      rewrite Heqf in Hf1. rewrite dom_app.
      match goal with
      | Hfr : α `notin` _ |- _ => clear - Hfr Hf1 Hf2; fsetdec
      end. }
    match goal with
    | IH : forall _ : uskl, _ |- _ =>
        solve
          [ eapply IH;
            [ exact HeqT
            | apply a_solvetag_sub_all_syn_open; exact Hst
            | exact Hlcρ
            | exact Hlcψ
            | apply a_wf_aenv__tvar;
                [ match goal with
                  | Hfr : α `notin` _ |- _ => clear - Hfr; fsetdec
                  end
                | exact Hwf ]
            | exact HlcT
            | eapply a_wf_pskl_all_syn_open_tvar;
                [ exact HwfP0
                | match goal with
                  | Hfr : α `notin` _ |- _ => clear - Hfr; fsetdec
                  end ]
            | eapply a_wf_pskl_weaken;
                [ intros x b Hb; unfold binds; simpl; right; exact Hb
                | exact HwfT ]
            | intros Hsk; discriminate Hsk ] ]
    end.
  - (* UnivGhostR : P0 = ◇ solves nothing; rebuild at the decorated subject *)
    assert (Hemp : Ψa [=] empty)
      by (eapply a_solvetag_sub_hole_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite uskl_to_pskl_msubst_strip.
    apply a_subtag__univ_ghost_r;
      [ apply guarded_msubst_decorate;
          [ exact Hlcρ | exact Hlcψ | rewrite <- HeqT; assumption ]
      | assumption ].
  - (* Arrow : split the solvetag run; decorate left via consistency,
       right via the IH threaded across the mid context *)
    inversion Hst; subst.
    + (* solvetag Var : sources coincide *)
      simpl in HeqT.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | fsetdec_empty ].
      rewrite <- HeqT.
      eapply a_subtag__arrow; eassumption.
    + (* solvetag ForallL : shape clash with the arrow subject *)
      simpl in HeqT. rewrite msubst_uskl_all_syn in HeqT. discriminate HeqT.
    + (* solvetag UnivGhostLG : shape clash *)
      simpl in HeqT. rewrite msubst_uskl_tophole in HeqT. discriminate HeqT.
    + (* solvetag Arrow : the decorated pair *)
      simpl in HeqT. rewrite msubst_uskl_arrow in HeqT.
      inversion HeqT; subst. clear HeqT.
      inversion Hlcψ; subst.
      apply lc_uskl_arrow_inv in HlcT as [HlcT1 HlcT2].
      simpl in HwfT.
      apply a_wf_pskl_arrow_inv in HwfT as [HwfT1 HwfT2].
      apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b].
      rewrite msubst_uskl_arrow.
      match goal with
      | Hc1 : _ ⊢ᵗ[ _ | _ | ?P0a | ?Ψ1 ] _ ∼˙ ?Q1 ⊣ ?Θm,
        Hs2 : ?Θm ⊢ᵗ[ _ | _ | ?P0b | ?Ψ2 ] _ ⩽˙ ?Q2 ⊣ _,
        HΨ : _ [=] union ?Ψ1 ?Ψ2,
        Hst1 : _ ∼ᵗ ?P0a ⤳ ?Ψa1,
        Hst2 : _ ≼ᵗ[ _ ] ?P0b ⤳ ?Ψa2,
        HΨa : Ψa [=] union ?Ψa1 ?Ψa2 |- _ =>
          destruct (a_consistag_sound_aux Hc1 Hwf HlcT1 HwfP0a HwfT1
                      (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
            as [Hle [HwfΘm _]];
          eapply a_subtag__arrow
            with (Ψ1 := Ψ1 `union` Ψa1) (Ψ2 := Ψ2 `union` Ψa2) (Θ1 := Θm);
          [ eapply a_consistag_decoration_var;
              [ exact Hst1 | exact Hlcρ | exact Hc1 | exact Hwf | exact HlcT1
              | exact HwfP0a | exact HwfT1
              | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ]
          | match goal with
            | IH : forall ψ : uskl, _ |- _ =>
                eapply IH;
                [ reflexivity | exact Hst2 | exact Hlcρ | assumption
                | exact HwfΘm | exact HlcT2
                | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
                | eapply a_wf_pskl_isub; [ exact HwfT2 | exact Hle ]
                | intros Hsk; specialize (Hmod Hsk); simpl in Hmod;
                  inversion Hmod; subst; assumption ]
            end
          | clear - HΨ HΨa; fsetdec ]
      end.
  - (* ForallL (tagged) : the strip never produces a tagged ∀ — the source
       must be a variable, and the two sources coincide *)
    destruct ψf; simpl in HeqT;
      try rewrite msubst_uskl_unit in HeqT;
      try rewrite msubst_uskl_arrow in HeqT;
      try rewrite msubst_uskl_all_syn in HeqT;
      try rewrite msubst_uskl_hole in HeqT;
      try rewrite msubst_uskl_tophole in HeqT;
      try discriminate HeqT;
      try solve [ inversion Hlcψ ].
    (* ψf = var *)
    assert (Hemp : Ψa [=] empty).
    { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
      simpl in Hb. clear - Hb. fsetdec. }
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT.
    eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
      eassumption.
  - (* ForallL (untagged) : variable (coincide), stripped tagged ∀ (the
       ρ-extension crux), or stripped untagged ∀ (vacuous input) *)
    destruct ψf; simpl in HeqT;
      try rewrite msubst_uskl_unit in HeqT;
      try rewrite msubst_uskl_arrow in HeqT;
      try rewrite msubst_uskl_all_syn in HeqT;
      try rewrite msubst_uskl_hole in HeqT;
      try rewrite msubst_uskl_tophole in HeqT;
      try discriminate HeqT;
      try solve [ inversion Hlcψ ].
    + (* ψf = var : sources coincide *)
      assert (Hemp : Ψa [=] empty).
      { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
        simpl in Hb. clear - Hb. fsetdec. }
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | clear - Hemp; fsetdec ].
      rewrite <- HeqT.
      eapply a_subtag__forall_l_untagged with (L := L) (Ξ := Ξ) (P1 := P1);
        eassumption.
    + (* ψf = all_syn ψ' : Vacuous, or dead Check/ForallR *)
      inversion Hst; subst.
      * (* Vacuous : P0 = ◇; the run is erasure-determined *)
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_syn R) ⩽˙ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; rewrite HeqT; simpl;
            rewrite msubst_uskl_all_syn; reflexivity ].
      * (* solvetag Check : the subject is not guarded *)
        match goal with Hg : guarded_uskl _ |- _ => inversion Hg end.
      * (* solvetag ForallR : P0 = ∀ contradicts guarded-or-hole *)
        match goal with
        | Ho : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Ho as [Hg | Hd]; [ inversion Hg | discriminate Hd ]
        end.
    + (* ψf = all_etag ε' ψ' : Vacuous or the ρ-extension crux; the
         injected subject equation is substituted throughout *)
      inversion HeqT; subst; clear HeqT.
      inversion Hlcψ; subst.
      inversion Hst; subst.
      * (* ForallL : the crux.  Extend ρ with β ↦ ψg per family instance. *)
        rewrite msubst_uskl_all_etag.
        match goal with
        | Hstb : forall b : atom, b `notin` ?L1 -> _ ≼ᵗ[ _ ] _ ⤳ _ |- _ =>
            rename Hstb into Hstbody; rename L1 into Lst
        end.
        eapply a_subtag__forall_l_tagged with (L := L) (Ξ := Ξ) (P1 := P1);
          [ assumption | assumption | | assumption | assumption | ].
        { (* extract family at the decorated source: erasures coincide *)
          intros α Hα.
          replace (⌊ open_uskl_wrt_uskl (msubst_uskl ρ ψf) (uskl_var_f α) ⌋ˢ)
            with (⌊ open_uskl_wrt_uskl
                      (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)))
                      (uskl_var_f α) ⌋ˢ)
            by (rewrite ! uskl_to_pskl_open;
                rewrite uskl_to_pskl_msubst_strip; reflexivity).
          auto. }
        (* the tag family *)
        intros Ψg ψg Hfr Hsort Hera.
        assert (Hlcg : lc_uskl ψg)
          by (apply is_tskl_lc; inversion Hsort; assumption).
        destruct (atom_fresh
                    (Lst `union` dom ρ `union` msubst_ftv ρ
                     `union` ftvar_in_uskl ψf
                     `union` ftvar_in_uskl
                         (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)))
                     `union` ftvar_in_uskl (msubst_uskl ρ ψf)))
          as [β Hβ].
        assert (Hβρ : β `notin` dom ρ) by (clear - Hβ; fsetdec).
        assert (Hβf : forall α1 ψg0, binds α1 ψg0 ρ ->
                        β `notin` ftvar_in_uskl ψg0).
        { intros α1 ψg0 Hb. pose proof (msubst_ftv_binds _ _ _ Hb) as Hsc.
          clear - Hβ Hsc. fsetdec. }
        assert (Hlcρ' : msubst_lc ((β, ψg) :: ρ)).
        { intros α1 ψg0 Hb. unfold binds in Hb. simpl in Hb.
          destruct Hb as [Hb | Hb];
            [ inversion Hb; subst; exact Hlcg | eapply Hlcρ; exact Hb ]. }
        assert (Hsubject :
            msubst_uskl ((β, ψg) :: ρ)
              (pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψf (uskl_var_f β))))
            = open_uskl_wrt_uskl
                (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf))) ψg).
        { simpl. rewrite strip_open.
          rewrite (@msubst_uskl_open_comm ρ _ β Hlcρ Hβρ Hβf).
          rewrite <- subst_bskl_in_uskl_intro;
            [ reflexivity | clear - Hβ; fsetdec ]. }
        assert (Hresult :
            msubst_uskl ((β, ψg) :: ρ) (open_uskl_wrt_uskl ψf (uskl_var_f β))
            = open_uskl_wrt_uskl (msubst_uskl ρ ψf) ψg).
        { simpl.
          rewrite (@msubst_uskl_open_comm ρ ψf β Hlcρ Hβρ Hβf).
          rewrite <- subst_bskl_in_uskl_intro;
            [ reflexivity | clear - Hβ; fsetdec ]. }
        (* wf of the extended context *)
        destruct (atom_fresh L) as [α0 Hα0].
        assert (Hdecls : a_decls Ξ)
          by (eapply a_extract_decls; eauto).
        assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0)).
        { apply a_wf_aenv_prepend_decls; auto.
          - match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
              clear - Hu; solve_uniq end.
          - intros α1 Hα1.
            match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
              clear - Hu Hα1; destruct_uniq;
              unfold disjoint in *; fsetdec end. }
        assert (Hmono : forall x (b : abind),
                   binds x b Θ0 -> binds x b (Ξ ++ Θ0))
          by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
        assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
          by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
        assert (HlcSψ : lc_uskl (open_uskl_wrt_uskl
                          (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf))) ψg)).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          eapply lc_body_uskl_all_syn_1. exact HlcT. }
        assert (HwfSψ : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                  ⌊ open_uskl_wrt_uskl
                      (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf))) ψg ⌋ˢ).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)) ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψf)) ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall α, α `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros α Hα;
                  eapply a_wf_pskl_weaken;
                    [ exact Hmono | apply Hbody; auto ]
                | assumption ]
          end. }
        (* the family IH at (Ψg,ψg), source (ψf^β), substitution ρ[β↦ψg];
           then re-express the subject and fix the tag algebra *)
        rewrite <- Hresult.
        eapply a_subtag_psi_cong;
          [ eapply (H5 Ψg ψg Hfr Hsort Hera
                      (open_uskl_wrt_uskl ψf (uskl_var_f β)) Ψa
                      ((β, ψg) :: ρ))
          | clear; fsetdec ].
        all: try solve [ rewrite Hsubject; reflexivity ].
        all: try solve [ apply Hstbody; clear - Hβ; fsetdec ].
        all: try solve [ exact Hlcρ' ].
        all: try solve [ apply lc_body_uskl_wrt_uskl;
                         [ eapply lc_body_uskl_all_etag_2; eassumption
                         | constructor ] ].
        all: try solve [ exact HwfΞΘ ].
        all: try solve [ exact HlcSψ ].
        all: try solve [ exact HwfP0' ].
        all: try solve [ exact HwfSψ ].
        all: solve [ exact Hmod ].
      * (* Vacuous : P0 = ◇; erasure-determined *)
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_syn
                             (msubst_uskl ρ (pskl_to_uskl ⌊ ψf ⌋ˢ))) ⩽˙ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; simpl;
            rewrite msubst_uskl_all_syn; reflexivity ].
      * (* solvetag Check : the subject is not guarded *)
        match goal with Hg : guarded_uskl _ |- _ => inversion Hg end.
      * (* solvetag ForallR : P0 = ∀ contradicts guarded-or-hole *)
        match goal with
        | Ho : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Ho as [Hg | Hd]; [ inversion Hg | discriminate Hd ]
        end.
  - (* Ghost : source ◇; the strip is ◇ or the source is a variable or ◈ *)
    destruct ψf; simpl in HeqT;
      try rewrite msubst_uskl_unit in HeqT;
      try rewrite msubst_uskl_arrow in HeqT;
      try rewrite msubst_uskl_all_syn in HeqT;
      try rewrite msubst_uskl_hole in HeqT;
      try rewrite msubst_uskl_tophole in HeqT;
      try discriminate HeqT;
      try solve [ inversion Hlcψ ].
    + (* ψf = var : sources coincide *)
      assert (Hemp : Ψa [=] empty).
      { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
        simpl in Hb. clear - Hb. fsetdec. }
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | clear - Hemp; fsetdec ].
      rewrite <- HeqT. apply a_subtag__ghost; assumption.
    + (* ψf = ◇ : identical *)
      assert (Hemp : Ψa [=] empty).
      { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
        simpl in Hb. clear - Hb. fsetdec. }
      rewrite msubst_uskl_hole.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghost; assumption | clear - Hemp; fsetdec ].
    + (* ψf = ◈ : the solvetag run pins P0 (Vacuous), or a ∀-target dies
         by the SK mode discipline *)
      inversion Hst; subst.
      * (* Vacuous : P0 = ◇ — GhostG replays the node *)
        rewrite msubst_uskl_holeg.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__ghostg; assumption
          | fsetdec_empty ].
      * (* solvetag Check : ◈ is not guarded *)
        match goal with Hg : guarded_uskl uskl_holeg |- _ =>
          inversion Hg end.
      * (* ForallR : SK ∀-target at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with Hs : is_sskl (bskl_all_inh _) |- _ =>
          inversion Hs end.
  - (* GhostG : the strip never produces ◈ — the source is a variable *)
    destruct ψf; simpl in HeqT;
      try rewrite msubst_uskl_unit in HeqT;
      try rewrite msubst_uskl_arrow in HeqT;
      try rewrite msubst_uskl_all_syn in HeqT;
      try rewrite msubst_uskl_hole in HeqT;
      try rewrite msubst_uskl_tophole in HeqT;
      try discriminate HeqT;
      try solve [ inversion Hlcψ ].
    assert (Hemp : Ψa [=] empty).
    { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
      simpl in Hb. clear - Hb. fsetdec. }
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT. apply a_subtag__ghostg; assumption.
  - (* UnivGhostL : variable, ∀◇ (vacuous input), or ∀◈ (the mirror) *)
    destruct ψf; simpl in HeqT;
      try rewrite msubst_uskl_unit in HeqT;
      try rewrite msubst_uskl_arrow in HeqT;
      try rewrite msubst_uskl_all_syn in HeqT;
      try rewrite msubst_uskl_hole in HeqT;
      try rewrite msubst_uskl_tophole in HeqT;
      try discriminate HeqT;
      try solve [ inversion Hlcψ ].
    + (* ψf = var : sources coincide *)
      assert (Hemp : Ψa [=] empty).
      { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
        simpl in Hb. clear - Hb. fsetdec. }
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ | clear - Hemp; fsetdec ].
      rewrite <- HeqT. apply a_subtag__univ_ghost_l; assumption.
    + (* ψf = ∀◇.ψ' : Vacuous (P0 = ◇) or a ∀-target (mode discipline) *)
      inversion HeqT; subst; clear HeqT.
      inversion Hlcψ; subst.
      inversion Hst; subst.
      * (* Vacuous : erasure-determined *)
        assert (Hnode : Θ0 ⊢ᵗ[ a_sub_mode_sk | M | pskl_hole | Ψ ]
                          (uskl_tophole
                             (msubst_uskl ρ (pskl_to_uskl ⌊ ψf ⌋ˢ))) ⩽˙ Q ⊣ Θ1)
          by (apply a_subtag__univ_ghost_l; assumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; simpl;
            rewrite msubst_uskl_tophole; reflexivity ].
      * (* solvetag Check : a ∀◇-headed subject is not guarded *)
        match goal with Hg : guarded_uskl (uskl_tophole _) |- _ =>
          inversion Hg end.
      * (* ForallR : SK ∀-target at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with Hs : is_sskl (bskl_all_inh _) |- _ =>
          inversion Hs end.
    + (* ψf = ∀◈.ψ' : the mirror (UnivGhostLG), Vacuous, or mode-killed ∀ *)
      inversion HeqT; subst; clear HeqT.
      inversion Hlcψ; subst.
      inversion Hst; subst.
      * (* UnivGhostLG mirror : recurse *)
        rewrite msubst_uskl_topholeg.
        apply a_subtag__univ_ghost_lg; [ assumption | ].
        match goal with
        | IH : forall ψ : uskl, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hlcρ | assumption
              | exact Hwf
              | apply lc_uskl_tophole_inv; exact HlcT
              | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_tophole_inv in HwfT;
                exact HwfT
              | exact Hmod ]
        end.
      * (* Vacuous : erasure-determined *)
        assert (Hnode : Θ0 ⊢ᵗ[ a_sub_mode_sk | M | pskl_hole | Ψ ]
                          (uskl_tophole
                             (msubst_uskl ρ (pskl_to_uskl ⌊ ψf ⌋ˢ))) ⩽˙ Q ⊣ Θ1)
          by (apply a_subtag__univ_ghost_l; assumption).
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply msubst_uskl_lc; assumption
          | apply erase_swap; simpl;
            rewrite msubst_uskl_tophole; reflexivity ].
      * (* solvetag Check : a ∀◇-headed subject is not guarded *)
        match goal with Hg : guarded_uskl (uskl_topholeg _) |- _ =>
          inversion Hg end.
      * (* ForallR : mode-killed *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with Hs : is_sskl (bskl_all_inh _) |- _ =>
          inversion Hs end.
  - (* UnivGhostLG : the strip never produces ∀◈ — the source is a variable *)
    destruct ψf; simpl in HeqT;
      try rewrite msubst_uskl_unit in HeqT;
      try rewrite msubst_uskl_arrow in HeqT;
      try rewrite msubst_uskl_all_syn in HeqT;
      try rewrite msubst_uskl_hole in HeqT;
      try rewrite msubst_uskl_tophole in HeqT;
      try discriminate HeqT;
      try solve [ inversion Hlcψ ].
    assert (Hemp : Ψa [=] empty).
    { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
      simpl in Hb. clear - Hb. fsetdec. }
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT. apply a_subtag__univ_ghost_lg; assumption.
  - (* FlexMono : the source is a variable *)
    destruct ψf; simpl in HeqT;
      try rewrite msubst_uskl_unit in HeqT;
      try rewrite msubst_uskl_arrow in HeqT;
      try rewrite msubst_uskl_all_syn in HeqT;
      try rewrite msubst_uskl_hole in HeqT;
      try rewrite msubst_uskl_tophole in HeqT;
      try discriminate HeqT;
      try solve [ inversion Hlcψ ].
    assert (Hemp : Ψa [=] empty).
    { pose proof (a_solvetag_sub_tags_bound Hst) as Hb.
      simpl in Hb. clear - Hb. fsetdec. }
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite <- HeqT. apply a_subtag__flex_mono; assumption.
Qed.

(* ===================================================================== *)
(*  §12  Consistency decoration (lemma:consistency-decoration,            *)
(*  consistency-proofs.tex:88-600) — the subst-level layer: a decorated   *)
(*  consistency run on R[⌊ψa⌋/α] replays on R[ψa/α], additionally         *)
(*  solving ψa's tags Ψa as computed by the solvetag run on the           *)
(*  constraints collected at α's occurrences.                             *)
(* ===================================================================== *)

(** A ghost-free, quantifier-free decoration is its own strip. *)
Lemma strip_id_ghost_free_no_all_syn : forall ψ,
  uskl_ghost_free ψ ->
  no_all_syn_uskl (pskl_to_uskl (uskl_to_pskl ψ)) ->
  pskl_to_uskl (uskl_to_pskl ψ) = ψ.
Proof.
  intros ψ Hgf; induction Hgf; intros Hnas; simpl in *.
  - reflexivity.
  - reflexivity.
  - inversion Hnas; subst. rewrite IHHgf1, IHHgf2; auto.
  - inversion Hnas.
  - inversion Hnas.
Qed.

(** [no_all_syn] descends to a substituted-in subterm at an occurring
    variable. *)
Lemma no_all_syn_subst_inv : forall R' R0 β,
  β `in` ftvar_in_uskl R' ->
  no_all_syn_uskl (subst_bskl_in_uskl R0 β R') ->
  no_all_syn_uskl R0.
Proof.
  induction R'; intros R0 β Hin Hnas; simpl in *;
    try solve [ exfalso; fsetdec ];
    try solve [ inversion Hnas ].
  - (* var_f *)
    revert Hnas.
    destruct_if as [-> | Hne]; intro Hnas; [ exact Hnas | exfalso; fsetdec ].
  - (* arrow *)
    inversion Hnas; subst.
    destruct (union_1 Hin);
      [ eapply IHR'1 | eapply IHR'2 ]; eauto.
  - (* tophole *)
    inversion Hnas; subst. eapply IHR'; eauto.
  - (* topholeg *)
    inversion Hnas; subst. eapply IHR'; eauto.
Qed.

(** Constraints collected against a flexible-variable input solve nothing,
    and the decoration coincides with its strip on the substituted subject:
    the solvetag run pins ψa to a variable or a ghost-free skeleton, and
    the (monotype) assigned subject is quantifier-free. *)
Lemma flexvar_decoration_swap : forall α P α0 Ξ 𝒞,
  P ∼[ α ] (pskl_var_f α0) ⤳ Ξ ⨾ 𝒞 ->
  forall R ψa Ψa,
    ⌊ R ⌋ˢ = P ->
    𝒞 ⊩ᵗ ψa ⤳ Ψa ->
    no_all_syn_uskl
      (subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R) ->
    Ψa [=] empty /\
    subst_bskl_in_uskl ψa α R
    = subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R.
Proof.
  intros α P α0 Ξ 𝒞 Hlk.
  remember (pskl_var_f α0) as Ptgt eqn:HPt.
  induction Hlk; intros R0 ψa Ψa HeS Hst Hnas; try discriminate HPt.
  - (* LE-Var : R0 = α; the single eq constraint pins ψa *)
    assert (HR : R0 = uskl_var_f α).
    { destruct R0; simpl in HeS; try discriminate; congruence. }
    subst R0. simpl in Hnas |- *.
    revert Hnas.
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    intro Hnas.
    inversion Hst; subst.
    match goal with
    | Hone : ψa ∼ᵗ _ ⤳ _ |- _ => inversion Hone; subst
    end.
    all: match goal with
         | Hnil : nil ⊩ᵗ _ ⤳ _ |- _ => inversion Hnil; subst
         end.
    all: split.
    all: try solve [ match goal with
                     | He1 : ?A0 [=] empty, He2 : ?B0 [=] empty,
                       HU : _ [=] union ?A0 ?B0 |- _ =>
                         clear - He1 He2 HU; fsetdec
                     end ].
    all: try solve [ simpl; reflexivity ].
    all: match goal with
         | Hgf : uskl_ghost_free _ |- _ =>
             rewrite (strip_id_ghost_free_no_all_syn Hgf Hnas); reflexivity
         end.
  - (* LE-Absent : both substitutions are the identity *)
    assert (HαR : α `notin` ftvar_in_uskl R0).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). rewrite HeS. assumption. }
    inversion Hst; subst.
    split; [ assumption | ].
    rewrite ! subst_bskl_in_uskl_fresh_eq; auto.
  - (* LE-FlexR : the eq constraint on the fresh flexible pins ψa *)
    assert (HαR : α `in` ftvar_in_uskl R0).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). rewrite HeS. assumption. }
    inversion Hst; subst.
    match goal with
    | Hone : ψa ∼ᵗ _ ⤳ _ |- _ => inversion Hone; subst
    end.
    all: match goal with
         | Hnil : nil ⊩ᵗ _ ⤳ _ |- _ => inversion Hnil; subst
         end.
    all: split.
    all: try solve [ match goal with
                     | He1 : ?A0 [=] empty, He2 : ?B0 [=] empty,
                       HU : _ [=] union ?A0 ?B0 |- _ =>
                         clear - He1 He2 HU; fsetdec
                     end ].
    all: try solve [ simpl; reflexivity ].
    all: pose proof (@no_all_syn_subst_inv R0
                       (pskl_to_uskl (uskl_to_pskl ψa)) α HαR Hnas) as Hnas'.
    all: match goal with
         | Hgf : uskl_ghost_free _ |- _ =>
             pose proof (strip_id_ghost_free_no_all_syn Hgf Hnas') as Hid
         end.
    all: rewrite Hid; reflexivity.
  - (* LE-UnivGhost2 : peel the source ∀◇/∀◈ and recurse *)
    destruct R0; simpl in HeS; try discriminate HeS;
      inversion HeS; subst.
    + (* tophole *)
      simpl in Hnas. inversion Hnas; subst.
      match goal with
      | Hin : no_all_syn_uskl (subst_bskl_in_uskl _ _ ?R1) |- _ =>
          destruct (IHHlk eq_refl R1 ψa Ψa ltac:(reflexivity) Hst Hin)
            as [HΨ Heq]
      end.
      split; [ exact HΨ | simpl; rewrite Heq; reflexivity ].
    + (* topholeg *)
      simpl in Hnas. inversion Hnas; subst.
      match goal with
      | Hin : no_all_syn_uskl (subst_bskl_in_uskl _ _ ?R1) |- _ =>
          destruct (IHHlk eq_refl R1 ψa Ψa ltac:(reflexivity) Hst Hin)
            as [HΨ Heq]
      end.
      split; [ exact HΨ | simpl; rewrite Heq; reflexivity ].
Qed.

Lemma a_consistag_decoration : forall α P P0 Ξc 𝒞,
  P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 ->
  forall R' ψa Ψa Δ1 Δ2 Ψ Θ0 P' Θ1,
    𝒞 ⊩ᵗ ψa ⤳ Ψa ->
    ⌊ R' ⌋ˢ = P ->
    α `notin` ftvar_in_uskl ψa ->
    lc_uskl ψa ->
    lc_uskl R' ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ]
      (subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R') ∼˙ P' ⊣ Θ1 ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty
      ⊢ₚₛᵃ ⌊ subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R' ⌋ˢ ->
    (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | (Ψ `union` Ψa) ]
      (subst_bskl_in_uskl ψa α R') ∼˙ P' ⊣ Θ1.
Proof.
  intros α P P0 Ξc 𝒞 Hlook; induction Hlook;
    intros R ψa Ψa Δ1 Δ2 Ψc Θ0 Qc Θ1
      Hst HeS Hαψ Hlcψ HlcS Hcons Hwf HwfP0 HwfSub Hrig Hnfd Hfaf.
  - (* LE-Var : R = α; the decoration-var lemma at ρ = nil *)
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    simpl in Hcons, HwfSub |- *.
    revert Hcons HwfSub.
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    intros Hcons HwfSub.
    inversion Hst; subst.
    match goal with
    | Hone : ψa ∼ᵗ P ⤳ ?Ψ1x, Hnil : nil ⊩ᵗ ψa ⤳ ?Ψ2x,
      HΨs : Ψa [=] union ?Ψ1x ?Ψ2x |- _ =>
        inversion Hnil; subst;
        eapply a_consistag_psi_cong with (Ψ := Ψc `union` Ψ1x);
        [ | match goal with He2 : ?Ψ2x [=] empty |- _ =>
              clear - HΨs He2; fsetdec end ]
    end.
    change ψa with (msubst_uskl nil ψa).
    eapply a_consistag_decoration_var;
      [ eassumption
      | intros α1 g Hb; inversion Hb
      | simpl; exact Hcons
      | exact Hwf
      | simpl;
        apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
      | exact HwfP0
      | simpl; exact HwfSub
      | exact Hrig | exact Hnfd | exact Hfaf ].
  - (* LE-Absent : α does not occur — both substitutions are the identity *)
    assert (HαR : α `notin` ftvar_in_uskl R).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl R). rewrite HeS. assumption. }
    rewrite subst_bskl_in_uskl_fresh_eq in Hcons; [ | exact HαR ].
    rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαR ].
    inversion Hst; subst.
    eapply a_consistag_psi_cong; [ exact Hcons | ].
    fsetdec_empty.
  - (* LE-Vacuous : P0 = ◇; the run is erasure-determined *)
    inversion Hst; subst.
    eapply a_consistag_psi_cong with (Ψ := Ψc);
      [ | fsetdec_empty ].
    eapply a_consistag_vacuous_erasure;
      [ exact Hcons | reflexivity
      | rewrite ! uskl_to_pskl_subst;
        rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
  - (* LE-FlexR : the input is a flexible variable; ψa is ghost-free and
       the assigned subject is quantifier-free, so ψa is its own strip *)
    inversion Hst; subst.
    match goal with
    | Hone : ψa ∼ᵗ _ ⤳ ?Ψ1x, Hnil : nil ⊩ᵗ ψa ⤳ ?Ψ2x,
      HΨs : Ψa [=] union ?Ψ1x ?Ψ2x |- _ =>
        inversion Hnil; subst;
        inversion Hone; subst
    end.
    + (* solvetag Var : ψa is a variable — its strip is itself *)
      simpl in Hcons |- *.
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      match goal with
      | He1 : ?A [=] empty, He2 : ?B [=] empty, HΨs : Ψa [=] union ?A ?B |- _ =>
          clear - He1 He2 HΨs; fsetdec
      end.
    + (* solvetag FlexR : ψa ghost-free; the subject is quantifier-free *)
      assert (Hnas : no_all_syn_uskl
                       (subst_bskl_in_uskl
                          (pskl_to_uskl (uskl_to_pskl ψa)) α R)).
      { eapply a_consistag_flexvar_subject_no_all_syn;
          [ exact Hcons | exact Hwf | exact HwfSub ]. }
      assert (Hid : pskl_to_uskl (uskl_to_pskl ψa) = ψa).
      { apply strip_id_ghost_free_no_all_syn; [ assumption | ].
        eapply no_all_syn_subst_inv; [ | exact Hnas ].
        rewrite <- (ftvar_in_pskl_uskl_to_pskl R).
        assumption. }
      rewrite Hid in Hcons.
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      match goal with
      | He1 : ?A [=] empty, He2 : ?B [=] empty, HΨs : Ψa [=] union ?A ?B |- _ =>
          clear - He1 He2 HΨs; fsetdec
      end.
  - (* LE-Arrow : split the solvetag run; the premise is an Arrow node *)
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    simpl in Hcons |- *.
    inversion HlcS; subst.
    destruct (a_solvetag_split _ _ Hst) as [Ψa1 [Ψa2 [Hst1 [Hst2 HΨs]]]].
    simpl in HwfSub.
    apply a_wf_pskl_arrow_inv in HwfSub as [HwfSub1 HwfSub2].
    inversion Hcons; subst.
    match goal with
    | Hc1 : _ ⊢ᵗ[ _ | _ | ?P0a | ?Ψ1 ] _ ∼˙ _ ⊣ ?Θm,
      Hc2 : ?Θm ⊢ᵗ[ _ | _ | ?P0b | ?Ψ2 ] _ ∼˙ _ ⊣ _,
      HΨc : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
        apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b];
        destruct (a_consistag_sound_aux Hc1 Hwf
                    ltac:(apply subst_bskl_in_uskl_lc_uskl;
                          [ assumption
                          | apply pskl_to_uskl_lc;
                            apply lc_uskl_to_pskl_local; assumption ])
                    HwfP0a HwfSub1 Hrig Hnfd Hfaf)
          as [Hle [HwfΘm [HnfdΘm [HfafΘm _]]]];
        eapply a_consistag__arrow
          with (Ψ1 := Ψ1 `union` Ψa1) (Ψ2 := Ψ2 `union` Ψa2) (Θ1 := Θm);
        [ eapply IHHlook1;
          [ exact Hst1 | reflexivity | exact Hαψ | exact Hlcψ | assumption
          | exact Hc1 | exact Hwf | exact HwfP0a | exact HwfSub1
          | exact Hrig | exact Hnfd | exact Hfaf ]
        | eapply IHHlook2;
          [ exact Hst2 | reflexivity | exact Hαψ | exact Hlcψ | assumption
          | exact Hc2 | exact HwfΘm
          | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
          | eapply a_wf_pskl_isub; [ exact HwfSub2 | exact Hle ]
          | intros α0 Hα0; eapply a_isub_binds_tvar;
              [ exact Hle | apply Hrig; exact Hα0 ]
          | exact HnfdΘm | exact HfafΘm ]
        | match goal with HΨc2 : _ [=] union _ _ |- _ =>
            clear - HΨc HΨs; fsetdec end ]
    end.
  - (* LE-ForallInh : ∀-headed sources; open a fresh rigid on both sides *)
    assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
      by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ).
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    + (* R = all_syn R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion HwfP0 as [ | | | LP ΘP ΔP P0b HbodyP HeqP' | | ]; subst.
      inversion Hcons; subst.
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      eapply a_consistag__forall_inh_untagged
        with (L := L `union` Lc `union` LS `union` LP
                   `union` singleton α `union` ftvar_in_uskl ψa
                   `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                   `union` dom Θ0).
      intros β Hβ.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | clear - Hβ; fsetdec | exact Hlcψ ].
      pose proof (Hcbody β ltac:(clear - Hβ; fsetdec)) as HcI.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var in HcI;
        [ | clear - Hβ; fsetdec | exact Hlcstrip ].
      match goal with
      | IH : forall b : atom, _ |- _ =>
          solve
            [ eapply (IH β ltac:(clear - Hβ; fsetdec));
              [ exact Hst
              | apply uskl_to_pskl_open
              | exact Hαψ
              | exact Hlcψ
              | apply HlcSbody
              | exact HcI
              | apply a_wf_aenv__tvar;
                  [ clear - Hβ; fsetdec | exact Hwf ]
              | eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc
                             (HbodyP β ltac:(clear - Hβ; fsetdec)) β)
                  | clear; fsetdec ]
              | rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
                  [ | clear - Hβ; fsetdec | exact Hlcstrip ];
                rewrite uskl_to_pskl_open;
                eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc
                             (HbodyS β ltac:(clear - Hβ; fsetdec)) β)
                  | clear; fsetdec ]
              | intros α0 Hα0; destruct (α0 == β) as [ -> | Hne ];
                  [ unfold binds; left; reflexivity
                  | unfold binds; right; apply Hrig;
                    clear - Hα0 Hne; fsetdec ]
              | apply no_flex_dep_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply no_flex_dep_open_tvar;
                      [ exact Hwf | exact Hnfd | clear - Hβ; fsetdec ] ]
              | apply faf_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply faf_open_tvar;
                      [ exact Hfaf | clear - Hβ; fsetdec ] ] ] ]
      end.
    + (* R = all_etag ε R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion HwfP0 as [ | | | LP ΘP ΔP P0b HbodyP HeqP' | | ]; subst.
      inversion Hcons; subst.
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      match goal with
      | HΨe : Ψc [=] add ?εx ?Ψ0x |- _ => rename HΨe into HΨc
      end.
      eapply a_consistag__forall_inh_tagged
        with (Ψ0 := Ψ0 `union` Ψa)
             (L := L `union` Lc `union` LS `union` LP
                   `union` singleton α `union` ftvar_in_uskl ψa
                   `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                   `union` dom Θ0);
        [ intros β Hβ | clear - HΨc; fsetdec ].
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | clear - Hβ; fsetdec | exact Hlcψ ].
      pose proof (Hcbody β ltac:(clear - Hβ; fsetdec)) as HcI.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var in HcI;
        [ | clear - Hβ; fsetdec | exact Hlcstrip ].
      match goal with
      | IH : forall b : atom, _ |- _ =>
          solve
            [ eapply (IH β ltac:(clear - Hβ; fsetdec));
              [ exact Hst
              | apply uskl_to_pskl_open
              | exact Hαψ
              | exact Hlcψ
              | apply HlcSbody
              | exact HcI
              | apply a_wf_aenv__tvar;
                  [ clear - Hβ; fsetdec | exact Hwf ]
              | eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc
                             (HbodyP β ltac:(clear - Hβ; fsetdec)) β)
                  | clear; fsetdec ]
              | rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
                  [ | clear - Hβ; fsetdec | exact Hlcstrip ];
                rewrite uskl_to_pskl_open;
                eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc
                             (HbodyS β ltac:(clear - Hβ; fsetdec)) β)
                  | clear; fsetdec ]
              | intros α0 Hα0; destruct (α0 == β) as [ -> | Hne ];
                  [ unfold binds; left; reflexivity
                  | unfold binds; right; apply Hrig;
                    clear - Hα0 Hne; fsetdec ]
              | apply no_flex_dep_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply no_flex_dep_open_tvar;
                      [ exact Hwf | exact Hnfd | clear - Hβ; fsetdec ] ]
              | apply faf_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply faf_open_tvar;
                      [ exact Hfaf | clear - Hβ; fsetdec ] ] ] ]
      end.
  - (* LE-ForallSyn : ∀-headed source, ∀◇ input (unchanged across opening) *)
    assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
      by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ).
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    + (* R = all_syn R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion Hcons; subst;
        try (match goal with Hg : guarded_uskl (uskl_all_syn _) |- _ =>
               solve [ inversion Hg ] end);
        try (match goal with Hg : guarded_uskl (uskl_all_etag _ _) |- _ =>
               solve [ inversion Hg ] end).
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      eapply a_consistag__forall_syn_untagged
        with (L := L `union` Lc `union` LS
                   `union` singleton α `union` ftvar_in_uskl ψa
                   `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                   `union` dom Θ0).
      intros β Hβ.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | clear - Hβ; fsetdec | exact Hlcψ ].
      pose proof (Hcbody β ltac:(clear - Hβ; fsetdec)) as HcI.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var in HcI;
        [ | clear - Hβ; fsetdec | exact Hlcstrip ].
      match goal with
      | IH : forall b : atom, _ |- _ =>
          solve
            [ eapply (IH β ltac:(clear - Hβ; fsetdec));
              [ exact Hst
              | apply uskl_to_pskl_open
              | exact Hαψ
              | exact Hlcψ
              | apply HlcSbody
              | exact HcI
              | apply a_wf_aenv__tvar;
                  [ clear - Hβ; fsetdec | exact Hwf ]
              | eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc HwfP0 β) | clear; fsetdec ]
              | rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
                  [ | clear - Hβ; fsetdec | exact Hlcstrip ];
                rewrite uskl_to_pskl_open;
                eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc
                             (HbodyS β ltac:(clear - Hβ; fsetdec)) β)
                  | clear; fsetdec ]
              | intros α0 Hα0; destruct (α0 == β) as [ -> | Hne ];
                  [ unfold binds; left; reflexivity
                  | unfold binds; right; apply Hrig;
                    clear - Hα0 Hne; fsetdec ]
              | apply no_flex_dep_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply no_flex_dep_open_tvar;
                      [ exact Hwf | exact Hnfd | clear - Hβ; fsetdec ] ]
              | apply faf_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply faf_open_tvar;
                      [ exact Hfaf | clear - Hβ; fsetdec ] ] ] ]
      end.
    + (* R = all_etag ε R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      match goal with
      | Hb : forall α0 : usklvar, lc_uskl _ |- _ => rename Hb into HlcSbody
      end.
      simpl in HwfSub.
      inversion HwfSub as [ | | | LS ΘR ΔR SbS HbodyS HeqS' | | ]; subst.
      inversion Hcons; subst;
        try (match goal with Hg : guarded_uskl (uskl_all_etag _ _) |- _ =>
               solve [ inversion Hg ] end).
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      eapply a_consistag__forall_syn_tagged
        with (L := L `union` Lc `union` LS
                   `union` singleton α `union` ftvar_in_uskl ψa
                   `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                   `union` dom Θ0).
      intros β Hβ.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ | clear - Hβ; fsetdec | exact Hlcψ ].
      pose proof (Hcbody β ltac:(clear - Hβ; fsetdec)) as HcI.
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var in HcI;
        [ | clear - Hβ; fsetdec | exact Hlcstrip ].
      match goal with
      | IH : forall b : atom, _ |- _ =>
          solve
            [ eapply (IH β ltac:(clear - Hβ; fsetdec));
              [ exact Hst
              | apply uskl_to_pskl_open
              | exact Hαψ
              | exact Hlcψ
              | apply HlcSbody
              | exact HcI
              | apply a_wf_aenv__tvar;
                  [ clear - Hβ; fsetdec | exact Hwf ]
              | eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc HwfP0 β) | clear; fsetdec ]
              | rewrite <- subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
                  [ | clear - Hβ; fsetdec | exact Hlcstrip ];
                rewrite uskl_to_pskl_open;
                eapply a_wf_pskl_delta_mono;
                  [ apply (a_wf_pskl_reassoc
                             (HbodyS β ltac:(clear - Hβ; fsetdec)) β)
                  | clear; fsetdec ]
              | intros α0 Hα0; destruct (α0 == β) as [ -> | Hne ];
                  [ unfold binds; left; reflexivity
                  | unfold binds; right; apply Hrig;
                    clear - Hα0 Hne; fsetdec ]
              | apply no_flex_dep_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply no_flex_dep_open_tvar;
                      [ exact Hwf | exact Hnfd | clear - Hβ; fsetdec ] ]
              | apply faf_cong with (Δ := add β (Δ1 `union` Δ2));
                  [ clear; fsetdec
                  | apply faf_open_tvar;
                      [ exact Hfaf | clear - Hβ; fsetdec ] ] ] ]
      end.
  - (* LE-UnivGhost : ∀◇-headed source and input; peel both *)
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    + (* R = tophole R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      apply a_wf_pskl_tophole_inv in HwfSub.
      apply a_wf_pskl_tophole_inv in HwfP0.
      inversion Hcons; subst;
        try (match goal with Hg : guarded_pskl (pskl_tophole _) |- _ =>
               solve [ inversion Hg ] end);
        try (match goal with Hg : guarded_uskl (uskl_tophole _) |- _ =>
               solve [ inversion Hg ] end).
      apply a_consistag__univ_ghost.
      match goal with
      | IH : forall R0 : uskl, _ |- _ =>
          eapply IH;
            [ exact Hst | reflexivity | exact Hαψ | exact Hlcψ | assumption
            | eassumption | exact Hwf | exact HwfP0 | exact HwfSub
            | exact Hrig | exact Hnfd | exact Hfaf ]
      end.
    + (* R = topholeg R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      apply a_wf_pskl_tophole_inv in HwfSub.
      apply a_wf_pskl_tophole_inv in HwfP0.
      inversion Hcons; subst;
        try (match goal with
             | Hg : guarded_uskl (uskl_topholeg _) |- _ =>
                 solve [ inversion Hg ] end).
      apply a_consistag__univ_ghostg.
      match goal with
      | IH : forall R0 : uskl, _ |- _ =>
          eapply IH;
            [ exact Hst | reflexivity | exact Hαψ | exact Hlcψ | assumption
            | eassumption | exact Hwf | exact HwfP0 | exact HwfSub
            | exact Hrig | exact Hnfd | exact Hfaf ]
      end.
  - (* LE-UnivGhost1 : ∀◇-headed source fixed, ∀-input opens *)
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    + (* R = tophole R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      inversion HwfP0 as [ | | | LP ΘP ΔP P0b HbodyP HeqP' | | ]; subst.
      inversion Hcons; subst;
        try (match goal with Hg : guarded_uskl (uskl_tophole _) |- _ =>
               solve [ inversion Hg ] end);
        try (match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
               solve [ inversion Hg ] end).
      match goal with
      | Hcb : forall a, a `notin` ?L1 -> _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
          rename Hcb into Hcbody; rename L1 into Lc
      end.
      eapply a_consistag__univ_ghost1
        with (L := L `union` Lc `union` LP
                   `union` singleton α `union` ftvar_in_uskl ψa
                   `union` ftvar_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                   `union` dom Θ0).
      intros β Hβ.
      pose proof (Hcbody β ltac:(clear - Hβ; fsetdec)) as HcI.
      change (uskl_tophole (subst_bskl_in_uskl ψa α R))
        with (subst_bskl_in_uskl ψa α (uskl_tophole R)).
      eapply (H0 β ltac:(clear - Hβ; fsetdec)).
      { exact Hst. }
      { reflexivity. }
      { exact Hαψ. }
      { exact Hlcψ. }
      { assumption. }
      { exact HcI. }
      { apply a_wf_aenv__tvar; [ clear - Hβ; fsetdec | exact Hwf ]. }
      { eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc
                     (HbodyP β ltac:(clear - Hβ; fsetdec)) β)
          | clear; fsetdec ]. }
      { eapply a_wf_pskl_weaken;
          [ intros x b Hb; unfold binds; simpl; right; exact Hb
          | exact HwfSub ]. }
      { intros α0 Hα0; destruct (α0 == β) as [ -> | Hne ];
          [ unfold binds; left; reflexivity
          | unfold binds; right; apply Hrig;
            clear - Hα0 Hne; fsetdec ]. }
      { apply no_flex_dep_cong with (Δ := add β (Δ1 `union` Δ2));
          [ clear; fsetdec
          | apply no_flex_dep_open_tvar;
              [ exact Hwf | exact Hnfd | clear - Hβ; fsetdec ] ]. }
      { apply faf_cong with (Δ := add β (Δ1 `union` Δ2));
          [ clear; fsetdec
          | apply faf_open_tvar;
              [ exact Hfaf | clear - Hβ; fsetdec ] ]. }
    + (* R = topholeg R' : no rule pairs ∀◈ with a ∀ input *)
      simpl in Hcons.
      inversion Hcons.
  - (* LE-UnivGhost2 : peel the source ∀◇ against a guarded input.  The
       input P' may itself be a flexible variable, in which case the whole
       ∀◇-headed subject is assigned and the decoration swap applies. *)
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ].
    + (* R = tophole R' *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      pose proof HwfSub as HwfSubT.
      apply a_wf_pskl_tophole_inv in HwfSub.
      pose proof Hcons as HconsSaved.
      inversion Hcons; subst;
        try (match goal with
             | Hg : guarded_pskl (pskl_tophole _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl (pskl_all_syn _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl pskl_hole |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_uskl (uskl_tophole _) |- _ =>
                 solve [ inversion Hg ] end).
      * (* FlexR assignment of the ∀◇-headed subject to the flexible input *)
        assert (Hnas : no_all_syn_uskl
                         (uskl_tophole
                            (subst_bskl_in_uskl
                               (pskl_to_uskl (uskl_to_pskl ψa)) α R)))
          by (eapply a_consistag_flexvar_subject_no_all_syn;
                [ exact HconsSaved | exact Hwf | exact HwfSubT ]).
        assert (Hnas' : no_all_syn_uskl
                          (subst_bskl_in_uskl
                             (pskl_to_uskl (uskl_to_pskl ψa)) α R))
          by (inversion Hnas; assumption).
        destruct (flexvar_decoration_swap Hlook R eq_refl Hst Hnas')
          as [HΨa Heqs].
        rewrite Heqs.
        eapply a_consistag_psi_cong; [ exact HconsSaved | ].
        clear - HΨa. fsetdec.
      * (* the mirror UnivGhost2 *)
        apply a_consistag__univ_ghost2; [ assumption | assumption | ].
        match goal with
        | IH : forall R0 : uskl, _ |- _ =>
            eapply IH;
              [ exact Hst | reflexivity | exact Hαψ | exact Hlcψ | assumption
              | eassumption | exact Hwf | exact HwfP0 | exact HwfSub
              | exact Hrig | exact Hnfd | exact Hfaf ]
        end.
    + (* R = topholeg R' : UnivGhostG pins a ∀◇ input (never guarded), and
         a FlexR assignment cannot produce a dotted ghost *)
      simpl in Hcons.
      inversion Hcons; subst;
        try (match goal with
             | Hg : guarded_pskl (pskl_tophole _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl (pskl_all_syn _) |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | Hg : guarded_pskl pskl_hole |- _ =>
                 solve [ inversion Hg ] end);
        try (match goal with
             | He : pskl_to_uskl ?Px = uskl_topholeg _ |- _ =>
                 solve [ destruct Px; simpl in He; discriminate He ] end).
  - (* LE-UnivGhostR : guarded source, ∀◇ input peeled on the right *)
    destruct R; simpl in HeS; inversion HeS; subst;
      try solve [ inversion HlcS ];
      try solve [ match goal with Hg : guarded_pskl _ |- _ =>
                    inversion Hg end ].
    + (* R = unit : α-free, both substitutions are the identity *)
      match goal with
      | Hl : _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
          destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ Hl)
            as [-> ->]; [ simpl; clear; fsetdec | ]
      end.
      inversion Hst; subst.
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      fsetdec_empty.
    + (* R = var α0 (α0 ≠ α since ⌊R⌋ = P ≠ var α) : α-free *)
      match goal with
      | Hne : pskl_var_f ?α0 <> pskl_var_f α |- _ =>
          assert (Hαα0 : α `notin` ftvar_in_uskl (uskl_var_f α0))
            by (simpl; intro Hin; apply Hne; f_equal; fsetdec)
      end.
      match goal with
      | Hl : _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
          destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ Hl)
            as [-> ->];
          [ simpl in Hαα0 |- *; clear - Hαα0; fsetdec | ]
      end.
      inversion Hst; subst.
      rewrite subst_bskl_in_uskl_fresh_eq; [ | exact Hαα0 ].
      rewrite subst_bskl_in_uskl_fresh_eq in Hcons; [ | exact Hαα0 ].
      eapply a_consistag_psi_cong; [ exact Hcons | ].
      fsetdec_empty.
    + (* R = arrow R1 R2 *)
      simpl in Hcons |- *.
      inversion HlcS; subst.
      simpl in HwfSub.
      inversion Hcons; subst;
        try (match goal with
             | Hnf : a_non_flex _ (pskl_tophole _) |- _ =>
                 solve [ destruct Hnf as [_ Hnf]; exfalso; apply Hnf;
                         constructor ] end).
      match goal with
      | Hin : _ ⊢ᵗ[ _ | _ | _ | _ ]
                (uskl_arrow (subst_bskl_in_uskl _ _ _)
                            (subst_bskl_in_uskl _ _ _)) ∼˙ _ ⊣ _ |- _ =>
          idtac
      end.
      apply a_consistag__univ_ghost_r.
      * constructor;
          apply subst_bskl_in_uskl_lc_uskl; assumption.
      * simpl. unfold a_non_flex. split.
        -- constructor; apply lc_uskl_to_pskl_local;
             apply subst_bskl_in_uskl_lc_uskl; assumption.
        -- intro Hf; inversion Hf.
      * change (uskl_arrow (subst_bskl_in_uskl ψa α R1)
                           (subst_bskl_in_uskl ψa α R2))
          with (subst_bskl_in_uskl ψa α (uskl_arrow R1 R2)).
        apply a_wf_pskl_tophole_inv in HwfP0.
        match goal with
        | IH : forall R0 : uskl, _ |- _ =>
            eapply IH;
              [ exact Hst | reflexivity | exact Hαψ | exact Hlcψ | exact HlcS
              | simpl; eassumption | exact Hwf | exact HwfP0
              | simpl; exact HwfSub
              | exact Hrig | exact Hnfd | exact Hfaf ]
        end.
Qed.

(* ===================================================================== *)
(*  §13  Target-opening transport for constraint collection              *)
(*                                                                        *)
(*  A look run against a ∀-target transports to the opened target with    *)
(*  possibly different constraints solving the SAME tags — the mechanized *)
(*  form of the paper's WLOG ForallR-first reordering (tex:824).  The     *)
(*  constraint list is existential per fresh variable (the KEY lemma's    *)
(*  ForallR case quantifies it per opened premise), so no uniformity      *)
(*  across the family is needed; inside the forall_l case uniformity is   *)
(*  recovered by source-side renaming (a_looksub_subst_stable).           *)
(* ===================================================================== *)

Lemma a_looksub_open_target : forall P' P0 α Ξ 𝒞 ψa Ψa,
  P' ≼[ α , mode_tc ] (pskl_all_syn P0) ⤳ Ξ ⨾ 𝒞 ->
  𝒞 ⊩ᵗ ψa ⤳ Ψa ->
  exists L, forall β, β `notin` L ->
    exists C',
      P' ≼[ α , mode_tc ] (open_pskl_wrt_pskl P0 (pskl_var_f β)) ⤳ Ξ ⨾ C' /\
      C' ⊩ᵗ ψa ⤳ Ψa.
Proof.
  intros P' P0 α Ξ 𝒞 ψa Ψa Hlk.
  remember (pskl_all_syn P0) as T eqn:HT.
  remember mode_tc as M eqn:HM.
  revert P0 HT. induction Hlk; intros B0 HT Hst; subst; try discriminate HT.
  - (* LS-Var : the deposit opens with the target *)
    inversion Hst; subst.
    exists empty. intros β _.
    exists (a_cstr_sub mode_tc (open_pskl_wrt_pskl B0 (pskl_var_f β)) :: nil).
    split; [ apply a_looksub__var | ].
    apply a_solvetag__sub.
    apply a_solvetag_sub_all_syn_open. assumption.
  - (* LS-Absent : nothing collected either way *)
    exists empty. intros β _.
    exists nil. split; [ apply a_looksub__absent; assumption | exact Hst ].
  - (* LS-Check : a guarded ∀ is absurd *)
    match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
      inversion Hg end.
  - (* LS-ForallR : the family is exactly what is needed *)
    inversion HT; subst.
    exists L. intros β Hβ.
    exists C. split; [ auto | exact Hst ].
  - (* LS-ForallL : one fresh instance, renamed across the family *)
    destruct (atom_fresh (L `union` singleton α `union` ftvar_in_pskl P))
      as [β0 Hβ0].
    destruct (H0 β0 ltac:(clear - Hβ0; fsetdec) eq_refl _ eq_refl Hst)
      as [L1 HL1].
    exists (L1 `union` L `union` singleton α `union` singleton β0
            `union` ftvar_in_pskl P).
    intros β Hβ.
    destruct (HL1 β ltac:(clear - Hβ; fsetdec)) as [C' [Hlk' Hst']].
    exists C'. split; [ | exact Hst' ].
    apply a_looksub__forall_l
      with (L := L `union` singleton α `union` singleton β0
                 `union` ftvar_in_pskl P `union` singleton β).
    intros β' Hβ'.
    (* rename the source opener β0 → β' via substitution stability *)
    replace (open_pskl_wrt_pskl P (pskl_var_f β'))
      with (subst_pskl_in_pskl (pskl_var_f β') β0
              (open_pskl_wrt_pskl P (pskl_var_f β0)))
      by (symmetry; apply subst_pskl_in_pskl_intro;
          clear - Hβ0; fsetdec).
    apply a_looksub_subst_stable;
      [ exact Hlk' | clear - Hβ0; fsetdec
      | simpl; clear - Hβ'; fsetdec | constructor ].
  - (* LS-UnivGhostL : peel the source ∀◇ *)
    destruct (IHHlk eq_refl _ eq_refl Hst) as [L1 HL1].
    exists L1. intros β Hβ.
    destruct (HL1 β Hβ) as [C' [Hlk' Hst']].
    exists C'. split; [ apply a_looksub__univ_ghost_l; exact Hlk' | exact Hst' ].
Qed.

(** …and at a GIVEN sufficiently fresh opener β — the exists-fresh ForallR
    consumers (2026-07-31) cannot pick the opener off the family's own [L].
    Each case rebuilds the β-instance directly; LS-ForallR moves ONE fresh
    representative to β with [a_looksub_lookeq_rename_tvar], which keeps the
    shared 𝒞 because the representative also avoids [ftv 𝒞]. *)
Lemma a_looksub_open_target_at : forall P' P0 α Ξ 𝒞 ψa Ψa,
  P' ≼[ α , mode_tc ] (pskl_all_syn P0) ⤳ Ξ ⨾ 𝒞 ->
  𝒞 ⊩ᵗ ψa ⤳ Ψa ->
  forall β, β <> α ->
  β `notin` ftvar_in_pskl P' `union` ftvar_in_pskl P0 ->
  exists C',
    P' ≼[ α , mode_tc ] (open_pskl_wrt_pskl P0 (pskl_var_f β)) ⤳ Ξ ⨾ C' /\
    C' ⊩ᵗ ψa ⤳ Ψa.
Proof.
  intros P' P0 α Ξ 𝒞 ψa Ψa Hlk.
  remember (pskl_all_syn P0) as T eqn:HT.
  remember mode_tc as M eqn:HM.
  revert P0 HT. induction Hlk; intros B0 HT Hst β1 Hβα Hβ; subst;
    try discriminate HT.
  - (* LS-Var : the deposit opens with the target *)
    inversion Hst; subst.
    exists (a_cstr_sub mode_tc (open_pskl_wrt_pskl B0 (pskl_var_f β1)) :: nil).
    split; [ apply a_looksub__var | ].
    apply a_solvetag__sub.
    apply a_solvetag_sub_all_syn_open. assumption.
  - (* LS-Absent : nothing collected either way *)
    exists nil. split; [ apply a_looksub__absent; assumption | exact Hst ].
  - (* LS-Check : a guarded ∀ is absurd *)
    match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
      inversion Hg end.
  - (* LS-ForallR : ONE fresh representative, renamed to β1 keeping 𝒞 *)
    inversion HT; subst.
    simpl in Hβ.
    destruct (atom_fresh (L `union` singleton α `union` singleton β1
                `union` ftvar_in_pskl A `union` ftvar_in_pskl B0
                `union` ftvar_in_cstrs C)) as [β0 Hβ0].
    exists C. split; [ | exact Hst ].
    pose proof ((proj1 a_looksub_lookeq_rename_tvar) _ _ _ _ _ _
                  (H β0 ltac:(clear - Hβ0; fsetdec)) β0 β1
                  ltac:(clear - Hβ0; fsetdec)
                  Hβα
                  ltac:(clear - Hβ0; fsetdec)) as Hren.
    rewrite (subst_pskl_in_pskl_fresh_eq A) in Hren
      by (clear - Hβ0; fsetdec).
    rewrite <- (subst_pskl_in_pskl_intro β0 B0 (pskl_var_f β1)) in Hren
      by (clear - Hβ0; fsetdec).
    exact Hren.
  - (* LS-ForallL : one fresh source opener; IH at the given β1; re-wrap *)
    simpl in Hβ.
    destruct (atom_fresh (L `union` singleton α `union` singleton β1
                `union` ftvar_in_pskl P `union` ftvar_in_pskl B0))
      as [β0 Hβ0].
    destruct (H0 β0 ltac:(clear - Hβ0; fsetdec) eq_refl _ eq_refl Hst β1 Hβα
                ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                        P (pskl_var_f β0)) as Hup;
                      simpl in Hup; clear - Hβ Hβ0 Hup; fsetdec))
      as [C' [Hlk' Hst']].
    exists C'. split; [ | exact Hst' ].
    apply a_looksub__forall_l
      with (L := L `union` singleton α `union` singleton β0
                 `union` ftvar_in_pskl P `union` singleton β1).
    intros β' Hβ'.
    replace (open_pskl_wrt_pskl P (pskl_var_f β'))
      with (subst_pskl_in_pskl (pskl_var_f β') β0
              (open_pskl_wrt_pskl P (pskl_var_f β0)))
      by (symmetry; apply subst_pskl_in_pskl_intro;
          clear - Hβ0; fsetdec).
    apply a_looksub_subst_stable;
      [ exact Hlk' | clear - Hβ0; fsetdec
      | simpl; clear - Hβ'; fsetdec | constructor ].
  - (* LS-UnivGhostL : peel the source ∀◇ *)
    simpl in Hβ.
    destruct (IHHlk eq_refl _ eq_refl Hst β1 Hβα
                ltac:(clear - Hβ; fsetdec)) as [C' [Hlk' Hst']].
    exists C'. split; [ apply a_looksub__univ_ghost_l; exact Hlk' | exact Hst' ].
Qed.

(** Constraints collected against ◇ solve nothing: only [sub _ ◇] and
    empty lists can be collected, and a ◇-target solvetag run is empty. *)
Lemma a_looksub_lookeq_hole_cstrs :
  (forall α m P P' Ξ 𝒞, P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> P' = pskl_hole ->
     forall ψa Ψa, 𝒞 ⊩ᵗ ψa ⤳ Ψa -> Ψa [=] empty) /\
  (forall α P P' Ξ 𝒞, P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> P' = pskl_hole ->
     forall ψa Ψa, 𝒞 ⊩ᵗ ψa ⤳ Ψa -> Ψa [=] empty).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ 𝒞 _ => P' = pskl_hole ->
              forall ψa Ψa, 𝒞 ⊩ᵗ ψa ⤳ Ψa -> Ψa [=] empty)
           (fun α P P' Ξ 𝒞 _ => P' = pskl_hole ->
              forall ψa Ψa, 𝒞 ⊩ᵗ ψa ⤳ Ψa -> Ψa [=] empty));
    intros; subst; try discriminate;
    (* empty collections *)
    try solve [ match goal with
                | Hst : nil ⊩ᵗ _ ⤳ _ |- _ => inversion Hst; subst; assumption
                end ];
    (* guarded ◇ side conditions *)
    try solve [ inv_guarded_hole ];
    (* singleton sub deposit *)
    try solve [ match goal with
                | Hst : (a_cstr_sub _ pskl_hole :: nil) ⊩ᵗ _ ⤳ _ |- _ =>
                    inversion Hst; subst;
                    eapply a_solvetag_sub_hole_empty; eassumption
                end ];
    (* singleton eq deposit *)
    try solve [ match goal with
                | Hst : (a_cstr_eq pskl_hole :: nil) ⊩ᵗ _ ⤳ _ |- _ =>
                    inversion Hst; subst;
                    match goal with
                    | Hnil : nil ⊩ᵗ _ ⤳ ?B, Hone : _ ∼ᵗ pskl_hole ⤳ ?A,
                      HU : _ [=] union ?A ?B |- _ =>
                        inversion Hnil; subst;
                        pose proof ((proj2 a_solvetag_sub_eq_hole_empty)
                                      _ _ _ Hone eq_refl) as He1;
                        match goal with
                        | He2 : ?B0 [=] empty |- _ =>
                            clear - He1 He2 HU; fsetdec
                        end
                    end
                end ];
    (* cofinite recursions *)
    try solve [ match goal with
                | IH : forall β, β `notin` ?L -> _ |- _ =>
                    destruct (atom_fresh L) as [β0 Hβ0];
                    eapply (IH β0 Hβ0 eq_refl); eassumption
                end ];
    (* direct recursions *)
    try solve [ match goal with
                | IH : ?P = pskl_hole -> _ |- _ =>
                    eapply IH; [ reflexivity | eassumption ]
                end ].
Qed.

Lemma a_looksub_hole_solvetag_empty : forall α m P Ξ 𝒞 ψa Ψa,
  P ≼[ α , m ] pskl_hole ⤳ Ξ ⨾ 𝒞 ->
  𝒞 ⊩ᵗ ψa ⤳ Ψa ->
  Ψa [=] empty.
Proof.
  intros; eapply (proj1 a_looksub_lookeq_hole_cstrs); eauto.
Qed.

(** Single-substitution analogs of the §11 helpers. *)
Lemma erase_swap_subst : forall ψa α R,
  ⌊ subst_bskl_in_uskl ψa α R ⌋ˢ
  = ⌊ subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R ⌋ˢ.
Proof.
  intros. rewrite ! uskl_to_pskl_subst.
  rewrite uskl_to_pskl_pskl_to_uskl. reflexivity.
Qed.

Lemma pskl_to_uskl_lc_inv : forall P,
  lc_uskl (pskl_to_uskl P) -> lc_pskl P.
Proof.
  intros P H.
  rewrite <- (uskl_to_pskl_pskl_to_uskl P).
  apply lc_uskl_to_pskl_local. exact H.
Qed.

Lemma pskl_to_uskl_guarded_inv : forall P,
  guarded_uskl (pskl_to_uskl P) -> guarded_pskl P.
Proof.
  intros P Hg; destruct P; simpl in Hg; inversion Hg; subst;
    constructor; apply pskl_to_uskl_lc_inv; assumption.
Qed.

Lemma guarded_subst_decorate : forall ψa α R',
  lc_uskl ψa ->
  lc_uskl R' ->
  guarded_uskl (subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) α R') ->
  guarded_uskl (subst_bskl_in_uskl ψa α R').
Proof.
  intros ψa α R' Hlcψ HlcS Hg. destruct R'; simpl in Hg |- *;
    try exact Hg; try solve [ inversion Hg ].
  - (* var *)
    revert Hg.
    destruct_if as [-> | Hne]; intro Hg; [ | exact Hg ].
    apply guarded_uskl_of_pskl.
    apply guarded_uskl_to_pskl_fwd in Hg.
    rewrite uskl_to_pskl_pskl_to_uskl in Hg. exact Hg.
  - (* arrow *)
    inversion HlcS; subst.
    constructor; apply subst_bskl_in_uskl_lc_uskl; assumption.
Qed.

