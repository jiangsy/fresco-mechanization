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
Require Import src.frost.algo.prop_decorate.
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
  (forall ψ M Q Ψ, ψ ≼ᵗ[ M ] Q ⤳ Ψ ->
     forall Ψ', Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] Q ⤳ Ψ') /\
  (forall ψ Q Ψ, ψ ∼ᵗ Q ⤳ Ψ ->
     forall Ψ', Ψ [=] Ψ' -> ψ ∼ᵗ Q ⤳ Ψ').
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M Q Ψ _ => forall Ψ', Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] Q ⤳ Ψ')
           (fun ψ Q Ψ _ => forall Ψ', Ψ [=] Ψ' -> ψ ∼ᵗ Q ⤳ Ψ'));
    intros; try (econstructor; eauto; fsetdec).
Qed.

Lemma a_solvetag_sub_psi_cong : forall ψ M Q Ψ Ψ',
  ψ ≼ᵗ[ M ] Q ⤳ Ψ -> Ψ [=] Ψ' -> ψ ≼ᵗ[ M ] Q ⤳ Ψ'.
Proof. intros; eapply (proj1 a_solvetag_sub_eq_psi_cong); eauto. Qed.

Lemma a_solvetag_eq_psi_cong : forall ψ Q Ψ Ψ',
  ψ ∼ᵗ Q ⤳ Ψ -> Ψ [=] Ψ' -> ψ ∼ᵗ Q ⤳ Ψ'.
Proof. intros; eapply (proj2 a_solvetag_sub_eq_psi_cong); eauto. Qed.

Lemma a_solvetag_psi_cong : forall C ψ Ψ Ψ',
  C ⊩ᵗ ψ ⤳ Ψ -> Ψ [=] Ψ' -> C ⊩ᵗ ψ ⤳ Ψ'.
Proof.
  intros C ψ Ψ Ψ' Hs; revert Ψ'; induction Hs; intros Ψ' Heq.
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
  match goal with |- context [ if ?e then _ else _ ] => destruct e end;
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
Lemma uskl_to_pskl_msubst : forall ρ T,
  ⌊ msubst_uskl ρ T ⌋ˢ = msubst_pskl_named (erase_msubst ρ) ⌊ T ⌋ˢ.
Proof.
  induction ρ as [ | [β ψg] ρ' IH ]; intros T; simpl; [ reflexivity | ].
  rewrite uskl_to_pskl_subst. rewrite IH. reflexivity.
Qed.

(** A variable outside the domain is untouched. *)
Lemma msubst_uskl_var_notin : forall ρ β,
  β `notin` dom ρ ->
  msubst_uskl ρ (uskl_var_f β) = uskl_var_f β.
Proof.
  induction ρ as [ | [γ ψg] ρ' IH ]; intros β Hβ; simpl; [ reflexivity | ].
  rewrite IH; [ | simpl in Hβ; clear - Hβ; fsetdec ].
  simpl.
  match goal with |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne] end;
    [ simpl in Hβ; exfalso; clear - Hβ; fsetdec | reflexivity ].
Qed.

(** Local closure of every range skeleton lets ρ commute with opening. *)
Definition msubst_lc (ρ : list (atom * uskl)) : Prop :=
  forall β ψg, binds β ψg ρ -> lc_uskl ψg.

Lemma msubst_uskl_open_comm : forall ρ T X,
  msubst_lc ρ ->
  X `notin` dom ρ ->
  (forall β ψg, binds β ψg ρ -> X `notin` ftvar_in_uskl ψg) ->
  msubst_uskl ρ (open_uskl_wrt_uskl T (uskl_var_f X))
  = open_uskl_wrt_uskl (msubst_uskl ρ T) (uskl_var_f X).
Proof.
  induction ρ as [ | [γ ψg] ρ' IH ]; intros T X Hlc Hdom Hftv;
    simpl; [ reflexivity | ].
  assert (Hlcγ : lc_uskl ψg)
    by (eapply Hlc; unfold binds; simpl; left; reflexivity).
  assert (Hlc' : msubst_lc ρ')
    by (intros b p Hb; eapply Hlc; unfold binds; simpl; right; exact Hb).
  assert (Hdom' : X `notin` dom ρ')
    by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (Hftv' : forall b p, binds b p ρ' -> X `notin` ftvar_in_uskl p)
    by (intros b p Hb; eapply Hftv; unfold binds; simpl; right; exact Hb).
  rewrite (IH T X Hlc' Hdom' Hftv').
  rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcγ ].
  f_equal.
  assert (HXγ : X <> γ) by (simpl in Hdom; clear - Hdom; fsetdec).
  assert (HXf : X `notin` ftvar_in_uskl ψg)
    by (eapply Hftv; unfold binds; simpl; left; reflexivity).
  simpl.
  match goal with |- context [ if ?e then _ else _ ] => destruct e as [-> | _] end;
    [ contradiction | reflexivity ].
Qed.
(* general erasure/open commute (open with an arbitrary skeleton) *)
Lemma uskl_to_pskl_open_gen : forall S ψg,
  ⌊ open_uskl_wrt_uskl S ψg ⌋ˢ
  = open_pskl_wrt_pskl ⌊ S ⌋ˢ ⌊ ψg ⌋ˢ.
Proof.
  intros. unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl.
  generalize 0. induction S; intros k; simpl; try (f_equal; auto; fail).
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

Lemma is_tskl_lc : forall ψ, is_tskl ψ -> lc_uskl ψ.
Proof.
  intros ψ H; induction H; try (constructor; auto; fail).
  destruct (atom_fresh L) as [X HX].
  eapply lc_uskl_all_etag_exists; eauto.
Qed.

Lemma a_subtag_vacuous_erasure : forall NM M P0 Ψ Θ0 T1 Q Θ1,
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] T1 ⊑ Q ⊣ Θ1 ->
  P0 = pskl_hole ->
  forall T2, lc_uskl T2 -> ⌊ T2 ⌋ˢ = ⌊ T1 ⌋ˢ ->
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] T2 ⊑ Q ⊣ Θ1.
Proof.
  intros NM M P0 Ψ Θ0 T1 Q Θ1 H.
  induction H; intros HP0 T2 HlcT2 Herase; subst; try discriminate HP0.
  - (* Infer : output is ⌊S⌋ = ⌊T2⌋ *)
    rewrite <- Herase. apply a_subtag__infer; assumption.
  - (* Check : P0 = B = ◇, but guarded_pskl ◇ is absurd *)
    match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end.
  - (* UnivGhostR : source guarded, output tophole ⌊S⌋ *)
    (* ⌊T2⌋ = ⌊S⌋ guarded ⇒ T2 top ∈ {unit,var,arrow} ⇒ T2 guarded *)
    assert (HgT2 : guarded_uskl T2).
    { inversion H; subst; simpl in Herase;
        destruct T2; simpl in Herase; inversion Herase; subst;
        inversion HlcT2; subst; constructor; assumption. }
    rewrite <- Herase. apply a_subtag__univ_ghost_r; assumption.
  - (* ForallL tagged : reconstruct on T2 (shape decides tagged/untagged) *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + (* T2 = all_syn *) eapply a_subtag__forall_l_untagged with
        (L := L) (Ξ := Ξ) (Ψg := Ψg) (ψg := ψg) (P1 := ⌊ ψg ⌋ˢ).
      * exact H.
      * right; reflexivity.
      * intros α Hα.
        replace (⌊ open_uskl_wrt_uskl T2 (uskl_var_f α) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl S (uskl_var_f α) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open; rewrite H8; reflexivity).
        apply H1; exact Hα.
      * exact H2.
      * exact H3.
      * exact H4.
      * exact H5.
      * reflexivity.
      * eapply IHa_subtag.
        -- reflexivity.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion H5; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen. rewrite H8. reflexivity.
    + (* T2 = all_etag *) eapply a_subtag__forall_l_tagged with
        (L := L) (Ξ := Ξ) (Ψg := Ψg) (ψg := ψg) (P1 := ⌊ ψg ⌋ˢ).
      * exact H.
      * right; reflexivity.
      * intros α Hα.
        replace (⌊ open_uskl_wrt_uskl T2 (uskl_var_f α) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl S (uskl_var_f α) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open; rewrite H8; reflexivity).
        apply H1; exact Hα.
      * exact H2.
      * exact H3.
      * exact H4.
      * exact H5.
      * reflexivity.
      * eapply IHa_subtag.
        -- reflexivity.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion H5; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen. rewrite H8. reflexivity.
  - (* ForallL untagged : identical reconstruction *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + eapply a_subtag__forall_l_untagged with
        (L := L) (Ξ := Ξ) (Ψg := Ψg) (ψg := ψg) (P1 := ⌊ ψg ⌋ˢ).
      * exact H.
      * right; reflexivity.
      * intros α Hα.
        replace (⌊ open_uskl_wrt_uskl T2 (uskl_var_f α) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl S (uskl_var_f α) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open; rewrite H8; reflexivity).
        apply H1; exact Hα.
      * exact H2.
      * exact H3.
      * exact H4.
      * exact H5.
      * reflexivity.
      * eapply IHa_subtag.
        -- reflexivity.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion H5; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen. rewrite H8. reflexivity.
    + eapply a_subtag__forall_l_tagged with
        (L := L) (Ξ := Ξ) (Ψg := Ψg) (ψg := ψg) (P1 := ⌊ ψg ⌋ˢ).
      * exact H.
      * right; reflexivity.
      * intros α Hα.
        replace (⌊ open_uskl_wrt_uskl T2 (uskl_var_f α) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl S (uskl_var_f α) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open; rewrite H8; reflexivity).
        apply H1; exact Hα.
      * exact H2.
      * exact H3.
      * exact H4.
      * exact H5.
      * reflexivity.
      * eapply IHa_subtag.
        -- reflexivity.
        -- apply lc_body_uskl_wrt_uskl;
             [ eauto using lc_body_uskl_all_syn_1, lc_body_uskl_all_etag_2
             | apply is_tskl_lc; inversion H5; assumption ].
        -- rewrite ! uskl_to_pskl_open_gen. rewrite H8. reflexivity.
  - (* Ghost : source hole, output P0=hole *)
    destruct T2; simpl in Herase; inversion Herase; subst.
    + apply a_subtag__ghost; assumption.
    + apply a_subtag__ghostg; assumption.
  - (* GhostG : source holeg, output hole *)
    destruct T2; simpl in Herase; inversion Herase; subst.
    + apply a_subtag__ghost; [ assumption ].
    + apply a_subtag__ghostg; assumption.
  - (* UnivGhostL : source tophole S *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + apply a_subtag__univ_ghost_l; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
    + apply a_subtag__univ_ghost_lg; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
  - (* UnivGhostLG : source topholeg S *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      match goal with Hl : lc_uskl _ |- _ => inversion Hl; subst end.
    + apply a_subtag__univ_ghost_l; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
    + apply a_subtag__univ_ghost_lg; [ assumption | ].
      eapply IHa_subtag; [ reflexivity | assumption | assumption ].
  - (* FlexMono : source var α ⇒ T2 = var α *)
    destruct T2; simpl in Herase; inversion Herase; subst.
    apply a_subtag__flex_mono; assumption.
Qed.

(* ===================================================================== *)
(*  §7  Ψ-congruence for decorated consistency and subtyping             *)
(*                                                                        *)
(*  The tag context threads through every rule via [=]-premises, so it    *)
(*  respects set equality.  Needed by the decoration-var lemmas (their    *)
(*  var/unit cases produce Ψ ∪ ∅).                                        *)
(* ===================================================================== *)

Lemma a_consistag_psi_cong : forall Δ1 Δ2 P0 Ψ Θ0 S Q Θ1,
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] S ≈ Q ⊣ Θ1 ->
  forall Ψ', Ψ [=] Ψ' ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ' ] S ≈ Q ⊣ Θ1.
Proof.
  intros Δ1 Δ2 P0 Ψ Θ0 S Q Θ1 H; induction H; intros Ψ' Heq; econstructor;
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
  induction ρ as [ | [γ g] ρ' IH ]; intros β ψg Hb; simpl in *;
    [ inversion Hb | ].
  destruct Hb as [Heq | Hb].
  - inversion Heq; subst. clear; fsetdec.
  - specialize (IH _ _ Hb). clear - IH; fsetdec.
Qed.

(** ρ distributes over every skeleton constructor (iterated subst). *)
Lemma msubst_uskl_arrow : forall ρ a b,
  msubst_uskl ρ (uskl_arrow a b)
  = uskl_arrow (msubst_uskl ρ a) (msubst_uskl ρ b).
Proof. induction ρ as [|[γ g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_tophole : forall ρ a,
  msubst_uskl ρ (uskl_tophole a) = uskl_tophole (msubst_uskl ρ a).
Proof. induction ρ as [|[γ g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_topholeg : forall ρ a,
  msubst_uskl ρ (uskl_topholeg a) = uskl_topholeg (msubst_uskl ρ a).
Proof. induction ρ as [|[γ g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_all_syn : forall ρ a,
  msubst_uskl ρ (uskl_all_syn a) = uskl_all_syn (msubst_uskl ρ a).
Proof. induction ρ as [|[γ g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

Lemma msubst_uskl_all_etag : forall ρ ε a,
  msubst_uskl ρ (uskl_all_etag ε a) = uskl_all_etag ε (msubst_uskl ρ a).
Proof. induction ρ as [|[γ g] ρ' IH]; intros; simpl; [reflexivity|]; rewrite IH; reflexivity. Qed.

(** strip = pskl_to_uskl ∘ uskl_to_pskl commutes with opening. *)
Lemma strip_open : forall ψ β,
  pskl_to_uskl (uskl_to_pskl (open_uskl_wrt_uskl ψ (uskl_var_f β)))
  = open_uskl_wrt_uskl (pskl_to_uskl (uskl_to_pskl ψ)) (uskl_var_f β).
Proof.
  intros. rewrite uskl_to_pskl_open. rewrite pskl_to_uskl_open_var. reflexivity.
Qed.

Lemma lc_uskl_to_pskl_local : forall S, lc_uskl S -> lc_pskl (uskl_to_pskl S).
Proof.
  intros S H; induction H; simpl;
    try (constructor; auto; fail);
    constructor; intros X; rewrite <- uskl_to_pskl_open; auto.
Qed.

(** Reflection of local closure / guardedness through the erasure. *)
Lemma degree_uskl_of_pskl : forall T k,
  degree_pskl_wrt_pskl k (uskl_to_pskl T) -> degree_uskl_wrt_uskl k T.
Proof.
  induction T; intros k Hd; simpl in Hd; inversion Hd; subst;
    constructor; auto.
Qed.

Lemma lc_uskl_of_pskl : forall T,
  lc_pskl (uskl_to_pskl T) -> lc_uskl T.
Proof.
  intros T H. apply lc_uskl_of_degree. apply degree_uskl_of_pskl.
  apply degree_pskl_wrt_pskl_of_lc_pskl. exact H.
Qed.

Lemma guarded_uskl_to_pskl_fwd : forall T,
  guarded_uskl T -> guarded_pskl (uskl_to_pskl T).
Proof.
  intros T H; inversion H; simpl; constructor;
    apply lc_uskl_to_pskl_local; assumption.
Qed.

Lemma guarded_uskl_of_pskl : forall T,
  guarded_pskl (uskl_to_pskl T) -> guarded_uskl T.
Proof.
  destruct T; simpl; intros H; inversion H; subst;
    try (constructor; apply lc_uskl_of_pskl; assumption).
Qed.

(** With input ◇ the consistency run is determined by the source's erasure
    (analogue of a_subtag_vacuous_erasure). *)
Lemma a_consistag_vacuous_erasure : forall Δ1 Δ2 P0 Ψ Θ0 T1 Q Θ1,
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] T1 ≈ Q ⊣ Θ1 ->
  P0 = pskl_hole ->
  forall T2, uskl_to_pskl T2 = uskl_to_pskl T1 ->
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] T2 ≈ Q ⊣ Θ1.
Proof.
  intros Δ1 Δ2 P0 Ψ Θ0 T1 Q Θ1 H;
    induction H; intros HP0 T2 Herase; subst; try discriminate HP0.
  - (* Ghost : T1 = ◇, output ◇ *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      [ apply a_consistag__ghost; [ simpl; clear; fsetdec | assumption ]
      | apply a_consistag__ghostg; assumption ].
  - (* FlexL : T1 = var α, so T2 = var α *)
    destruct T2; simpl in Herase; inversion Herase; subst.
    eapply a_consistag__flex_l; eassumption.
  - (* GhostG : T1 = holeg, output ◇ *)
    destruct T2; simpl in Herase; inversion Herase; subst;
      [ apply a_consistag__ghost; [ simpl; clear; fsetdec | assumption ]
      | apply a_consistag__ghostg; assumption ].
  - (* UnivGhost2 : guarded_pskl ◇ is absurd *)
    match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end.
  - (* GhostR : output ⌊S⌋; reconstruct with T2 (same erasure) *)
    rewrite <- Herase.
    apply a_consistag__ghost_r; [ rewrite Herase; assumption | assumption ].
Qed.

Lemma a_consistag_decoration_var : forall ψ P0 Ψa,
  ψ ∼ᵗ P0 ⤳ Ψa ->
  forall Δ1 Δ2 Ψ Θ0 Q Θ1 ρ,
    msubst_lc ρ ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ]
      (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ≈ Q ⊣ Θ1 ->
    Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | (Ψ `union` Ψa) ]
      (msubst_uskl ρ ψ) ≈ Q ⊣ Θ1.
Proof.
  intros ψ P0 Ψa H; induction H;
    intros Δ1 Δ2 Ψc Θ0 Qc Θ1 ρ Hlcρ Hcons.
  - (* SEq-Unit : ψ = unit, strip = unit, sources identical *)
    simpl in Hcons |- *.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H; fsetdec ].
  - (* SEq-Var : ψ = var X, strip = var X, sources identical *)
    simpl in Hcons |- *.
    eapply a_consistag_psi_cong; [ exact Hcons | clear - H; fsetdec ].
  - (* SEq-Vacuous : P0 = ◇, both sources erase equally *)
    eapply a_consistag_psi_cong;
      [ eapply a_consistag_vacuous_erasure;
          [ exact Hcons | reflexivity | ]
      | clear - H; fsetdec ].
    rewrite ! uskl_to_pskl_msubst. f_equal.
    rewrite uskl_to_pskl_pskl_to_uskl. reflexivity.
  - (* SEq-Arrow : invert the consistency arrow, IH each part *)
    rewrite msubst_uskl_arrow.
    simpl in Hcons. rewrite msubst_uskl_arrow in Hcons.
    inversion Hcons; subst.
    match goal with
    | Hc1 : _ ⊢ᵗ[ _ | _ | ?p1 | ?Ψi1 ] _ ≈ _ ⊣ ?Θm,
      Hc2 : ?Θm ⊢ᵗ[ _ | _ | ?p2 | ?Ψi2 ] _ ≈ _ ⊣ _,
      HΨi : _ [=] union ?Ψi1 ?Ψi2 |- _ =>
        eapply a_consistag__arrow with
          (Ψ1 := Ψi1 `union` Ψ1) (Ψ2 := Ψi2 `union` Ψ2) (Θ1 := Θm);
        [ eapply IHa_solvetag_eq1; [ exact Hlcρ | exact Hc1 ]
        | eapply IHa_solvetag_eq2; [ exact Hlcρ | exact Hc2 ]
        | clear - HΨi H1; fsetdec ]
    end.
  - (* SEq-ForallInh : open a fresh rigid on both sides; ρ unchanged.
       H0 = the IH; H8 = the inverted (untagged) consistency body. *)
    rewrite msubst_uskl_all_etag.
    simpl in Hcons. rewrite msubst_uskl_all_syn in Hcons.
    inversion Hcons; subst.
    eapply a_consistag__forall_inh_tagged
      with (Ψ0 := Ψc `union` Ψ0) (ε := ε)
           (L := L0 `union` L `union` dom ρ `union` msubst_ftv ρ);
      [ intros β Hβ | clear - H1; fsetdec ].
    assert (Hβρ : β `notin` dom ρ) by (clear - Hβ; fsetdec).
    assert (Hβf : forall γ ψg, binds γ ψg ρ -> β `notin` ftvar_in_uskl ψg).
    { intros γ ψg Hb. pose proof (msubst_ftv_binds _ _ _ Hb) as Hsc.
      clear - Hβ Hsc. fsetdec. }
    rewrite <- (@msubst_uskl_open_comm ρ ψ β Hlcρ Hβρ Hβf).
    eapply (H0 β ltac:(clear - Hβ; fsetdec)); [ exact Hlcρ | ].
    rewrite strip_open.
    specialize (H8 β ltac:(clear - Hβ; fsetdec)).
    rewrite <- (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                  Hlcρ Hβρ Hβf) in H8.
    exact H8.
  - (* SEq-UnivGhostG : invert UnivGhost, IH the inner *)
    rewrite msubst_uskl_topholeg.
    simpl in Hcons. rewrite msubst_uskl_tophole in Hcons.
    inversion Hcons; subst;
      try (match goal with Hg : guarded_pskl (pskl_tophole _) |- _ =>
             solve [ inversion Hg ] end);
      try (match goal with Hg : guarded_uskl (uskl_tophole _) |- _ =>
             solve [ inversion Hg ] end).
    match goal with
    | Hc : _ ⊢ᵗ[ _ | _ | _ | _ ]
             (msubst_uskl ρ (pskl_to_uskl (uskl_to_pskl ψ))) ≈ _ ⊣ _ |- _ =>
        apply a_consistag__univ_ghostg;
        eapply IHa_solvetag_eq; [ exact Hlcρ | exact Hc ]
    end.
  - (* SEq-ForallSyn : as ForallInh but input ⊤◇, tag pass-through *)
    rewrite msubst_uskl_all_etag.
    simpl in Hcons. rewrite msubst_uskl_all_syn in Hcons.
    inversion Hcons; subst;
      try (match goal with Hg : guarded_uskl (uskl_all_syn _) |- _ =>
             solve [ inversion Hg ] end).
    eapply a_consistag__forall_syn_tagged
      with (ε := ε) (L := L0 `union` L `union` dom ρ `union` msubst_ftv ρ);
      intros β Hβ.
    assert (Hβρ : β `notin` dom ρ) by (clear - Hβ; fsetdec).
    assert (Hβf : forall γ ψg, binds γ ψg ρ -> β `notin` ftvar_in_uskl ψg).
    { intros γ ψg Hb. pose proof (msubst_ftv_binds _ _ _ Hb) as Hsc.
      clear - Hβ Hsc. fsetdec. }
    rewrite <- (@msubst_uskl_open_comm ρ ψ β Hlcρ Hβρ Hβf).
    eapply (H0 β ltac:(clear - Hβ; fsetdec)); [ exact Hlcρ | ].
    rewrite strip_open.
    specialize (H7 β ltac:(clear - Hβ; fsetdec)).
    rewrite <- (@msubst_uskl_open_comm ρ (pskl_to_uskl (uskl_to_pskl ψ)) β
                  Hlcρ Hβρ Hβf) in H7.
    exact H7.
  - (* SEq-UnivGhostR : reflection helpers (below) are ready; the
       unit/var sub-cases need the inner-solvetag Ψ=∅ inversion wired and
       the arrow sub-case its invert+IH+reconstruct.  Honest admit. *)
    admit.
  - (* SEq-FlexR : P0 = var α, ghost-free ψ *)
    admit.
Admitted.
