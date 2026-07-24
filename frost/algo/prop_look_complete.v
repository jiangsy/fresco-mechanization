(** P6 — COMPLETENESS OF CONSTRAINT COLLECTION AND SOLVING (the "look"
    cluster [a_looksub]/[a_lookeq]/[a_solve_sub]/[a_solve_eq]/
    [a_solve_cstr]/[a_extract], algo/def_extra.v:287-498).

    Paper lemmas (docs/DESIGN-completeness-subtyping.md §7):
      P6-Cv  [a_solve_eq_complete_var]   consistency-proofs.tex:1180
      P6-Cs  [a_lookeq_solve_complete]   consistency-proofs.tex:920
      P6-Sv  [a_solve_sub_complete_var]  subtyping-proofs.tex:1696
      P6-Ss  [a_looksub_solve_complete]  subtyping-proofs.tex:2202
      P6-L   [a_extract_complete]        subtyping-proofs.tex:2729

    THE ρ REPRESENTATION (design locked in DESIGN §7, 2026-07-24): the
    paper's "capture-avoiding substitution ρ from rigid type variables to
    decorated skeletons" is mechanized as the RELATION [uskl_rho]
    ("ψsub ⊒ρ ψa"): same-constructor congruences + a REFL rule (identity-ρ
    call sites) + one replace-leaf [ψ'' ⊒ var X].  [Δρ] collects the
    replaced variables, [Ψρ] the tags introduced by the replacements
    (unions WITHOUT cross-copy disjointness — several occurrences of one
    variable share their image's tags).

    [paper-gap] The paper's positional side condition "for every rigid
    variable in ψa substituted by ρ, P_i has the same rigid variable in
    the same position" is mechanized WITHOUT a positional predicate: it
    is RECOVERED as a lemma ([ad_ppre_delta_var_inv]) from FRESHNESS of
    the replaced variables — [X ∈ Δ] (blocks the precision hole rule),
    [binds X abind_tvar Θ] (blocks flex_r), X avoided by θ's images, by
    Θ's definition images ([rho_fresh]), and by the subject's ⊤◇-shielded
    variables ([pskl_shielded_ftv]).  Δ-membership ALONE is insufficient
    (counterexamples v4/v5, DESIGN §7): precision's tophole_remove/flex_l
    admit ⊤◇-wrapped or definition-chained leaf positions whose
    SE-GhostForall output breaks the conclusion precision.  The freshness
    facts hold at the one leaf-creating call site (P6-Sv ForallL: the
    freshly opened binder postdates θ and Θ's definitions, and the
    [a_wf_pskl__tophole] empty-Δ-body discipline keeps it out of ⊤◇
    bodies), and are threaded through the conclusions for chaining. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_consis_precise.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_sub_complete.

Set Implicit Arguments.

(* ===================================================================== *)
(*  The ρ relation  [ψsub ⊒ρ[Δρ;Ψρ] ψa]  (DESIGN §7).                      *)
(* ===================================================================== *)

Inductive uskl_rho (NM : a_sub_mode) (Θ : aenv)
  : atoms -> atoms -> uskl -> uskl -> Prop :=
| urho__refl : forall Δρ Ψρ R,
    lc_uskl R ->
    Ψρ [=] empty ->
    uskl_rho NM Θ Δρ Ψρ R R
| urho__leaf : forall Δρ Ψρ X Ψ'' ψ'',
    X `in` Δρ ->
    a_tags_sort NM Ψ'' ψ'' ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ'' ⌋ˢ ->
    Ψρ [=] Ψ'' ->
    uskl_rho NM Θ Δρ Ψρ ψ'' (uskl_var_f X)
| urho__arrow : forall Δρ Ψρ Ψ1 Ψ2 S1 S2 R1 R2,
    uskl_rho NM Θ Δρ Ψ1 S1 R1 ->
    uskl_rho NM Θ Δρ Ψ2 S2 R2 ->
    Ψρ [=] Ψ1 `union` Ψ2 ->
    uskl_rho NM Θ Δρ Ψρ (uskl_arrow S1 S2) (uskl_arrow R1 R2)
| urho__all_syn : forall L Δρ Ψρ S R,
    (forall X, X `notin` L ->
       uskl_rho NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl S (uskl_var_f X))
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    uskl_rho NM Θ Δρ Ψρ (uskl_all_syn S) (uskl_all_syn R)
| urho__all_etag : forall L Δρ Ψρ ε S R,
    (forall X, X `notin` L ->
       uskl_rho NM Θ Δρ Ψρ
         (open_uskl_wrt_uskl S (uskl_var_f X))
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    uskl_rho NM Θ Δρ Ψρ (uskl_all_etag ε S) (uskl_all_etag ε R)
| urho__tophole : forall Δρ Ψρ S R,
    uskl_rho NM Θ Δρ Ψρ S R ->
    uskl_rho NM Θ Δρ Ψρ (uskl_tophole S) (uskl_tophole R)
| urho__topholeg : forall Δρ Ψρ S R,
    uskl_rho NM Θ Δρ Ψρ S R ->
    uskl_rho NM Θ Δρ Ψρ (uskl_topholeg S) (uskl_topholeg R).

(** Re-tag under set equality. *)
Lemma uskl_rho_psi_cong : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  forall Ψρ', Ψρ [=] Ψρ' ->
  uskl_rho NM Θ Δρ Ψρ' S R.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; intros Ψρ' Heq.
  - apply urho__refl; [ assumption | fsetdec ].
  - eapply urho__leaf; [ exact H | exact H0 | exact H1 | fsetdec ].
  - eapply urho__arrow; [ exact H | exact H0 | fsetdec ].
  - eapply urho__all_syn with (L := L); intros X HX; eauto.
  - eapply urho__all_etag with (L := L); intros X HX; eauto.
  - apply urho__tophole; eauto.
  - apply urho__topholeg; eauto.
Qed.

(** Widen the replaced-variable bound. *)
Lemma uskl_rho_delta_mono : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  forall Δρ', Δρ [<=] Δρ' ->
  uskl_rho NM Θ Δρ' Ψρ S R.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; intros Δρ' Hsub.
  - apply urho__refl; assumption.
  - eapply urho__leaf; [ | exact H0 | exact H1 | exact H2 ]. fsetdec.
  - eapply urho__arrow; [ apply IHuskl_rho1 | apply IHuskl_rho2 | ];
      assumption.
  - eapply urho__all_syn with (L := L); intros X HX; eauto.
  - eapply urho__all_etag with (L := L); intros X HX; eauto.
  - apply urho__tophole; eauto.
  - apply urho__topholeg; eauto.
Qed.

(** The subject's tags are bounded by the replacement tags plus ψa's. *)
Lemma uskl_rho_ftag_sub : forall NM Θ Δρ Ψρ S R,
  uskl_rho NM Θ Δρ Ψρ S R ->
  ftag_in_uskl S [<=] Ψρ `union` ftag_in_uskl R.
Proof.
  intros NM Θ Δρ Ψρ S R H; induction H; simpl; try fsetdec.
  - (* leaf: tags of the image are exactly Ψ'' *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags H0)) as Ht.
    fsetdec.
  - (* all_syn *)
    pick fresh X for L.
    pose proof (H0 X ltac:(fsetdec)) as HX.
    pose proof (ftag_in_uskl_open_var S X).
    pose proof (ftag_in_uskl_open_var R X).
    fsetdec.
  - (* all_etag *)
    pick fresh X for L.
    pose proof (H0 X ltac:(fsetdec)) as HX.
    pose proof (ftag_in_uskl_open_var S X).
    pose proof (ftag_in_uskl_open_var R X).
    fsetdec.
Qed.

(* ===================================================================== *)
(*  Shielded free variables + the ρ-freshness pack (DESIGN §7).            *)
(*                                                                         *)
(*  [pskl_shielded_ftv P] collects the free type variables occurring       *)
(*  UNDER some ⊤◇ of [P].  The replaced variables of ρ must avoid them     *)
(*  (together with θ's and Θ's definition images): this is what recovers   *)
(*  the paper's positional side condition as a LEMMA                       *)
(*  ([ad_ppre_delta_var_inv]) instead of a positional predicate.           *)
(* ===================================================================== *)

Fixpoint pskl_shielded_ftv (P : pskl) : atoms :=
  match P with
  | pskl_unit => {}
  | pskl_var_b _ => {}
  | pskl_var_f _ => {}
  | pskl_arrow P1 P2 => pskl_shielded_ftv P1 `union` pskl_shielded_ftv P2
  | pskl_all_syn P0 => pskl_shielded_ftv P0
  | pskl_hole => {}
  | pskl_tophole P0 => ftvar_in_pskl P0
  end.

Lemma pskl_shielded_ftv_sub_ftv : forall P,
  pskl_shielded_ftv P [<=] ftvar_in_pskl P.
Proof. induction P; simpl; fsetdec. Qed.

(** The ρ-freshness pack for the Θ/θ-stable components: every replaced
    variable is a rigid tvar of Θ that postdates θ's flexible images and
    Θ's definition images.  (The Pi-dependent component —
    [X ∉ pskl_shielded_ftv (msubst_pskl θ Pi)] — and the Δ-membership
    [X ∈ Δ] are separate premises, since Pi and Δ vary per case.) *)
Definition rho_fresh (Δρ : atoms) (Θ : aenv) (θ : metasubst) : Prop :=
  forall X, X `in` Δρ ->
    binds X abind_tvar Θ /\
    (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) /\
    (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
       X `notin` ftvar_in_ptyp τ).

(* ===================================================================== *)
(*  Leaf inversion: partial precision at a rigid replaced-variable target  *)
(*  forces the subject to be EXACTLY that variable.                        *)
(* ===================================================================== *)

(** No partial-precision derivation targets [var X] from an [X]-free
    subject when [X] is a Δ-visible rigid tvar avoided by Θ's definition
    images: the var rule needs the occurrence, the hole rule is blocked
    by its Δ-disjointness premise, flex_l chains stay inside Θ's
    definition images, flex_r clashes with X's rigidity. *)
Lemma ad_ppre_var_target_absent : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall X, ψ = uskl_var_f X ->
  a_wf_aenv Θ ->
  X `in` Δ ->
  binds X abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     X `notin` ftvar_in_ptyp τ) ->
  X `notin` ftvar_in_pskl P ->
  False.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros X0 Heq Hwf HXΔ HXb Hdef Hftv; try discriminate Heq.
  - (* var *)
    inversion Heq; subst. simpl in Hftv. clear - Hftv; fsetdec.
  - (* hole: Δ ∩ ftvar(var X0) = ∅ vs X0 ∈ Δ *)
    subst ψ. simpl in H0. clear - H0 HXΔ; fsetdec.
  - (* tophole_remove *)
    simpl in Hftv. eapply IHad_partial_precise; eauto.
  - (* flex_l: subject var α unfolds to its Θ-scoped definition *)
    eapply IHad_partial_precise; eauto.
    pose proof (ptyp_to_pskl_ftv τ) as Hp.
    pose proof (Hdef _ _ H) as Hd. clear - Hp Hd; fsetdec.
  - (* flex_r: X0 both rigid and defined-flexible — wf-uniq clash *)
    inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H HXb (a_wf_aenv_uniq Hwf)) as Habs.
    discriminate Habs.
Qed.

(** THE LEAF INVERSION ([paper-gap]: the paper's positional side condition
    "P_i has the same rigid variable in the same position", recovered from
    the freshness of the replaced variable): at target [var X] with
    [X ∈ Δ], [X] rigid in Θ, [X] avoided by Θ's definition images and by
    the subject's ⊤◇-shielded variables, the subject IS [var X] and the
    solved tags are empty. *)
Lemma ad_ppre_delta_var_inv : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall X, ψ = uskl_var_f X ->
  a_wf_aenv Θ ->
  X `in` Δ ->
  binds X abind_tvar Θ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     X `notin` ftvar_in_ptyp τ) ->
  X `notin` pskl_shielded_ftv P ->
  P = pskl_var_f X /\ Ψ [=] empty.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros X0 Heq Hwf HXΔ HXb Hdef Hsh; try discriminate Heq.
  - (* var *)
    inversion Heq; subst. split; [ reflexivity | assumption ].
  - (* hole: blocked by Δ-disjointness *)
    exfalso. subst ψ. simpl in H0. clear - H0 HXΔ; fsetdec.
  - (* tophole_remove: the body is wholly shielded — absent-lemma kills *)
    exfalso. simpl in Hsh.
    eapply ad_ppre_var_target_absent; eauto.
  - (* flex_l: the unfolded definition is X0-free — absent-lemma kills *)
    exfalso.
    eapply (ad_ppre_var_target_absent H0 Heq Hwf HXΔ HXb Hdef).
    pose proof (ptyp_to_pskl_ftv τ) as Hp.
    pose proof (Hdef _ _ H) as Hd. clear - Hp Hd; fsetdec.
  - (* flex_r: rigidity clash *)
    exfalso. inversion Heq; subst.
    pose proof (binds_unique _ _ _ _ _ H HXb (a_wf_aenv_uniq Hwf)) as Habs.
    discriminate Habs.
Qed.

(* ===================================================================== *)
(*  Solve-cluster context transport + rigid-variable rename.               *)
(*  The -var lemmas conclude at Θ0; their binder cases get IH conclusions  *)
(*  at (β~tvar)++Θ0 and must strengthen back, then reassemble the          *)
(*  cofinite SE/SS-Forall premises from a single fresh witness by rename.  *)
(* ===================================================================== *)

(** Generic context change: the solve judgments consult Θ only through
    [binds _ abind_flex_mono] (positively) and [a_flex] (negatively). *)
Lemma a_solve_sub_eq_ctx_change :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     forall Θ',
     (forall α, binds α abind_flex_mono Θ -> binds α abind_flex_mono Θ') ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     Θ' ⊢ₛ P ≼[ m ] Q ⤳ P') /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     forall Θ',
     (forall α, binds α abind_flex_mono Θ -> binds α abind_flex_mono Θ') ->
     (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
     Θ' ⊢ₑ P ∼ Q ⤳ P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve [ econstructor; eauto ].
  - (* SE-FlexR *)
    match goal with
      Hb : binds _ abind_flex_mono _,
      Hnf : a_non_flex _ _,
      Hmono : forall _ : atom, binds _ _ _ -> binds _ _ _,
      Hfl : forall _ : pskl, a_flex _ _ -> a_flex _ _ |- _ =>
        destruct Hnf as [Hlc Hnf'];
        apply a_solve_eq__flex_r; [ apply Hmono; exact Hb | ];
        split; [ exact Hlc | intro Hf; exact (Hnf' (Hfl _ Hf)) ]
    end.
Qed.

(** Strengthening: drop a rigid tvar cons. *)
Lemma a_solve_eq_strengthen_tvar : forall β Θ0 P Q P',
  ((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ Q ⤳ P' ->
  Θ0 ⊢ₑ P ∼ Q ⤳ P'.
Proof.
  intros β Θ0 P Q P' H.
  eapply (proj2 a_solve_sub_eq_ctx_change); [ exact H | | ].
  - intros α Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
      [ discriminate Habs | exact Hb' ].
  - intros P0 Hf; inversion Hf; subst.
    + apply a_flex__var with (α := α); unfold binds; simpl; right; auto.
    + apply a_flex__var_def with (α := α) (τ := τ);
        unfold binds; simpl; right; auto.
Qed.

Lemma a_solve_sub_strengthen_tvar : forall β Θ0 m P Q P',
  ((β ~ abind_tvar) ++ Θ0) ⊢ₛ P ≼[ m ] Q ⤳ P' ->
  Θ0 ⊢ₛ P ≼[ m ] Q ⤳ P'.
Proof.
  intros β Θ0 m P Q P' H.
  eapply (proj1 a_solve_sub_eq_ctx_change); [ exact H | | ].
  - intros α Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
      [ discriminate Habs | exact Hb' ].
  - intros P0 Hf; inversion Hf; subst.
    + apply a_flex__var with (α := α); unfold binds; simpl; right; auto.
    + apply a_flex__var_def with (α := α) (τ := τ);
        unfold binds; simpl; right; auto.
Qed.

(** Weakening: add a rigid tvar cons. *)
Lemma a_solve_eq_weaken_tvar : forall β Θ0 P Q P',
  Θ0 ⊢ₑ P ∼ Q ⤳ P' ->
  ((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ Q ⤳ P'.
Proof.
  intros β Θ0 P Q P' H.
  eapply (proj2 a_solve_sub_eq_ctx_change); [ exact H | | ].
  - intros α Hb; unfold binds; simpl; right; exact Hb.
  - intros P0 Hf; inversion Hf; subst;
      match goal with
        Hb : binds _ _ ((_ ~ abind_tvar) ++ _) |- _ =>
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
          [ discriminate Habs
          | solve [ eapply a_flex__var; exact Hb'
                  | eapply a_flex__var_def; exact Hb' ] ]
      end.
Qed.

(** Rename preserves non-flexibility when both names are fresh from Θ. *)
Lemma a_non_flex_rename : forall Θ P X Y,
  X `notin` dom Θ -> Y `notin` dom Θ ->
  a_non_flex Θ P ->
  a_non_flex Θ (subst_pskl_in_pskl (pskl_var_f Y) X P).
Proof.
  intros Θ P X Y HX HY [Hlc Hnf].
  split.
  - apply subst_pskl_in_pskl_lc_pskl; [ exact Hlc | constructor ].
  - intros Hf.
    destruct P; simpl in Hf; try solve [ inversion Hf ].
    match type of Hf with context [ if ?e then _ else _ ] =>
      destruct e end.
    + inversion Hf; subst;
        match goal with Hb : binds _ _ Θ |- _ =>
          apply binds_In in Hb; contradiction end.
    + apply Hnf; exact Hf.
Qed.

(** Rename preserves guardedness ([var Y] is guarded). *)
Lemma guarded_pskl_rename : forall A X Y,
  guarded_pskl A ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f Y) X A).
Proof.
  intros A X Y Hg; inversion Hg; subst; simpl.
  - constructor.
  - match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      constructor.
  - constructor;
      (apply subst_pskl_in_pskl_lc_pskl;
        [ assumption | apply lc_pskl_var_f ]).
Qed.

(** Rigid-variable rename through the solve judgments (X, Y fresh from Θ,
    so the flex rules are untouched). *)
Lemma a_solve_sub_eq_rename :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     forall X Y, X `notin` dom Θ -> Y `notin` dom Θ ->
     Θ ⊢ₛ (subst_pskl_in_pskl (pskl_var_f Y) X P) ≼[ m ]
          (subst_pskl_in_pskl (pskl_var_f Y) X Q)
          ⤳ (subst_pskl_in_pskl (pskl_var_f Y) X P')) /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     forall X Y, X `notin` dom Θ -> Y `notin` dom Θ ->
     Θ ⊢ₑ (subst_pskl_in_pskl (pskl_var_f Y) X P)
        ∼ (subst_pskl_in_pskl (pskl_var_f Y) X Q)
        ⤳ (subst_pskl_in_pskl (pskl_var_f Y) X P')).
Proof.
  apply a_solve_sub_eq_mutind; intros; simpl;
    (* var-subject rules: the substituted subject is still a var *)
    try solve
      [ match goal with |- context [ if ?e then _ else _ ] => destruct e end;
        constructor
      | constructor ].
  - (* SS-ForallL *)
    apply a_solve_sub__forall_l with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    apply H; [ clear - Hβ; fsetdec | assumption | assumption ].
  - (* SS-UnivGhostL *)
    apply a_solve_sub__univ_ghost_l; apply H; assumption.
  - (* SS-Check *)
    apply a_solve_sub__check;
      [ apply guarded_pskl_rename; assumption
      | apply guarded_pskl_rename; assumption
      | apply H; assumption ].
  - (* SS-ForallR *)
    apply a_solve_sub__forall_r with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var B (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    apply H; [ clear - Hβ; fsetdec | assumption | assumption ].
  - (* SS-Arrow *)
    apply a_solve_sub__arrow; [ apply H | apply H0 ]; assumption.
  - (* SS-GhostLF *)
    apply a_solve_sub__ghost_l_fn; [ apply H | apply H0 ]; assumption.
  - (* SS-GhostL *)
    apply a_solve_sub__ghost_l; apply guarded_pskl_rename; assumption.
  - (* SE-FlexR *)
    assert (Hne : α <> X)
      by (apply binds_In in b; intro Heq; subst; contradiction).
    match goal with |- context [ if ?e then _ else _ ] => destruct e end;
      [ exfalso; congruence | ].
    apply a_solve_eq__flex_r;
      [ assumption | apply a_non_flex_rename; assumption ].
  - (* SE-Arrow *)
    apply a_solve_eq__arrow; [ apply H | apply H0 ]; assumption.
  - (* SE-Forall *)
    apply a_solve_eq__forall with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    apply H; [ clear - Hβ; fsetdec | assumption | assumption ].
  - (* SE-UnivGhost *)
    apply a_solve_eq__tophole_both; apply H; assumption.
  - (* SE-GhostForall *)
    apply a_solve_eq__tophole_l_all with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var Q (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    specialize (H β ltac:(clear - Hβ; fsetdec) X Y H0 H1).
    simpl in H. exact H.
  - (* SE-GhostGuarded *)
    apply a_solve_eq__tophole_l_guarded;
      [ apply guarded_pskl_rename; assumption | apply H; assumption ].
  - (* SE-ForallGhost *)
    apply a_solve_eq__all_l_tophole with
      (L := L `union` singleton X `union` singleton Y).
    intros β Hβ.
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    rewrite (subst_pskl_in_pskl_open_pskl_wrt_pskl_var P' (pskl_var_f Y))
      by (solve [ clear - Hβ; fsetdec | constructor ]).
    specialize (H β ltac:(clear - Hβ; fsetdec) X Y H0 H1).
    simpl in H. exact H.
  - (* SE-GuardedGhost *)
    apply a_solve_eq__tophole_r_guarded;
      [ apply guarded_pskl_rename; assumption | apply H; assumption ].
Qed.

(* ===================================================================== *)
(*  Shape/tags helpers for the special cases (P0 = □; synthesized Q).      *)
(* ===================================================================== *)

(** Syn-paintings are synthesized skeletons. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
  lc_pskl P -> is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_sskl__all with (L := {}).
  intros X _. rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** Refining the hole yields a synthesized skeleton (paper: "by inversion
    on the refinement premise, Q is a synthesised skeleton"). *)
Lemma ad_refine_syn_hole_sskl : forall Θ Δ Qh Q,
  Θ ⨟ Δ ⊢ᵣᵃ Qh ⊳ Q ->
  Qh = bskl_hole ->
  is_sskl Q.
Proof.
  intros Θ Δ Qh Q H; induction H; intros Heq; try discriminate Heq.
  - (* hole *)
    apply is_sskl_pskl_to_bskl_syn.
    eapply a_wf_pskl_lc; eassumption.
  - (* flex_r *)
    apply is_sskl__var.
Qed.

(** Consistency against a synthesized target solves no tags (the only
    tag-consuming rule targets [all_inh]). *)
Lemma ad_pat_consis_sskl_tags : forall Ψ Θ S Q,
  Ψ ⨟ Θ ⊢ₛᵃ S ∼ Q ->
  a_wf_aenv Θ ->
  is_sskl Q ->
  Ψ [=] empty.
Proof.
  intros Ψ Θ S Q H; induction H; intros Hwf Hsk;
    try solve [ assumption | inversion Hsk ].
  - (* arrow *)
    inversion Hsk; subst.
    specialize (IHad_pat_consis1 Hwf ltac:(assumption)).
    specialize (IHad_pat_consis2 Hwf ltac:(assumption)).
    fsetdec.
  - (* forall_syn_tagged *)
    inversion Hsk; subst.
    match goal with HskB : forall X, X `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh X for (L `union` L0 `union` dom Θ);
      apply (H0 X ltac:(fsetdec));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  - (* forall_syn *)
    inversion Hsk; subst.
    match goal with HskB : forall X, X `notin` ?L0 -> is_sskl _ |- _ =>
      pick fresh X for (L `union` L0 `union` dom Θ);
      apply (H0 X ltac:(fsetdec));
      [ apply a_wf_aenv__tvar; [ fsetdec | exact Hwf ]
      | apply HskB; fsetdec ]
    end.
  - (* topholeg *)
    inversion Hsk; subst. apply IHad_pat_consis; assumption.
  - (* tophole *)
    inversion Hsk; subst. apply IHad_pat_consis; assumption.
  - (* tophole_drop *)
    apply IHad_pat_consis; assumption.
  - (* flex_l *)
    apply IHad_pat_consis; assumption.
  - (* flex_r *)
    apply IHad_pat_consis; [ assumption | ].
    unfold ptyp_to_bskl_syn.
    apply is_sskl_pskl_to_bskl_syn.
    apply lc_ptyp_to_pskl.
    eapply a_wf_ptyp_lc.
    eapply a_wf_aenv_binds_def_wf; eassumption.
Qed.

(* ===================================================================== *)
(*  Shielded-variable bounds through solving (chaining the freshness       *)
(*  pack through a_solve_cstr / the arrow case).                           *)
(* ===================================================================== *)

Lemma pskl_shielded_ftv_open_rec_lower : forall P V k,
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k V P).
Proof.
  induction P; intros V k; simpl; try fsetdec.
  - pose proof (IHP1 V k); pose proof (IHP2 V k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_lower P V k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_rec_upper : forall P V k,
  pskl_shielded_ftv (open_pskl_wrt_pskl_rec k V P) [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl V.
Proof.
  induction P; intros V k; simpl; try fsetdec.
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl;
      try fsetdec.
    pose proof (pskl_shielded_ftv_sub_ftv V); fsetdec.
  - pose proof (IHP1 V k); pose proof (IHP2 V k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_rec_upper P V k); fsetdec.
Qed.

Lemma pskl_shielded_ftv_open_lower : forall P V,
  pskl_shielded_ftv P [<=]
  pskl_shielded_ftv (open_pskl_wrt_pskl P V).
Proof. intros; apply pskl_shielded_ftv_open_rec_lower. Qed.

Lemma pskl_shielded_ftv_open_upper : forall P V,
  pskl_shielded_ftv (open_pskl_wrt_pskl P V) [<=]
  pskl_shielded_ftv P `union` ftvar_in_pskl V.
Proof. intros; apply pskl_shielded_ftv_open_rec_upper. Qed.

(** Solving bounds the output's shielded variables by the subject's
    shielded variables plus ALL of the target's variables. *)
Lemma a_solve_sub_eq_shielded :
  (forall Θ m P Q P', Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
     pskl_shielded_ftv P' [<=]
     pskl_shielded_ftv P `union` ftvar_in_pskl Q) /\
  (forall Θ P Q P', Θ ⊢ₑ P ∼ Q ⤳ P' ->
     pskl_shielded_ftv P' [<=]
     pskl_shielded_ftv P `union` ftvar_in_pskl Q).
Proof.
  apply a_solve_sub_eq_mutind; intros; simpl in *;
    (* ⊤◇-bodied outputs: switch to the ftv bound *)
    try solve
      [ fsetdec
      | match goal with
        | Hs : _ ⊢ₛ ?P0 ≼[ _ ] ?Q0 ⤳ ?P0' |- _ =>
            pose proof (a_solve_sub_ftv Hs)
        | He : _ ⊢ₑ ?P0 ∼ ?Q0 ⤳ ?P0' |- _ =>
            pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ He)
        end; fsetdec
      | pose proof (pskl_shielded_ftv_sub_ftv Q); fsetdec ].
  - (* SS-ForallL: ∀P ≼ Q ⤳ ∀P' *)
    pick fresh β for
      (L `union` pskl_shielded_ftv P' `union` pskl_shielded_ftv P).
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SS-ForallR: target opens *)
    pick fresh β for (L `union` pskl_shielded_ftv P').
    specialize (H β ltac:(fsetdec)).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SS-GhostLF: output ⊤◇(P1'→P2') *)
    match goal with
      He1 : _ ⊢ₑ pskl_hole ∼ _ ⤳ _, Hs2 : _ ⊢ₛ pskl_hole ≼[ _ ] _ ⤳ _ |- _ =>
        pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ He1);
        pose proof (a_solve_sub_ftv Hs2)
    end.
    simpl in *. fsetdec.
  - (* SE-Forall *)
    pick fresh β for
      (L `union` pskl_shielded_ftv P' `union` pskl_shielded_ftv P).
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f β)).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SE-GhostForall: subject stays ⊤◇P *)
    pick fresh β for (L `union` pskl_shielded_ftv P').
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)).
    simpl in *. fsetdec.
  - (* SE-GhostGuarded: subject ⊤◇P peels *)
    pose proof (pskl_shielded_ftv_sub_ftv P).
    simpl in *. fsetdec.
  - (* SE-ForallGhost *)
    pick fresh β for
      (L `union` pskl_shielded_ftv P' `union` pskl_shielded_ftv P).
    specialize (H β ltac:(fsetdec)).
    pose proof (pskl_shielded_ftv_open_lower P' (pskl_var_f β)).
    pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f β)).
    simpl in *. fsetdec.
Qed.

(* ===================================================================== *)
(*  msubst-avoidance: a variable fresh from θ's images survives msubst.    *)
(* ===================================================================== *)

Lemma msubst_lookup_ftv_avoid : forall θ X Y,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  X `in` ftvar_in_ptyp (msubst_lookup θ Y) ->
  Y = X.
Proof.
  induction θ as [ | [Z τ] θ' IH ]; intros X Y Hav HX; simpl in HX.
  - clear - HX; fsetdec.
  - destruct (Y == Z) as [Heq | Hne].
    + exfalso. apply (Hav (Z, τ) (or_introl eq_refl)). exact HX.
    + apply IH; [ intros p Hp; apply Hav; right; exact Hp | exact HX ].
Qed.

Lemma msubst_pskl_ftv_avoid : forall θ P X,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  X `notin` ftvar_in_pskl P ->
  X `notin` ftvar_in_pskl (msubst_pskl θ P).
Proof.
  intros θ P X Hav.
  induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hni HX; simpl in *.
  - fsetdec.
  - fsetdec.
  - (* var *)
    pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup θ Y)) as Hp.
    assert (HX' : X `in` ftvar_in_ptyp (msubst_lookup θ Y))
      by (clear - HX Hp; fsetdec).
    apply msubst_lookup_ftv_avoid in HX'; [ subst | exact Hav ].
    clear - Hni; fsetdec.
  - apply AtomSetImpl.union_1 in HX; destruct HX as [HX | HX];
      [ apply IHa | apply IHb ];
      solve [ clear - Hni; fsetdec | exact HX ].
  - apply IHall; [ clear - Hni; fsetdec | exact HX ].
  - fsetdec.
  - apply IHt; [ clear - Hni; fsetdec | exact HX ].
Qed.

(** Monotype paintings shield nothing. *)
Lemma pskl_shielded_ftv_ptyp_to_pskl : forall A,
  pskl_shielded_ftv (ptyp_to_pskl A) [=] {}.
Proof. induction A; simpl; fsetdec. Qed.

Lemma msubst_pskl_shielded_avoid : forall θ P X,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  X `notin` pskl_shielded_ftv P ->
  X `notin` pskl_shielded_ftv (msubst_pskl θ P).
Proof.
  intros θ P X Hav.
  induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hni HX; simpl in *.
  - fsetdec.
  - fsetdec.
  - (* var: the image is a painting — nothing shielded *)
    pose proof (pskl_shielded_ftv_ptyp_to_pskl (msubst_lookup θ Y)) as He.
    clear - He HX; fsetdec.
  - apply AtomSetImpl.union_1 in HX; destruct HX as [HX | HX];
      [ apply IHa | apply IHb ];
      solve [ clear - Hni; fsetdec | exact HX ].
  - apply IHall; [ exact Hni | exact HX ].
  - fsetdec.
  - (* tophole: the whole body's ftv *)
    revert HX. apply msubst_pskl_ftv_avoid; [ exact Hav | exact Hni ].
Qed.

(** msubst-image of a var: recover the var (X avoided by θ's images). *)
Lemma msubst_pskl_var_inv : forall θ Pi X,
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  msubst_pskl θ Pi = pskl_var_f X ->
  Pi = pskl_var_f X.
Proof.
  intros θ Pi X Hav Heq.
  destruct Pi as [ | n | Y | | | | ]; simpl in Heq; try discriminate Heq.
  f_equal.
  assert (HX : X `in` ftvar_in_ptyp (msubst_lookup θ Y)).
  { pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup θ Y)) as Hp.
    rewrite Heq in Hp. simpl in Hp. clear - Hp; fsetdec. }
  eapply msubst_lookup_ftv_avoid; eassumption.
Qed.

(* ===================================================================== *)
(*  The packaged -var LEAF case (paper: <<If ψa is a rigid variable        *)
(*  substituted by ρ, then P_i = ψa.  The tag contexts Ψ_i and Ψ_a are     *)
(*  empty, and the goal follows from SE-Var (SS-Var), choosing             *)
(*  P_a = P_i and θ_a = θ.>>  consistency-proofs.tex:1249-1252).           *)
(*  Both P6-Cv and P6-Sv consume it: [SE-Var]/[SS-Var] fire on the         *)
(*  recovered var subject against ANY target.                              *)
(* ===================================================================== *)

Lemma p6_leaf_var : forall NM Θ θ Pi Δ X Ψ' Ψi Ψna,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' (uskl_var_f X) ->
  Ψi [<=] Ψ' ->
  Ψna [<=] Ψ' ->
  X `in` Δ ->
  binds X abind_tvar Θ ->
  (forall p, In p θ -> X `notin` ftvar_in_ptyp (snd p)) ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     X `notin` ftvar_in_ptyp τ) ->
  X `notin` pskl_shielded_ftv Pi ->
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f X) ->
  Pi = pskl_var_f X /\
  Ψi [=] empty /\
  Ψna [=] empty /\
  Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi `union` Ψna ] (uskl_var_f X).
Proof.
  intros NM Θ θ Pi Δ X Ψ' Ψi Ψna
    Hwf Htag HΨi HΨna HXΔ HXb Hθav Hdef Hsh Hpre.
  assert (Hshθ : X `notin` pskl_shielded_ftv (msubst_pskl θ Pi))
    by (apply msubst_pskl_shielded_avoid; assumption).
  destruct (ad_ppre_delta_var_inv Hpre eq_refl Hwf HXΔ HXb Hdef Hshθ)
    as [Heqm HΨie].
  assert (HeqPi : Pi = pskl_var_f X)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htag))).
  split; [ exact HeqPi | ].
  split; [ exact HΨie | ].
  split; [ clear - HΨna HΨ'e; fsetdec | ].
  rewrite Heqm.
  apply ad_ppre__var; [ clear - HΨie HΨna HΨ'e; fsetdec | left; exact HXΔ ].
Qed.
