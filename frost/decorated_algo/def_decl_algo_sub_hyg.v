(** TAG-HYGIENIC FUEL MIRROR of [ad_pat_sub] (completeness-only).

    [ad_pat_sub_g] refines [ad_pat_sub_n] (def_decl_algo_sub.v) in two ways,
    both forced by precision-substitution
    (docs/DESIGN-completeness-subtyping.md §5.4):

    1. TAG HYGIENE.  The paper's ForallL side condition [fresh Ψ'] means the
       instantiation's tags are GLOBALLY fresh; the [_n] mirror renders it
       only as freshness from the tag context, which does not survive the
       Arrow split (a tag can leave the context on one branch while the
       subject still carries it on the other), and precision-substitution
       is FALSE over such derivations.  Both ForallL rules therefore also
       require the instantiation's tags fresh from the SUBJECT's syntactic
       tags ([ftag_in_uskl], def_extra.v).

    2. FUEL DISCIPLINE.  Precision-substitution must be fuel-PRESERVING
       (the completeness ForallL case applies its induction hypothesis to
       the substituted premise, subtyping-proofs.tex:3416-3429), but the
       ghostier subject may carry extra [∀◇]-wrappers (UnivGhostL steps)
       or fold flexible definitions (FlexMono steps) that the original
       derivation does not have.  So: leaves conclude at ANY fuel,
       UnivGhostL/UnivGhostLG/FlexMono are NON-incrementing, and only
       Arrow/ForallR/ForallL increment — which is all the completeness
       measure needs (its ForallL premise still strictly decreases; the
       non-incrementing rules recurse on structural sub-derivations, so
       the main induction uses lex(fuel, derivation)).

    Bridges ([_g] erasure to the plain judgment; the renaming-based
    freshening [_n → _g]) live in prop_sub_complete.v / are deferred —
    see the DESIGN doc. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo_sub.

Set Implicit Arguments.

Inductive ad_pat_sub_g :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_g__infer : forall n NM Ψ Θ R Q,                  (* Infer *)
    Ψ [=] empty ->
    empty ⨟ Θ ⊢ₛᵃ R ∼ Q ->
    is_sskl Q ->
    ad_pat_sub_g n NM mode_ti Ψ Θ R Q
| ad_pat_sub_g__check : forall n Ψ Θ T B,                     (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    Ψ ⨟ Θ ⊢ₛᵃ T ∼ (pskl_to_bskl_inh B) ->
    ad_pat_sub_g n a_sub_mode_ty mode_tc Ψ Θ T (pskl_to_bskl_inh B)
| ad_pat_sub_g__forall_r : forall n L Ψ Θ T B,               (* ForallR (TY) *)
    (forall α, α `notin` L ->
       ad_pat_sub_g n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ)
         T (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    ad_pat_sub_g (S n) a_sub_mode_ty mode_tc Ψ Θ T (bskl_all_inh B)
| ad_pat_sub_g__univ_ghost_r : forall n Ψ Θ R Q,             (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    empty ⨟ Θ ⊢ₛᵃ R ∼ Q ->
    ad_pat_sub_g n a_sub_mode_sk mode_tc Ψ Θ R (bskl_tophole Q)
| ad_pat_sub_g__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    Ψ1 ⨟ Θ ⊢ₛᵃ R1 ∼ Q1 ->
    ad_pat_sub_g n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_g (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_g__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q, (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_etag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_g n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_g (S n) NM M Ψ Θ (uskl_all_etag ε R) Q
| ad_pat_sub_g__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q, (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_g n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_g (S n) NM M Ψ Θ (uskl_all_syn R) Q
| ad_pat_sub_g__ghost : forall n Ψ Θ M P,                     (* Ghost (SK) *)
    Ψ [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ uskl_hole (pskl_to_bskl_inh P)
| ad_pat_sub_g__ghostg : forall n Ψ Θ M,                      (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ uskl_holeg bskl_hole
| ad_pat_sub_g__univ_ghost_l : forall n Ψ Θ M R Q,           (* UnivGhostL (SK) *)
    M <> mode_ti ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q
| ad_pat_sub_g__univ_ghost_lg : forall n Ψ Θ M R Q,          (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_g n a_sub_mode_sk M Ψ Θ (uskl_topholeg R) Q
| ad_pat_sub_g__flex_mono : forall n NM Ψ Θ M α τ Q,          (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_g n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_g n NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.

(* ===================================================================== *)
(*  LEAF-VALID variant [ad_pat_sub_gv] (completeness-only, P7's join).     *)
(*                                                                        *)
(*  Same rules as [ad_pat_sub_g], except the three CONSISTENCY-LEAF rows  *)
(*  — [__infer], [__check], [__univ_ghost_r] — additionally carry the     *)
(*  SUBJECT's refinement into the leaf's counterpart (for [UnivGhostR],   *)
(*  into the STRIPPED counterpart [Q], not [∀◇.Q]).                       *)
(*                                                                        *)
(*  WHY.  thm:complete-subtyping needs, at each leaf, exactly the third   *)
(*  solution condition of the AUGMENTED thm:complete-consistency          *)
(*  (consistency-proofs.tex:2230-2242) for the consistency subproblem it  *)
(*  invokes there — and that condition is NOT derivable from the paper's  *)
(*  two subtyping-solution conditions (the capture configuration          *)
(*  [(P0=◇, P=∀X.◇, Q=∀X.X)] passes both).  Stating it at the ROOT        *)
(*  instead — as one [⊢ᵣₚᵃ κ⌊S⌋ˢ ⊳ ⌊Q⌋] premise on the theorem — is       *)
(*  WRONG: refinement is a lockstep relation, so a root condition         *)
(*  excludes every solution whose sides disagree at a head through       *)
(*  ForallL / ForallR / UnivGhostR, i.e. instantiation and               *)
(*  generalisation themselves (machine-checked:                          *)
(*  cex/cex_p7_univ_ghost_r_vacuous.v, cex/cex_p7_third_premise_forall.v).*)
(*  The ghost leaves [__ghost] / [__ghostg] need no condition: they do    *)
(*  not invoke consistency completeness, and their subject's refinement   *)
(*  is derivable from the rule's own wf premise.                          *)
(*                                                                        *)
(*  [ad_pat_sub_gv_forget] recovers the plain mirror wherever leaf data   *)
(*  is not needed (in particular for every P5/P6 invocation).             *)
(* ===================================================================== *)

Inductive ad_pat_sub_gv :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_gv__infer : forall n NM Ψ Θ R Q,                 (* Infer *)
    Ψ [=] empty ->
    empty ⨟ Θ ⊢ₛᵃ R ∼ Q ->
    is_sskl Q ->
    Θ ⨟ empty ⊢ᵣₚᵃ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) ->
    ad_pat_sub_gv n NM mode_ti Ψ Θ R Q
| ad_pat_sub_gv__check : forall n Ψ Θ T B,                    (* Check (TY) *)
    guarded_uskl T ->
    guarded_pskl B ->
    Ψ ⨟ Θ ⊢ₛᵃ T ∼ (pskl_to_bskl_inh B) ->
    Θ ⨟ empty ⊢ᵣₚᵃ ⌊ T ⌋ˢ ⊳ B ->
    ad_pat_sub_gv n a_sub_mode_ty mode_tc Ψ Θ T (pskl_to_bskl_inh B)
| ad_pat_sub_gv__forall_r : forall n L Ψ Θ T B,              (* ForallR (TY) *)
    (forall α, α `notin` L ->
       ad_pat_sub_gv n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ)
         T (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    ad_pat_sub_gv (S n) a_sub_mode_ty mode_tc Ψ Θ T (bskl_all_inh B)
| ad_pat_sub_gv__univ_ghost_r : forall n Ψ Θ R Q,            (* UnivGhostR (SK) *)
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    empty ⨟ Θ ⊢ₛᵃ R ∼ Q ->
    Θ ⨟ empty ⊢ᵣₚᵃ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) ->
    ad_pat_sub_gv n a_sub_mode_sk mode_tc Ψ Θ R (bskl_tophole Q)
| ad_pat_sub_gv__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2, (* Arrow *)
    Ψ1 ⨟ Θ ⊢ₛᵃ R1 ∼ Q1 ->
    (* the DOMAIN premise is itself a consistency leaf — Sub-Arrow invokes
       thm:complete-consistency on it (:3334), so it carries the same
       subject-refinement data as [__infer] *)
    Θ ⨟ empty ⊢ᵣₚᵃ ⌊ R1 ⌋ˢ ⊳ (bskl_to_pskl Q1) ->
    ad_pat_sub_gv n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_gv (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_gv__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q, (* ForallL, β1=ε *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_etag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_gv n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_gv (S n) NM M Ψ Θ (uskl_all_etag ε R) Q
| ad_pat_sub_gv__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q, (* ForallL, β1=· *)
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
    ad_pat_sub_gv n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_gv (S n) NM M Ψ Θ (uskl_all_syn R) Q
| ad_pat_sub_gv__ghost : forall n Ψ Θ M P,                    (* Ghost (SK) *)
    Ψ [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ uskl_hole (pskl_to_bskl_inh P)
| ad_pat_sub_gv__ghostg : forall n Ψ Θ M,                     (* GhostG (SK) *)
    Ψ [=] empty ->
    mod_comp_sk bskl_hole M ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ uskl_holeg bskl_hole
| ad_pat_sub_gv__univ_ghost_l : forall n Ψ Θ M R Q,          (* UnivGhostL (SK) *)
    M <> mode_ti ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q
| ad_pat_sub_gv__univ_ghost_lg : forall n Ψ Θ M R Q,         (* UnivGhostLG (SK) *)
    M <> mode_ti ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ (uskl_topholeg R) Q
| ad_pat_sub_gv__flex_mono : forall n NM Ψ Θ M α τ Q,         (* FlexMono *)
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_gv n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_gv n NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.

(** Forgetting the leaf data recovers the plain hygienic mirror. *)
Lemma ad_pat_sub_gv_forget : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  ad_pat_sub_g n NM M Ψ Θ R Q.
Proof.
  intros * H; induction H; eauto using ad_pat_sub_g.
Qed.

(* ===================================================================== *)
(*  The three ERASURES + fuel monotonicity.                               *)
(*                                                                        *)
(*  ⚙ [ad_pat_sub_g_of] and [ad_pat_sub_gv_fuel_weaken] used to live in    *)
(*  algo/prop_completeness_sub_precise.v and algo/prop_completeness_sub.v. *)
(*  They moved here 2026-08-06: the SOUNDNESS side now has to CONCLUDE     *)
(*  [_gv] (hand-off §6.1/§6.2 — [ad_pat] / [ad_sd_typing] embed the        *)
(*  leaf-valid join, so thm:complete-skeleton/type-inference can consume   *)
(*  it), and algo/prop_soundness_sub.v sits BEFORE both completeness files *)
(*  in the dependency order.  Both are plain inductions over the mirrors   *)
(*  and need nothing this file does not already import.                    *)
(* ===================================================================== *)

(** Erase hygiene + fuel: a hygienic derivation is a plain one. *)
Lemma ad_pat_sub_g_of : forall n NM M Ψ Θ R Q,
  ad_pat_sub_g n NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q.
Proof.
  intros n NM M Ψ Θ R Q H. induction H.
  - eapply ad_pat_sub__infer; eauto.
  - eapply ad_pat_sub__check; eauto.
  - eapply ad_pat_sub__forall_r; eauto.
  - eapply ad_pat_sub__univ_ghost_r; eauto.
  - eapply ad_pat_sub__arrow; eauto.
  - eapply ad_pat_sub__forall_l_tagged; eauto.
  - eapply ad_pat_sub__forall_l_untagged; eauto.
  - eapply ad_pat_sub__ghost; eauto.
  - eapply ad_pat_sub__ghostg; eauto.
  - eapply ad_pat_sub__univ_ghost_l; eauto.
  - eapply ad_pat_sub__univ_ghost_lg; eauto.
  - eapply ad_pat_sub__flex_mono; eauto.
Qed.

(** Fuel monotonicity for the leaf-valid hygienic join.  The fuel is the
    declarative derivation's HEIGHT, so a derivation of height [n] is also
    one of every larger height.  Needed because the permutation below
    returns the family at whatever height the extraction yields, while
    [a_sub_complete_forall_r] wants it at exactly [n] for a conclusion at
    [S n]. *)
Lemma ad_pat_sub_gv_fuel_weaken : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  forall m, n <= m -> ad_pat_sub_gv m NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros m Hle;
    try solve [ econstructor; eauto ].
  - (* forall_r : the conclusion's fuel is [S n] *)
    destruct m as [ | m' ]; [ lia | ].
    apply ad_pat_sub_gv__forall_r with (L := L).
    intros α Hα. apply H0; [ exact Hα | lia ].
  - (* arrow *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__arrow;
      [ exact H | exact H0 | apply IHad_pat_sub_gv; lia | assumption ].
  - (* forall_l_tagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__forall_l_tagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_gv; lia ].
  - (* forall_l_untagged *)
    destruct m as [ | m' ]; [ lia | ].
    eapply ad_pat_sub_gv__forall_l_untagged;
      [ eassumption | eassumption | eassumption | eassumption | eassumption
      | apply IHad_pat_sub_gv; lia ].
Qed.

(** The composite erasure the [ad_pat] / [ad_sd_typing] consumers want:
    a leaf-valid join IS a plain declarative subtyping derivation. *)
Lemma ad_pat_sub_of_gv : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q.
Proof. intros * H. exact (ad_pat_sub_g_of (ad_pat_sub_gv_forget H)). Qed.

(** ⭐ THE LEAF-VALID JOIN WITH THE FUEL FORGOTTEN — what the
    declarative-in-algo judgements [ad_pat] / [ad_sd_typing] embed in their
    base rows (hand-off §6.2).  The fuel is an artefact of the completeness
    measure, so it has no business in a judgement's premise; what those rules
    must carry is the LEAF DATUM, which the capture configuration shows is not
    recoverable from a plain join (cex/cex_ad_pat_join_not_leaf_valid.v).

    ⚙ No notation, deliberately: like [ad_pat_sub_g] / [_gv] / [_n], this is a
    mech-internal variant of the paper's box, not a paper judgement. *)
Definition ad_pat_sub_v (NM : a_sub_mode) (M : mode) (Ψ : atoms)
    (Θ : aenv) (R : uskl) (Q : bskl) : Prop :=
  exists n, ad_pat_sub_gv n NM M Ψ Θ R Q.

(** A leaf-valid join IS a plain declarative subtyping derivation. *)
Lemma ad_pat_sub_of_v : forall NM M Ψ Θ R Q,
  ad_pat_sub_v NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q.
Proof. intros * [n H]. exact (ad_pat_sub_of_gv H). Qed.
