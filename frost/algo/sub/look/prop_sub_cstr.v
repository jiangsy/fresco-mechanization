(** P6-Ss — completeness of subtyping CONSTRAINT COLLECTION AND SOLVING
    (paper [lemma:complete-constraint-collection-solving],
    subtyping-proofs.tex:2202).  The subtyping twin of the closed P6-Cs
    ([a_lookeq_solve_complete], sub/look/prop_eq_cstr.v).

    ⚠️ THE PAPER'S STATEMENT INHERITS P6-Sv'S FALSITY.  Its first special
    case ("if P = α then S = α") applies P6-Sv WITH THE IDENTITY
    substitution, i.e. at Δρ = ∅ — exactly the configuration of
    [cex/cex_p6sv_forall_flex.v].  The witness transports directly: with
    the lookup variable α and S = R' = α the subject (κS)[ψa/α] IS ψa, and
    since [a_looksub] has NO FlexR rule, LS-Var is FORCED, so 𝒞 is the
    single subtyping constraint whose solving the counterexample refutes.
    This file therefore carries the SAME repair as P6-Sv; see
    docs/PAPER-GAPS.md and DESIGN-completeness-subtyping.md §8.

    THE REPAIR HERE IS A P0-ONLY WALK.  P6-Sv's [flex_shield] pairs P0 and
    ψa positionally, both descending together.  P6-Ss's recursion is
    different: ψa is FIXED (it is the single guess for α) while P0
    descends, so the pairing at a leaf is (P0-subterm, the WHOLE ψa).  Only
    two cases move P0 — Sub-Arrow takes the RIGHT component (the left one
    goes to P6-Cs, which needs no shield: consistency has no ForallL, so
    tags never become dirt there) and Sub-ForallR opens the body — and
    [flex_shield] supports only the second ([fsh_all_l]); [fsh_arrow]
    descends BOTH sides at once.  So the closure under those two descents
    is threaded, exactly as P6-Sv threads [flex_apart_walk]. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.deco_algo.prop_decorate_sub.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.consis.prop_consis_precise.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.sub.prop_soundness_sub.    (* a_wf_pskl_open *)
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.algo.sub.prop_completeness_sub_precise.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.sub.look.prop_rho_relation.
Require Import src.frost.algo.sub.look.prop_solve_ext.
Require Import src.frost.algo.sub.look.prop_flex_apart.
Require Import src.frost.algo.sub.look.prop_eq_var.

Set Implicit Arguments.

Require Import src.frost.algo.sub.look.prop_eq_cstr.
Require Import src.frost.algo.sub.look.prop_sub_var.

(* ===================================================================== *)
(*  ⭕⭕ [ss_step] / [ss_walk] / [sub_shield] AND THEIR KIT DELETED          *)
(*     (2026-08-05) — P6-Ss TAKES [flex_apart_deep] DIRECTLY                  *)
(*                                                                        *)
(*  [sub_shield] was the mech's repair of [lemma:complete-look]: P6-Cv's   *)
(*  [flex_apart] premise, indexed along an [ss_walk] that stepped [P0] and *)
(*  the SUBJECT in lockstep, with a positional guard on the guess-         *)
(*  descending half.  Under the authors' repaired [SolE-FlexR] the guarded *)
(*  half died (P6-Cv stopped consuming [flex_apart] at all), and what      *)
(*  remained was a SYNONYM for [flex_apart_deep]: derivable from it by       *)
(*  [flex_apart_deep_sub_shield] and yielding it back by                     *)
(*  [sub_shield_here_p0].  A synonym carrying its own walk index is pure   *)
(*  bookkeeping, so P6-Ss now takes [flex_apart_deep] itself.                *)
(*                                                                        *)
(*  ⚙ How each descent re-establishes it, for the record:                  *)
(*    · Sub-Arrow's right branch — [flex_apart_deep_step] at                 *)
(*      [p0step_arrow_r], then [flex_apart_deep_weaken_flex_prefix] twice.   *)
(*    · Sub-ForallR — [p0step_all] at the row's fresh binder, then         *)
(*      [flex_apart_deep_weaken_tvar].                                       *)
(*    · Sub-ForallL — P0 does NOT move; only Δρ grows, by a rigid fresh    *)
(*      for the guess, which is [flex_apart_deep_delta_grow].                *)
(*    · Sub-UnivGhostL/LG and every other row — neither P0 nor Δρ moves,   *)
(*      so the premise passes through unchanged.                           *)
(*                                                                        *)
(*  ⚠️ The ONE thing the walk bought that a plain closure does not: the     *)
(*  guarded conjunct's [fa_walk] had no guess-fixed arrow descent (it made *)
(*  the walk unsatisfiable), so THAT half could never be derived and had   *)
(*  to be assumed.  [flex_apart_deep] closes over [p0_step], which DOES have *)
(*  the arrow rows — which is why this collapse is possible at all.        *)
(*                                                                        *)
(*  Also deleted with it: [prop_sub_shield_supply.v] in full (its seven    *)
(*  supplies had no consumers once the premise became free at Δρ = ∅), and *)
(*  [sub_shield_empty].  Coq text at commit `4351531`.                     *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  Δ-SHRINKING for partial precision                                     *)
(* ===================================================================== *)

(** The mirror of [ad_partial_precise_delta_weaken_fresh]
    (sub/look/prop_rho_relation.v): a Δ-entry the TARGET does not mention can be
    dropped again.  Sub-ForallL needs both directions — it hands the IH the
    precision premise at [add β Δ] (β joins Δρ, and [Δρ ⊆ Δ]) and must
    return the IH's conclusion at plain Δ.

    Only two rows read Δ: [ad_ppre__var]'s disjunct, whose variable IS the
    target, so a target-fresh Δ-entry is never the one used; and
    [ad_ppre__hole]'s disjointness side condition, which is ANTITONE in Δ
    and so only gets easier.  (Unrestricted Δ-shrinking is of course fine
    for the □ row and false for the var row — hence the freshness.) *)
Lemma ad_partial_precise_delta_shrink_fresh : forall Θ Δf Ψ P ψ,
  {{ Θ ⨟ Δf ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Δ Δ', Δf [=] Δ `union` Δ' ->
  Δ' ∩ ftvar_in_uskl ψ [=] empty ->
  delta_def_fresh Δ' Θ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δf Ψ P ψ H; induction H; intros Δ0 Δ' Heq HΔ' Hdf.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; cbn [ftvar_in_uskl] in HΔ'; clear - HΔ Heq HΔ'; fsetdec
      | right; assumption ] end.
  - cbn [ftvar_in_uskl] in HΔ'.
    eapply ad_ppre__arrow;
      [ eapply (IHad_partial_precise1 Δ0 Δ');
          [ exact Heq | clear - HΔ'; fsetdec | exact Hdf ]
      | eapply (IHad_partial_precise2 Δ0 Δ');
          [ exact Heq | clear - HΔ'; fsetdec | exact Hdf ]
      | assumption ].
  - (* forall *)
    cbn [ftvar_in_uskl] in HΔ'.
    eapply ad_ppre__forall with (L := L `union` Δ'); [ | eassumption ].
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      cbn [ftvar_in_uskl] in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    (* Δ and Δ' MUST be pinned: left as evars the [=] goal below is an
       evar-fsetdec and does not terminate *)
    eapply (H0 α0 ltac:(clear - Hα0; solve_notin_auto) (add α0 Δ0) Δ');
      [ clear - Heq; fsetdec | exact HSX | exact Hdf ].
  - (* hole : the side condition is antitone in Δ *)
    apply ad_ppre__hole; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint Heq; fsetdec end.
  - apply ad_ppre__tophole_remove.
    eapply (IHad_partial_precise Δ0 Δ'); [ exact Heq | exact HΔ' | exact Hdf ].
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill with (L := L `union` Δ').
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      cbn [ftvar_in_uskl] in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    assert (Hdf' : delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ)).
    { intros β0 α3 τ3 Hβ0 Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdf β0 α3 τ3 Hβ0 Hb') ]. }
    eapply (H0 α0 ltac:(clear - Hα0; solve_notin_auto) Δ0 Δ');
      [ exact Heq | exact HSX | exact Hdf' ].
  - (* tophole_keep *)
    cbn [ftvar_in_uskl] in HΔ'.
    apply ad_ppre__tophole_keep.
    eapply (IHad_partial_precise Δ0 Δ');
      [ exact Heq | clear - HΔ'; fsetdec | exact Hdf ].
  - eapply ad_ppre__flex_l; [ eassumption | ].
    eapply (IHad_partial_precise Δ0 Δ'); [ exact Heq | exact HΔ' | exact Hdf ].
  - (* flex_r : the target hops to the definition's paint — this is the row
       [delta_def_fresh] is for, exactly as in the weakening twin *)
    eapply ad_ppre__flex_r; [ eassumption | ].
    eapply (IHad_partial_precise Δ0 Δ'); [ exact Heq | | exact Hdf ].
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
    apply atoms_inter_empty_pointwise.
    intros y Hy. eapply Hdf; [ exact Hy | eassumption ].
Qed.

(* ===================================================================== *)
(*  wf preservation for [a_solve_sub]                                     *)
(* ===================================================================== *)

(* RESTART NOTE (freshness campaign, DESIGN.md §4.3).  This is where
   [all_tvar] / [a_solve_eq_weaken_tvars] / [a_solve_sub_wf] used to live.

   [a_solve_sub_wf] claimed that sub-solving preserves well-formedness at the
   same context (modulo a rigid prefix Ξ the proof grew for SolS-ForallR).
   That is FALSE once SS-ForallR is faithful — its binder escapes into the
   output, and an escaped binder is a free variable the conclusion's context
   does not bind.  Machine-checked witness, at Ξ = · and Δ = ∅ (this file's
   own call configuration): cex/cex_solve_sub_wf_leak.v

       ◇ ≼[TC] ∀a. a ⤳ ∀◇ b        (SS-ForallR at b, then SS-GhostL)

   The lemma was an artefact of the mech, not of the paper: the paper's
   P6-Sv states [Θ0 ⊢ P_a] as one of its OWN conclusions
   (subtyping-proofs.tex:1737) and proves it inside the induction, carrying
   it at [Θ0,β] through the SolS-ForallR row and removing β there from
   [β ∉ ftv ψa] plus the PRECISION conclusion (:1897-1900).  So
   [a_solve_sub_complete_var] now returns it directly, and this file's α-stack
   row simply reads it off — closer to the paper than the mech was before. *)

(* ===================================================================== *)
(*  ψa SURVIVES INTO THE SUBJECT — the ForallL rows' tag bookkeeping       *)
(* ===================================================================== *)

(** [ad_pat_sub_g] renders the paper's GLOBAL freshness of an instantiation's
    tags as TWO conjuncts — freshness from the tag index and from the
    SUBJECT's syntactic tags (def_subtyping.v).  Sub-ForallL needs a
    third, freshness from ψa's tags Ψ', to keep the ρ-dirt bound
    [Ψρ ∩ Ψ' = ∅] as it absorbs the guess.  That is NOT a new side condition:
    the main induction runs under [α ∈ ftv R'], so ψa sits inside the ideal
    [(κR')[ψa/α]] — κ leaves α alone and substitution keeps the tags it
    inserts — and [uskl_rho] only ever ADDS tags going to the image
    ([uskl_rho_ftag_target_sub]).  Hence Ψ' ⊆ ftag Rsub, and the rule's own
    subject-freshness delivers the third conjunct. *)
Lemma ftag_in_uskl_subst_lower : forall ψ α R,
  α `in` ftvar_in_uskl R ->
  ftag_in_uskl ψ [<=] ftag_in_uskl (subst_uskl_in_uskl ψ α R).
Proof.
  intros ψ α R; induction R;
    cbn [ftvar_in_uskl subst_uskl_in_uskl ftag_in_uskl]; intros Hin;
    try solve [ clear - Hin; exfalso; fsetdec
              | specialize (IHR Hin); clear - IHR; fsetdec ].
  - (* var_f *)
    match goal with |- context [if ?c then _ else _] => destruct c end;
      [ clear; fsetdec | exfalso; clear - Hin n; fsetdec ].
  - (* arrow *)
    destruct (AtomSetProperties.In_dec α (ftvar_in_uskl R1)) as [H1 | H1];
      [ specialize (IHR1 H1); clear - IHR1; fsetdec
      | assert (H2 : α `in` ftvar_in_uskl R2) by (clear - Hin H1; fsetdec);
        specialize (IHR2 H2); clear - IHR2; fsetdec ].
Qed.

(** …and a variable outside κ's domain survives the metasubstitution. *)
Lemma msubst_uskl_syn_ftv_keep : forall κ α R,
  α `notin` dom κ ->
  α `in` ftvar_in_uskl R ->
  α `in` ftvar_in_uskl (msubst_uskl_syn κ R).
Proof.
  intros κ α R Hκ; induction R;
    cbn [ftvar_in_uskl msubst_uskl_syn]; intros Hin;
    try solve [ clear - Hin; exfalso; fsetdec
              | specialize (IHR Hin); clear - IHR; fsetdec ].
  - (* var_f : looks up to itself *)
    assert (Heq : α0 = α) by (clear - Hin; fsetdec); subst α0.
    rewrite (msubst_lookup_notin_dom _ Hκ). rewrite ptyp_to_uskl_syn_var.
    cbn [ftvar_in_uskl]; clear; fsetdec.
  - (* arrow *)
    destruct (AtomSetProperties.In_dec α (ftvar_in_uskl R1)) as [H1 | H1];
      [ specialize (IHR1 H1); clear - IHR1; fsetdec
      | assert (H2 : α `in` ftvar_in_uskl R2) by (clear - Hin H1; fsetdec);
        specialize (IHR2 H2); clear - IHR2; fsetdec ].
Qed.

(** NB the auxiliary fact behind the ForallL row below — an ABSENT subject
    collects nothing — is [a_looksub_lookeq_absent_nil] (prop_looksub.v §4),
    and the REVERSE of [lemma:constraint-collection-stable-substitution] it
    feeds is [a_looksub_subst_stable_rev] (prop_looksub.v §4b, Qed). *)

(** The two SPECIAL CASES of P6-Ss, factored out.  They are needed as a
    standalone lemma, not just at the top of the theorem: the main proof
    inducts on the SUBTYPING DERIVATION (P6-Cs's measure is unusable — see
    the theorem's header), and a recursive row can land on a special case
    (e.g. Sub-UnivGhostL at [R' = ∀◇α], whose erasure ∀◇α is not α, so the
    level above is NOT special while the level below is).  A measure
    induction would re-run the dispatch at every recursive use; a
    derivation induction cannot, because the derivation is consumed.  So
    every recursive site dispatches through this lemma instead. *)
(** The looksub twin of [a_lookeq_all_flex_mono]: [a_looksub] collects
    flexibles only through LS-Check and LS-Arrow's left premise, both of
    which are [a_lookeq]. *)
Lemma a_looksub_all_flex_mono : forall Θ α m P P0 Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] P0 ⤳ Ξ ⨾ 𝒞 }}a -> all_flex_mono Ξ.
Proof.
  intros Θ α m P P0 Ξ 𝒞 H; unfold all_flex_mono; induction H.
  - constructor.                                       (* LS-Var *)
  - constructor.                                       (* LS-Absent *)
  - constructor.                                       (* LS-Vacuous *)
  - eapply a_lookeq_all_flex_mono; eassumption.        (* LS-Check *)
  - assumption.                                        (* LS-ForallR *)
  - apply Forall_app; split;
      [ eapply a_lookeq_all_flex_mono; eassumption | assumption ]. (* LS-Arrow *)
  - assumption.                                        (* LS-ForallL *)
  - assumption.                                        (* LS-UnivGhostL *)
Qed.

(* ===================================================================== *)
(*  α-STACKS — Sub-ForallR's second branch                                *)
(*                                                                        *)
(*  [a_looksub__forall_r] is COFINITE in β with ONE [Ξ ⨾ 𝒞], so a          *)
(*  β-mentioning 𝒞 cannot be rebuilt from a single instance — and 𝒞 CAN   *)
(*  mention β: the sub-side analogue of [ad_pat_consis_target_ftv] is      *)
(*  FALSE at [ad_pat_sub_g__forall_l_tagged] (cex/cex_p6ss_sub_target_ftv  *)
(*  .v), because a ForallL guess is bounded only by [dom Θ] and            *)
(*  [ad_pat_sub_g__forall_r] grows that Θ by the very binder being         *)
(*  stripped.                                                             *)
(*                                                                        *)
(*  The escape: [ad_pat_sub_g__forall_r] forces [a_sub_mode_ty] +          *)
(*  [mode_tc], and NM is invariant along a derivation, so at (ty, tc) the  *)
(*  ONLY rows are [__check] (whose subtree is pure CONSISTENCY — no        *)
(*  guesses), [__forall_r] and [__forall_l_*].  Mirroring that on the      *)
(*  lookup side, the only descents that keep P are LS-ForallL and          *)
(*  LS-UnivGhostL, so under a Sub-ForallR the P6-Ss LEAF ([P = α]) is      *)
(*  reachable ONLY for a P of this shape — every other α-leaf sits under   *)
(*  LS-Check, i.e. inside P6-Cs, whose ftv-𝒞 bound is already ψa-relative. *)
(*  And such a P never needs to descend the target at all.                *)
(*  docs/DESIGN-completeness-subtyping.md §8 (h).                          *)
(* ===================================================================== *)

Inductive alpha_stack (α : atom) : pskl -> Prop :=
| ast_var : alpha_stack α (pskl_var_f α)
| ast_all : forall L P,
    (forall β, β `notin` L ->
       alpha_stack α (open_pskl_wrt_pskl P (pskl_var_f β))) ->
    alpha_stack α (pskl_all_syn P)
| ast_tophole : forall P,
    alpha_stack α P -> alpha_stack α (pskl_tophole P).

(** The stack's leaf is α itself, so a binder ≠ α is never reached and the
    shape is renaming-stable.  This is what lifts a SINGLE β-instance to
    [ast_all]'s cofinite family (Sub-ForallL hands back one instance). *)
Lemma alpha_stack_subst_var : forall α P β γ,
  alpha_stack α P -> β <> α ->
  alpha_stack α (subst_pskl_in_pskl (pskl_var_f γ) β P).
Proof.
  intros α P β γ H; induction H; intros Hne; cbn.
  - destruct_if; [ exfalso; congruence | apply ast_var ].
  - apply ast_all with (L := L `union` singleton β).
    intros β1 Hβ1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ1; fsetdec | apply lc_pskl_var_f ].
    apply H0; [ clear - Hβ1; solve_notin | exact Hne ].
  - apply ast_tophole; apply IHalpha_stack; exact Hne.
Qed.

Lemma alpha_stack_all_of_one : forall α P β,
  alpha_stack α (open_pskl_wrt_pskl P (pskl_var_f β)) ->
  β <> α -> β `notin` ftvar_in_pskl P ->
  alpha_stack α (pskl_all_syn P).
Proof.
  intros α P β Hst Hne Hfr.
  apply ast_all with (L := add β (add α (ftvar_in_pskl P))).
  intros β1 Hβ1.
  (* β ∉ ftv P, so opening at β1 IS the β-instance with β renamed *)
  rewrite (subst_pskl_in_pskl_intro β P (pskl_var_f β1)) by exact Hfr.
  apply alpha_stack_subst_var; assumption.
Qed.

(** THE POINT: an α-stack collects the WHOLE target, undescended, whatever
    that target is — LS-ForallL / LS-UnivGhostL peel the stack (both cofinite
    with a FIXED 𝒞, which is legal here because the target never moves) and
    LS-Var fires at the leaf.  So Sub-ForallR's stack branch never invokes
    LS-ForallR, and the β it would have had to strip is simply never
    introduced. *)
Lemma alpha_stack_looksub : forall α P,
  alpha_stack α P ->
  forall Θ m P0, {{ Θ ⊢ P ≼[ α , m ] P0 ⤳ nil ⨾ (a_cstr_sub m P0 :: nil) }}a.
Proof.
  intros α P H; induction H; intros Θ m P0.
  - apply a_looksub__var.
  - (* EXISTS-FRESH (cluster 3): pick the ONE binder here, avoiding the rule's
       own inputs, and run the α-stack's cofinite premise at it *)
    pick fresh β for
      (L `union` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
         `union` ftvar_in_pskl P0)).
    apply a_looksub__forall_l with (β := β);
      [ clear - Fr; solve_notin | apply H0; clear - Fr; fsetdec ].
  - apply a_looksub__univ_ghost_l; apply IHalpha_stack.
Qed.

(** THE MODE RESTRICTION, MACHINE-CHECKED.  [ad_pat_sub_g__forall_r] forces
    [a_sub_mode_ty] + [mode_tc], and NM is invariant along a derivation, so
    under a Sub-ForallR only three rows can fire: [__check], [__forall_r] and
    [__forall_l_*].  Hence the subject there is either GUARDED (the next step
    is [__check], whose subtree is pure CONSISTENCY — no guesses) or
    ∀-HEADED (the next step is [__forall_l]).

    In particular a ⊤◇ / ◇ / ◈ subject is IMPOSSIBLE at (ty, tc): stripping
    those needs [a_sub_mode_sk].  That is what lets Sub-ForallR's α-stack
    branch assume the stack is built from ∀s alone. *)
Lemma ad_pat_sub_g_ty_tc_subject : forall n Ψ Θ R Q,
  ad_pat_sub_g n a_sub_mode_ty mode_tc Ψ Θ R Q ->
  guarded_uskl R
  \/ (exists ε R0, R = uskl_all_tag ε R0)
  \/ (exists R0, R = uskl_all_syn R0).
Proof.
  intros n Ψ Θ R Q H.
  remember a_sub_mode_ty as NM eqn:HNM; remember mode_tc as M eqn:HM.
  induction H; try discriminate HNM; try discriminate HM.
  - (* Check : the rule's own premise *) left; assumption.
  - (* ForallR : the subject does not move, so the cofinite premise's own IH
       answers for it directly *)
    match goal with
    | IH : forall α, α `notin` ?L -> _ |- _ =>
        pick fresh α for L; apply (IH α ltac:(auto) HNM HM)
    end.
  - (* ForallL, tagged *) right; left; do 2 eexists; reflexivity.
  - (* ForallL, untagged *) right; right; eexists; reflexivity.
Qed.

Lemma a_looksub_solve_complete_leaf :
  forall n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  (* ⭐ THE Θw PACK (2026-08-05, the SolE-FlexR repair) — the same one P6-Cs
     and P6-Sv carry, and needed here because BOTH are called: the SOLVE now
     emits a block whose payloads must be well-formed in a context that
     predates every ∀ binder the induction opens.  [Θw] is FIXED; only the two
     [binds] conditions and the κ-image bound move.  [ψa] is FIXED across this
     induction too (only R' and P0 move), so its scope premise IS invariant
     here — unlike in P6-Sv, whose ForallL row moves the guess. *)
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  Δρ ∩ dom Θw [=] empty ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->       (* the paper's "Ψ disjoint from Ψ'" *)
  Ψi `union` Ψa [=] Ψ' ->                   (* the paper's Ψi,Ψa = Ψ' *)
  delta_def_fresh Δ Θ ->
  flex_apart_deep Θ0 Δρ P0 ψa ->              (* ⇐ THE REPAIR (see the header) *)
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* subject = the ρ-IMAGE of the paper's (κR')[ψa/α] (ρ = id ⇒ the paper's).
     ⚠️ The derivation lives in the SMALLER context [Θs]: Sub-ForallL runs the
     recursion at [Θ,β] while the derivation's own context is an INDEX and
     cannot move, so every other premise speaks of a [Θ] related to [Θs] only
     by binds-monotonicity ([Hext], the last premise).  At the top level and
     in every non-∀ row [Θs = Θ].  This is P6-Sv's device
     (sub/look/prop_sub_var.v:1674) and NOT P6-Cs's same-named one
     (whose [Θs] fixes the ρ-IMAGES' scope for the ftv-𝒞 bound — Phase B). *)
  ad_pat_sub_g n NM M Ψsub Θs Rsub Q ->
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  (* --- the ρ pack (all vacuous at ρ = identity) --- *)
  uskl_rho NM Θ Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  Ψρ ∩ Ψ' [=] empty ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (α `notin` ftvar_in_pskl P \/ P = pskl_var_f α) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  (* ⭐ THE AVOID-SET PARAMETER: the SOLVE generates its own block now, and at
     a binder row the witness must be fixed BEFORE that block is picked. *)
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\        (* looksub α P P0 𝒞 Ξc *)
    (* ⭐ the SOLVE's own block [Ξs] and its aligned extension [κs], stacked
       the way [a_extract__solve] (def_extra.v:764) consumes them *)
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\          (* solve 𝒞 Pi Ξs Pa *)
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    Forall (fun p => (ftvar_in_ptyp (snd p)) ∩ Δρ [=] empty) κc /\
    (* NB no [ftvar_in_cstrs] conjunct: the STRUCTURAL bound
       [ftv 𝒞 ⊆ ftv P0 ∪ dom Ξc] is already available to every consumer as
       [a_looksub_ftv] (prop_looksub.v).  P6-Cs carries a ψa-RELATIVE bound
       instead, because its ∀ rows need the collected constraints to avoid a
       fresh binder; whether P6-Ss's Sub-ForallR row can re-derive that is
       the open design point recorded at the [P = α] case below. *)
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (* PHASE B.  The collected constraints are ψa-RELATIVE — so a Sub-ForallR
       above can strip its fresh binder β from them (β is fresh for ψa, Ξc and
       κ, and is a rigid, hence not in [def_ftv Θ]).  UNLESS the lookup
       subject is an α-STACK, the one shape whose 𝒞 is [a_cstr_sub M P0] at
       whatever target it is handed — and that shape never needs LS-ForallR
       at all ([alpha_stack_looksub]), so the binder is never introduced.
       The [mode_tc] guard is what makes Sub-Arrow VACUOUS (its conclusion is
       [mode_fn M]); that is the row which could not otherwise concatenate a
       left disjunct with a right one.
       ⚠️ The disjunct-free bound is UNREACHABLE: its leaf would need a
       sub-side [ad_pat_consis_target_ftv], and that is FALSE at
       [ad_pat_sub_g__forall_l_tagged] — cex/cex_p6ss_sub_target_ftv.v.
       docs/DESIGN-completeness-subtyping.md §8 (h). *)
    (M = mode_tc ->
       ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                             `union` dom κ `union` def_ftv Θ
       \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil
           /\ 𝒞 = a_cstr_sub M P0 :: nil)).
Proof.
  intros n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr Hκw Hψaw HΔρw
         HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hdfresh Hapart Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine Hrho HΨρ Hrfr HΔρΔ HΔρPi Hspecial Hext L HL.
  destruct Hspecial as [Hnin | Heqα].
  - (* α ∉ ftv P : LS-Absent *)
  { assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
      { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
        clear - HαΘ Hb; fsetdec. }
      assert (HαMS : α `notin` ftvar_in_uskl (msubst_uskl_syn κ R')).
      { rewrite <- ftvar_in_pskl_uskl_to_pskl.
        rewrite uskl_to_pskl_msubst_uskl_syn. rewrite HeraseR.
        apply msubst_pskl_ftv_avoid; [ exact Hκav | exact Hnin ]. }
      (* under ρ the tag bound reads off the IMAGE, so ρ's own tags join it —
         and they are ⊥ Ψ' by [HΨρ], as R'-tags are by [Hdisj] *)
      rewrite (subst_uskl_in_uskl_fresh_eq (msubst_uskl_syn κ R') ψa α HαMS)
        in Hrho.
      assert (HΨsR : Ψsub [<=] ftag_in_uskl Rsub)
        by (apply (ad_pat_sub_g_ftag_sub Hsubty)).
      pose proof (uskl_rho_ftag_sub Hrho) as Hftr.
      rewrite ftag_in_uskl_msubst_uskl_syn in Hftr.
      assert (HΨa0 : Ψa [=] empty)
        by (clear - HΨs2 HΨsR Hftr Hdisj Hsub HΨρ; fsetdec).
      exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
      repeat split.
      - apply a_looksub__absent; exact Hnin.
      - simpl. apply a_solve_cstr__empty.
      - apply Forall_nil.
      - apply uniq_nil.
      - intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
      - apply Forall_nil.
      - simpl. exact HwfPi.
      - simpl. exact HwfΘ0.
      - simpl; clear; fsetdec.
      - apply Forall_nil.
      - apply Forall_nil.
      - simpl. exact Hκ.
      - simpl. apply a_inc_equiv_refl; exact Hκ.
      - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
      - simpl. eapply ad_partial_precise_psi_cong;
          [ exact Hpre | clear - HΨa0; fsetdec ].
      - (* ftv 𝒞 : LS-Absent collects nothing *)
        intros _; left; simpl; clear; fsetdec. }
  - (* P = α : LS-Var, then P6-Sv at ρ = IDENTITY.  NB not [subst P]: the
       erase-tie [⌊R'⌋ˢ = P] is also an equation on P, and [subst] would
       orient it the wrong way and discard it. *)
    rewrite Heqα in HeraseR |- *.
  { assert (Hlk : msubst_lookup κ α = ptyp_var_f α).
    { apply msubst_lookup_notin_dom.
      intro Hc. apply (a_inc_dom_sub Hκ) in Hc. contradiction. }
    assert (HR : R' = uskl_var_f α).
    { destruct R'; simpl in HeraseR; try discriminate HeraseR.
      injection HeraseR as ->. reflexivity. }
    subst R'.
    assert (Hms : msubst_uskl_syn κ (uskl_var_f α) = uskl_var_f α)
      by (cbn; rewrite Hlk; apply ptyp_to_uskl_syn_var).
    (* under ρ it is the IDEAL side of [Hrho] that collapses to ψa —
       [Hsubty] / [HwfSubj] are already in the shape P6-Sv wants *)
    rewrite Hms in Hrho.
    assert (Hsubj : subst_uskl_in_uskl ψa α (uskl_var_f α) = ψa).
    { cbn. match goal with |- context [if ?c then _ else _] => destruct c end;
        [ reflexivity | contradiction ]. }
    rewrite Hsubj in Hrho.
    cbn in HΨs1.        (* ftag_in_uskl (uskl_var_f α) = empty *)
    assert (Hlcψa : lc_uskl ψa)
      by (apply is_tskl_lc; inversion Htags; assumption).
    (* ⭕ (2026-08-05) THE GUESS-DESCENDING HALF IS GONE.  This was the ONLY
       row that consumed it — [R'] is pinned to [uskl_var_f α] here, the very
       position the guess replaces, so the positional guard was free.  P6-Sv
       no longer takes [flex_apart_walk] at all (under the repaired rule P6-Cv
       does not consume [flex_apart], and every use in P6-Sv was a relay into
       that premise), so nothing is read off the shield here. *)
    (* ⭐ P6-Sv now returns the whole [solve_sub_ext] package, at the SAME
       [Θw] and the SAME avoid-set [L] — the collection generates nothing on
       this row, so the solve's block IS the conclusion's. *)
    assert (Hsv : solve_sub_ext Θ0 Θw M Pi P0 L
                    (fun κ' Pa =>
                       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
                         ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad)).
    { eapply a_solve_sub_complete_var
        with (Δρ := Δρ) (Ψρ := Ψρ) (ψsub := Rsub) (Ψsub := Ψsub)
             (Θs := Θs);
      [ exact HwfΘ | exact HwfΘ0
      | exact HwfΘw | exact Hmon | exact Hnr | exact Hκw | exact HΔρw
      | exact HwfPi | exact HwfP0
      | exact HmodSK | exact HmodTY | exact Hκ
      | exact Hrho
      | exact Htags | exact HwfSubj | exact Hsub | exact HΨρ
      | exact Hrfr
      | exact HΔρΔ
      | exact HΔρPi
      | exact Hdfresh | exact Hpre
      | clear - HΨs1; fsetdec | exact HΨs2
      | exact Hext | exact Hsubty | exact Hrefine | exact HL ]. }
    destruct Hsv as (Ξs & Pa & κs & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
                     & HwfPa & Hprec).
    exists (a_cstr_sub M P0 :: nil), nil, Ξs, Pa, (@nil (atom * ptyp)), κs.
    repeat split.
    - apply a_looksub__var.
    - simpl. apply a_solve_cstr__sub; exact Hsolve.
    - exact Hfms.
    - exact Hus.
    - exact Hks.
    - exact Hfrs.
    - exact HFs.
    - (* the paper's [Θ0,Ξc ⊢ P_a] at Ξc = ·, read straight off P6-Sv, which
         states it (subtyping-proofs.tex:1737) — at [Ξs ++ Θ0] now *)
      simpl. exact HwfPa.
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - apply Forall_nil.
    - (* the a_inc: the collection block is empty, so only [κs] is prefixed *)
      simpl. apply a_inc_flex_prefix_build;
        [ exact Hfms | exact Hks
        | eapply forall_wf_mono_weaken; [ exact Hmon | exact HFs ]
        | exact Hκ ].
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. exact Hprec.
    - (* ftv 𝒞 : the RIGHT disjunct — [P = α] is the trivial α-stack, so this
         run never descends the target and 𝒞 is [a_cstr_sub M P0] whatever P0
         is.  (The LEFT bound genuinely fails here: the derivation's own
         ForallL can guess a variable ψa does not mention.) *)
      intros _; right;
        repeat split; try reflexivity; apply ast_var. }
Qed.

(* ===================================================================== *)
(*  P6-Ss — THE REPAIRED STATEMENT                                        *)
(*  [lemma:complete-constraint-collection-solving]                        *)
(* ===================================================================== *)

(** The premise set is P6-Cs's, plus the mode data ([M], [skmod]) that the
    subtyping side carries and the [sub_shield] repair.  Everything else —
    the erase-tie [⌊R'⌋ˢ = P], the scoping and tag-flow bounds, the
    subject's well-formedness (load-bearing: without it P6-Cs is FALSE,
    cex/cex_p6cs_subject_wf.v), and the conclusion's
    [𝒞 / Ξc / Pa / κc] bundle with its [keys] / [Forall] side conditions —
    is verbatim P6-Cs.

    ρ-GENERALIZED (Phase A, 2026-07-29).  Sub-ForallL cannot instantiate the
    IH the way the paper does — that step needs [κψ_b = ψ_b], which fails
    even for a legitimate κ (three machine-checked facts in
    cex/cex_p6ss_inc_compat.v).  The repair is P6-Sv's: carry an ACCUMULATED
    RIGID SUBSTITUTION ρ, so each Sub-ForallL opens with a FRESH RIGID β and
    absorbs its guess as [ρ ∘ [ψ_b/β]] ([uskl_rho_subst]); the subject is the
    ρ-IMAGE [Rsub] of the paper's ideal [(κR')[ψa/α]], and the theorem is the
    ρ = identity instance ([a_looksub_solve_complete], below).  Under ρ the
    lookup side stays on VAR-opened subjects, so LS-ForallL rebuilds through
    its cofinite family ([a_looksub_lookeq_rename_tvar]).

    TWO context parameters, and they are NOT the same device:
      · [Θs] — the DERIVATION's context (P6-Sv's, sub/look/prop_sub_var.v:1674).
        The ∀ rows must run the recursion at [Θ,β] while the derivation's own
        context is an INDEX and cannot move.
      · P6-Cs's [Θs] (the ρ-images' fixed scope, for its ftv-𝒞 conclusion) is
        NOT taken here: this statement has no ftv-𝒞 conjunct.  That is Phase B,
        and it is what Sub-ForallR needs. *)
Theorem a_looksub_solve_complete_gen :
  forall n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  (* ⭐ THE Θw PACK (2026-08-05, the SolE-FlexR repair) — the same one P6-Cs
     and P6-Sv carry, and needed here because BOTH are called: the SOLVE now
     emits a block whose payloads must be well-formed in a context that
     predates every ∀ binder the induction opens.  [Θw] is FIXED; only the two
     [binds] conditions and the κ-image bound move.  [ψa] is FIXED across this
     induction too (only R' and P0 move), so its scope premise IS invariant
     here — unlike in P6-Sv, whose ForallL row moves the guess. *)
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  Δρ ∩ dom Θw [=] empty ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->       (* the paper's "Ψ disjoint from Ψ'" *)
  Ψi `union` Ψa [=] Ψ' ->                   (* the paper's Ψi,Ψa = Ψ' *)
  delta_def_fresh Δ Θ ->
  flex_apart_deep Θ0 Δρ P0 ψa ->              (* ⇐ THE REPAIR (see the header) *)
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* subject = the ρ-IMAGE of the paper's (κR')[ψa/α] (ρ = id ⇒ the paper's),
     in the DERIVATION's context Θs (see the header) *)
  ad_pat_sub_g n NM M Ψsub Θs Rsub Q ->
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  (* --- the ρ pack (all VACUOUS at ρ = identity) --- *)
  uskl_rho NM Θ Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  Ψρ ∩ Ψ' [=] empty ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (* ρ's binders avoid the source and target skeletons.  ⚠️ NOT the stronger
     [Δρ ∩ dom Θ0 = ∅] P6-Cs used to take: with [κ ∷ Θ0 ⊑ Θ] and [rho_fresh]
     that forces Δρ = ∅ (cex/cex_p6cs_rho_delta_vacuous.v), and Sub-ForallL's
     β enters Θ0 and Θ TOGETHER ([a_inc_cons_tvar]) as well as Δρ. *)
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  (* THE IDEAL GUESS-SKELETON IS ρ-APART.  ψa is FIXED across this induction
     (only R' and P0 move), and every Sub-ForallL binder is picked fresh for
     it, so this is maintained by the one row that grows Δρ.  It is what makes
     P6-Cs's ftv-𝒞 output name no context — which Phase B's Sub-ForallR needs,
     since a nested Sub-ForallL's guess drags the stripped binder into the
     ρ-images' scope.  See docs/DESIGN-completeness-subtyping.md §8 (h). *)
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  (* ⭐ THE AVOID-SET PARAMETER: the SOLVE generates its own block now, and at
     a binder row the witness must be fixed BEFORE that block is picked. *)
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\        (* looksub α P P0 𝒞 Ξc *)
    (* ⭐ the SOLVE's own block [Ξs] and its aligned extension [κs], stacked
       the way [a_extract__solve] (def_extra.v:764) consumes them *)
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\          (* solve 𝒞 Pi Ξs Pa *)
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (* …and κc's images avoid the ρ-replaced variables — P6-Cs's new output
       conjunct, needed here for the same reason: Sub-Arrow's RIGHT branch
       runs at [Pi := Pa1] under [κc1 ++ κ] and must re-establish the
       ρ-freshness of its new Pi. *)
    Forall (fun p => (ftvar_in_ptyp (snd p)) ∩ Δρ [=] empty) κc /\
    (* NB no [ftvar_in_cstrs] conjunct: the STRUCTURAL bound
       [ftv 𝒞 ⊆ ftv P0 ∪ dom Ξc] is already available to every consumer as
       [a_looksub_ftv] (prop_looksub.v).  P6-Cs carries a ψa-RELATIVE bound
       instead, because its ∀ rows need the collected constraints to avoid a
       fresh binder; re-acquiring it here is Phase B, and it is what
       Sub-ForallR needs. *)
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (* PHASE B.  The collected constraints are ψa-RELATIVE — so a Sub-ForallR
       above can strip its fresh binder β from them (β is fresh for ψa, Ξc and
       κ, and is a rigid, hence not in [def_ftv Θ]).  UNLESS the lookup
       subject is an α-STACK, the one shape whose 𝒞 is [a_cstr_sub M P0] at
       whatever target it is handed — and that shape never needs LS-ForallR
       at all ([alpha_stack_looksub]), so the binder is never introduced.
       The [mode_tc] guard is what makes Sub-Arrow VACUOUS (its conclusion is
       [mode_fn M]); that is the row which could not otherwise concatenate a
       left disjunct with a right one.
       ⚠️ The disjunct-free bound is UNREACHABLE: its leaf would need a
       sub-side [ad_pat_consis_target_ftv], and that is FALSE at
       [ad_pat_sub_g__forall_l_tagged] — cex/cex_p6ss_sub_target_ftv.v.
       docs/DESIGN-completeness-subtyping.md §8 (h). *)
    (M = mode_tc ->
       ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                             `union` dom κ `union` def_ftv Θ
       \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil
           /\ 𝒞 = a_cstr_sub M P0 :: nil)).
Proof.
  intros n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr Hκw Hψaw HΔρw
         HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hdfresh Hapart Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext Hψaap
         L HL.
  (* ---------------------------------------------------------------- *)
  (* The two special cases go through [a_looksub_solve_complete_leaf],   *)
  (* which every recursive row of the induction below also calls.        *)
  (* ---------------------------------------------------------------- *)
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P)) as [Hin | Hnin];
    [ | eapply a_looksub_solve_complete_leaf;
        solve [ eassumption | left; exact Hnin ] ].
  destruct (pskl_eq_var_dec P α) as [Heqα | HPnα];
    [ eapply a_looksub_solve_complete_leaf;
        solve [ eassumption | right; exact Heqα ] | ].
  (* ---------------------------------------------------------------- *)
  (* Main induction: P ≠ α, α ∈ ftv P, and P is not a flexible variable  *)
  (* (that is the absent case).  Induct on the SUBTYPING DERIVATION —    *)
  (* NOT on P6-Cs's measure [size R' + size P0]: consistency's ∀ rules   *)
  (* open with a VARIABLE, but Sub-ForallL opens with the GUESS ψ_b, so  *)
  (* the subject can grow.                                              *)
  (*                                                                    *)
  (* Under ρ the derivation runs on the VARIABLE [Rsub], which           *)
  (* [induction] abstracts directly — so the pre-ρ [remember]/[HeqSub]   *)
  (* device is GONE: each row now reads R''s shape by [destruct R'] and  *)
  (* inverts [Hrho] (the ideal's shape is fixed by R', the rule fixes    *)
  (* [Rsub]'s, and mismatched pairs have no [uskl_rho] constructor).     *)
  (* ---------------------------------------------------------------- *)
  assert (Hακdom : α `notin` dom κ)
    by (intro Hc; apply (a_inc_dom_sub Hκ) in Hc; contradiction).
  assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
  { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
    clear - HαΘ Hb; fsetdec. }
  assert (HαR : α `in` ftvar_in_uskl R').
  { rewrite <- HeraseR in Hin. rewrite ftvar_in_pskl_uskl_to_pskl in Hin.
    exact Hin. }
  (* Θ0/κ are GENERALIZED (Sub-Arrow's right branch runs at [Ξc1,Θ0] with
     [κc1,κ] — the two constraint sets are solved in SEQUENCE), and so are
     Θ/Δ/Δρ/Ψρ (Sub-ForallL grows all four by its fresh rigid β). *)
  (* ⚠️ [Θw] is NOT reverted — it is the FIXED well-formedness context, and
     keeping it fixed under the ∀ rows is what lets a binder be stripped out
     of the increase.  Its companions DO move (each mentions a reverted
     variable) except [Hψaw], since ψa is fixed across this induction. *)
  revert Θ Θ0 κ Δ Δρ Ψρ R' P P0 Pi Ψi Ψa
         HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
         HαΘ0 Hκ Hακdom Hκav HeraseR HscopeR HlcR Hdisj
         HwfP0 HwfPi HmodSK HmodTY HαΘ Hsub HΨs1 HΨs2 Hdfresh Hapart Hpre
         Hrefine Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext
         HPnα Hin HαR HwfSubj Hψaap L HL.
  (* the lemma's [P] comes back as [P''] and its [Θ] as [Θe]: both are BINDER
     NAMES of the rules, so [induction] has already claimed them.  Renaming
     [Θe] back to [Θ] (and the rule's own context to [Θsm]) keeps every row
     textually unchanged — each rule premise stated in the SMALL context is
     weakened on the spot, exactly as P6-Sv does. *)
  induction Hsubty; intros
    Θe Θ0 κ Δ Δρ Ψρ R' P'' P0 Pi Ψi Ψa
    HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
    HαΘ0 Hκ Hακdom Hκav HeraseR HscopeR HlcR Hdisj
    HwfP0 HwfPi HmodSK HmodTY HαΘ Hsub HΨs1 HΨs2 Hdfresh Hapart Hpre
    Hrefine Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext
    HPnα Hin HαR HwfSubj Hψaap Lav HLav;
    rename Θ into Θsm; rename Θe into Θ.
  all: match goal with
       | Hx : forall x b, binds x b ?S -> binds x b _ |- _ =>
         repeat match goal with
         | H : {{ _ ⨟ S ⊢ˢ _ ∼ _ }}ad |- _ =>
             let H' := fresh "Hw" in
             pose proof (ad_pat_consis_weaken H _ Hx) as H';
             clear H; rename H' into H
         | H : {{ S ⨟ _ ⊢ₚₛ _ }}a |- _ =>
             let H' := fresh "Hw" in
             pose proof (a_wf_pskl_weaken Hx H) as H';
             clear H; rename H' into H
         | H : binds _ _ S |- _ => apply Hx in H
         end
       end.
  (* R' is NEVER a variable here: a var erases to [P = α] (the special
     case) or has α ∉ ftv, so the ρ-ideal's top constructor is R''s. *)
  all: assert (HRnv : forall β, R' <> uskl_var_f β);
    [ intros β Heq; subst R'; cbn in HαR;
      assert (Heqβ : β = α) by (clear - HαR; fsetdec); subst β;
      cbn in HeraseR; contradiction (HPnα (eq_sym HeraseR)) | ].
  - (* Infer : M = TI, so [skmod] forces P0 = □; LS-Vacuous collects
       nothing and the identity solve returns Pi.  The rule's Ψ = ∅ gives
       Ψa = ∅, so the conclusion's precision is the premise's. *)
    assert (HP0 : P0 = pskl_hole).
    { destruct NM;
        [ pose proof (HmodTY eq_refl) as Hm
        | pose proof (HmodSK eq_refl) as Hm ];
        inversion Hm; reflexivity. }
    subst P0.
    exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
    repeat split.
    + apply a_looksub__vacuous.
    + simpl. apply a_solve_cstr__empty.
    + apply Forall_nil.
    + apply uniq_nil.
    + intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
    + apply Forall_nil.
    + simpl. exact HwfPi.
    + simpl. exact HwfΘ0.
    + simpl; clear; fsetdec.
    + apply Forall_nil.
    + apply Forall_nil.
    + simpl. exact Hκ.
    + simpl. apply a_inc_equiv_refl; exact Hκ.
    + intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    + simpl. eapply ad_partial_precise_psi_cong;
        [ exact Hpre | assert (HΨae : Ψa [=] empty)
                         by (clear - HΨs2 H; fsetdec);
          clear - HΨae; fsetdec ].
    + (* ftv 𝒞 : no constraints *) intros _; left; simpl; clear; fsetdec.
  - (* Check : delegates WHOLE to P6-Cs ([a_lookeq_solve_complete]) on the
       consistency premise, then re-wraps with LS-Check.  LS-Check's side
       conditions: P ≠ α (HPnα) and P, P0 guarded. *)
    (* …and a TYPE, which is LS-Check's SORT premise *)
    assert (HgfP0 : pskl_ghost_free P0)
      by (apply a_ty_mode_compat_tc_ghost_free; exact (HmodTY eq_refl)).
    assert (HgP0 : guarded_pskl P0).
    { pose proof (HmodTY eq_refl) as Hmod.
      inversion Hmod as [ | A HeqA | ]; subst.
      destruct A as [ | nA | αA | A1 A2 | A0 ]; cbn [ptyp_to_pskl] in *.
      - apply guarded_pskl__unit.
      - inversion HwfP0.
      - apply guarded_pskl__var.
      - pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption.
      - (* ∀ : its inherited painting is a [bskl_all_inh], and the target is
           the inherited painting of a GUARDED B — which is never one *)
        exfalso.
        assert (HgQ : guarded_bskl (pskl_to_bskl_inh B))
          by (apply guarded_pskl_to_bskl_inh; exact H0).
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        destruct B; cbn [pskl_to_bskl_inh] in Hrefine, HgQ;
          try solve [ inversion HgQ ];
          inversion Hrefine; subst;
          solve [ eapply ad_refine_allinh_lhs_mono_absurd;
                    [ exact HwfΘ | eassumption | reflexivity | reflexivity
                    | eapply a_wf_aenv_binds_def_mono;
                        [ exact HwfΘ | eassumption ] ] ]. }
    (* the SUBJECT's guardedness transports to its erasure: R' is not a
       variable ([HRnv]), so the ρ-IDEAL's top constructor is R''s, ρ keeps
       that constructor (the [_r_inv] family), and a non-guarded shape
       contradicts the rule's [guarded_uskl T] *)
    assert (HgP : guarded_pskl P'').
    { rewrite <- HeraseR.
      destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
        cbn in Hrho |- *;
        try solve [ contradiction (HRnv _ eq_refl) | inversion HlcR
                  | inversion Hrho; subst; inversion H ].
      - apply guarded_pskl__unit.
      - inversion HlcR; subst.
        apply guarded_pskl__arrow; apply lc_uskl_to_pskl_local; assumption. }
    (* this [⊆] must be discharged OUTSIDE the [edestruct]: as a bullet it
       runs while Ψi and Ψa are still EVARS (the goal does not constrain the
       lemma's conclusion), and [fsetdec] on an evar goal does not
       terminate *)
    assert (Hsub' : Ψi `union` Ψa [<=] Ψ') by (clear - Hsub; fsetdec).
    (* the whole subject goes to P6-Cs — under ρ that is the GENERALIZED
       [a_lookeq_solve_complete_gen], at THIS ρ (the corollary would demand a
       ρ-free subject, which is exactly what a Sub-ForallL above destroys).
       P6-Cs's own [Θs] slot takes our [Θ]: it fixes the ρ-images' scope for
       an ftv-𝒞 conclusion this statement does not carry. *)
    (* the guess-FIXED conjunct, straight off the shield: no guard, since
       this closure never descends ψa (DESIGN §14.3) *)
    assert (Hfawp0 : flex_apart_deep Θ0 Δρ P0 ψa)
      by exact Hapart.
    edestruct (@a_lookeq_solve_complete_gen
                 (size_uskl R' + size_pskl P0)
                 a_sub_mode_ty Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψ ψa (pskl_to_bskl_inh B)
                 P'' P0 Pi R' α Θ Δρ Ψρ T)
      as (𝒞 & Ξc & Ξs & Pa & κc & κs
          & Hlook & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
          & HwfPa & HwfΞ & HαΞ & Hkeys
          & HFor & HForΔ & Hftv & Hinc & Heqv & Hκcfresh0 & Hprec);
      [ exact (le_n _) | exact HwfΘ | exact HwfΘ0
      | exact HwfΘw | exact Hmon | exact Hnr
      | exact HwfP0 | exact HwfPi | exact Hκ | exact Hκw | exact Hψaw
      | exact HαΘ | exact HαΘ0 | exact HeraseR
      | exact HscopeR | exact HlcR | exact Htags | exact Hdisj
      | exact Hsub' | exact Hdfresh | exact Hpre | exact HΨs1
      | exact HΨs2 | exact H1 | exact HwfSubj
      | exact Hrefine
      | exact Hrho | intros x b Hb; exact Hb | exact HΨρ | exact Hrfr
      | exact HΔρΔ | exact HΔρw | exact HΔρftv | exact HΔρPi | exact Hfawp0
      | exact Hψaap | exact HLav | ].
    (* P6-Cs's generated-names conjunct is STRONGER since cluster 3 (it also
       avoids [ftvar_in_uskl ψa]); P6-Ss states the weaker form, so drop the
       extra disjunct here rather than carry it through every row *)
    rename Hκcfresh0 into Hκcfresh.
    exists 𝒞, Ξc, Ξs, Pa, κc, κs.
    split;
      [ apply a_looksub__check;
          [ exact HgfP0 | exact HPnα | exact HgP | exact HgP0
          | exact Hlook ] | ].
    repeat split; try assumption.
    (* ftv 𝒞 : P6-Cs's own ψa-relative output — the LEFT disjunct, and this is
       why the Check row needed P6-Cs's bound to name no context *)
    intros _; left; exact Hftv.
  - (* ForallR : the refinement premise forces P0 = ∀β.P0'; descend with
       [sss_all] + [sub_shield_step], run the IH at Θ,β, rebuild with
       LS-ForallR, then strip β.

       THE β ∉ ftv 𝒞 OBLIGATION IS A MECH-ENCODING ARTEFACT, NOT A PAPER
       GAP (author resolution, 2026-07-29).  Constraint collection is
       deliberately scoping-AGNOSTIC; the scope check is the SEPARATE
       [Θ0,Ξ ⊢ P1] premise at the EXTRACT use site.  So \lslab{ForallR}
       carries no side condition and the paper's proof owes nothing.  The
       locally nameless [a_looksub__forall_r] is COFINITE in β with one
       [Ξ ⨾ 𝒞], which IS that side condition, so the mech rule is strictly
       narrower — KEEP IT: completeness of a NARROWER algorithm is a
       STRONGER theorem, and soundness is unaffected.

       Do NOT justify the cofinite rule by "the wf check catches a
       β-mentioning 𝒞 anyway" — the two encodings are NOT literally
       equivalent.  [a_solve_sub__var] is [α̂ ≼[m] Q ⤳ α̂]: it DISCARDS the
       target, so a 𝒞 mentioning β can solve to a β-FREE P1 that
       [Θ0,Ξ ⊢ P1] happily accepts.  The lax rule admits strictly more.

       WHAT THE ROW ACTUALLY NEEDS: re-acquire the ψa-RELATIVE bound P6-Cs
       carries as a conclusion,
         ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ,
       which this statement dropped; β is fresh for all four.  That route
       was thought closed ("Sub-ForallL instantiates with a GUESS bounded
       only by ftv ψb ⊆ dom Θ") — the ρ-GENERALIZED INDUCTION dissolves the
       objection: under ρ the lookup side never sees a guess, every ForallL
       opens with a fresh RIGID, and the constraints stay ψa-bounded exactly
       as on the consistency side.  ρ's binders live in Δρ; ForallR's β is a
       genuine context rigid, never a Δρ entry.  ⇒ ForallL and ForallR are
       fixed by the SAME change.  docs/PAPER-GAPS.md carries the record.

       THE ROUTE, AS EXECUTED (docs/DESIGN-completeness-subtyping.md §8 (h)).
       The ψa-relative bound alone is UNREACHABLE — its leaf needs a sub-side
       [ad_pat_consis_target_ftv], FALSE at [ad_pat_sub_g__forall_l_tagged]
       (cex/cex_p6ss_sub_target_ftv.v).  What the conclusion carries instead
       is the MODE-GUARDED DISJUNCTION, and this row consumes it:
         · LEFT  — β ∉ ftv 𝒞, so strip β from every output with P6-Cs's
                   ∀-binder kit and rebuild with LS-ForallR, exactly as the
                   Sub-ForallL rows do (only the renamed side differs: there
                   the SUBJECT moves, here the TARGET does).
         · RIGHT — P'' is an α-STACK, and such a run never descends the
                   target at all: [alpha_stack_looksub] collects
                   [a_cstr_sub tc P0] at the UNDESCENDED P0, so the binder is
                   never introduced.  The IH still supplies the solve, and
                   lifting it over the ∀ is P6-Sv's strengthen-then-rename
                   recipe (sub/look/prop_sub_var.v:2036). *)
    (* [skmod{TY}] makes P0 a TYPE, so the refinement's inherited-∀ target
       forces P0 = ∀.P0': every other type shape is GUARDED, and a guarded
       source refines only to a guarded target.  This block is P6-Sv's
       (sub/look/prop_sub_var.v:1880) verbatim. *)
    pose proof (HmodTY eq_refl) as Hmod.
    inversion Hmod as [ | A HeqA | ]; subst.
    destruct A as [ | nA | αA | A1 A2 | A0 ];
      cbn [ptyp_to_pskl] in HwfP0, Hrefine, Hapart, Hpre, HΔρftv |- *.
    + (* ⟨⟩ : guarded *)
      exfalso;
        assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc;
                [ exact Hκ | apply guarded_pskl__unit ] ]
        | inversion Hbad ].
    + (* a bound variable is not well-formed *) inversion HwfP0.
    + (* a variable : guarded *)
      exfalso;
        assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc;
                [ exact Hκ | apply guarded_pskl__var ] ]
        | inversion Hbad ].
    + (* an arrow : guarded *)
      exfalso.
      assert (Hg : guarded_pskl
                     (pskl_arrow (ptyp_to_pskl A1) (ptyp_to_pskl A2))).
      { pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption. }
      assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact Hg ] ]
        | inversion Hbad ].
    + (* P0 = ∀.P0' : the real row *)
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      match goal with Hr : forall α, α `notin` ?Lr -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
        rename Hr into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
      inversion HwfP0; subst.
      match goal with Hw : forall α, α `notin` ?Lw -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
        rename Hw into Hw0body; remember Lw as Lw0 eqn:HeqLw; clear HeqLw end.
      (* ONE fresh rigid β.  Unlike Sub-ForallL it does NOT join Δρ: β is a
         genuine context rigid, not a ρ-replaced variable. *)
      pick fresh β for
        (L `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
           `union` dom Θsm `union` dom κ `union` ftvar_in_uskl ψa
           `union` ftvar_in_uskl T `union` ftvar_in_pskl Pi
           `union` ftvar_in_uskl R' `union` ftvar_in_pskl ⌊ R' ⌋ˢ
           `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` def_ftv Θ
           (* the ∀ rule's own avoid-input (cluster 3) *)
           `union` ftvar_in_aenv Θ0
           `union` Δ `union` Δρ `union` singleton α).
      assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
      assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
      assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
      assert (Hβα : β <> α) by (clear - Fr; solve_notin).
      assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
      assert (Hwfβ : {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a)
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hwfβ0 : {{ ⊢ ((β ~ abind_tvar) ++ Θ0) }}a)
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hweak0 : forall (x : atom) (b : abind),
                binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
        by (intros x b Hb; apply binds_app_3; exact Hb).
      assert (Hweak : forall (x : atom) (b : abind),
                binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
        by (intros x b Hb; apply binds_app_3; exact Hb).
      (* --- the target descends; the subject R' does not --- *)
      assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                ⊢ₚₛ (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β)) }}a).
      { eapply a_wf_pskl_delta_to_tvar_mid
          with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
          [ apply (Hw0body β ltac:(clear - Fr; solve_notin))
          | reflexivity | clear; fsetdec ]. }
      assert (HwfPiβ : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pi }}a)
        by (eapply a_wf_pskl_weaken; [ exact Hweak0 | exact HwfPi ]).
      assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
        by (apply a_inc_cons_tvar; exact Hκ).
      assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
      { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ]. }
      assert (Hrfrβ : rho_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
        by (apply rho_fresh_weaken_tvar; exact Hrfr).
      assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
        by (eapply ad_partial_precise_weaken; [ exact Hpre | exact Hweak ]).
      assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                (pskl_to_bskl_inh
                   (msubst_pskl κ (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                                     (pskl_var_f β))))
                ⊳ (open_bskl_wrt_bskl B (bskl_var_f β)) }}ad).
      { rewrite (@msubst_pskl_open Θ0 κ Θ (ptyp_to_pskl A0) β Hκ Hβκ).
        rewrite pskl_to_bskl_inh_open.
        eapply ad_refine_syn_delta_to_tvar_mid
          with (α1 := β) (Θ1 := nil) (Θ0 := Θ) (Δr' := empty);
          [ apply (Hrbody β ltac:(clear - Fr; solve_notin))
          | reflexivity | clear; fsetdec ]. }
      (* Sub-ForallR OPENS P0, which is a [p0_step]; then weaken to Θ0,β *)
      assert (Hapartβ : flex_apart_deep ((β ~ abind_tvar) ++ Θ0) Δρ
                (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β)) ψa).
      { apply flex_apart_deep_weaken_tvar.
        eapply flex_apart_deep_step;
          [ exact Hapart | apply p0step_all; clear - Fr; solve_notin ]. }
      assert (Hrhoβ : uskl_rho a_sub_mode_ty ((β ~ abind_tvar) ++ Θ) Δρ Ψρ T
                (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')))
        by (eapply uskl_rho_weaken; [ exact Hrho | exact Hweak ]).
      assert (HΔρftvβ : forall α0, α0 `in` Δρ ->
                α0 `notin` ftvar_in_pskl
                     (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β))
                   `union` ftvar_in_pskl Pi).
      { intros α0 Hα0. pose proof (HΔρftv α0 Hα0) as Hd0.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      (ptyp_to_pskl A0) (pskl_var_f β)) as Hup.
        cbn [ftvar_in_pskl] in Hd0, Hup.
        assert (Hβ0 : α0 <> β) by (intro Hc; subst; contradiction).
        clear - Hd0 Hup Hβ0; fsetdec. }
      assert (HscopeRβ : ftvar_in_uskl R'
                [<=] add α (dom ((β ~ abind_tvar) ++ Θ0)
                              `union` dom ((β ~ abind_tvar) ++ Θ)))
        by (simpl; clear - HscopeR; fsetdec).
      assert (HwfSubjβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ ⌊ T ⌋ˢ }}a)
        by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfSubj ]).
      assert (Hextβ : forall (x : atom) (b : abind),
                binds x b ((β ~ abind_tvar) ++ Θsm) ->
                binds x b ((β ~ abind_tvar) ++ Θ)).
      { intros x b Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'];
          [ simpl; auto | apply binds_app_3; apply Hext; exact Hb' ]. }
      assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
        by (simpl; clear - HαΘ Hβα; fsetdec).
      assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
        by (simpl; clear - HαΘ0 Hβα; fsetdec).
      (* the Θw pack under the binder — [Θw] does NOT move; keeping it fixed
         is what lets β be stripped out of the increase.  Δρ does not grow on
         this row, so [HΔρw] rides through unchanged. *)
      assert (HβΘw : β `notin` dom Θw)
        by (pose proof (@aenv_binds_dom_sub Θw Θ Hmon) as Hdw;
            clear - Hdw HβΘ; fsetdec).
      assert (Hmonβ : forall x b, binds x b Θw ->
                binds x b ((β ~ abind_tvar) ++ Θ))
        by (intros x b Hb; apply binds_app_3; apply Hmon; exact Hb).
      assert (Hnrβ : forall x b, binds x b ((β ~ abind_tvar) ++ Θ) ->
                binds x b Θw \/ b = abind_tvar).
      { intros x b Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
          [ right; exact Heq | exact (Hnr _ _ Hb') ]. }
      assert (Hκwβ : forall α0, a_flex_tvar ((β ~ abind_tvar) ++ Θ0) α0 ->
                ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw)
        by (intros α0 Hf; apply Hκw; eapply a_flex_tvar_strip_tvar; exact Hf).
      assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
        by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
      edestruct (H0 β ltac:(clear - Fr; solve_notin) Htags
                   ((β ~ abind_tvar) ++ Θ) ((β ~ abind_tvar) ++ Θ0) κ Δ Δρ Ψρ
                   R' ⌊ R' ⌋ˢ (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                             (pskl_var_f β)) Pi Ψi Ψa
                   Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρw
                   HαΘ0β Hκβ Hακdom Hκav eq_refl HscopeRβ HlcR
                   Hdisj HwfP0β HwfPiβ
                   ltac:(intro Hc; discriminate Hc)
                   ltac:(intros _; rewrite <- ptyp_to_pskl_open;
                         apply a_ty_mode_compat__tc)
                   HαΘβ Hsub HΨs1 HΨs2 Hdfreshβ Hapartβ Hpreβ Hrefβ
                   Hrhoβ HΨρ Hrfrβ HΔρΔ HΔρftvβ HΔρPi Hextβ
                   HPnα Hin HαR HwfSubjβ Hψaap (add β Lav) HLavβ)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs
            & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
            & HwfPa & HwfΞ & HαΞ
            & Hmapfst & Himg & HimgΔ & Hinc & Hinceq & Hκfresh
            & Hprec & HftvC).
      assert (HβΞs : β `notin` dom Ξs)
        by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
      assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
      { rewrite Forall_forall. intros p Hp0.
        pose proof (forall_wf_mono_images_dom HFs p Hp0) as Hb.
        clear - Hb HβΘw; fsetdec. }
      assert (HβR : β `notin` ftvar_in_pskl ⌊ R' ⌋ˢ).
      { rewrite ftvar_in_pskl_uskl_to_pskl. clear - Fr; solve_notin. }
      pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
      assert (HβΞc : β `notin` dom Ξc).
      { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
        apply Hκfresh. simpl; clear; fsetdec. }
      assert (Hfmc : all_flex_mono Ξc)
        by (eapply a_looksub_all_flex_mono; exact HLK).
      assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
      { rewrite Forall_forall in Himg |- *. intros p Hp.
        specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
      (* ---------------------------------------------------------------- *)
      (* THE CASE SPLIT.  The IH's own ftv-𝒞 disjunct decides which rule    *)
      (* the lookup side takes — no decidability of [alpha_stack] needed.   *)
      (* ---------------------------------------------------------------- *)
      destruct (HftvC eq_refl) as [Hleft | (Hstk & -> & -> & ->)].
      * (* ---- LEFT: 𝒞 is ψa-RELATIVE, so β ∉ ftv 𝒞 and LS-ForallR
             rebuilds from the single instance.  β is fresh for ψa, for the
             collected Ξc and for κ, and it is a RIGID — [def_ftv] never
             sees it.  From there the row is the Sub-ForallL rows with the
             renamed side swapped: there the SUBJECT moves and the target
             is fixed, here the TARGET moves and the subject is fixed. ---- *)
        assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
        { cbn [def_ftv] in Hleft. pose proof (def_ftv_dom HwfΘ) as Hdf.
          clear - Hleft HβΞc Hβκ Hβψa HβΘ Hdf; fsetdec. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        { (* [a_solve_cstr_ftv] is DISJUNCTIVE since SS-ForallR leaks; the
             escape arm asks β to be fresh for the solve's context, and β is
             a RIGID ENTRY of it, so only the input arm survives.  ⭐ Its
             bound now also carries [dom Ξs] — the solve GENERATES names —
             and [HβΞs] eliminates that term. *)
          intro Hin0.
          destruct (a_solve_cstr_ftv HSolve Hin0) as [Hl | Hr];
            [ pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi;
              clear - Hl Hfi HβC HβΘ0 HβΞs; fsetdec
            | apply Hr; repeat rewrite dom_app; simpl; clear; fsetdec ]. }
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        repeat split.
        -- (* a_looksub : LS-ForallR, the single β-instance renamed into the
              cofinite family *)
           (* EXISTS-FRESH (cluster 3): fire at the β this row already picked *)
           apply a_looksub__forall_r with (β := β);
             [ exact (ptyp_to_pskl_ghost_free (ptyp_all A0))
             | clear - Fr; solve_notin | exact HLK ].
        -- (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
        -- (* all_flex_mono Ξs *) exact Hfms.
        -- (* uniq Ξs *) exact Hus.
        -- (* keys κs = keys Ξs *) exact Hks.
        -- (* dom Ξs ∩ Lav = ∅ *)
           intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
        -- (* the SOLVE block's payloads — at the FIXED Θw *) exact HFs.
        -- (* wf Pa *)
           rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
           apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
             [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
               exact HwfPa
             | exact HβPa ].
        -- (* a_wf_aenv *)
           eapply a_wf_aenv_strip_mid;
             [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
        -- (* α ∉ dom Ξc *) exact HαΞ.
        -- (* keys *) exact Hmapfst.
        -- (* κc images ⊆ ftv ψa *) exact Himg.
        -- (* κc images ⊥ Δρ *) exact HimgΔ.
        -- (* a_inc — the strip peels BOTH blocks at once *)
           rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
           rewrite <- (list_app_assoc κs κc κ).
           eapply a_inc_strip_tvar_mid;
             [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
             | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
             | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
             | exact HβΘ
             | rewrite (list_app_assoc κs κc κ);
               rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
               exact Hinc ].
        -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
        -- (* κc fresh *)
           intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
           clear - Hκfresh; fsetdec.
        -- (* precision : only the CONTEXT gained β here — Sub-ForallR leaves
              Δ alone, so no [delta_shrink] step (unlike Sub-ForallL) *)
           assert (HβPaκ : β `notin`
                     ftvar_in_pskl (msubst_pskl (κs ++ κc ++ κ) Pa)).
           { apply msubst_pskl_ftv_avoid;
               [ intros pp Hpp; apply in_app_or in Hpp;
                 destruct Hpp as [Hpp | Hpp];
                   [ rewrite Forall_forall in Hβκs; apply Hβκs; exact Hpp
                   | apply in_app_or in Hpp; destruct Hpp as [Hpp | Hpp];
                       [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hpp
                       | pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
                         clear - Hb HβΘ; fsetdec ] ]
               | exact HβPa ]. }
           eapply ad_partial_precise_strip_tvar_mid
             with (β := β) (Θ1 := nil) (Θ2 := Θ);
             [ exact Hprec | reflexivity
             | intros α0 τ0 Hb;
               assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                 by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                       [ discriminate Habs | exact Hb' ]);
               pose proof (a_wf_ptyp_ftv_dom
                             (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb')) as Hftd;
               clear - Hftd HβΘ; fsetdec
             | exact HβPaκ
             | exact Hβψa ].
        -- (* ftv 𝒞 : still the LEFT disjunct — [def_ftv] ignores the rigid β *)
           intros _; left. cbn [def_ftv] in Hleft. exact Hleft.
      * (* ---- RIGHT: the lookup subject is an α-STACK.  Such a run never
             descends the target ([alpha_stack_looksub]), so LS-ForallR is
             not used at all and the binder is never introduced — which is
             exactly the configuration in which β genuinely CAN occur in the
             descended 𝒞 (cex/cex_p6ss_sub_target_ftv.v).  The IH still
             supplies the solve, at the descended target; lifting it over
             the ∀ is P6-Sv's strengthen-then-rename recipe
             (sub/look/prop_sub_var.v:2036). ---- *)
        cbn [ftvar_in_cstrs] in *.
        (* the IH's solve is a ONE-constraint run, so it inverts to SS *)
        assert (Hss : {{ ((β ~ abind_tvar) ++ Θ0) ⊢ₛ Pi
                  ≼[ mode_tc ] (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                                  (pskl_var_f β)) ⤳ Ξs ⨾ Pa }}a).
        { cbn in HSolve. inversion HSolve; subst. assumption. }
        (* β ∉ ftv Pa comes from PRECISION, not from the solve's ftv bound:
           the target here legitimately mentions β (that is the whole point of
           this branch), so [a_solve_sub_ftv] is useless.  Precision bounds the
           SOURCE by ψa ∪ Δ ∪ def_ftv Θ, all β-free.  P6-Sv's ForallR row does
           exactly this (sub/look/prop_sub_var.v:2020). *)
        cbn [app] in Hprec.
        assert (Hdκs : dom κs [=] dom Ξs) by (apply keys_eq_dom; exact Hks).
        assert (HβPaκ0 : β `notin`
                  ftvar_in_pskl (msubst_pskl (κs ++ κ) Pa)).
        { eapply ad_partial_precise_src_ftv_avoid;
            [ exact Hprec | exact Hβψa | clear - Fr; solve_notin
            | intros τ0 Hb;
              destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                [ discriminate Habs
                | apply HβΘ; eapply binds_In; exact Hb' ]
            | cbn [def_ftv]; clear - Fr; solve_notin ]. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        { pose proof (msubst_pskl_ftv_dom_lower (κs ++ κ) Pa) as Hlo.
          repeat rewrite dom_app in Hlo.
          clear - HβPaκ0 Hlo Hβκ HβΞs Hdκs; fsetdec. }
        (* ⭐ the block passes THROUGH SS-ForallR (its output is the premise's),
           so it is the conclusion's own — and since the repair the premise
           already runs at [(β ~ tvar) ++ Θ0], so there is nothing to
           strengthen away. *)
        exists (a_cstr_sub mode_tc (pskl_all_syn (ptyp_to_pskl A0)) :: nil),
               nil, Ξs, Pa, (@nil (atom * ptyp)), κs.
        repeat split.
        -- (* a_looksub : LS-ForallL* / LS-UnivGhostL* then LS-Var, at the
              UNDESCENDED target *)
           apply alpha_stack_looksub; exact Hstk.
        -- (* solve : lift the β-instance over the ∀ by SS-ForallR, which is
              EXISTS-FRESH and LEAKS its binder (DESIGN §4.3) — the instance
              at β IS the premise, no family to build *)
           cbn. apply a_solve_cstr__sub.
           apply a_solve_sub__forall_r with (β := β);
             [ exact (ptyp_to_pskl_ghost_free (ptyp_all A0))
             | clear - Fr; solve_notin | exact Hss ].
        -- (* all_flex_mono Ξs *) exact Hfms.
        -- (* uniq Ξs *) exact Hus.
        -- (* keys κs = keys Ξs *) exact Hks.
        -- (* dom Ξs ∩ Lav = ∅ *)
           intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
        -- (* the SOLVE block's payloads *) exact HFs.
        -- (* wf Pa : PIN the split — with Ξc = nil the [Θ1 ++ Θ2] reading is
              [Ξs ++ Θ0], and an unpinned [eapply] shelves an evar that
              reappears later in the bullet list *)
           cbn [app].
           eapply (@a_wf_pskl_strip_tvar Ξs β Θ0);
             [ cbn [app] in HwfPa; exact HwfPa | exact HβPa ].
        -- (* a_wf_aenv *) cbn. exact HwfΘ0.
        -- (* α ∉ dom nil *) cbn; clear; fsetdec.
        (* NB no [keys] bullet: [repeat split] closes [keys nil = keys nil]
           itself — [split] on a convertible equality IS [eq_refl] *)
        -- (* κc images *) apply Forall_nil.
        -- (* κc images ⊥ Δρ *) apply Forall_nil.
        -- (* a_inc : only the SOLVE block is prefixed here (Ξc = ·).  It is
              REBUILT from [Hκ] rather than stripped, since the strip would
              have to see through the empty collection block. *)
           cbn [app].
           apply a_inc_flex_prefix_build;
             [ exact Hfms | exact Hks
             | eapply forall_wf_mono_weaken; [ exact Hmon | exact HFs ]
             | exact Hκ ].
        -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
        -- (* κc fresh *) intros α0 Hα0; cbn in Hα0; clear - Hα0; fsetdec.
        -- (* precision *)
           assert (HβPaκ : β `notin`
                     ftvar_in_pskl (msubst_pskl (κs ++ κ) Pa))
             by exact HβPaκ0.
           cbn [app] in Hprec |- *.
           eapply ad_partial_precise_strip_tvar_mid
             with (β := β) (Θ1 := nil) (Θ2 := Θ);
             [ exact Hprec | reflexivity
             | intros α0 τ0 Hb;
               assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                 by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                       [ discriminate Habs | exact Hb' ]);
               pose proof (a_wf_ptyp_ftv_dom
                             (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb')) as Hftd;
               clear - Hftd HβΘ; fsetdec
             | exact HβPaκ
             | exact Hβψa ].
        -- (* ftv 𝒞 : the RIGHT disjunct, now at the UNDESCENDED P0 *)
           intros _; right; repeat split; try reflexivity; exact Hstk.
  - (* UnivGhostR : NM = SK at M = TC, so [skmod] forces P0 = □ again and
       the case closes exactly like Infer. *)
    assert (HP0 : P0 = pskl_hole)
      by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
    subst P0.
    exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
    repeat split.
    + apply a_looksub__vacuous.
    + simpl. apply a_solve_cstr__empty.
    + apply Forall_nil.
    + apply uniq_nil.
    + intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
    + apply Forall_nil.
    + simpl. exact HwfPi.
    + simpl. exact HwfΘ0.
    + simpl; clear; fsetdec.
    + apply Forall_nil.
    + apply Forall_nil.
    + simpl. exact Hκ.
    + simpl. apply a_inc_equiv_refl; exact Hκ.
    + intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    + simpl. eapply ad_partial_precise_psi_cong;
        [ exact Hpre | assert (HΨae : Ψa [=] empty)
                         by (clear - HΨs2 H; fsetdec);
          clear - HΨae; fsetdec ].
    + (* ftv 𝒞 : no constraints *) intros _; left; simpl; clear; fsetdec.
  - (* Arrow : [skmod] forces P0 = P01→P02 and the refinement splits.  The
       LEFT premise is a consistency judgment and goes to P6-Cs; the RIGHT
       one is the IH, with [sss_arrow_r] + [sub_shield_step].  The two
       constraint sets concatenate (LS-Arrow) and the two solves compose —
       note P6-Cs's 𝒞1 holds no SUBTYPING constraint, which is what lets
       [a_solve_cstr] run them in sequence. *)
    (* R' is an arrow, and [uskl_rho_arrow_r_inv] returns a SINGLE congruence
       (the leaf disjunct needs a VARIABLE ideal), so [Rsub] is an arrow of
       ρ-images and the row's text survives with those in place of the ideal's
       components — each with its own slice of Ψρ. *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    destruct (uskl_rho_arrow_r_inv Hrho)
      as (R1' & R2' & Ψρ1 & Ψρ2 & HRs & Hrhoa & Hrhob & HΨρeq).
    injection HRs as HRsA HRsB.
    rewrite <- HRsA in Hrhoa. rewrite <- HRsB in Hrhob. clear HRsA HRsB.
    (* [skmod] forces P0's arrow shape, in either sort *)
    assert (HP0arr : exists P01 P02, P0 = pskl_arrow P01 P02 /\
              (NM = a_sub_mode_sk -> a_sk_mode_compat M P02) /\
              (NM = a_sub_mode_ty -> a_ty_mode_compat M P02)).
    { destruct NM.
      - specialize (HmodTY eq_refl); inversion HmodTY; subst.
        match goal with |- exists _ _, pskl_arrow ?A ?B = _ /\ _ =>
          exists A, B end.
        repeat split; [ intros Habs; discriminate Habs | intros _; assumption ].
      - specialize (HmodSK eq_refl); inversion HmodSK; subst.
        match goal with |- exists _ _, pskl_arrow ?A ?B = _ /\ _ =>
          exists A, B end.
        repeat split; [ intros _; assumption | intros Habs; discriminate Habs ]. }
    destruct HP0arr as (P01 & P02 & HP0eq & HmodSK2 & HmodTY2).
    subst P0.
    destruct (a_wf_pskl_arrow_inv HwfP0) as [HwfP01 HwfP02].
    (* the refinement splits with P0 *)
    cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
    destruct (ad_refine_arrow_arrow_inv Hrefine) as [Href1 Href2].
    (* the subject's wf splits too *)
    cbn [uskl_to_pskl] in HwfSubj.
    destruct (a_wf_pskl_arrow_inv HwfSubj) as [HwfSubjA HwfSubjB].
    destruct (lc_uskl_arrow_inv HlcR) as [HlcRa HlcRb].
    (* --- tag algebra: Ψa = (Ψ1∩Ψ') ∪ (Ψ2∩Ψ') --- *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
    assert (HΨa : Ψa [=] union (Ψ1 ∩ Ψ') (Ψ2 ∩ Ψ'))
      by (clear - HΨs1 HΨs2 Hsub H0 Hdisj HΨρ; fsetdec).
    (* under ρ the per-component bounds read off the ρ-IMAGES, so each picks up
       its own slice of Ψρ ([uskl_rho_ftag_sub]) *)
    assert (HΨ1sub : Ψ1 [<=] union (ftag_in_uskl Ra) (union Ψρ1 Ψ')).
    { pose proof (ad_pat_consis_ftag_sub H) as Hf1.
      pose proof (uskl_rho_ftag_sub Hrhoa) as Hr1.
      pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α
                    (msubst_uskl_syn κ Ra)) as Hb1.
      pose proof (ftag_in_uskl_msubst_uskl_syn κ Ra) as Hm1.
      clear - Hf1 Hr1 Hb1 Hm1 Hψatag; fsetdec. }
    assert (HΨ2sub : Ψ2 [<=] union (ftag_in_uskl Rb) (union Ψρ2 Ψ')).
    { pose proof (ad_pat_sub_g_ftag_sub Hsubty) as Hf2.
      pose proof (uskl_rho_ftag_sub Hrhob) as Hr2.
      pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α
                    (msubst_uskl_syn κ Rb)) as Hb2.
      pose proof (ftag_in_uskl_msubst_uskl_syn κ Rb) as Hm2.
      clear - Hf2 Hr2 Hb2 Hm2 Hψatag; fsetdec. }
    assert (HΨρ1e : Ψρ1 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).
    assert (HΨρ2e : Ψρ2 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).
    (* --- LEFT branch: the consistency premise, straight to P6-Cs --- *)
    assert (HsubL : Ψi `union` (Ψ1 ∩ Ψ') [<=] Ψ') by (clear - Hsub; fsetdec).
    assert (HΨs1L : Ψ1 [<=] union (ftag_in_uskl Ra) (union Ψρ1 (Ψ1 ∩ Ψ')))
      by (clear - HΨ1sub; fsetdec).
    assert (HΨs2L : Ψ1 ∩ Ψ' [<=] Ψ1) by (clear; fsetdec).
    assert (Hfawa : flex_apart_deep Θ0 Δρ P01 ψa)
      by (eapply flex_apart_deep_step;
            [ exact Hapart
            | apply p0step_arrow_l ]).
    assert (HΔρftvL : forall α0, α0 `in` Δρ ->
              α0 `notin` ftvar_in_pskl P01 `union` ftvar_in_pskl Pi)
      by (intros α0 Hα0; pose proof (HΔρftv α0 Hα0) as Hd0;
          cbn [ftvar_in_pskl] in Hd0; clear - Hd0; fsetdec).
    (* ⚠️ THE AVOID-SET MUST BE NAMED BEFORE THE CALL.  [L] is the LAST
       ∀-bound variable of P6-Cs, so an [ltac:(… solve_notin_auto)] in its premise slot
       runs against a goal whose [?L] is still an EVAR — and [fsetdec] on a
       goal with a set metavariable does not terminate in any useful time
       (measured: >200 s for this one call).  Naming it first makes [exact]
       instantiate [?L] structurally. *)
    assert (HLav1 : ftvar_in_aenv Θ0 [<=] add α (union Lav (dom Θ)))
      by (clear - HLav; fsetdec).
    edestruct (@a_lookeq_solve_complete_gen
                 (size_uskl Ra + size_pskl P01)
                 NM Θ0 Θ Θw κ Δ Ψ' Ψi (Ψ1 ∩ Ψ') Ψ1 ψa Q1
                 (uskl_to_pskl Ra) P01 Pi Ra α Θ Δρ Ψρ1 R1)
      as (C1 & Ξc1 & Ξs1 & Pa1 & κc1 & κs1
          & HLK1 & HSolve1 & Hfms1 & Hus1 & Hks1 & Hfrs1 & HFs1
          & HwfPa1 & HwfΞ1 & HαΞ1
          & Hmap1 & Himg1 & HimgΔ1 & HftvC1 & Hinc1 & Hinceq1 & Hκf1 & Hpre1);
      [ exact (le_n _) | exact HwfΘ | exact HwfΘ0
      | exact HwfΘw | exact Hmon | exact Hnr
      | exact HwfP01 | exact HwfPi
      | exact Hκ | exact Hκw | exact Hψaw | exact HαΘ | exact HαΘ0 | reflexivity
      | clear - HscopeR; cbn in HscopeR; fsetdec
      | exact HlcRa | exact Htags
      | clear - Hdisj; cbn in Hdisj; fsetdec
      | exact HsubL | exact Hdfresh | exact Hpre | exact HΨs1L | exact HΨs2L
      | exact H | exact HwfSubjA | exact Href1
      | exact Hrhoa | intros x b Hb; exact Hb | exact HΨρ1e | exact Hrfr
      | exact HΔρΔ | exact HΔρw | exact HΔρftvL | exact HΔρPi | exact Hfawa
      | exact Hψaap
      (* ⭐ the LEFT branch's avoid-set is WIDENED by [α] and [dom Θ]: the row
         needs [α ∉ dom Ξs1] to rebuild [α ∉ dom (Ξs1 ++ Ξc1 ++ Θ0)], and the
         ρ- and refinement-transports carry [Rb] (scoped at α, Θ0 and Θ)
         across the LEFT solve's block.  Same widening as P6-Cs's arrow row. *)
      | exact HLav1 | ].
    (* ⭐ THE RIGHT BRANCH RUNS AT [Ξs1 ++ Ξc1 ++ Θ0] UNDER [κs1 ++ κc1 ++ κ]
       (2026-08-05, the SolE-FlexR repair).  [Pa1] is the LEFT SOLVE's output
       and mentions the flexibles solve invented, so the precision it consumes
       is stated under all three blocks — and the only context at which that is
       an [a_inc] is [Hinc1] verbatim.  This is P6-Cs's arrow merge, and the
       same toolkit applies. *)
    pose proof (@keys_eq_dom _ _ κc1 Ξc1 Hmap1) as Hd1.
    assert (Hd_s1 : dom κs1 [=] dom Ξs1) by (apply keys_eq_dom; exact Hks1).
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf0.
    assert (HαΞs1 : α `notin` dom Ξs1)
      by (intro Hc; pose proof (Hfrs1 α Hc) as Hf; clear - Hf; fsetdec).
    assert (HΞs1Θ : forall x, x `in` dom Ξs1 -> x `notin` dom Θ)
      by (intros x Hx; pose proof (Hfrs1 x Hx) as Hf; clear - Hf; fsetdec).
    assert (HΞs1L : forall x, x `in` dom Ξs1 -> x `notin` Lav)
      by (intros x Hx; pose proof (Hfrs1 x Hx) as Hf; clear - Hf; fsetdec).
    assert (Hfrs1c : forall x, x `in` dom Ξs1 ->
              x `notin` ftvar_in_aenv (Ξc1 ++ Θ0))
      by (intros x Hx; eapply a_solve_cstr_generated_fresh;
            [ exact HSolve1 | exact Hx ]).
    assert (HwfΞs1 : {{ ⊢ (Ξs1 ++ Ξc1 ++ Θ0) }}a).
    { apply a_wf_aenv_flex_prefix; [ exact Hfms1 | | exact HwfΞ1 ].
      assert (Hdd : dom Ξs1 ∩ dom (Ξc1 ++ Θ0) [<=] empty).
      { intros x Hx.
        assert (Hx1 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
        assert (Hx2 : x `in` dom (Ξc1 ++ Θ0)) by (clear - Hx; fsetdec).
        pose proof (Hfrs1c x Hx1) as Hf.
        pose proof (dom_subset_ftvar_in_aenv (Ξc1 ++ Θ0)) as Hds.
        exfalso; clear - Hf Hds Hx2; fsetdec. }
      apply uniq_app_4;
        [ exact Hus1 | eapply a_wf_aenv_uniq; exact HwfΞ1 | exact Hdd ]. }
    assert (HF1Θ : Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κs1)
      by (eapply forall_wf_mono_weaken; [ exact Hmon | exact HFs1 ]).
    assert (Himg1F : forall p, In p κc1 ->
              ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa)
      by (rewrite Forall_forall in Himg1; exact Himg1).
    assert (HimgΔ1F : forall p, In p κc1 ->
              (ftvar_in_ptyp (snd p)) ∩ Δρ [=] empty)
      by (rewrite Forall_forall in HimgΔ1; exact HimgΔ1).
    pose proof (forall_wf_mono_images_dom HFs1) as HFs1d.
    assert (Hαr : α `notin` dom (Ξs1 ++ Ξc1 ++ Θ0))
      by (repeat rewrite dom_app; clear - HαΞs1 HαΞ1 HαΘ0; fsetdec).
    assert (Hinc1' : (κs1 ++ κc1 ++ κ) ∷ (Ξs1 ++ Ξc1 ++ Θ0) ⊑ Θ) by exact Hinc1.
    assert (Hακdom' : α `notin` dom (κs1 ++ κc1 ++ κ)).
    { intro Hc. apply (a_inc_dom_sub Hinc1') in Hc. contradiction. }
    assert (Hκav' : forall p, In p (κs1 ++ κc1 ++ κ) ->
              α `notin` ftvar_in_ptyp (snd p)).
    { intros p Hp. pose proof (a_inc_image_ftv_dom Hinc1' p Hp) as Hb.
      clear - HαΘ Hb; fsetdec. }
    assert (Hκw1 : forall α0, a_flex_tvar (Ξs1 ++ Ξc1 ++ Θ0) α0 ->
              ftvar_in_ptyp (msubst_lookup (κs1 ++ κc1 ++ κ) α0) [<=] dom Θw).
    { intros α0 Hf. apply msubst_lookup_ftv_app; [ exact HFs1d | ].
      intros Hn1. apply msubst_lookup_ftv_app.
      - intros p Hp. pose proof (Himg1F p Hp) as Hb. clear - Hb Hψaw; fsetdec.
      - intros Hn2. apply Hκw.
        assert (Hns : α0 `notin` dom Ξs1) by (clear - Hn1 Hd_s1; fsetdec).
        assert (Hnc : α0 `notin` dom Ξc1) by (clear - Hn2 Hd1; fsetdec).
        destruct Hf as [Hb | (τ0 & Hb)]; [ left | right; exists τ0 ];
          (apply binds_app_1 in Hb; destruct Hb as [Hb | Hb];
           [ exfalso; apply binds_In in Hb; clear - Hb Hns; fsetdec | ];
           apply binds_app_1 in Hb; destruct Hb as [Hb | Hb];
           [ exfalso; apply binds_In in Hb; clear - Hb Hnc; fsetdec
           | exact Hb ]). }
    assert (HscopeRb : ftvar_in_uskl Rb
              [<=] add α (dom (Ξs1 ++ Ξc1 ++ Θ0) `union` dom Θ))
      by (repeat rewrite dom_app; clear - HscopeR; cbn in HscopeR; fsetdec).
    assert (HwfP02R : {{ (Ξs1 ++ Ξc1 ++ Θ0) ⨟ empty ⊢ₚₛ P02 }}a)
      by (eapply a_wf_pskl_weaken;
            [ intros x b Hb; apply binds_app_3; apply binds_app_3; exact Hb
            | exact HwfP02 ]).
    (* the two blocks the LEFT branch generated are peeled off the ρ and
       refinement premises: [κc1] by [Hκf1], [κs1] by [Hfrs1c] *)
    assert (Htr_c1 : msubst_uskl_syn (κc1 ++ κ) Rb = msubst_uskl_syn κ Rb).
    { apply msubst_uskl_syn_prepend_fresh. intros α0 Hα0.
      specialize (Hκf1 α0 Hα0).
      clear - Hκf1 HscopeR; cbn in HscopeR; fsetdec. }
    assert (Htr_c : msubst_uskl_syn (κs1 ++ κc1 ++ κ) Rb
                    = msubst_uskl_syn κ Rb).
    { rewrite <- Htr_c1. apply msubst_uskl_syn_prepend_fresh.
      intros α0 Hα0.
      assert (Hin1 : α0 `in` dom Ξs1) by (clear - Hα0 Hd_s1; fsetdec).
      pose proof (Hfrs1 α0 Hin1) as Hf.
      clear - Hf HscopeR HLav Hdf0; cbn in HscopeR; fsetdec. }
    assert (Htr_r1 : msubst_pskl (κc1 ++ κ) P02 = msubst_pskl κ P02).
    { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
      specialize (Hκf1 α0 Hα0).
      pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
      clear - Hκf1 Hfd; fsetdec. }
    assert (Htr_r : msubst_pskl (κs1 ++ κc1 ++ κ) P02 = msubst_pskl κ P02).
    { rewrite <- Htr_r1. apply msubst_pskl_prepend_fresh. intros α0 Hα0.
      assert (Hin1 : α0 `in` dom Ξs1) by (clear - Hα0 Hd_s1; fsetdec).
      pose proof (Hfrs1 α0 Hin1) as Hf.
      pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
      clear - Hf Hfd HLav Hdf0; fsetdec. }
    rewrite <- Htr_c in Hrhob.
    assert (Href2' : {{ Θ ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl (κs1 ++ κc1 ++ κ) P02)) ⊳ Q2 }}ad)
      by (rewrite Htr_r; exact Href2).
    (* the shield descends with [sss_arrow_r] and then crosses BOTH blocks *)
    assert (HfrΞ1 : (ftvar_in_pskl P02) ∩ (dom Ξc1) [=] empty).
    { pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
      intros x; split; intros Hx; [ exfalso | clear - Hx; fsetdec ].
      assert (Hx1 : x `in` ftvar_in_pskl P02) by (clear - Hx; fsetdec).
      assert (Hx2 : x `in` dom Ξc1) by (clear - Hx; fsetdec).
      rewrite <- Hd1 in Hx2. specialize (Hκf1 x Hx2).
      clear - Hκf1 Hfd Hx1; fsetdec. }
    assert (HfrΞs1 : (ftvar_in_pskl P02) ∩ (dom Ξs1) [=] empty).
    { pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
      intros x; split; intros Hx; [ exfalso | clear - Hx; fsetdec ].
      assert (Hx1 : x `in` ftvar_in_pskl P02) by (clear - Hx; fsetdec).
      assert (Hx2 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
      pose proof (Hfrs1 x Hx2) as Hf.
      clear - Hf Hfd HLav Hdf0 Hx1; fsetdec. }
    assert (HapartR : flex_apart_deep (Ξs1 ++ Ξc1 ++ Θ0) Δρ P02 ψa).
    { apply flex_apart_deep_weaken_flex_prefix; [ | exact HfrΞs1 ].
      apply flex_apart_deep_weaken_flex_prefix; [ | exact HfrΞ1 ].
      eapply flex_apart_deep_step; [ exact Hapart | apply p0step_arrow_r ]. }
    assert (HsubR : (Ψi `union` (Ψ1 ∩ Ψ')) `union` (Ψ2 ∩ Ψ') [=] Ψ')
      by (clear - Hsub HΨa; fsetdec).
    assert (HΨs1R : Ψ2 [<=] union (ftag_in_uskl Rb) (union Ψρ2 (Ψ2 ∩ Ψ')))
      by (clear - HΨ2sub; fsetdec).
    assert (HΨs2R : Ψ2 ∩ Ψ' [<=] Ψ2) by (clear; fsetdec).
    assert (HdisjRb : (ftag_in_uskl Rb) ∩ Ψ' [=] empty)
      by (clear - Hdisj; cbn in Hdisj; fsetdec).
    assert (HΔρΘ0 : Δρ [<=] dom Θ0).
    { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & _ & _).
      apply binds_In with (a := abind_tvar).
      eapply a_inc_binds_tvar_rev; [ exact Hκ | exact Hb ]. }
    assert (HΔρΞc1 : forall α0, α0 `in` Δρ -> α0 `notin` dom Ξc1).
    { intros α0 Hα0 Hc. rewrite <- Hd1 in Hc. specialize (Hκf1 α0 Hc).
      destruct (Hrfr α0 Hα0) as (Hb & _ & _). apply binds_In in Hb.
      clear - Hκf1 Hb; fsetdec. }
    assert (HΔρΞs1 : forall α0, α0 `in` Δρ -> α0 `notin` dom Ξs1).
    { intros α0 Hα0 Hc. pose proof (Hfrs1 α0 Hc) as Hf.
      pose proof (HΔρΘ0 α0 Hα0) as Hd00.
      clear - Hf Hd00 HLav Hdf0; fsetdec. }
    assert (HΔρPa1ftv : forall α0, α0 `in` Δρ ->
              α0 `notin` ftvar_in_pskl Pa1).
    { intros α0 Hα0.
      pose proof (a_solve_cstr_ftv_eq HSolve1 (a_lookeq_cstr_eq HLK1))
        as Hs1.
      pose proof (HΔρftv α0 Hα0) as Hd0. cbn [ftvar_in_pskl] in Hd0.
      pose proof (HΔρΞc1 α0 Hα0) as HΞ.
      pose proof (HΔρΞs1 α0 Hα0) as HΞs.
      assert (Hα0Θ0 : α0 `in` dom Θ0) by (apply HΔρΘ0; exact Hα0).
      assert (Hc1 : α0 `notin` ftvar_in_cstrs C1)
        by (eapply a_lookeq_ftv_ctx;
              [ exact HLK1 | exact Hα0Θ0 | clear - Hd0; fsetdec | exact HΞ ]).
      clear - Hs1 Hc1 Hd0 HΞ HΞs; fsetdec. }
    assert (HΔρftvR : forall α0, α0 `in` Δρ ->
              α0 `notin` ftvar_in_pskl P02 `union` ftvar_in_pskl Pa1).
    { intros α0 Hα0. pose proof (HΔρftv α0 Hα0) as Hd0.
      cbn [ftvar_in_pskl] in Hd0.
      pose proof (HΔρPa1ftv α0 Hα0) as Hp1. clear - Hd0 Hp1; fsetdec. }
    assert (Hκs1Δρ : forall p, In p κs1 ->
              forall α0, α0 `in` Δρ -> α0 `notin` ftvar_in_ptyp (snd p)).
    { intros p Hp α0 Hα0. pose proof (HFs1d p Hp) as Hb.
      clear - Hb HΔρw Hα0; fsetdec. }
    assert (HΔρPa1 : forall α0, α0 `in` Δρ ->
              α0 `notin` pskl_shielded_ftv
                           (msubst_pskl (κs1 ++ κc1 ++ κ) Pa1)).
    { intros α0 Hα0.
      pose proof (pskl_shielded_ftv_sub_ftv
                    (msubst_pskl (κs1 ++ κc1 ++ κ) Pa1)) as Hsh.
      enough (Hne : α0 `notin`
                ftvar_in_pskl (msubst_pskl (κs1 ++ κc1 ++ κ) Pa1))
        by (clear - Hsh Hne; fsetdec).
      apply msubst_pskl_ftv_avoid.
      - intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp].
        + exact (Hκs1Δρ p Hp α0 Hα0).
        + apply in_app_or in Hp; destruct Hp as [Hp | Hp].
          * pose proof (HimgΔ1F p Hp) as Hi. clear - Hi Hα0; fsetdec.
          * destruct (Hrfr α0 Hα0) as (_ & Hκim & _). apply Hκim; exact Hp.
      - exact (HΔρPa1ftv α0 Hα0). }
    assert (HrfrR : rho_fresh Δρ Θ (κs1 ++ κc1 ++ κ)).
    { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & Hκim & Hdef).
      repeat split; [ exact Hb | | exact Hdef ].
      intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp].
      - exact (Hκs1Δρ p Hp α0 Hα0).
      - apply in_app_or in Hp; destruct Hp as [Hp | Hp].
        + pose proof (HimgΔ1F p Hp) as Hi. clear - Hi Hα0; fsetdec.
        + apply Hκim; exact Hp. }
    assert (HLavR : ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)
              [<=] add α (union Lav (union (dom Ξs1) (dom Ξc1)))).
    { repeat rewrite ftvar_in_aenv_app.
      pose proof (all_flex_mono_ftvar_in_aenv Hfms1) as Hs1f.
      pose proof (all_flex_mono_ftvar_in_aenv
                    (a_lookeq_all_flex_mono HLK1)) as Hc1f.
      clear - Hs1f Hc1f HLav; fsetdec. }
    (* --- RIGHT branch: the IH, dispatching through the leaf lemma exactly
       as every other recursive row does (Rb may itself be [var α]) --- *)
    assert (REC : exists 𝒞 Ξc Ξs Pa κc κs,
      ({{ (Ξs1 ++ Ξc1 ++ Θ0) ⊢ ⌊ Rb ⌋ˢ ≼[ α , M ] P02 ⤳ Ξc ⨾ 𝒞 }}a) /\
      {{ (Ξc ++ (Ξs1 ++ Ξc1 ++ Θ0)) ⊩ 𝒞 ⨾ Pa1 ⤳ Ξs ⨾ Pa }}a /\
      all_flex_mono Ξs /\
      uniq Ξs /\
      keys κs = keys Ξs /\
      (forall α0, α0 `in` dom Ξs ->
         α0 `notin` add α (union Lav (union (dom Ξs1) (dom Ξc1)))) /\
      Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
      {{ (Ξs ++ Ξc ++ (Ξs1 ++ Ξc1 ++ Θ0)) ⨟ empty ⊢ₚₛ Pa }}a /\
      {{ ⊢ (Ξc ++ (Ξs1 ++ Ξc1 ++ Θ0)) }}a /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      Forall (fun p => (ftvar_in_ptyp (snd p)) ∩ Δρ [=] empty) κc /\
      (κs ++ κc ++ (κs1 ++ κc1 ++ κ)) ∷ (Ξs ++ Ξc ++ (Ξs1 ++ Ξc1 ++ Θ0)) ⊑ Θ /\
      a_inc_equiv (Ξs1 ++ Ξc1 ++ Θ0) (κs1 ++ κc1 ++ κ) (κs1 ++ κc1 ++ κ) Θ /\
      (forall α0, α0 `in` dom κc ->
         α0 `notin` add α (dom (Ξs1 ++ Ξc1 ++ Θ0) `union` dom Θ
                             `union` ftvar_in_uskl ψa)) /\
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ (κs1 ++ κc1 ++ κ)) Pa)
        ⊑ᵖ[ (Ψi `union` (Ψ1 ∩ Ψ')) `union` (Ψ2 ∩ Ψ') ] ψa }}ad /\
      (M = mode_tc ->
         ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                               `union` dom (κs1 ++ κc1 ++ κ) `union` def_ftv Θ
         \/ (alpha_stack α ⌊ Rb ⌋ˢ /\ Ξc = nil /\ κc = nil
             /\ 𝒞 = a_cstr_sub M P02 :: nil))).
    { destruct (AtomSetProperties.In_dec α (ftvar_in_pskl ⌊ Rb ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_eq_var_dec ⌊ Rb ⌋ˢ α) as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply (@a_looksub_solve_complete_leaf n NM M
                    (Ξs1 ++ Ξc1 ++ Θ0) Θsm Θ Θw
                    (κs1 ++ κc1 ++ κ) Δ Δρ Ψρ2 Ψ' (Ψi `union` (Ψ1 ∩ Ψ'))
                    (Ψ2 ∩ Ψ')
                    Ψ2 ψa Q2 (uskl_to_pskl Rb) P02 Pa1 Rb R2 α
                    HwfΘ HwfΞs1 HwfΘw Hmon Hnr Hκw1 Hψaw HΔρw
                    HwfP02R HwfPa1 HmodSK2 HmodTY2 Hinc1'
                    HαΘ Hαr eq_refl HscopeRb HlcRb Htags HdisjRb HsubR
                    Hdfresh HapartR Hpre1 HΨs1R HΨs2R
                    Hsubty HwfSubjB Href2'
                    Hrhob HΨρ2e HrfrR HΔρΔ HΔρPa1);
            [ right; exact Heq0 | exact Hext | exact HLavR ].
        + (* recurse *)
          assert (HαRb : α `in` ftvar_in_uskl Rb)
            by (rewrite <- ftvar_in_pskl_uskl_to_pskl; exact Hin0).
          eapply (IHHsubty Htags Θ (Ξs1 ++ Ξc1 ++ Θ0) (κs1 ++ κc1 ++ κ)
                    Δ Δρ Ψρ2
                    Rb (uskl_to_pskl Rb) P02 Pa1
                    (Ψi `union` (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ')
                    HwfΘ HwfΞs1 Hmon Hnr Hκw1 HΔρw
                    Hαr Hinc1' Hακdom' Hκav'
                    eq_refl HscopeRb HlcRb HdisjRb HwfP02R HwfPa1
                    HmodSK2 HmodTY2 HαΘ HsubR HΨs1R HΨs2R Hdfresh HapartR
                    Hpre1 Href2' Hrhob HΨρ2e HrfrR HΔρΔ HΔρftvR HΔρPa1 Hext
                    Hne0 Hin0 HαRb HwfSubjB Hψaap
                    (add α (union Lav (union (dom Ξs1) (dom Ξc1)))) HLavR).
      - (* leaf, absent *)
        eapply (@a_looksub_solve_complete_leaf n NM M
                  (Ξs1 ++ Ξc1 ++ Θ0) Θsm Θ Θw
                  (κs1 ++ κc1 ++ κ) Δ Δρ Ψρ2 Ψ' (Ψi `union` (Ψ1 ∩ Ψ'))
                  (Ψ2 ∩ Ψ')
                  Ψ2 ψa Q2 (uskl_to_pskl Rb) P02 Pa1 Rb R2 α
                  HwfΘ HwfΞs1 HwfΘw Hmon Hnr Hκw1 Hψaw HΔρw
                  HwfP02R HwfPa1 HmodSK2 HmodTY2 Hinc1'
                  HαΘ Hαr eq_refl HscopeRb HlcRb Htags HdisjRb HsubR
                  Hdfresh HapartR Hpre1 HΨs1R HΨs2R
                  Hsubty HwfSubjB Href2'
                  Hrhob HΨρ2e HrfrR HΔρΔ HΔρPa1);
          [ left; exact Hnin0 | exact Hext | exact HLavR ]. }
    destruct REC as (C2 & Ξc2 & Ξs2 & Pa2 & κc2 & κs2
                     & HLK2 & HSolve2 & Hfms2 & Hus2 & Hks2 & Hfrs2 & HFs2
                     & HwfPa2 & HwfΞ2
                     & HαΞ2 & Hmap2 & Himg2 & HimgΔ2 & Hinc2 & Hinceq2
                     & Hκf2 & Hpre2 & HftvC2).
    (* --- ASSEMBLY.  LS-Arrow pairs [Ξc1,Ξc2] with [C1++C2]; the two solves
       compose because C1 (a LOOKEQ's output) holds no subtyping constraint,
       and their BLOCKS stack the other way round, [Ξs2 ++ Ξs1].  Line for line
       P6-Cs's arrow merge: the permutation is free because [binds] over an
       append is plain membership, and the [a_inc] is REBUILT from [Hκ] by four
       [a_inc_flex_prefix_build] steps rather than permuted. --- *)
    pose proof (a_lookeq_all_flex_mono HLK1) as HfmΞ1.
    pose proof (a_looksub_all_flex_mono HLK2) as HfmΞ2.
    destruct (@a_inc_flex_prefix_split Ξs1 κs1 (Ξc1 ++ Θ0) (κc1 ++ κ) Θ
                Hfms1 Hks1 Hinc1) as [_ HincC1].
    destruct (@a_inc_flex_prefix_split Ξc1 κc1 Θ0 κ Θ HfmΞ1 Hmap1 HincC1)
      as [Hwm1 _].
    destruct (@a_inc_flex_prefix_split Ξs2 κs2
                (Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0) (κc2 ++ κs1 ++ κc1 ++ κ) Θ
                Hfms2 Hks2 Hinc2) as [_ HincC2].
    destruct (@a_inc_flex_prefix_split Ξc2 κc2 (Ξs1 ++ Ξc1 ++ Θ0)
                (κs1 ++ κc1 ++ κ) Θ HfmΞ2 Hmap2 HincC2) as [Hwm2 _].
    pose proof (@keys_eq_dom _ _ κc2 Ξc2 Hmap2) as Hd2.
    assert (Hd_s2 : dom κs2 [=] dom Ξs2) by (apply keys_eq_dom; exact Hks2).
    assert (Hmapc : keys (κc1 ++ κc2) = keys (Ξc1 ++ Ξc2))
      by (rewrite !keys_app; rewrite Hmap1, Hmap2; reflexivity).
    assert (Hmaps : keys (κs2 ++ κs1) = keys (Ξs2 ++ Ξs1))
      by (rewrite !keys_app; rewrite Hks1, Hks2; reflexivity).
    assert (HΞ2disj : forall x, x `in` dom Ξc2 ->
              x `notin` dom (Ξs1 ++ Ξc1 ++ Θ0)).
    { intros x Hx. rewrite <- Hd2 in Hx. pose proof (Hκf2 x Hx) as Hf.
      clear - Hf; fsetdec. }
    assert (HΞ2Ξs1 : forall x, x `in` dom Ξc2 -> x `notin` dom Ξs1)
      by (intros x Hx; pose proof (HΞ2disj x Hx) as Hf;
          repeat rewrite dom_app in Hf; clear - Hf; fsetdec).
    assert (HΞ2Ξc1Θ0 : forall x, x `in` dom Ξc2 ->
              x `notin` dom (Ξc1 ++ Θ0))
      by (intros x Hx; pose proof (HΞ2disj x Hx) as Hf;
          repeat rewrite dom_app in Hf; rewrite dom_app; clear - Hf; fsetdec).
    assert (Hdisj12 : forall β0, β0 `in` dom κc1 -> β0 `notin` dom κc2).
    { intros β0 Hβ0 Hin2. pose proof (Hκf2 β0 Hin2) as Hf2.
      repeat rewrite dom_app in Hf2. rewrite Hd1 in Hβ0.
      clear - Hf2 Hβ0; fsetdec. }
    assert (Hdisj2s1 : forall β0, β0 `in` dom κc2 -> β0 `notin` dom κs1).
    { intros β0 Hβ0. pose proof (Hκf2 β0 Hβ0) as Hf2.
      repeat rewrite dom_app in Hf2. clear - Hf2 Hd_s1; fsetdec. }
    exists (C1 ++ C2), (Ξc1 ++ Ξc2), (Ξs2 ++ Ξs1), Pa2,
           (κc1 ++ κc2), (κs2 ++ κs1).
    repeat split.
    -- (* a_looksub : LS-Arrow.  The RIGHT branch ran at the GROWN
          [Ξs1 ++ Ξc1 ++ Θ0]; dropping declarations only SHRINKS the
          avoid-set, which is the direction [a_looksub_ctx_ftv_mono] goes. *)
       rewrite <- HeraseR. apply a_looksub__arrow;
         [ exact HLK1
         | eapply a_looksub_ctx_ftv_mono;
             [ exact HLK2
             | repeat rewrite ftvar_in_aenv_app; clear; fsetdec ] ].
    -- (* solve *)
       assert (HΞ2Pi : forall x, x `in` dom Ξc2 -> x `notin` ftvar_in_pskl Pi).
       { intros x Hx; pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfd;
         pose proof (HΞ2Ξc1Θ0 x Hx) as Hf; rewrite dom_app in Hf;
         simpl in Hfd; clear - Hfd Hf; fsetdec. }
       assert (HΞ2C1 : forall x, x `in` dom Ξc2 ->
                 x `notin` ftvar_in_cstrs C1).
       { (* the exact bound is gone (the ∀ rules leak) and x is a name the
            RIGHT run INVENTED, so the ctx corollary does not apply either;
            what does is P6-Cs's OWN ftv-𝒞 bound *)
         intros x Hx. rewrite <- Hd2 in Hx.
         pose proof (Hκf2 x Hx) as Hf. repeat rewrite dom_app in Hf.
         assert (Hxκ : x `notin` dom κ).
         { intro Hc. destruct (a_inc_dom_flex Hκ Hc) as [Hb | [τ0 Hb]];
             apply binds_In in Hb; clear - Hf Hb; fsetdec. }
         pose proof (def_ftv_dom HwfΘ) as Hdf.
         clear - HftvC1 Hf Hxκ Hdf; fsetdec. }
       assert (HΞ2Pa1 : forall x, x `in` dom Ξc2 ->
                 x `notin` ftvar_in_pskl Pa1).
       { intros x Hx;
         pose proof (a_solve_cstr_ftv_eq HSolve1 (a_lookeq_cstr_eq HLK1))
           as Hfe;
         pose proof (HΞ2Pi x Hx) as HxPi;
         pose proof (HΞ2C1 x Hx) as HxC1;
         pose proof (HΞ2Ξs1 x Hx) as HxS1;
         clear - Hfe HxPi HxC1 HxS1; fsetdec. }
       rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
       eapply a_solve_cstr_app;
         [ exact (a_lookeq_cstr_eq HLK1)
         | apply a_solve_cstr_weaken_mid_flex;
             [ exact HfmΞ2 | exact HΞ2Ξc1Θ0 | exact HΞ2Pi | exact HΞ2C1
             | exact HΞ2Pa1 | exact HΞ2Ξs1 | exact HSolve1 ]
         | eapply a_solve_cstr_ctx_change;
             [ exact HSolve2
             | repeat rewrite ftvar_in_aenv_app; clear; fsetdec
             | intros α1 Hg; destruct Hg as [Hb | [τ Hb]];
                 [ left | right; exists τ ]; apply binds_rot_app; exact Hb
             | intros P0 Hf; inversion Hf; subst;
                 [ apply a_flex__var with (α := α0)
                 | apply a_flex__var_def with (α := α0) (τ := τ) ];
                 apply binds_rot_app_rev; assumption ] ].
    -- (* all_flex_mono (Ξs2 ++ Ξs1) *) apply all_flex_mono_app; assumption.
    -- (* uniq (Ξs2 ++ Ξs1) *)
       assert (Hdd : dom Ξs2 ∩ dom Ξs1 [<=] empty).
       { intros x Hx.
         assert (Hx2 : x `in` dom Ξs2) by (clear - Hx; fsetdec).
         assert (Hx1 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
         pose proof (Hfrs2 x Hx2) as Hf. exfalso; clear - Hf Hx1; fsetdec. }
       apply uniq_app_4; [ exact Hus2 | exact Hus1 | exact Hdd ].
    -- (* keys *) exact Hmaps.
    -- (* dom Ξs ∩ Lav = ∅ *)
       intros α0 Hα0. rewrite dom_app in Hα0.
       apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0];
         [ pose proof (Hfrs2 α0 Hα0) as Hf | pose proof (Hfrs1 α0 Hα0) as Hf ];
         clear - Hf; fsetdec.
    -- (* the SOLVE blocks' payloads *) apply Forall_app; split; assumption.
    -- (* wf Pa2 : [Ξs2,Ξc2,Ξs1,Ξc1,Θ0] → [Ξs2,Ξs1,Ξc1,Ξc2,Θ0] *)
       eapply a_wf_pskl_weaken; [ | exact HwfPa2 ].
       intros x b Hb.
       rewrite (aenv_app_assoc Ξs2 Ξs1 ((Ξc1 ++ Ξc2) ++ Θ0)).
       rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
       apply binds_app_perm5; exact Hb.
    -- (* a_wf_aenv *)
       apply a_wf_aenv_flex_prefix;
         [ apply all_flex_mono_app; assumption
         | pose proof (a_wf_aenv_uniq HwfΞ2) as Huq;
           clear - Huq; solve_uniq
         | exact HwfΘ0 ].
    -- (* α ∉ dom (Ξc1++Ξc2) *)
       rewrite dom_app; clear - HαΞ1 HαΞ2; fsetdec.
    -- (* keys *) exact Hmapc.
    -- (* κc images ⊆ ftv ψa *) apply Forall_app; split; assumption.
    -- (* κc images ⊥ Δρ *) apply Forall_app; split; assumption.
    -- (* a_inc : REBUILT from [Hκ] one block at a time *)
       assert (Hb1 : (κc2 ++ κ) ∷ (Ξc2 ++ Θ0) ⊑ Θ)
         by (apply a_inc_flex_prefix_build;
               [ exact HfmΞ2 | exact Hmap2 | exact Hwm2 | exact Hκ ]).
       assert (Hb2 : (κc1 ++ κc2 ++ κ) ∷ (Ξc1 ++ Ξc2 ++ Θ0) ⊑ Θ)
         by (apply a_inc_flex_prefix_build;
               [ exact HfmΞ1 | exact Hmap1 | exact Hwm1 | exact Hb1 ]).
       assert (Hb3 : (κs1 ++ κc1 ++ κc2 ++ κ)
                       ∷ (Ξs1 ++ Ξc1 ++ Ξc2 ++ Θ0) ⊑ Θ)
         by (apply a_inc_flex_prefix_build;
               [ exact Hfms1 | exact Hks1
               | eapply forall_wf_mono_weaken; [ exact Hmon | exact HFs1 ]
               | exact Hb2 ]).
       assert (Hb4 : (κs2 ++ κs1 ++ κc1 ++ κc2 ++ κ)
                       ∷ (Ξs2 ++ Ξs1 ++ Ξc1 ++ Ξc2 ++ Θ0) ⊑ Θ)
         by (apply a_inc_flex_prefix_build;
               [ exact Hfms2 | exact Hks2
               | eapply forall_wf_mono_weaken; [ exact Hmon | exact HFs2 ]
               | exact Hb3 ]).
       rewrite (list_app_assoc κs2 κs1 ((κc1 ++ κc2) ++ κ)).
       rewrite (list_app_assoc κc1 κc2 κ).
       rewrite (aenv_app_assoc Ξs2 Ξs1 ((Ξc1 ++ Ξc2) ++ Θ0)).
       rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
       exact Hb4.
    -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
    -- (* κc fresh *)
       intros α0 Hα0. rewrite dom_app in Hα0.
       apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0].
       ++ apply Hκf1; exact Hα0.
       ++ pose proof (Hκf2 α0 Hα0) as Hf. repeat rewrite dom_app in Hf.
          clear - Hf; fsetdec.
    -- (* precision.  [Hpre2] is under [κs2 ++ κc2 ++ κs1 ++ κc1 ++ κ] and the
          goal wants [(κs2 ++ κs1) ++ (κc1 ++ κc2) ++ κ] — the same bindings on
          pairwise-disjoint domains, so it is a lookup-level identity. *)
       assert (Hperm : msubst_pskl ((κs2 ++ κs1) ++ (κc1 ++ κc2) ++ κ) Pa2
                     = msubst_pskl (κs2 ++ κc2 ++ κs1 ++ κc1 ++ κ) Pa2).
       { rewrite (list_app_assoc κs2 κs1 ((κc1 ++ κc2) ++ κ)).
         rewrite (list_app_assoc κc1 κc2 κ).
         apply msubst_pskl_lookup_congr. intro β0.
         apply msubst_lookup_app_congr. intro β1.
         rewrite (@msubst_lookup_app_swap κc2 κs1 (κc1 ++ κ) β1 Hdisj2s1).
         apply msubst_lookup_app_congr. intro β2.
         apply (@msubst_lookup_app_swap κc1 κc2 κ β2 Hdisj12). }
       rewrite Hperm.
       eapply ad_partial_precise_psi_cong;
         [ exact Hpre2 | clear - HΨa; fsetdec ].
    -- (* ftv 𝒞 : VACUOUS.  Sub-Arrow concludes at [mode_fn M], never at
          [mode_tc] — which is exactly why the conjunct carries that guard:
          the left branch (a lookeq, so P6-Cs) always gives the LEFT disjunct
          while the right branch may give the RIGHT one, and no bound could
          concatenate the two. *)
       intros Habs; discriminate Habs.
  - (* ForallL, tagged : the subject's ∀ is instantiated, so the IH must run
       at [open R' ψb] — this is why the induction is on the DERIVATION and
       not on P6-Cs's measure.

       PREREQUISITE — DONE.  The REVERSE of
       [lemma:constraint-collection-stable-substitution] is now
       [a_looksub_subst_stable_rev] (prop_looksub.v §4b, Qed, axiom-free):

         (subst Pg βg Pu) ≼[α,m] P' ⤳ Ξ ⨾ 𝒞 ->
         βg <> α -> α ∉ ftv Pg -> lc Pg -> lc Pu ->
         Pu ≼[α,m] P' ⤳ Ξ ⨾ 𝒞.

       BLOCKER — THE PAPER'S IH INSTANCE DOES NOT TYPE-CHECK IN THIS
       ENCODING.  subtyping-proofs.tex:2600–2643 applies the IH with
       [S := S'[ψ_b/β]] and, in passing from \refb to \refe, uses

           θ (S'[ψ_b/β])  =  (θ S')[ψ_b/β],

       which holds ONLY IF [θ ψ_b = ψ_b].  Here the subject is written
       EXACTLY as the paper writes it, [(κ R')[ψa/α]] with R' κ-FREE and
       Θ0-scoped, so choosing [R'' := open R0 ψ] forces

           msubst_uskl_syn κ (open R0 ψ) = open (msubst_uskl_syn κ R0) ψ,

       i.e. [msubst_uskl_syn κ ψ = ψ] — and NOTHING in the premises gives
       it.  ψ is the ForallL rule's guess, constrained only by
       [{{ Θ ⨟ empty ⊢ₚₛ ⌊ψ⌋ˢ }}a], so [ftv ψ ⊆ dom Θ]; and [a_inc]'s flexible
       rows ([a_inc__flex], [a_inc__flex_def]) leave the TARGET arbitrary,
       so a Θ-scoped ψ may perfectly well mention a [dom κ] variable.  Nor
       can a pre-image be manufactured: κ's images are MONOTYPES
       ([metasubst = list (atom * ptyp)] + [mono_ptyp]) while ψ is a
       general tagged skeleton, so extending κ (or Θ0) to name ψ is not an
       option either.

       ⚠️ AND NO PREMISE ON κ RESCUES THAT STEP — three machine-checked
       facts, all in cex/cex_p6ss_inc_compat.v (two rounds of review):

       - Barendregt disjointness [dom κ ∩ dom Θ = ∅] is UNSATISFIABLE at
         identity metasubstitutions, whose flexible entries are all
         PRESERVED in the target (algorithmic.tex:135-140) — and identity
         is what the pipeline supplies ([id_inc_dom_overlap]).
       - Syntactic compatibility [∀ α̂ ∈ dom κ ∩ dom Θ, κα̂ = α̂] EXCLUDES a
         legitimate θ: at Θ = [α̂ := ⟨⟩], the θ with θα̂ = ⟨⟩ substitutes a
         DEFINED survivor's definition — licensed by the paper's own
         "preserved ... but possibly with more monomorphic information" —
         and is inc-EQUIVALENT to ι ([def_subst_theta_is_legit]).
       - The strongest defensible invariant — SEMANTIC compatibility,
         [α̂ ∈ dom Θ ⟹ Θ ⊢ κα̂ ≡ᵗ α̂], which kills the junk θ that moves
         an UNDEFINED survivor ([inc_moves_survivor], derivable only
         because the figure's flex rule demands nothing but wf of the
         image) while keeping the definition-substituting θ — STILL leaves
         [κψ_b ≠ ψ_b] on that legitimate θ (third conjunct of
         [def_subst_theta_is_legit]).  The written step holds essentially
         only at ι-like κ; the lemma quantifies over general κ.

       REPAIR (decided after review; NOT yet built): PROOF-side, statement
       UNCHANGED — restructure the induction the way P6-Sv already does.
       Generalize the motive over an accumulated rigid substitution ρ: each
       ForallL opens with a FRESH RIGID β and the guess rides OUTSIDE κ as
       ρ := ρ ∘ [ψ/β], so the subject is ρ((κR'')[ψa/α]) with β ∉ dom κ ∪
       dom Θ0 and κ's images β-free — no κ/ψ commutation ever arises.  The
       theorem is the ρ = identity instance.  The looksub side then runs on
       var-opened subjects, so LS-ForallL rebuilds via its cofinite family
       directly ([a_looksub_lookeq_rename_tvar]); the reverse-substitution
       lemma [a_looksub_subst_stable_rev] is NOT needed on this route (it
       stays in prop_looksub.v as a true, independently useful fact).  The
       [P = α] leaf calls [a_solve_sub_complete_var] at the ACCUMULATED ρ —
       the general-ρ interface P6-Sv was built with, which the current
       identity-ρ leaf leaves unused.  Cost: the aux lemma carries P6-Sv's
       ρ premise kit ([uskl_rho], [rho_fresh] via the binds-monotone
       Θs-generalization, [flex_apart_walk]/[flex_shield] at Δρ — so
       [sub_shield] generalizes to carry Δρ) and the eight closed rows are
       re-dispatched under the generalized motive (mechanical).  The tag
       bookkeeping (the instantiated binder's ε, previously an open
       sub-question) is expected to follow P6-Sv's Ψρ treatment — the
       guesses' tags accumulate in Ψρ, with [Ψρ ∩ Ψ' = ∅] from the rule's
       own freshness premises; verify when executing.

       The SCOPE-premise relaxation ([ftv R' ⊆ add α (dom Θ0 ∪ dom Θ)],
       done here and in P6-Cs with the dual κc-freshness conclusion
       strengthened) predates this decision and is kept: it is harmless,
       and the Arrow row wants the strengthened conclusion anyway.  (It is
       also all that is needed on the scope side: β enters Θ0 AND Θ as a
       rigid — [rho_fresh] insists every ρ-replaced variable be a rigid of
       the context — so [ftv (open R0 (var β))] stays inside the bound.)

       SCOPE OF THE REPAIR, MEASURED.  The Check row hands its WHOLE
       subject to P6-Cs, and a ForallL can sit above a Check, so **P6-Cs
       must be ρ-generalized too**.  That is threading, not new theory:
       P6-Cv ([a_solve_eq_complete_var_gen], sub/look/prop_eq_var.v:505)
       ALREADY takes [uskl_rho NM Θ Δρ Ψρ ψsub ψa]; the [uskl_rho_*_l_inv]
       kit exists; P6-Cs's measure ([size R' + size P0], on the ρ-FREE
       ideal subject) is unaffected; its ∀ rows open with fresh VARIABLES
       so ρ never grows inside it; and its leaf passes the real ρ down
       instead of [urho__refl].

       READY HERE for that step: [sub_shield] already carries Δρ (the
       statement below instantiates it at [empty], so nothing has moved
       yet) with [sub_shield_add_fresh] / [_weaken_tvar], and
       [ad_partial_precise_delta_shrink_fresh] is the Δ-return the row
       needs.  P6-Sv's ForallL row (sub/look/prop_sub_var.v:2308) is
       the line-by-line template for the rest — with one simplification:
       P6-Ss's ∀ comes from the SUBJECT, so ψa, P0, Pi, Ψi and Ψa do NOT
       move, and only Θ0/Θ/Δ/Δρ grow by β. *)
    (* --- the ρ-inversion: the ideal is a ∀^ε too, and its body's ρ-family is
       what Sub-ForallL extends --- *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    destruct (uskl_rho_all_tag_r_inv Hrho) as (Lρ & Rb0 & HRs & Hfam).
    injection HRs as HRsE HRsB. rewrite <- HRsB in Hfam. clear HRsB HRsE.
    (* --- THE THIRD COMPONENT OF THE PAPER'S GLOBAL FRESHNESS.  ψa sits inside
       the ideal (α ∈ ftv R'), and ρ only ADDS tags, so ψa's tags Ψ' are among
       the SUBJECT's — where the rule's own freshness premise already excludes
       the instantiation's.  (See the two lemmas above.) --- *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
    assert (HΨ'sub : Ψ' [<=] ftag_in_uskl (uskl_all_tag ε R)).
    { pose proof (uskl_rho_ftag_target_sub Hrho) as Ht.
      pose proof (@ftag_in_uskl_subst_lower ψa α
                    (msubst_uskl_syn κ (uskl_all_tag εr R0))
                    (@msubst_uskl_syn_ftv_keep κ α (uskl_all_tag εr R0)
                       Hακdom HαR)) as Hl.
      cbn [ftag_in_uskl subst_uskl_in_uskl msubst_uskl_syn] in Ht, Hl |- *.
      clear - Ht Hl Hψatag; fsetdec. }
    assert (HΨgfresh : Ψ'0 ∩ Ψ' [=] empty) by (clear - H1 HΨ'sub; fsetdec).
    (* --- the fresh RIGID β, and ρ_b = ρ ∘ [ψ/β] --- *)
    (* the guess's wf comes at the DERIVATION's context; weaken it here *)
    assert (Hwfψ : {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hext | exact H3 ]).
    assert (Hlcψ : lc_uskl ψ)
      by (apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact Hwfψ).
    assert (Hlcψa : lc_uskl ψa)
      by (apply is_tskl_lc; inversion Htags; assumption).
    pick fresh β for
      (Lρ `union` dom Θ `union` dom Θ0 `union` dom κ `union` Δ `union` Δρ
         `union` def_ftv Θ `union` singleton α `union` ftvar_in_uskl R
         `union` ftvar_in_uskl R0 `union` ftvar_in_uskl ψ
         `union` ftvar_in_uskl ψa `union` ftvar_in_pskl P0
         `union` ftvar_in_pskl Pi `union` ftvar_in_pskl (uskl_to_pskl R0)
         (* the ∀ rule's own avoid-input (cluster 3) *)
         `union` ftvar_in_aenv Θ0).
    assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
    assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
    assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
    assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
    assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
    assert (HβR : β `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
    assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
    assert (Hβα : β <> α) by (clear - Fr; solve_notin).
    destruct (@uskl_rho_subst NM Θ Δρ Ψρ
                (open_uskl_wrt_uskl R (uskl_var_f β))
                (open_uskl_wrt_uskl
                   (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R0))
                   (uskl_var_f β))
                (Hfam β ltac:(clear - Fr; solve_notin))
                β ψ Ψ'0 H2 Hwfψ Hlcψ HβΘ HβΔρ)
      as (Ψρ' & HΨρ'sub & HΨρ'mono & _ & Hrho').
    rewrite <- (@subst_uskl_in_uskl_intro β R ψ) in Hrho'; [ | exact HβR ].
    rewrite <- (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa)
      in Hrho'.
    (* --- the recursive call's premises at Θ0,β / Θ,β / add β Δ / add β Δρ --- *)
    assert (Hweak0 : forall (x : atom) (b : abind),
              binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
      by (intros x b Hb; apply binds_app_3; exact Hb).
    assert (Hweak : forall (x : atom) (b : abind),
              binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; exact Hb).
    assert (Hwfβ : {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; assumption).
    assert (Hwfβ0 : {{ ⊢ ((β ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; assumption).
    assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - HαΘ Hβα; fsetdec).
    assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
      by (simpl; clear - HαΘ0 Hβα; fsetdec).
    assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
      by (apply a_inc_cons_tvar; exact Hκ).
    assert (HeraseRβ : ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ
              = open_pskl_wrt_pskl (uskl_to_pskl R0) (pskl_var_f β))
      by (apply uskl_to_pskl_open).
    assert (HscopeRβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
              [<=] add α (dom ((β ~ abind_tvar) ++ Θ0)
                            `union` dom ((β ~ abind_tvar) ++ Θ))).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β))
        as Hup.
      simpl in Hup, HscopeR |- *. clear - Hup HscopeR; fsetdec. }
    assert (HlcR0β : lc_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))).
    { inversion HlcR; subst.
      match goal with Hb : forall α0, lc_uskl _ |- _ => apply Hb end. }
    assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
              ∩ Ψ' [=] empty).
    { rewrite ftag_in_uskl_open_var.
      cbn [ftag_in_uskl] in Hdisj. clear - Hdisj; fsetdec. }
    assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hweak0 | exact HwfP0 ]).
    assert (HwfPiβ : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pi }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hweak0 | exact HwfPi ]).
    assert (HΨs1β : (Ψ `union` Ψ'0)
              [<=] union (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                     (union Ψρ' Ψa)).
    { (* the premise's index is bounded by its own subject [open R ψ], whose
         tags ρ bounds by Ψρ' plus the IDEAL's — and the ideal's are ψa's
         (⊆ Ψ') plus R0's.  Ψ' is then killed on both sides: the guess's tags
         miss it ([HΨgfresh]) and Ψ's own bound [HΨs1] only offers εr there,
         which [Hdisj] excludes. *)
      rewrite ftag_in_uskl_open_var.
      pose proof (ad_pat_sub_g_ftag_sub Hsubty) as Hs.
      pose proof (uskl_rho_ftag_sub Hrho') as Hr.
      pose proof (@ftag_in_uskl_subst_uskl_in_uskl ψa α
                    (msubst_uskl_syn κ
                       (open_uskl_wrt_uskl R0 (uskl_var_f β)))) as Hb.
      pose proof (ftag_in_uskl_msubst_uskl_syn κ
                    (open_uskl_wrt_uskl R0 (uskl_var_f β))) as Hm.
      pose proof (ftag_in_uskl_open_var R0 β) as Hop.
      cbn [ftag_in_uskl] in HΨs1, Hdisj.
      clear - Hs Hr Hb Hm Hop HΨs1 Hdisj Hψatag HΨgfresh HΨρ'mono; fsetdec. }
    assert (HΨs2β : Ψa [<=] Ψ `union` Ψ'0) by (clear - HΨs2; fsetdec).
    assert (Hdfreshβ : delta_def_fresh (add β Δ) ((β ~ abind_tvar) ++ Θ)).
    { intros β0 α3 τ3 Hβ0 Hb.
      assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
        by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
              [ discriminate Habs | exact Hb' ]).
      destruct (AtomSetProperties.In_dec β0 Δ) as [Hin1 | Hni1];
        [ eapply Hdfresh; [ exact Hin1 | exact Hb' ] | ].
      assert (Heqβ : β0 = β) by (clear - Hβ0 Hni1; fsetdec); subst β0.
      pose proof (a_wf_ptyp_ftv_dom
                    (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
      clear - Hd HβΘ; fsetdec. }
    (* the SHIELD steps the SUBJECT by [sss_forall_l_tag] — Sub-ForallL is
       so P0 does NOT move — only Δρ grows, by a rigid β fresh for the guess,
       and the context gains it too *)
    assert (Hapartβ : flex_apart_deep ((β ~ abind_tvar) ++ Θ0) (add β Δρ) P0 ψa)
      by (apply flex_apart_deep_weaken_tvar;
          eapply flex_apart_deep_delta_grow;
            [ exact Hapart | clear; fsetdec
            | clear - Hβψa; fsetdec ]).
    assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
              ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad).
    { (* the Δ-congruence's set argument is PINNED by a named [assert] —
         inline, its Δ is an evar when the [=] side goal runs and [fsetdec]
         does not terminate *)
      assert (Hp0 : {{ ((β ~ abind_tvar) ++ Θ) ⨟ (Δ `union` singleton β)
                ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad).
      { eapply ad_partial_precise_delta_weaken_fresh;
          [ eapply ad_partial_precise_weaken; [ exact Hpre | exact Hweak ]
          | clear - Hβψa; fsetdec
          | intros β0 α3 τ3 Hβ0 Hb;
            assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
              by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                    [ discriminate Habs | exact Hb' ]);
            assert (Heqβ : β0 = β) by (clear - Hβ0; fsetdec); subst β0;
            pose proof (a_wf_ptyp_ftv_dom
                          (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd;
            clear - Hd HβΘ; fsetdec ]. }
      eapply ad_partial_precise_delta_cong; [ exact Hp0 | clear; fsetdec ]. }
    assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad)
      by (eapply ad_refine_syn_weaken; [ exact Hrefine | exact Hweak ]).
    assert (Hrhoβ : uskl_rho NM ((β ~ abind_tvar) ++ Θ) (add β Δρ) Ψρ'
              (open_uskl_wrt_uskl R ψ)
              (subst_uskl_in_uskl ψa α
                 (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))))
      by (eapply uskl_rho_weaken; [ exact Hrho' | exact Hweak ]).
    assert (HΨρβ : Ψρ' ∩ Ψ' [=] empty)
      by (clear - HΨρ'sub HΨρ HΨgfresh; fsetdec).
    assert (Hrfrβ : rho_fresh (add β Δρ) ((β ~ abind_tvar) ++ Θ) κ).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1].
      - destruct (Hrfr α0 Hin1) as (Hb & Him & Hdf).
        repeat split; [ apply binds_app_3; exact Hb | exact Him | ].
        intros α3 τ3 Hb3. eapply Hdf.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb3) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ].
      - assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
        repeat split.
        + unfold binds; left; reflexivity.
        + intros pp Hpp.
          pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb.
          clear - Hb HβΘ; fsetdec.
        + intros α3 τ3 Hb3.
          assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
            by (destruct (binds_cons_1 _ _ _ _ _ _ Hb3) as [[_ Habs] | Hb'];
                  [ discriminate Habs | exact Hb' ]).
          pose proof (a_wf_ptyp_ftv_dom
                        (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
          clear - Hd HβΘ; fsetdec. }
    assert (HΔρΔβ : add β Δρ [<=] add β Δ) by (clear - HΔρΔ; fsetdec).
    assert (HΔρftvβ : forall α0, α0 `in` (add β Δρ) ->
              α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1];
        [ exact (HΔρftv α0 Hin1) | ].
      assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
      clear - Fr; solve_notin. }
    assert (HΔρPiβ : forall α0, α0 `in` (add β Δρ) ->
              α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1];
        [ exact (HΔρPi α0 Hin1) | ].
      assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
      pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi)) as Hsh.
      enough (Hne : β `notin` ftvar_in_pskl (msubst_pskl κ Pi))
        by (clear - Hsh Hne; fsetdec).
      apply msubst_pskl_ftv_avoid;
        [ intros pp Hpp;
          pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
          clear - Hb HβΘ; fsetdec
        | clear - Fr; solve_notin ]. }
    assert (Hextβ : forall (x : atom) (b : abind),
              binds x b Θsm -> binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; apply Hext; exact Hb).
    (* the subject's wf opens with the GUESS (the ∀ is on the subject side) *)
    assert (HwfSubjβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty
              ⊢ₚₛ ⌊ open_uskl_wrt_uskl R ψ ⌋ˢ }}a).
    { assert (Hexs : exists Lb, forall α0, α0 `notin` Lb ->
                {{ Θ ⨟ (add α0 empty)
                  ⊢ₚₛ (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α0)) }}a).
      { cbn [uskl_to_pskl] in HwfSubj; inversion HwfSubj; subst;
        eexists; eassumption. }
      destruct Hexs as (Lb & Hbody).
      rewrite uskl_to_pskl_open_gen.
      eapply a_wf_pskl_weaken; [ exact Hweak | ].
      eapply a_wf_pskl_open; [ exact Hbody | exact Hwfψ ]. }
    (* the ρ-opened body may itself be a special case, so dispatch as usual *)
    (* the Θw pack under the binder — [Θw] does NOT move; keeping it fixed is
       what lets β be stripped out of the increase.  Δρ DOES grow here (β is a
       ρ-replaced variable on this row), and [HΔρw] survives because β is
       picked fresh for Θ ⊇ Θw. *)
    assert (HβΘw : β `notin` dom Θw)
      by (pose proof (@aenv_binds_dom_sub Θw Θ Hmon) as Hdw;
          clear - Hdw HβΘ; fsetdec).
    assert (Hmonβ : forall x b, binds x b Θw ->
              binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; apply Hmon; exact Hb).
    assert (Hnrβ : forall x b, binds x b ((β ~ abind_tvar) ++ Θ) ->
              binds x b Θw \/ b = abind_tvar).
    { intros x b Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
        [ right; exact Heq | exact (Hnr _ _ Hb') ]. }
    assert (Hκwβ : forall α0, a_flex_tvar ((β ~ abind_tvar) ++ Θ0) α0 ->
              ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw)
      by (intros α0 Hf; apply Hκw; eapply a_flex_tvar_strip_tvar; exact Hf).
    assert (HΔρwβ : (add β Δρ) ∩ dom Θw [=] empty)
      by (clear - HΔρw HβΘw; fsetdec).
    assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
      by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
    assert (REC : exists 𝒞 Ξc Ξs Pa κc κs,
      ({{ ((β ~ abind_tvar) ++ Θ0) ⊢
         ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
      {{ (Ξc ++ ((β ~ abind_tvar) ++ Θ0)) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
      all_flex_mono Ξs /\
      uniq Ξs /\
      keys κs = keys Ξs /\
      (forall α0, α0 `in` dom Ξs -> α0 `notin` add β Lav) /\
      Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
      {{ (Ξs ++ Ξc ++ ((β ~ abind_tvar) ++ Θ0)) ⨟ empty ⊢ₚₛ Pa }}a /\
      {{ ⊢ (Ξc ++ ((β ~ abind_tvar) ++ Θ0)) }}a /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      Forall (fun p => (ftvar_in_ptyp (snd p)) ∩ (add β Δρ) [=] empty) κc /\
      (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ ((β ~ abind_tvar) ++ Θ0))
        ⊑ ((β ~ abind_tvar) ++ Θ) /\
      a_inc_equiv ((β ~ abind_tvar) ++ Θ0) κ κ ((β ~ abind_tvar) ++ Θ) /\
      (forall α0, α0 `in` dom κc ->
         α0 `notin` add α (dom ((β ~ abind_tvar) ++ Θ0)
                             `union` dom ((β ~ abind_tvar) ++ Θ)
                             `union` ftvar_in_uskl ψa)) /\
      {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
        ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
      (M = mode_tc ->
         ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                               `union` dom κ
                               `union` def_ftv ((β ~ abind_tvar) ++ Θ)
         \/ (alpha_stack α ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ
             /\ Ξc = nil /\ κc = nil /\ 𝒞 = a_cstr_sub M P0 :: nil))).
    { destruct (AtomSetProperties.In_dec α
                  (ftvar_in_pskl ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_eq_var_dec
                    ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ α)
          as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply (@a_looksub_solve_complete_leaf n NM M
                    ((β ~ abind_tvar) ++ Θ0) Θsm ((β ~ abind_tvar) ++ Θ) Θw κ
                    (add β Δ) (add β Δρ) Ψρ' Ψ' Ψi Ψa (Ψ `union` Ψ'0) ψa Q
                    ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ P0 Pi
                    (open_uskl_wrt_uskl R0 (uskl_var_f β))
                    (open_uskl_wrt_uskl R ψ) α
                    Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ Hκwβ Hψaw HΔρwβ
                    HwfP0β HwfPiβ HmodSK HmodTY Hκβ HαΘβ HαΘ0β
                    eq_refl HscopeRβ HlcR0β Htags Hdisjβ Hsub Hdfreshβ
                    Hapartβ Hpreβ HΨs1β HΨs2β Hsubty HwfSubjβ Hrefβ
                    Hrhoβ HΨρβ Hrfrβ HΔρΔβ HΔρPiβ);
            [ right; exact Heq0 | exact Hextβ | exact HLavβ ].
        + (* recurse *)
          assert (HαRβ : α `in`
                    ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
            by (rewrite <- ftvar_in_pskl_uskl_to_pskl; exact Hin0).
          eapply (IHHsubty Htags ((β ~ abind_tvar) ++ Θ)
                    ((β ~ abind_tvar) ++ Θ0) κ (add β Δ) (add β Δρ) Ψρ'
                    (open_uskl_wrt_uskl R0 (uskl_var_f β))
                    ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ P0 Pi Ψi Ψa
                    Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρwβ
                    HαΘ0β Hκβ Hακdom Hκav eq_refl HscopeRβ
                    HlcR0β Hdisjβ HwfP0β HwfPiβ HmodSK HmodTY HαΘβ Hsub
                    HΨs1β HΨs2β Hdfreshβ Hapartβ Hpreβ Hrefβ Hrhoβ HΨρβ
                    Hrfrβ HΔρΔβ HΔρftvβ HΔρPiβ Hextβ Hne0 Hin0 HαRβ
                    HwfSubjβ
                    (* ρ-apartness survives the fresh binder: β ∉ ftv ψa *)
                    ltac:(clear - Hψaap Hβψa; solve_notin_auto)
                    (add β Lav) HLavβ).
      - (* leaf, absent *)
        eapply (@a_looksub_solve_complete_leaf n NM M
                  ((β ~ abind_tvar) ++ Θ0) Θsm ((β ~ abind_tvar) ++ Θ) Θw κ
                  (add β Δ) (add β Δρ) Ψρ' Ψ' Ψi Ψa (Ψ `union` Ψ'0) ψa Q
                  ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ P0 Pi
                  (open_uskl_wrt_uskl R0 (uskl_var_f β))
                  (open_uskl_wrt_uskl R ψ) α
                  Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ Hκwβ Hψaw HΔρwβ
                  HwfP0β HwfPiβ HmodSK HmodTY Hκβ HαΘβ HαΘ0β
                  eq_refl HscopeRβ HlcR0β Htags Hdisjβ Hsub Hdfreshβ
                  Hapartβ Hpreβ HΨs1β HΨs2β Hsubty HwfSubjβ Hrefβ
                  Hrhoβ HΨρβ Hrfrβ HΔρΔβ HΔρPiβ);
          [ left; exact Hnin0 | exact Hextβ | exact HLavβ ]. }
    destruct REC as (𝒞 & Ξc & Ξs & Pa & κc & κs
                     & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                     & HwfPa & HwfΞ & HαΞ
                     & Hmapfst & Himg & HimgΔ & Hinc & Hinceq & Hκfresh
                     & Hprec & HftvC).
    (* --- β-freeness of every output, then STRIP it --- *)
    pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
    assert (HβΞc : β `notin` dom Ξc).
    { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
      apply Hκfresh. simpl; clear; fsetdec. }
    assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
    { (* β is a rigid of the PREMISE's context, hence not a name the run can
         have invented — [a_looksub_ftv_ctx] restores the exact bound *)
      pose proof (a_wf_pskl_ftv_dom HwfP0) as Hpf.
      eapply a_looksub_ftv_ctx;
        [ exact HLK | simpl; clear; fsetdec
        | clear - Hpf HβΘ0; fsetdec | exact HβΞc ]. }
    assert (HβΞs : β `notin` dom Ξs)
      by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
    assert (HβPa : β `notin` ftvar_in_pskl Pa).
    { intro Hin0.
      destruct (a_solve_cstr_ftv HSolve Hin0) as [Hl | Hr];
        [ pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi;
          clear - Hl Hfi HβC HβΘ0 HβΞs; fsetdec
        | apply Hr; repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
    { rewrite Forall_forall in Himg |- *. intros p Hp.
      specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
    assert (Hfmc : all_flex_mono Ξc)
      by (eapply a_looksub_all_flex_mono; exact HLK).
    (* ⭐ the SOLVE BLOCK's payloads dodge β because they are well-formed in
       the FIXED [Θw], which predates the binder *)
    assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
    { rewrite Forall_forall. intros p Hp0.
      pose proof (forall_wf_mono_images_dom HFs p Hp0) as Hb.
      clear - Hb HβΘw; fsetdec. }
    exists 𝒞, Ξc, Ξs, Pa, κc, κs.
    repeat split.
    -- (* a_looksub : LS-ForallL, the single β-instance renamed into the
          cofinite family — β ∉ ftv 𝒞 because the TARGET P0 does not move *)
       rewrite <- HeraseR.
       (* EXISTS-FRESH (cluster 3): fire at the β this row already picked *)
       rewrite HeraseRβ in HLK.
       apply a_looksub__forall_l with (β := β);
         [ clear - Fr; solve_notin | exact HLK ].
    -- (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
    -- (* all_flex_mono Ξs *) exact Hfms.
    -- (* uniq Ξs *) exact Hus.
    -- (* keys κs = keys Ξs *) exact Hks.
    -- (* dom Ξs ∩ Lav = ∅ *)
       intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
    -- (* the SOLVE block's payloads — at the FIXED Θw *) exact HFs.
    -- (* wf Pa *)
       rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
       apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
         [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
           exact HwfPa
         | exact HβPa ].
    -- (* a_wf_aenv *)
       eapply a_wf_aenv_strip_mid;
         [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
    -- (* α ∉ dom Ξc *) exact HαΞ.
    -- (* keys *) exact Hmapfst.
    -- (* κc images ⊆ ftv ψa *) exact Himg.
    -- (* κc images ⊥ Δρ *)
       rewrite Forall_forall in HimgΔ |- *. intros p Hp.
       specialize (HimgΔ p Hp). clear - HimgΔ; fsetdec.
    -- (* a_inc — the strip peels BOTH blocks at once *)
       rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
       rewrite <- (list_app_assoc κs κc κ).
       eapply a_inc_strip_tvar_mid;
         [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
         | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
         | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
         | exact HβΘ
         | rewrite (list_app_assoc κs κc κ);
           rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
           exact Hinc ].
    -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
    -- (* κc fresh *)
       intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
       clear - Hκfresh; fsetdec.
    -- (* precision : strip β from the context, then from Δ *)
       assert (HβPaκ : β `notin`
                 ftvar_in_pskl (msubst_pskl (κs ++ κc ++ κ) Pa)).
       { apply msubst_pskl_ftv_avoid;
           [ intros pp Hpp; apply in_app_or in Hpp; destruct Hpp as [Hpp | Hpp];
               [ rewrite Forall_forall in Hβκs; apply Hβκs; exact Hpp
               | apply in_app_or in Hpp; destruct Hpp as [Hpp | Hpp];
                   [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hpp
                   | pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
                     clear - Hb HβΘ; fsetdec ] ]
           | exact HβPa ]. }
       eapply ad_partial_precise_delta_shrink_fresh
         with (Δ := Δ) (Δ' := singleton β);
         [ eapply ad_partial_precise_strip_tvar_mid
             with (β := β) (Θ1 := nil) (Θ2 := Θ);
             [ exact Hprec | reflexivity
             | intros α0 τ0 Hb;
               assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                 by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                       [ discriminate Habs | exact Hb' ]);
               pose proof (a_wf_ptyp_ftv_dom
                             (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb')) as Hftd;
               clear - Hftd HβΘ; fsetdec
             | exact HβPaκ
             | exact Hβψa ]
         | clear; fsetdec
         | clear - Hβψa; fsetdec
         | intros β0 α3 τ3 Hβ0 Hb;
           assert (Heqβ : β0 = β) by (clear - Hβ0; fsetdec); subst β0;
           pose proof (a_wf_ptyp_ftv_dom
                         (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb)) as Hd;
           clear - Hd HβΘ; fsetdec ].
    -- (* ftv 𝒞 : both disjuncts survive the binder.  LEFT — [def_ftv] ignores
          a rigid entry, so Θ,β contributes nothing new.  RIGHT — an α-stack
          under the opener lifts to one under the ∀ ([alpha_stack_all_of_one]
          turns this SINGLE β-instance into [ast_all]'s cofinite family), and
          ⌊∀^ε R0⌋ˢ IS [pskl_all_syn ⌊R0⌋ˢ]. *)
       intros HMtc; destruct (HftvC HMtc) as [Hleft | (Hstk & -> & -> & ->)].
       ++ left. cbn [def_ftv] in Hleft. exact Hleft.
       ++ right. repeat split; try reflexivity.
          rewrite <- HeraseR. cbn [uskl_to_pskl].
          rewrite HeraseRβ in Hstk.
          eapply alpha_stack_all_of_one;
            [ exact Hstk | clear - Hβα; auto | clear - Fr; solve_notin ].
  - (* ForallL, untagged : identical to the tagged row; the mech splits the
       paper's single rule by the subject's POTENTIAL tag.  The only textual
       difference is the ρ-inversion ([uskl_rho_all_syn_r_inv]) and the
       absence of a binder tag from the subject's tags. *)
    (* --- the ρ-inversion: the ideal is an UNTAGGED ∀ too, and its body's ρ-family is
       what Sub-ForallL extends --- *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    destruct (uskl_rho_all_syn_r_inv Hrho) as (Lρ & Rb0 & HRs & Hfam).
    injection HRs as HRsB. rewrite <- HRsB in Hfam. clear HRsB.
    (* --- THE THIRD COMPONENT OF THE PAPER'S GLOBAL FRESHNESS.  ψa sits inside
       the ideal (α ∈ ftv R'), and ρ only ADDS tags, so ψa's tags Ψ' are among
       the SUBJECT's — where the rule's own freshness premise already excludes
       the instantiation's.  (See the two lemmas above.) --- *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
    assert (HΨ'sub : Ψ' [<=] ftag_in_uskl (uskl_all_syn R)).
    { pose proof (uskl_rho_ftag_target_sub Hrho) as Ht.
      pose proof (@ftag_in_uskl_subst_lower ψa α
                    (msubst_uskl_syn κ (uskl_all_syn R0))
                    (@msubst_uskl_syn_ftv_keep κ α (uskl_all_syn R0)
                       Hακdom HαR)) as Hl.
      cbn [ftag_in_uskl subst_uskl_in_uskl msubst_uskl_syn] in Ht, Hl |- *.
      clear - Ht Hl Hψatag; fsetdec. }
    assert (HΨgfresh : Ψ'0 ∩ Ψ' [=] empty) by (clear - H1 HΨ'sub; fsetdec).
    (* --- the fresh RIGID β, and ρ_b = ρ ∘ [ψ/β] --- *)
    (* the guess's wf comes at the DERIVATION's context; weaken it here *)
    assert (Hwfψ : {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hext | exact H3 ]).
    assert (Hlcψ : lc_uskl ψ)
      by (apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact Hwfψ).
    assert (Hlcψa : lc_uskl ψa)
      by (apply is_tskl_lc; inversion Htags; assumption).
    pick fresh β for
      (Lρ `union` dom Θ `union` dom Θ0 `union` dom κ `union` Δ `union` Δρ
         `union` def_ftv Θ `union` singleton α `union` ftvar_in_uskl R
         `union` ftvar_in_uskl R0 `union` ftvar_in_uskl ψ
         `union` ftvar_in_uskl ψa `union` ftvar_in_pskl P0
         `union` ftvar_in_pskl Pi `union` ftvar_in_pskl (uskl_to_pskl R0)
         (* the ∀ rule's own avoid-input (cluster 3) *)
         `union` ftvar_in_aenv Θ0).
    assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
    assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
    assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
    assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
    assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
    assert (HβR : β `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
    assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
    assert (Hβα : β <> α) by (clear - Fr; solve_notin).
    destruct (@uskl_rho_subst NM Θ Δρ Ψρ
                (open_uskl_wrt_uskl R (uskl_var_f β))
                (open_uskl_wrt_uskl
                   (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R0))
                   (uskl_var_f β))
                (Hfam β ltac:(clear - Fr; solve_notin))
                β ψ Ψ'0 H2 Hwfψ Hlcψ HβΘ HβΔρ)
      as (Ψρ' & HΨρ'sub & HΨρ'mono & _ & Hrho').
    rewrite <- (@subst_uskl_in_uskl_intro β R ψ) in Hrho'; [ | exact HβR ].
    rewrite <- (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa)
      in Hrho'.
    (* --- the recursive call's premises at Θ0,β / Θ,β / add β Δ / add β Δρ --- *)
    assert (Hweak0 : forall (x : atom) (b : abind),
              binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
      by (intros x b Hb; apply binds_app_3; exact Hb).
    assert (Hweak : forall (x : atom) (b : abind),
              binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; exact Hb).
    assert (Hwfβ : {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; assumption).
    assert (Hwfβ0 : {{ ⊢ ((β ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; assumption).
    assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - HαΘ Hβα; fsetdec).
    assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
      by (simpl; clear - HαΘ0 Hβα; fsetdec).
    assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
      by (apply a_inc_cons_tvar; exact Hκ).
    assert (HeraseRβ : ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ
              = open_pskl_wrt_pskl (uskl_to_pskl R0) (pskl_var_f β))
      by (apply uskl_to_pskl_open).
    assert (HscopeRβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
              [<=] add α (dom ((β ~ abind_tvar) ++ Θ0)
                            `union` dom ((β ~ abind_tvar) ++ Θ))).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β))
        as Hup.
      simpl in Hup, HscopeR |- *. clear - Hup HscopeR; fsetdec. }
    assert (HlcR0β : lc_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))).
    { inversion HlcR; subst.
      match goal with Hb : forall α0, lc_uskl _ |- _ => apply Hb end. }
    assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
              ∩ Ψ' [=] empty).
    { rewrite ftag_in_uskl_open_var.
      cbn [ftag_in_uskl] in Hdisj. clear - Hdisj; fsetdec. }
    assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hweak0 | exact HwfP0 ]).
    assert (HwfPiβ : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pi }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hweak0 | exact HwfPi ]).
    assert (HΨs1β : (Ψ `union` Ψ'0)
              [<=] union (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                     (union Ψρ' Ψa)).
    { (* the premise's index is bounded by its own subject [open R ψ], whose
         tags ρ bounds by Ψρ' plus the IDEAL's — and the ideal's are ψa's
         (⊆ Ψ') plus R0's.  Ψ' is then killed on both sides: the guess's tags
         miss it ([HΨgfresh]) and Ψ's own bound [HΨs1] offers nothing there. *)
      rewrite ftag_in_uskl_open_var.
      pose proof (ad_pat_sub_g_ftag_sub Hsubty) as Hs.
      pose proof (uskl_rho_ftag_sub Hrho') as Hr.
      pose proof (@ftag_in_uskl_subst_uskl_in_uskl ψa α
                    (msubst_uskl_syn κ
                       (open_uskl_wrt_uskl R0 (uskl_var_f β)))) as Hb.
      pose proof (ftag_in_uskl_msubst_uskl_syn κ
                    (open_uskl_wrt_uskl R0 (uskl_var_f β))) as Hm.
      pose proof (ftag_in_uskl_open_var R0 β) as Hop.
      cbn [ftag_in_uskl] in HΨs1, Hdisj.
      clear - Hs Hr Hb Hm Hop HΨs1 Hdisj Hψatag HΨgfresh HΨρ'mono; fsetdec. }
    assert (HΨs2β : Ψa [<=] Ψ `union` Ψ'0) by (clear - HΨs2; fsetdec).
    assert (Hdfreshβ : delta_def_fresh (add β Δ) ((β ~ abind_tvar) ++ Θ)).
    { intros β0 α3 τ3 Hβ0 Hb.
      assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
        by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
              [ discriminate Habs | exact Hb' ]).
      destruct (AtomSetProperties.In_dec β0 Δ) as [Hin1 | Hni1];
        [ eapply Hdfresh; [ exact Hin1 | exact Hb' ] | ].
      assert (Heqβ : β0 = β) by (clear - Hβ0 Hni1; fsetdec); subst β0.
      pose proof (a_wf_ptyp_ftv_dom
                    (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
      clear - Hd HβΘ; fsetdec. }
    (* the SHIELD steps the SUBJECT by [sss_forall_l_syn] — Sub-ForallL is
       so P0 does NOT move — only Δρ grows, by a rigid β fresh for the guess,
       and the context gains it too *)
    assert (Hapartβ : flex_apart_deep ((β ~ abind_tvar) ++ Θ0) (add β Δρ) P0 ψa)
      by (apply flex_apart_deep_weaken_tvar;
          eapply flex_apart_deep_delta_grow;
            [ exact Hapart | clear; fsetdec
            | clear - Hβψa; fsetdec ]).
    assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
              ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad).
    { (* the Δ-congruence's set argument is PINNED by a named [assert] —
         inline, its Δ is an evar when the [=] side goal runs and [fsetdec]
         does not terminate *)
      assert (Hp0 : {{ ((β ~ abind_tvar) ++ Θ) ⨟ (Δ `union` singleton β)
                ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad).
      { eapply ad_partial_precise_delta_weaken_fresh;
          [ eapply ad_partial_precise_weaken; [ exact Hpre | exact Hweak ]
          | clear - Hβψa; fsetdec
          | intros β0 α3 τ3 Hβ0 Hb;
            assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
              by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                    [ discriminate Habs | exact Hb' ]);
            assert (Heqβ : β0 = β) by (clear - Hβ0; fsetdec); subst β0;
            pose proof (a_wf_ptyp_ftv_dom
                          (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd;
            clear - Hd HβΘ; fsetdec ]. }
      eapply ad_partial_precise_delta_cong; [ exact Hp0 | clear; fsetdec ]. }
    assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad)
      by (eapply ad_refine_syn_weaken; [ exact Hrefine | exact Hweak ]).
    assert (Hrhoβ : uskl_rho NM ((β ~ abind_tvar) ++ Θ) (add β Δρ) Ψρ'
              (open_uskl_wrt_uskl R ψ)
              (subst_uskl_in_uskl ψa α
                 (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))))
      by (eapply uskl_rho_weaken; [ exact Hrho' | exact Hweak ]).
    assert (HΨρβ : Ψρ' ∩ Ψ' [=] empty)
      by (clear - HΨρ'sub HΨρ HΨgfresh; fsetdec).
    assert (Hrfrβ : rho_fresh (add β Δρ) ((β ~ abind_tvar) ++ Θ) κ).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1].
      - destruct (Hrfr α0 Hin1) as (Hb & Him & Hdf).
        repeat split; [ apply binds_app_3; exact Hb | exact Him | ].
        intros α3 τ3 Hb3. eapply Hdf.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb3) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ].
      - assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
        repeat split.
        + unfold binds; left; reflexivity.
        + intros pp Hpp.
          pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb.
          clear - Hb HβΘ; fsetdec.
        + intros α3 τ3 Hb3.
          assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
            by (destruct (binds_cons_1 _ _ _ _ _ _ Hb3) as [[_ Habs] | Hb'];
                  [ discriminate Habs | exact Hb' ]).
          pose proof (a_wf_ptyp_ftv_dom
                        (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
          clear - Hd HβΘ; fsetdec. }
    assert (HΔρΔβ : add β Δρ [<=] add β Δ) by (clear - HΔρΔ; fsetdec).
    assert (HΔρftvβ : forall α0, α0 `in` (add β Δρ) ->
              α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1];
        [ exact (HΔρftv α0 Hin1) | ].
      assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
      clear - Fr; solve_notin. }
    assert (HΔρPiβ : forall α0, α0 `in` (add β Δρ) ->
              α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1];
        [ exact (HΔρPi α0 Hin1) | ].
      assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
      pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi)) as Hsh.
      enough (Hne : β `notin` ftvar_in_pskl (msubst_pskl κ Pi))
        by (clear - Hsh Hne; fsetdec).
      apply msubst_pskl_ftv_avoid;
        [ intros pp Hpp;
          pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
          clear - Hb HβΘ; fsetdec
        | clear - Fr; solve_notin ]. }
    assert (Hextβ : forall (x : atom) (b : abind),
              binds x b Θsm -> binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; apply Hext; exact Hb).
    (* the subject's wf opens with the GUESS (the ∀ is on the subject side) *)
    assert (HwfSubjβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty
              ⊢ₚₛ ⌊ open_uskl_wrt_uskl R ψ ⌋ˢ }}a).
    { assert (Hexs : exists Lb, forall α0, α0 `notin` Lb ->
                {{ Θ ⨟ (add α0 empty)
                  ⊢ₚₛ (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α0)) }}a).
      { cbn [uskl_to_pskl] in HwfSubj; inversion HwfSubj; subst;
        eexists; eassumption. }
      destruct Hexs as (Lb & Hbody).
      rewrite uskl_to_pskl_open_gen.
      eapply a_wf_pskl_weaken; [ exact Hweak | ].
      eapply a_wf_pskl_open; [ exact Hbody | exact Hwfψ ]. }
    (* the ρ-opened body may itself be a special case, so dispatch as usual *)
    (* the Θw pack under the binder — [Θw] does NOT move; keeping it fixed is
       what lets β be stripped out of the increase.  Δρ DOES grow here (β is a
       ρ-replaced variable on this row), and [HΔρw] survives because β is
       picked fresh for Θ ⊇ Θw. *)
    assert (HβΘw : β `notin` dom Θw)
      by (pose proof (@aenv_binds_dom_sub Θw Θ Hmon) as Hdw;
          clear - Hdw HβΘ; fsetdec).
    assert (Hmonβ : forall x b, binds x b Θw ->
              binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; apply Hmon; exact Hb).
    assert (Hnrβ : forall x b, binds x b ((β ~ abind_tvar) ++ Θ) ->
              binds x b Θw \/ b = abind_tvar).
    { intros x b Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
        [ right; exact Heq | exact (Hnr _ _ Hb') ]. }
    assert (Hκwβ : forall α0, a_flex_tvar ((β ~ abind_tvar) ++ Θ0) α0 ->
              ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw)
      by (intros α0 Hf; apply Hκw; eapply a_flex_tvar_strip_tvar; exact Hf).
    assert (HΔρwβ : (add β Δρ) ∩ dom Θw [=] empty)
      by (clear - HΔρw HβΘw; fsetdec).
    assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
      by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
    assert (REC : exists 𝒞 Ξc Ξs Pa κc κs,
      ({{ ((β ~ abind_tvar) ++ Θ0) ⊢
         ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
      {{ (Ξc ++ ((β ~ abind_tvar) ++ Θ0)) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
      all_flex_mono Ξs /\
      uniq Ξs /\
      keys κs = keys Ξs /\
      (forall α0, α0 `in` dom Ξs -> α0 `notin` add β Lav) /\
      Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
      {{ (Ξs ++ Ξc ++ ((β ~ abind_tvar) ++ Θ0)) ⨟ empty ⊢ₚₛ Pa }}a /\
      {{ ⊢ (Ξc ++ ((β ~ abind_tvar) ++ Θ0)) }}a /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      Forall (fun p => (ftvar_in_ptyp (snd p)) ∩ (add β Δρ) [=] empty) κc /\
      (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ ((β ~ abind_tvar) ++ Θ0))
        ⊑ ((β ~ abind_tvar) ++ Θ) /\
      a_inc_equiv ((β ~ abind_tvar) ++ Θ0) κ κ ((β ~ abind_tvar) ++ Θ) /\
      (forall α0, α0 `in` dom κc ->
         α0 `notin` add α (dom ((β ~ abind_tvar) ++ Θ0)
                             `union` dom ((β ~ abind_tvar) ++ Θ)
                             `union` ftvar_in_uskl ψa)) /\
      {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
        ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
      (M = mode_tc ->
         ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                               `union` dom κ
                               `union` def_ftv ((β ~ abind_tvar) ++ Θ)
         \/ (alpha_stack α ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ
             /\ Ξc = nil /\ κc = nil /\ 𝒞 = a_cstr_sub M P0 :: nil))).
    { destruct (AtomSetProperties.In_dec α
                  (ftvar_in_pskl ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_eq_var_dec
                    ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ α)
          as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply (@a_looksub_solve_complete_leaf n NM M
                    ((β ~ abind_tvar) ++ Θ0) Θsm ((β ~ abind_tvar) ++ Θ) Θw κ
                    (add β Δ) (add β Δρ) Ψρ' Ψ' Ψi Ψa (Ψ `union` Ψ'0) ψa Q
                    ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ P0 Pi
                    (open_uskl_wrt_uskl R0 (uskl_var_f β))
                    (open_uskl_wrt_uskl R ψ) α
                    Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ Hκwβ Hψaw HΔρwβ
                    HwfP0β HwfPiβ HmodSK HmodTY Hκβ HαΘβ HαΘ0β
                    eq_refl HscopeRβ HlcR0β Htags Hdisjβ Hsub Hdfreshβ
                    Hapartβ Hpreβ HΨs1β HΨs2β Hsubty HwfSubjβ Hrefβ
                    Hrhoβ HΨρβ Hrfrβ HΔρΔβ HΔρPiβ);
            [ right; exact Heq0 | exact Hextβ | exact HLavβ ].
        + (* recurse *)
          assert (HαRβ : α `in`
                    ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
            by (rewrite <- ftvar_in_pskl_uskl_to_pskl; exact Hin0).
          eapply (IHHsubty Htags ((β ~ abind_tvar) ++ Θ)
                    ((β ~ abind_tvar) ++ Θ0) κ (add β Δ) (add β Δρ) Ψρ'
                    (open_uskl_wrt_uskl R0 (uskl_var_f β))
                    ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ P0 Pi Ψi Ψa
                    Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρwβ
                    HαΘ0β Hκβ Hακdom Hκav eq_refl HscopeRβ
                    HlcR0β Hdisjβ HwfP0β HwfPiβ HmodSK HmodTY HαΘβ Hsub
                    HΨs1β HΨs2β Hdfreshβ Hapartβ Hpreβ Hrefβ Hrhoβ HΨρβ
                    Hrfrβ HΔρΔβ HΔρftvβ HΔρPiβ Hextβ Hne0 Hin0 HαRβ
                    HwfSubjβ
                    (* ρ-apartness survives the fresh binder: β ∉ ftv ψa *)
                    ltac:(clear - Hψaap Hβψa; solve_notin_auto)
                    (add β Lav) HLavβ).
      - (* leaf, absent *)
        eapply (@a_looksub_solve_complete_leaf n NM M
                  ((β ~ abind_tvar) ++ Θ0) Θsm ((β ~ abind_tvar) ++ Θ) Θw κ
                  (add β Δ) (add β Δρ) Ψρ' Ψ' Ψi Ψa (Ψ `union` Ψ'0) ψa Q
                  ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ P0 Pi
                  (open_uskl_wrt_uskl R0 (uskl_var_f β))
                  (open_uskl_wrt_uskl R ψ) α
                  Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ Hκwβ Hψaw HΔρwβ
                  HwfP0β HwfPiβ HmodSK HmodTY Hκβ HαΘβ HαΘ0β
                  eq_refl HscopeRβ HlcR0β Htags Hdisjβ Hsub Hdfreshβ
                  Hapartβ Hpreβ HΨs1β HΨs2β Hsubty HwfSubjβ Hrefβ
                  Hrhoβ HΨρβ Hrfrβ HΔρΔβ HΔρPiβ);
          [ left; exact Hnin0 | exact Hextβ | exact HLavβ ]. }
    destruct REC as (𝒞 & Ξc & Ξs & Pa & κc & κs
                     & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                     & HwfPa & HwfΞ & HαΞ
                     & Hmapfst & Himg & HimgΔ & Hinc & Hinceq & Hκfresh
                     & Hprec & HftvC).
    (* --- β-freeness of every output, then STRIP it --- *)
    pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
    assert (HβΞc : β `notin` dom Ξc).
    { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
      apply Hκfresh. simpl; clear; fsetdec. }
    assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
    { (* β is a rigid of the PREMISE's context, hence not a name the run can
         have invented — [a_looksub_ftv_ctx] restores the exact bound *)
      pose proof (a_wf_pskl_ftv_dom HwfP0) as Hpf.
      eapply a_looksub_ftv_ctx;
        [ exact HLK | simpl; clear; fsetdec
        | clear - Hpf HβΘ0; fsetdec | exact HβΞc ]. }
    assert (HβΞs : β `notin` dom Ξs)
      by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
    assert (HβPa : β `notin` ftvar_in_pskl Pa).
    { intro Hin0.
      destruct (a_solve_cstr_ftv HSolve Hin0) as [Hl | Hr];
        [ pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi;
          clear - Hl Hfi HβC HβΘ0 HβΞs; fsetdec
        | apply Hr; repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
    { rewrite Forall_forall in Himg |- *. intros p Hp.
      specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
    assert (Hfmc : all_flex_mono Ξc)
      by (eapply a_looksub_all_flex_mono; exact HLK).
    (* ⭐ the SOLVE BLOCK's payloads dodge β because they are well-formed in
       the FIXED [Θw], which predates the binder *)
    assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
    { rewrite Forall_forall. intros p Hp0.
      pose proof (forall_wf_mono_images_dom HFs p Hp0) as Hb.
      clear - Hb HβΘw; fsetdec. }
    exists 𝒞, Ξc, Ξs, Pa, κc, κs.
    repeat split.
    -- (* a_looksub : LS-ForallL, the single β-instance renamed into the
          cofinite family — β ∉ ftv 𝒞 because the TARGET P0 does not move *)
       rewrite <- HeraseR.
       (* EXISTS-FRESH (cluster 3): fire at the β this row already picked *)
       rewrite HeraseRβ in HLK.
       apply a_looksub__forall_l with (β := β);
         [ clear - Fr; solve_notin | exact HLK ].
    -- (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
    -- (* all_flex_mono Ξs *) exact Hfms.
    -- (* uniq Ξs *) exact Hus.
    -- (* keys κs = keys Ξs *) exact Hks.
    -- (* dom Ξs ∩ Lav = ∅ *)
       intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
    -- (* the SOLVE block's payloads — at the FIXED Θw *) exact HFs.
    -- (* wf Pa *)
       rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
       apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
         [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
           exact HwfPa
         | exact HβPa ].
    -- (* a_wf_aenv *)
       eapply a_wf_aenv_strip_mid;
         [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
    -- (* α ∉ dom Ξc *) exact HαΞ.
    -- (* keys *) exact Hmapfst.
    -- (* κc images ⊆ ftv ψa *) exact Himg.
    -- (* κc images ⊥ Δρ *)
       rewrite Forall_forall in HimgΔ |- *. intros p Hp.
       specialize (HimgΔ p Hp). clear - HimgΔ; fsetdec.
    -- (* a_inc — the strip peels BOTH blocks at once *)
       rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
       rewrite <- (list_app_assoc κs κc κ).
       eapply a_inc_strip_tvar_mid;
         [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
         | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
         | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
         | exact HβΘ
         | rewrite (list_app_assoc κs κc κ);
           rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
           exact Hinc ].
    -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
    -- (* κc fresh *)
       intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
       clear - Hκfresh; fsetdec.
    -- (* precision : strip β from the context, then from Δ *)
       assert (HβPaκ : β `notin`
                 ftvar_in_pskl (msubst_pskl (κs ++ κc ++ κ) Pa)).
       { apply msubst_pskl_ftv_avoid;
           [ intros pp Hpp; apply in_app_or in Hpp; destruct Hpp as [Hpp | Hpp];
               [ rewrite Forall_forall in Hβκs; apply Hβκs; exact Hpp
               | apply in_app_or in Hpp; destruct Hpp as [Hpp | Hpp];
                   [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hpp
                   | pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
                     clear - Hb HβΘ; fsetdec ] ]
           | exact HβPa ]. }
       eapply ad_partial_precise_delta_shrink_fresh
         with (Δ := Δ) (Δ' := singleton β);
         [ eapply ad_partial_precise_strip_tvar_mid
             with (β := β) (Θ1 := nil) (Θ2 := Θ);
             [ exact Hprec | reflexivity
             | intros α0 τ0 Hb;
               assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                 by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                       [ discriminate Habs | exact Hb' ]);
               pose proof (a_wf_ptyp_ftv_dom
                             (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb')) as Hftd;
               clear - Hftd HβΘ; fsetdec
             | exact HβPaκ
             | exact Hβψa ]
         | clear; fsetdec
         | clear - Hβψa; fsetdec
         | intros β0 α3 τ3 Hβ0 Hb;
           assert (Heqβ : β0 = β) by (clear - Hβ0; fsetdec); subst β0;
           pose proof (a_wf_ptyp_ftv_dom
                         (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb)) as Hd;
           clear - Hd HβΘ; fsetdec ].
    -- (* ftv 𝒞 : both disjuncts survive the binder.  LEFT — [def_ftv] ignores
          a rigid entry, so Θ,β contributes nothing new.  RIGHT — an α-stack
          under the opener lifts to one under the ∀ ([alpha_stack_all_of_one]
          turns this SINGLE β-instance into [ast_all]'s cofinite family), and
          ⌊∀^ε R0⌋ˢ IS [pskl_all_syn ⌊R0⌋ˢ]. *)
       intros HMtc; destruct (HftvC HMtc) as [Hleft | (Hstk & -> & -> & ->)].
       ++ left. cbn [def_ftv] in Hleft. exact Hleft.
       ++ right. repeat split; try reflexivity.
          rewrite <- HeraseR. cbn [uskl_to_pskl].
          rewrite HeraseRβ in Hstk.
          eapply alpha_stack_all_of_one;
            [ exact Hstk | clear - Hβα; auto | clear - Fr; solve_notin ].

  - (* Ghost : IMPOSSIBLE — the subject is [uskl_hole], so R' is □ and has
       no free variables, contradicting α ∈ ftv R'. *)
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR;
      solve [ contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec
            | inversion Hrho ].
  - (* GhostG : IMPOSSIBLE for the same reason (subject [uskl_holeg]). *)
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR;
      solve [ contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec
            | inversion Hrho ].
  - (* UnivGhostL : R' = ∀◇R0; the IH runs at the body with P0 UNCHANGED
       (so [sub_shield] is threaded as is), then LS-UnivGhostL rebuilds.

       RECIPE (the structural point that used to block this is SOLVED —
       [a_looksub_solve_complete_leaf] above).  A recursive row can land on
       a special case: here R0 may be [var α], and then R' = ∀◇α, whose
       erasure is ∀◇α ≠ α, so THIS level is not special while the level
       below is.  The IH cannot serve it — it demands [HPnα] and [Hin],
       which were reverted into the induction — and a derivation induction
       cannot re-run the dispatch the way P6-Cs's measure induction does.
       So every recursive site dispatches:

         destruct (In_dec α (ftv ⌊R0⌋ˢ)) as [Hin0 | Hnin0];
           [ destruct (pskl_eq_var_dec ⌊R0⌋ˢ α) as [Heq0 | Hne0];
               [ (* leaf, var  *) eapply a_looksub_solve_complete_leaf …
               | (* recurse    *) eapply IHHsubty … ]
           | (* leaf, absent *) eapply a_looksub_solve_complete_leaf … ].

       Then rebuild with LS-UnivGhostL: the conclusion at R0 is about
       [⌊R0⌋ˢ], and [a_looksub__univ_ghost_l] lifts it to [∀◇⌊R0⌋ˢ] = ⌊R'⌋ˢ
       with 𝒞, Ξc, Pa, κc ALL UNCHANGED — P0 does not move, so [sub_shield]
       threads as is and every other conjunct of the conclusion is
       literally the recursive one.  R''s shape comes from [HeqSub] by
       [destruct R']: every branch but [tophole] discriminates, and the
       variable branch is [HRnv]. *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    (* the ρ-IMAGE keeps the ghost: the rule already fixes it as [∀◇R], so the
       inversion's equation is an injection and the sub-ρ is at the SAME Ψρ *)
    destruct (uskl_rho_tophole_r_inv Hrho) as (Rb0 & HeqRs & Hrho0).
    injection HeqRs as HeqRs. rewrite <- HeqRs in Hrho0. clear HeqRs.
    (* the SUBJECT moves, so the shield steps with [sss_univ_ghost_l] —
       P0 stands still *)
    assert (Hapart0 : flex_apart_deep Θ0 Δρ P0 ψa) by exact Hapart.
    assert (REC : exists 𝒞 Ξc Ξs Pa κc κs,
      ({{ Θ0 ⊢ ⌊ R0 ⌋ˢ ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
      {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
      all_flex_mono Ξs /\
      uniq Ξs /\
      keys κs = keys Ξs /\
      (forall α0, α0 `in` dom Ξs -> α0 `notin` Lav) /\
      Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
      {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
      {{ ⊢ (Ξc ++ Θ0) }}a /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      Forall (fun p => (ftvar_in_ptyp (snd p)) ∩ Δρ [=] empty) κc /\
      (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
      a_inc_equiv Θ0 κ κ Θ /\
      (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
      (M = mode_tc ->
         ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                               `union` dom κ `union` def_ftv Θ
         \/ (alpha_stack α ⌊ R0 ⌋ˢ /\ Ξc = nil /\ κc = nil
             /\ 𝒞 = a_cstr_sub M P0 :: nil))).
    { assert (HlcR0 : lc_uskl R0) by (inversion HlcR; assumption).
      (* the wf premise is on the IMAGE now, so it strips directly *)
      assert (HwfSubj0 : {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a)
        by (cbn [uskl_to_pskl] in HwfSubj;
            eapply a_wf_pskl_tophole_inv; exact HwfSubj).
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl ⌊ R0 ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_eq_var_dec ⌊ R0 ⌋ˢ α) as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply (a_looksub_solve_complete_leaf
                    (Θ0 := Θ0) (Θs := Θsm) (Θ := Θ) (Θw := Θw) (κ := κ)
                    (Δρ := Δρ)
                    (Ψρ := Ψρ) (R' := R0) (Rsub := R) (P0 := P0) (Pi := Pi));
            solve [ exact HLav | eassumption | reflexivity | assumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | exact Hrho0 | exact HwfSubj0
                  | right; exact Heq0 ].
        + (* recurse *)
          eapply (IHHsubty Htags Θ Θ0 κ Δ Δρ Ψρ R0 (uskl_to_pskl R0) P0 Pi Ψi Ψa);
            solve [ exact HLav | eassumption | reflexivity | assumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | exact Hrho0 | exact HwfSubj0
                  | exact Hne0 | exact Hin0
                  | clear - HαR; cbn in HαR; fsetdec ].
      - (* leaf, absent *)
        eapply (a_looksub_solve_complete_leaf
                  (Θ0 := Θ0) (Θs := Θsm) (Θ := Θ) (Θw := Θw) (κ := κ)
                  (Δρ := Δρ)
                  (Ψρ := Ψρ) (R' := R0) (Rsub := R) (P0 := P0) (Pi := Pi));
          solve [ exact HLav | eassumption | reflexivity | assumption
                | clear - HscopeR; cbn in HscopeR; fsetdec
                | exact HlcR0
                | clear - Hdisj; cbn in Hdisj; fsetdec
                | clear - HΨs1; cbn in HΨs1; fsetdec
                | exact Hrho0 | exact HwfSubj0
                | left; exact Hnin0 ]. }
    destruct REC as (𝒞 & Ξc & Ξs & Pa & κc & κs
                     & Hlook & Hsolve0 & Hfms0 & Hus0 & Hks0 & Hfrs0 & HFs0
                     & HwfPa0 & HwfΞ0
                     & HαΞ0 & Hkeys0 & Himg0 & HimgΔ0 & Hinc0 & Hinceq0
                     & Hκf0 & Hprec0 & HftvC0).
    exists 𝒞, Ξc, Ξs, Pa, κc, κs.
    (* everything but the two ends passes through untouched; the ftv
       conjunct's RIGHT disjunct gains the ghost wrapper ([ast_tophole]),
       since ⌊∀◇R0⌋ˢ = ⌊∀◈R0⌋ˢ = [pskl_tophole ⌊R0⌋ˢ] *)
    repeat split; try assumption;
      [ rewrite <- HeraseR; apply a_looksub__univ_ghost_l; exact Hlook
      | intros HMtc;
        destruct (HftvC0 HMtc) as [Hleft | (Hstk & -> & -> & ->)];
          [ left; exact Hleft
          | right; repeat split; try reflexivity;
            rewrite <- HeraseR; cbn [uskl_to_pskl];
            apply ast_tophole; exact Hstk ] ].
  - (* UnivGhostLG : identical, for the dotted ghost — both ∀◇ and ∀◈
       ERASE to [pskl_tophole], so the very same LS-UnivGhostL rebuild
       applies and only the surviving [destruct R'] branch differs. *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    (* the ρ-IMAGE keeps the ghost: the rule already fixes it as [∀◇R], so the
       inversion's equation is an injection and the sub-ρ is at the SAME Ψρ *)
    destruct (uskl_rho_topholeg_r_inv Hrho) as (Rb0 & HeqRs & Hrho0).
    injection HeqRs as HeqRs. rewrite <- HeqRs in Hrho0. clear HeqRs.
    (* the SUBJECT moves, so the shield steps with [sss_univ_ghost_lg] —
       P0 stands still *)
    assert (Hapart0 : flex_apart_deep Θ0 Δρ P0 ψa) by exact Hapart.
    assert (REC : exists 𝒞 Ξc Ξs Pa κc κs,
      ({{ Θ0 ⊢ ⌊ R0 ⌋ˢ ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
      {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
      all_flex_mono Ξs /\
      uniq Ξs /\
      keys κs = keys Ξs /\
      (forall α0, α0 `in` dom Ξs -> α0 `notin` Lav) /\
      Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
      {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
      {{ ⊢ (Ξc ++ Θ0) }}a /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      Forall (fun p => (ftvar_in_ptyp (snd p)) ∩ Δρ [=] empty) κc /\
      (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
      a_inc_equiv Θ0 κ κ Θ /\
      (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
      (M = mode_tc ->
         ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                               `union` dom κ `union` def_ftv Θ
         \/ (alpha_stack α ⌊ R0 ⌋ˢ /\ Ξc = nil /\ κc = nil
             /\ 𝒞 = a_cstr_sub M P0 :: nil))).
    { assert (HlcR0 : lc_uskl R0) by (inversion HlcR; assumption).
      (* the wf premise is on the IMAGE now, so it strips directly *)
      assert (HwfSubj0 : {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a)
        by (cbn [uskl_to_pskl] in HwfSubj;
            eapply a_wf_pskl_tophole_inv; exact HwfSubj).
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl ⌊ R0 ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_eq_var_dec ⌊ R0 ⌋ˢ α) as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply (a_looksub_solve_complete_leaf
                    (Θ0 := Θ0) (Θs := Θsm) (Θ := Θ) (Θw := Θw) (κ := κ)
                    (Δρ := Δρ)
                    (Ψρ := Ψρ) (R' := R0) (Rsub := R) (P0 := P0) (Pi := Pi));
            solve [ exact HLav | eassumption | reflexivity | assumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | exact Hrho0 | exact HwfSubj0
                  | right; exact Heq0 ].
        + (* recurse *)
          eapply (IHHsubty Htags Θ Θ0 κ Δ Δρ Ψρ R0 (uskl_to_pskl R0) P0 Pi Ψi Ψa);
            solve [ exact HLav | eassumption | reflexivity | assumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | exact Hrho0 | exact HwfSubj0
                  | exact Hne0 | exact Hin0
                  | clear - HαR; cbn in HαR; fsetdec ].
      - (* leaf, absent *)
        eapply (a_looksub_solve_complete_leaf
                  (Θ0 := Θ0) (Θs := Θsm) (Θ := Θ) (Θw := Θw) (κ := κ)
                  (Δρ := Δρ)
                  (Ψρ := Ψρ) (R' := R0) (Rsub := R) (P0 := P0) (Pi := Pi));
          solve [ exact HLav | eassumption | reflexivity | assumption
                | clear - HscopeR; cbn in HscopeR; fsetdec
                | exact HlcR0
                | clear - Hdisj; cbn in Hdisj; fsetdec
                | clear - HΨs1; cbn in HΨs1; fsetdec
                | exact Hrho0 | exact HwfSubj0
                | left; exact Hnin0 ]. }
    destruct REC as (𝒞 & Ξc & Ξs & Pa & κc & κs
                     & Hlook & Hsolve0 & Hfms0 & Hus0 & Hks0 & Hfrs0 & HFs0
                     & HwfPa0 & HwfΞ0
                     & HαΞ0 & Hkeys0 & Himg0 & HimgΔ0 & Hinc0 & Hinceq0
                     & Hκf0 & Hprec0 & HftvC0).
    exists 𝒞, Ξc, Ξs, Pa, κc, κs.
    (* everything but the two ends passes through untouched; the ftv
       conjunct's RIGHT disjunct gains the ghost wrapper ([ast_tophole]),
       since ⌊∀◇R0⌋ˢ = ⌊∀◈R0⌋ˢ = [pskl_tophole ⌊R0⌋ˢ] *)
    repeat split; try assumption;
      [ rewrite <- HeraseR; apply a_looksub__univ_ghost_l; exact Hlook
      | intros HMtc;
        destruct (HftvC0 HMtc) as [Hleft | (Hstk & -> & -> & ->)];
          [ left; exact Hleft
          | right; repeat split; try reflexivity;
            rewrite <- HeraseR; cbn [uskl_to_pskl];
            apply ast_tophole; exact Hstk ] ].
  - (* FlexMono : IMPOSSIBLE — the subject is a bare flexible variable, so
       R' would have to be a variable, which [HRnv] excludes. *)
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR;
      solve [ contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec
            | inversion Hrho ].
Qed.

(* ===================================================================== *)
(*  P6-Ss IS CLOSED.  All twelve rows and both special cases are proved;   *)
(*  the statement is the ρ-GENERALIZED one (see the header), and the       *)
(*  paper's is the premise-free ρ = identity corollary below.              *)
(*                                                                        *)
(*  Sub-ForallR was the last row, and the route it takes is NOT the one    *)
(*  originally planned.  A ψa-relative ftv-𝒞 conclusion alone is           *)
(*  UNREACHABLE: its leaf needs the sub-side analogue of                   *)
(*  [ad_pat_consis_target_ftv], and that is FALSE — machine-checked,       *)
(*  cex/cex_p6ss_sub_target_ftv.v.  [is_tskl] excludes [__ghost] but NOT   *)
(*  [__forall_l_tagged] ([uskl_all_tag] IS [is_tskl]), whose guess is     *)
(*  bounded only by [dom Θ], the DERIVATION's context — which              *)
(*  [__forall_r] grows by the very β being stripped.                       *)
(*                                                                        *)
(*  What works instead is the MODE-GUARDED DISJUNCTION this statement now  *)
(*  carries.  [__forall_r] forces [a_sub_mode_ty] + [mode_tc], and NM is   *)
(*  invariant along a derivation, so there only [__check], [__forall_r]    *)
(*  and [__forall_l_*] can fire ([ad_pat_sub_g_ty_tc_subject]).  Hence     *)
(*  under a Sub-ForallR this LEAF ([P = α]) is reachable only when P is an *)
(*  α-STACK — every other α-leaf sits under LS-Check, i.e. inside P6-Cs,   *)
(*  whose bound is already ψa-relative — and an α-stack never descends the *)
(*  target at all ([alpha_stack_looksub]), so the binder is never          *)
(*  introduced.  The mode guard is what makes Sub-Arrow vacuous, the row   *)
(*  that could not otherwise concatenate a left disjunct with a right one. *)
(*  docs/DESIGN-completeness-subtyping.md §8 (h).                          *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  P6-Ss — the PAPER'S statement, as the ρ = IDENTITY corollary.          *)
(*                                                                        *)
(*  Every added premise is discharged here, with no residue: [uskl_rho]    *)
(*  degenerates to [urho__refl] (local closure comes from the subject-wf   *)
(*  premise the paper already owes), [Θs := Θ], and [rho_fresh] / [Δρ ⊆ Δ] *)
(*  / the two ftv conditions are vacuous over an empty Δρ — which also     *)
(*  collapses [sub_shield]'s Δρ to [empty], i.e. the pre-generalization     *)
(*  premise.  Use THIS one unless you are threading a ρ down from a         *)
(*  Sub-ForallL.                                                           *)
(* ===================================================================== *)

Theorem a_looksub_solve_complete :
  forall n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->       (* the paper's "Ψ disjoint from Ψ'" *)
  Ψi `union` Ψa [=] Ψ' ->                   (* the paper's Ψi,Ψa = Ψ' *)
  (* ⭐ THE IDEAL GUESS IS Θ-SCOPED (2026-08-05, the SolE-FlexR repair).  The
     repaired SolE-FlexR reads the SOLVE block's payloads off [ψa], so they are
     well-formed only if it is; and it is NOT derivable from the premises below
     — when α does not occur in [κR'] the subject does not mention ψa at all.
     The generalized theorem states it at the fixed [Θw]; here [Θw := Θ].
     [paper-external wf side condition — docs/WF-SIDE-CONDITIONS.md] *)
  ftvar_in_uskl ψa [<=] dom Θ ->
  delta_def_fresh Δ Θ ->
  (* ⭕ (2026-08-05) the repair premise [flex_apart_deep Θ0 ∅ P0 ψa] is GONE:
     at Δρ = ∅ it is [fa_clean] at every reachable state, so the corollary
     discharges it internally ([flex_apart_deep_clean]). *)
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* subject = (κR')[ψa/α], EXACTLY the paper's form *)
  ad_pat_sub_g n NM M Ψsub Θ
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  {{ Θ ⨟ empty ⊢ₚₛ
    (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  (* ⭐ THE AVOID-SET PARAMETER: the SOLVE generates its own block now, and at
     a binder row the witness must be fixed BEFORE that block is picked. *)
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\        (* looksub α P P0 𝒞 Ξc *)
    (* ⭐ the SOLVE's own block [Ξs] and its aligned extension [κs], stacked
       the way [a_extract__solve] (def_extra.v:764) consumes them *)
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\          (* solve 𝒞 Pi Ξs Pa *)
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (* PHASE B.  The collected constraints are ψa-RELATIVE — so a Sub-ForallR
       above can strip its fresh binder β from them (β is fresh for ψa, Ξc and
       κ, and is a rigid, hence not in [def_ftv Θ]).  UNLESS the lookup
       subject is an α-STACK, the one shape whose 𝒞 is [a_cstr_sub M P0] at
       whatever target it is handed — and that shape never needs LS-ForallR
       at all ([alpha_stack_looksub]), so the binder is never introduced.
       The [mode_tc] guard is what makes Sub-Arrow VACUOUS (its conclusion is
       [mode_fn M]); that is the row which could not otherwise concatenate a
       left disjunct with a right one.
       ⚠️ The disjunct-free bound is UNREACHABLE: its leaf would need a
       sub-side [ad_pat_consis_target_ftv], and that is FALSE at
       [ad_pat_sub_g__forall_l_tagged] — cex/cex_p6ss_sub_target_ftv.v.
       docs/DESIGN-completeness-subtyping.md §8 (h). *)
    (M = mode_tc ->
       ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                             `union` dom κ `union` def_ftv Θ
       \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil
           /\ 𝒞 = a_cstr_sub M P0 :: nil)).
Proof.
  intros n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α.
  intros HwfΘ HwfΘ0 HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hψaw Hdfresh Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine L HL.
  (* ⭐ the repair premise, DISCHARGED: at Δρ = ∅ every state the P0-walk
     reaches is [fa_clean] (the guess cannot meet an empty ρ-replaced set). *)
  assert (Hapart : flex_apart_deep Θ0 empty P0 ψa)
    by (apply flex_apart_deep_clean; clear; fsetdec).
  (* [Θw := Θ] collapses the whole Θw pack: the two binds conditions are the
     identity and the κ-image bound is [a_inc_lookup_flex_ftv_dom] on [Hκ]. *)
  edestruct (@a_looksub_solve_complete_gen n NM M Θ0 Θ Θ Θ κ Δ empty empty Ψ'
               Ψi Ψa Ψsub ψa Q P P0 Pi R'
               (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) α)
    as (𝒞 & Ξc & Ξs & Pa & κc & κs
        & Hlook & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
        & HwfPa & HwfΞ & HαΞ & Hkeys
        & HFor & _ & Hinc & Heqv & Hκcfresh & Hprec & HftvC);
    [ exact HwfΘ | exact HwfΘ0
    | exact HwfΘ | intros x b Hb; exact Hb | intros x b Hb; left; exact Hb
    | intros α0 Hf; eapply a_inc_lookup_flex_ftv_dom; [ exact Hκ | exact Hf ]
    | exact Hψaw | clear; fsetdec
    | exact HwfP0 | exact HwfPi
    | exact HmodSK | exact HmodTY | exact Hκ | exact HαΘ | exact HαΘ0
    | exact HeraseR | exact HscopeR | exact HlcR | exact Htags | exact Hdisj
    | exact Hsub | exact Hdfresh | exact Hapart | exact Hpre
    | clear - HΨs1; fsetdec | exact HΨs2
    | exact Hsubty | exact HwfSubj | exact Hrefine
    | apply urho__refl;
        [ apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfSubj
        | clear; fsetdec ]
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | intros x b Hb; exact Hb
    | clear; fsetdec
    | exact HL
    | ].
  exists 𝒞, Ξc, Ξs, Pa, κc, κs.
  repeat split; assumption.
Qed.

