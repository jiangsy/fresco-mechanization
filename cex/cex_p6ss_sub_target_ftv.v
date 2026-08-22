(** ⚠️ THE SUB-SIDE ANALOGUE OF [ad_pat_consis_target_ftv] IS FALSE, AND
    [is_tskl] DOES NOT REPAIR IT — [ad_pat_sub_fuel__forall_l_tagged] IS THE
    CULPRIT.

    P6-Ss Phase B (docs/DESIGN-completeness-subtyping.md §8 (g)) planned to
    re-acquire P6-Cs's ψa-relative conclusion

        ftv 𝒞 ⊆ ftv ψa ∪ dom Θρ ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ

    so that Sub-ForallR could strip its fresh binder β from 𝒞.  P6-Cs
    discharges that conjunct at its leaf by the chain
    (prop_look_complete_cstr.v:2031-2041)

        ad_refine_syn_src_ftv → ad_pat_consis_target_ftv
                              → uskl_rsubst_ftv_subject_bound

    whose MIDDLE link is "a decorated subject's counterpart only mentions the
    subject's own variables and the context's DEFINITIONS":

        {{ Ψ ⨟ Θ ⊢ˢ ψ ∼ Q }}ad  →  is_tskl ψ  →  ftv Q ⊆ ftv ψ ∪ def_ftv Θ.

    The sub-side needs the same statement over [ad_pat_sub_fuel].  It was known
    to fail for [ad_pat_sub_fuel__ghost] (subject ◇, target an ARBITRARY
    Θ-scoped P), and [is_tskl] does exclude that row — [is_tskl] admits the
    DOTTED ghost ◈ ([uskl_holeg]) but not the plain ◇ ([uskl_hole]).  It also
    excludes [__ghostg], [__univ_ghost_l], [__forall_l_untagged] (whose
    subject is the tag-elided [uskl_all_syn]), and — via [__forall_r]'s
    [a_sub_mode_ty], which no [a_sub_mode_sk] rule can sit under — every
    other ghost row that matters for Sub-ForallR.

    IT DOES NOT EXCLUDE [__forall_l_tagged], and THAT row breaks the bound on
    its own: the subject [∀^ε α. α] IS [is_tskl], ForallL instantiates it
    with a guess ψ constrained only by [{{ Θ ⨟ empty ⊢ₚₛ ⌊ψ⌋ˢ }}a] — i.e. by
    [dom Θ], not [def_ftv Θ] — and the leaf then reads the target straight
    off that guess.  Below: Θ = β, subject [∀^ε α. α], target [β].

        ftv Q = {β}   ⊄   ∅ ∪ ∅ = ftv (∀^ε α. α) ∪ def_ftv Θ.

    WHY NO SHAPE PREMISE REPAIRS IT.  The strongest bound the sub side can
    carry is [ftv Q ⊆ ftv R ∪ dom Θ] — the guess is Θ-scoped and nothing
    more.  But that Θ is the DERIVATION's context, and
    [ad_pat_sub_fuel__forall_r] runs its premise at [Θ,β], so the only sound
    bound readmits exactly the binder Sub-ForallR has to strip.  ForallL is
    the essential subtyping rule; consistency escapes the problem only
    because it HAS no ForallL.

    WHAT SURVIVES — AND THE ROUTE THAT WORKS.  The P6-Ss THEOREM is NOT
    refuted.  In every configuration this lemma fails on, the algorithm
    still collects a β-free 𝒞, by taking LS-ForallL / LS-UnivGhostL BEFORE
    LS-ForallR: LS-Var then fires at the UNDESCENDED [∀β.P0].  And those
    configurations are exactly characterised, because
    [ad_pat_sub_fuel__forall_r] forces [a_sub_mode_ty] + [mode_tc], where the
    ONLY applicable rows are [__check], [__forall_r] and [__forall_l_*] —
    so under a Sub-ForallR the P6-Ss LEAF ([P = α]) is reachable only when
    P is a ∀/⊤◇-STACK over α, and then every ∀-body is constant, every
    ForallL guess is discarded, and the direct construction applies.
    Everywhere else the α-leaves sit under [__check], i.e. inside P6-Cs,
    whose ftv-𝒞 bound is already ψa-relative.

    Hence the ftv-𝒞 conclusion is carried as a mode-guarded DISJUNCTION
    (see docs/DESIGN-completeness-subtyping.md §8 (h)):

        M = mode_tc ->
          ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ  \/  α_stack α P

    — the mode guard makes Sub-Arrow vacuous (its conclusion is [mode_fn M]),
    and the [dom Θρ] term P6-Cs currently carries is dropped in favour of the
    apartness premise [Δρ ∩ ftv ψa = ∅], which P6-Ss maintains because ψa
    never moves and every ρ-binder is picked fresh. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_shapes.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.algo.sub.look.prop_eq_cstr.   (* def_ftv *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The witness                                                           *)
(* ===================================================================== *)

Section CexSubTargetFtv.

(** One rigid [β] in the context, and one instantiation tag [ε]. *)
Variables β ε : atom.

Definition Θcex : aenv := (β ~ abind_tvar) ++ nil.

(** Subject: the decorated identity quantifier [∀^ε α. α] — [is_tskl], and
    for [a_sub_mode_ty] also ghost-free. *)
Definition Rcex : uskl := uskl_all_tag ε (uskl_var_b 0).

(** Target: the context's rigid, which the subject does not mention. *)
Definition Qcex : bskl := bskl_var_f β.

Lemma Θcex_wf : {{ ⊢ Θcex }}a.
Proof. apply a_wf_aenv__tvar; [ simpl; auto | apply a_wf_aenv__nil ]. Qed.

Lemma Rcex_tskl : is_tskl Rcex.
Proof.
  apply is_tskl__all_tag with (L := empty); intros α _; cbn.
  apply is_tskl__var.
Qed.

(** The guess ForallL instantiates with: the rigid [β] itself.  It is a
    legitimate instantiation — [a_tags_sort] at TY (decorated, tag-free,
    ghost-free) and well-scoped in Θ. *)
Lemma guess_tags_sort : a_tags_sort a_sub_mode_ty empty (uskl_var_f β).
Proof.
  apply a_tags_sort__ty;
    [ apply is_tskl__var
    | apply d_tags_skl__var; clear; fsetdec
    | apply uskl_ghost_free__var ].
Qed.

Lemma guess_wf : {{ Θcex ⨟ empty ⊢ₚₛ ⌊ uskl_var_f β ⌋ˢ }}a.
Proof.
  cbn. apply a_wf_pskl__var. right. left. simpl; auto.
Qed.

(** The derivation.  ForallL (tagged) instantiates with [β]; the premise is
    then the Check leaf, whose consistency is the plain variable rule. *)
Lemma cex_derivation :
  ad_pat_sub_fuel 1 a_sub_mode_ty mode_tc empty Θcex Rcex Qcex.
Proof.
  unfold Rcex, Qcex, Θcex.
  apply ad_pat_sub_fuel__forall_l_tagged
    with (Ψ' := empty) (ψ := uskl_var_f β).
  - intro Hc; discriminate Hc.
  - clear; fsetdec.
  - clear; fsetdec.
  - apply guess_tags_sort.
  - apply guess_wf.
  - cbn [open_uskl_wrt_uskl open_uskl_wrt_uskl_rec].
    (* [pskl_to_bskl_inh (pskl_var_f β) = bskl_var_f β] *)
    change (bskl_var_f β) with (pskl_to_bskl_inh (pskl_var_f β)).
    apply ad_pat_sub_fuel__check.
    + apply guarded_uskl__var.
    + apply guarded_pskl__var.
    + apply ad_consis_join_inh_intro.
      * cbn. apply ad_pat_consis__var;
          [ clear; fsetdec
          | left; simpl; auto ].
      * (* the leaf presupposition: subject and counterpart are the SAME rigid,
           so the refinement is its variable row *)
        cbn. apply ad_refine_pskl__var. right. unfold a_binds_tvar. eauto.
Qed.

(** …and the bound the plan wanted is violated. *)
Lemma cex_bound_violated :
  ~ (ftvar_in_bskl Qcex [<=] ftvar_in_uskl Rcex `union` def_ftv Θcex).
Proof.
  unfold Qcex, Rcex, Θcex; cbn.
  intro Hc. assert (Hin : β `in` singleton β) by (clear; fsetdec).
  apply Hc in Hin. clear - Hin; fsetdec.
Qed.

End CexSubTargetFtv.

(* ===================================================================== *)
(*  The refutation                                                        *)
(* ===================================================================== *)

(** THE SUB-SIDE [target_ftv] LEMMA IS FALSE even with [is_tskl] on the
    subject and [a_wf_aenv] on the context. *)
Theorem p6ss_sub_target_ftv_is_false :
  ~ (forall n NM M Ψ Θ R Q,
       ad_pat_sub_fuel n NM M Ψ Θ R Q ->
       {{ ⊢ Θ }}a ->
       is_tskl R ->
       ftvar_in_bskl Q [<=] ftvar_in_uskl R `union` def_ftv Θ).
Proof.
  intro Hall.
  (* two distinct atoms: the rigid β and the instantiation tag ε *)
  pick fresh β. pick fresh ε.
  apply (@cex_bound_violated β ε).
  eapply Hall;
    [ apply (@cex_derivation β ε) | apply (@Θcex_wf β) | apply Rcex_tskl ].
Qed.

(** NON-VACUITY: the witness derivation really is a derivation, and its
    subject really is a decorated skeleton. *)
Theorem p6ss_sub_target_ftv_cex_nonvacuous :
  exists β ε, ad_pat_sub_fuel 1 a_sub_mode_ty mode_tc empty (Θcex β)
                (Rcex ε) (Qcex β)
              /\ is_tskl (Rcex ε)
              /\ {{ ⊢ (Θcex β) }}a.
Proof.
  pick fresh β. pick fresh ε.
  exists β, ε; repeat split;
    [ apply cex_derivation | apply Rcex_tskl | apply Θcex_wf ].
Qed.
