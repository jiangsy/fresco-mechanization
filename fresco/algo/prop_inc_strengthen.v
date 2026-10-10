(** ⚠️ DO NOT MERGE THIS INTO [prop_inc.v].  It shares that file's topic but
    NOT its layer: this one needs [prop_basic], [prop_compose] and
    [prop_normal], and all three import [prop_inc] — so folding it back is an
    import CYCLE, not a tidy-up.  Checked 2026-08-09 during the file-reorg
    pass; the [_strengthen] suffix marks the layer, not a size accident. *)

(** Increment strengthening / mid-strip infrastructure for the OPTIMALITY
    walk cases (consis/prop_completeness_consis.v).

    The assign walk sandwiches the skipped binding as [Ξ ++ [β] ++ Θ0]
    (unlike Flex-Flex-Skip's clean head-flex).  [a_inc_peel_suffix] only peels
    an all-flex suffix; here we need to peel the suffix AND the mid flex binding
    together, then RE-INSERT the suffix over the smaller tail — producing the
    sub-node's competing increment [κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ].

    The suffix here is [a_decls Ξ] (every entry an UNDEFINED flexible), the
    algorithm's own invariant on the pending suffix (full-algo-spec.tex:1508).
    That is what keeps the re-insertion clean: with no [flex_mono_def] entry in
    Ξ there is no definition whose image depends on the dropped [β], so the
    reconstructed increment's premises transport unchanged.  (With a general
    [a_suffix] Ξ a def entry [a ≔ τd] could have [β ∈ ftv τd], and dropping
    β's metasubst entry would change [msubst τd] — the flex_def premise
    [τa' ≡ᵗ msubst (κ1++κ2) τd] would then be false.) *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_compose.
Require Import src.fresco.algo.prop_normal.

Set Implicit Arguments.

(** MID-STRIP of a flexible binding sandwiched under an [a_decls] suffix.
    Peels the suffix Ξ and the mid flex [β] off a competing increment
    [κ ∷ (Ξ ++ β̂ ++ Θ0) ⊑ Θ], returning
      - the split [κ = κ1 ++ (β,τ) :: κ2] (κ1 = the Ξ-part, dom κ1 = dom Ξ),
      - the tail increment [κ2 ∷ Θ0 ⊑ Θ], and
      - the RE-INSERTED increment [κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ] with β dropped.
    The target [Θ] is UNCHANGED (flex/suffix entries do not extend it). *)
Lemma a_inc_mid_strip_flex : forall Ξ β Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\
    dom κ1 [=] dom Ξ /\
    κ2 ∷ Θ0 ⊑ Θ /\
    κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β Θ0 κ Θ Hdec Hinc.
  - (* Ξ = nil : head is the mid flex β itself *)
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqκ] Heqt
                      | | | | ]; subst.
    exists (@nil (atom * ptyp)), τ, κs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | exact Hinc' ].
  - (* Ξ = (a ~ flex) ++ Ξ' : peel the head flex a, recurse *)
    inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqκ] Heqt
                      | | | | ]; subst.
    destruct (IH _ _ _ _ Hdec' Hinc')
      as [κ1 [τ2 [κ2 [Heqκ [Hdom [Hinc2 Hrec]]]]]].
    exists ((a, τ) :: κ1), τ2, κ2. simpl.
    split; [ rewrite Heqκ; reflexivity | ].
    split; [ clear - Hdom; simpl_env; fsetdec | ].
    split; [ exact Hinc2 | ].
    apply a_inc__flex; auto.
Qed.

(* ===================================================================== *)
(*  FLEX-KIND PRESERVATION over the algorithm.                             *)
(*                                                                        *)
(*  The algorithm never rigidifies a flexible variable: every [a_assign]/  *)
(*  [a_unify]/[a_consis] step maps a flexible (defined or not) of its      *)
(*  source to a flexible of its target.  NOT derivable from soundness's    *)
(*  [⊴] alone — [a_inc__flex]'s image [α̂ ↦ α] only forces [α] to be SOME   *)
(*  tvar in the target, and the relation tolerates a rigid one.  Needed by  *)
(*  the optimality walk cases: the ζ-override must know that a Θ0-flexible  *)
(*  free in a walked-past term binding still has a ζ-entry (i.e. is still   *)
(*  flexible in the algorithm's output).                                    *)
(* ===================================================================== *)

Lemma a_assign_unify_consis_flex_preserve :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar (Ξ ++ Θ0) α1 -> a_flex_tvar Θ1 α1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ =>
              forall α1, a_flex_tvar (Ξ ++ Θ0) α1 -> a_flex_tvar Θ1 α1)
           (fun Θ0 α β Θ1 _ =>
              forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1)
           (fun Δ1 Δ2 Θ0 P0 P P' Θ1 _ =>
              forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1));
    intros;
    (* Instantiate preservation at the queried atom, then reduce context
       surgery to disjunctions of flexible occurrences. *)
    try match goal with
    | H : _ = abind_tvar \/ (exists _, _ = abind_var_typ _) \/ (exists _, _ = abind_var_skl _) |- _ =>
        destruct H as [-> | [[? ->] | [? ->]]]
    end;
    match goal with |- a_flex_tvar _ ?x =>
      repeat match goal with
      | IH : forall y, a_flex_tvar _ y -> _ |- _ => specialize (IH x)
      end
    end;
    simpl_env in *;
    repeat rewrite a_flex_tvar_cons_tvar_any in *;
    repeat rewrite a_flex_tvar_cons_nonflex in * by (split; intros; discriminate);
    repeat rewrite a_flex_tvar_app_iff in *;
    repeat rewrite a_flex_tvar_one_flex in * by eauto;
    try tauto.
  all: match goal with
  | H : context [a_flex_tvar (?c ~ ?bd) ?x] |- _ =>
      assert (~ a_flex_tvar (c ~ bd) x)
        by (apply a_flex_tvar_one_nonflex; intros; discriminate); tauto
  end.

Qed.

(* ===================================================================== *)
(*  ftv of a bound entry lives in the context's domain.                    *)
(* ===================================================================== *)

(** In a wf context, a term binding's payload draws its variables from the
    context's domain.  (Applied at a TAIL context to separate a fresh head.) *)
Lemma a_wf_aenv_binds_var_typ_ftv : forall Θ x A,
  {{ ⊢ Θ }}a -> binds x (abind_var_typ A) Θ ->
  ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ x A Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ pose proof (IHHwf Hb') as Hs; simpl; clear - Hs; fsetdec ].
  (* var_typ head : A is wf in the tail *)
  injection Heq2 as Heq2. subst.
  pose proof (a_wf_ptyp_ftv_dom H0) as Hs. simpl. clear - Hs. fsetdec.
Qed.

(** ⭐ A well-formed context's term entry is DISCIPLINED-well-formed in the
    WHOLE context.  [a_wf_aenv__var] stores it in the entry's TAIL (2026-08-09);
    this weakens that to the full context, which is the form every consumer
    wants.  It is what retired the two
    [binds y (abind_var_skl Ps) Θ -> {{ Θ ⨟ ∅ ⊢ₚₛ Ps }}a] hypotheses from
    [a_pat_complete] / [a_typing_complete] — before the constructor was
    strengthened they were EXTERNAL side conditions (docs/WF-SIDE-CONDITIONS.md),
    and now they are theorems. *)
Lemma a_wf_aenv_binds_var_skl_wf : forall Θ x P,
  {{ ⊢ Θ }}a -> binds x (abind_var_skl P) Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ P }}a.
Proof.
  intros Θ x P Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ eapply a_wf_pskl_weaken;
                  [ intros ? ? Hb2; apply binds_cons_3; exact Hb2
                  | exact (IHHwf Hb') ] ].
  (* var_skl head : the entry's own stored wf, weakened past the entry *)
  injection Heq2 as Heq2. subst.
  eapply a_wf_pskl_weaken;
    [ intros ? ? Hb2; apply binds_cons_3; exact Hb2 | exact H0 ].
Qed.

Lemma a_wf_aenv_binds_var_skl_ftv : forall Θ x P,
  {{ ⊢ Θ }}a -> binds x (abind_var_skl P) Θ ->
  ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros * Hwf Hb. apply a_scope_pskl_ftv_dom.
  eapply a_scope_pskl_of_wf, a_wf_aenv_binds_var_skl_wf; eauto.
Qed.

(* ===================================================================== *)
(*  Term bindings transport along increments (both directions).            *)
(* ===================================================================== *)

Lemma a_suffix_no_var_typ : forall Ξ x A,
  a_suffix Ξ -> binds x (abind_var_typ A) Ξ -> False.
Proof.
  intros Ξ x A Hsuf; induction Hsuf; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    [ subst; inversion H | auto ].
Qed.

Lemma a_suffix_no_var_skl : forall Ξ x P,
  a_suffix Ξ -> binds x (abind_var_skl P) Ξ -> False.
Proof.
  intros Ξ x P Hsuf; induction Hsuf; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    [ subst; inversion H | auto ].
Qed.

(* NB the forward/backward SYNTACTIC binding transports that lived here
   (a_inc_binds_var_typ/skl and their _src converses) were deleted with the
   move to GMM-style SEMANTIC entries in [a_inc] (def_meta.v): the target's
   binder payload is now only ≡ᵗ/≡ˢ-related to the substituted source
   payload, and the ζ-override machinery they supported is gone (see
   algo/cex/cex_assign_optimal_syn_middle.v for why it had to go). *)

