(** ⚠️ THE SUBTYPING-SIDE ANALOGUE OF [ad_pat_consis_monoish_counterpart] IS
    FALSE.

    On the CONSISTENCY side,

        {{ Ψs ⨟ Θ ⊢ˢ ψ ∼ Q }}ad  →  is_tskl ψ  →  bskl_monoish Q
          →  Ψs }}ad = ∅  ∧  ψ is a mono PAINT      ([ad_pat_consis_monoish_counterpart])

    holds, and it is load-bearing — it is how P6-Cv reads the counterpart
    monotype off a mono-ish [Q].  The SUBTYPING join has no such lemma, and
    [ad_pat_sub_g__forall_l_tagged] is why.

    ⭐ THE ASYMMETRY, worth remembering on its own terms.  Consistency's ∀
    rules all require the COUNTERPART to be a quantifier too, so a mono-ish
    counterpart forces the subject mono there.  Subtyping's ForallL does not —
    it INSTANTIATES, so a tagged-∀ subject can face a mono-ish counterpart
    directly.  Below, [∀^ε α. α] — which IS [is_tskl] and ghost-free, hence
    legal at [a_sub_mode_ty] — is instantiated with the context's rigid [β]
    and lands on the target [β], which is [bskl_monoish] by [bmi_var].  The
    subject is not a mono paint (a mono paint is unit / var / arrow, never a
    [uskl_all_tag]), so the conclusion fails outright.
 *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo_decl.def_decl_algo.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_decl_algo_sub.
Require Import src.frost.algo.sub.look.prop_rho_relation.
Require Import src.frost.algo.sub.look.prop_solve_ext.
Require Import src.frost.algo.sub.look.prop_flex_apart.   (* bskl_monoish *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The witness — one rigid β, one instantiation tag ε                     *)
(* ===================================================================== *)

Section CexP7SubMonoish.

Variables β ε : atom.

Definition Θw : aenv := (β ~ abind_tvar) ++ nil.

(** Subject: the decorated identity quantifier [∀^ε α. α]. *)
Definition Rw : uskl := uskl_all_tag ε (uskl_var_b 0).

(** Counterpart: the context's rigid — and a variable IS mono-ish. *)
Definition Qw : bskl := bskl_var_f β.

Lemma Θw_wf : {{ ⊢ Θw }}a.
Proof. apply a_wf_aenv__tvar; [ simpl; auto | apply a_wf_aenv__nil ]. Qed.

Lemma Rw_tskl : is_tskl Rw.
Proof.
  apply is_tskl__all_tag with (L := empty); intros α _; cbn.
  apply is_tskl__var.
Qed.

Lemma Qw_monoish : bskl_monoish Qw.
Proof. apply bmi_var. Qed.

(** The guess ForallL instantiates with: the rigid β itself — a legitimate
    instantiation (decorated, TAG-FREE, ghost-free, Θ-scoped). *)
Lemma guess_tags_sort : a_tags_sort a_sub_mode_ty empty (uskl_var_f β).
Proof.
  apply a_tags_sort__ty;
    [ apply is_tskl__var
    | apply d_tags_skl__var; clear; fsetdec
    | apply uskl_ghost_free__var ].
Qed.

Lemma guess_wf : {{ Θw ⨟ empty ⊢ₚₛ ⌊ uskl_var_f β ⌋ˢ }}a.
Proof. cbn. apply a_wf_pskl__var. right. left. simpl; auto. Qed.

(** The derivation: ForallL (tagged) instantiates with β, and the premise is
    the Check leaf, whose consistency is the plain variable rule. *)
Lemma cex_derivation :
  ad_pat_sub_g 1 a_sub_mode_ty mode_tc empty Θw Rw Qw.
Proof.
  unfold Rw, Qw, Θw.
  apply ad_pat_sub_g__forall_l_tagged
    with (Ψ' := empty) (ψ := uskl_var_f β).
  - intro Hc; discriminate Hc.
  - clear; fsetdec.
  - clear; fsetdec.
  - apply guess_tags_sort.
  - apply guess_wf.
  - cbn [open_uskl_wrt_uskl open_uskl_wrt_uskl_rec].
    change (bskl_var_f β) with (pskl_to_bskl_inh (pskl_var_f β)).
    apply ad_pat_sub_g__check;
      [ apply guarded_uskl__var | apply guarded_pskl__var | ].
    cbn. apply ad_pat_consis__var; [ clear; fsetdec | left; simpl; auto ].
Qed.

(** A [uskl_all_tag] is never a monotype's painting — mono paints are
    unit / var / arrow, by [mono_ptyp]'s three constructors. *)
Lemma cex_not_a_mono_paint :
  ~ (exists τ, mono_ptyp τ /\ Rw = ptyp_to_uskl_syn τ).
Proof.
  unfold Rw. intros (τ & Hm & Heq).
  destruct Hm; cbn in Heq; discriminate Heq.
Qed.

End CexP7SubMonoish.

(* ===================================================================== *)
(*  The refutation                                                        *)
(* ===================================================================== *)

(** THE SUB-SIDE MONOISH-COUNTERPART LEMMA IS FALSE, even with [is_tskl] on
    the subject and [a_wf_aenv] on the context — so P7's TASK 0 needs the
    flex-mono wall stated directly, not this route. *)
Theorem p7_sub_monoish_counterpart_is_false :
  ~ (forall n NM M Ψ Θ ψ Q,
       ad_pat_sub_g n NM M Ψ Θ ψ Q ->
       {{ ⊢ Θ }}a ->
       is_tskl ψ ->
       bskl_monoish Q ->
       Ψ [=] empty /\ exists τ, mono_ptyp τ /\ ψ = ptyp_to_uskl_syn τ).
Proof.
  intro Hall.
  (* two distinct atoms: the rigid β and the instantiation tag ε *)
  pick fresh β. pick fresh ε.
  (* NB [Section]-discharge gives each lemma only the variables it USES:
     Θw / Qw depend on β alone, Rw on ε alone. *)
  apply (@cex_not_a_mono_paint ε).
  refine (proj2 (Hall _ _ _ _ _ _ _ (cex_derivation β ε) (Θw_wf β)
                   (Rw_tskl ε) (Qw_monoish β))).
Qed.

(** ⚠️ READ THIS BEFORE CONCLUDING ANYTHING FROM THE ABOVE.  Only the
    MONO-PAINT half of the statement is false.  The OTHER conjunct — [Ψ = ∅],
    i.e. "against a mono-ish counterpart NO TAG IS SOLVED" — is TRUE, and it
    was proved as [ad_pat_sub_g_monoish_tag_free] (in the deleted
    prop_sub_shield_supply.v).  That was also the half the retired shield
    needed, because its clean rule's
    [ftag ψa ∩ Ψa = ∅] plus [d_tags_skl]'s [Ψa ⊆ ftag ψa] is exactly
    "Ψa = ∅".

    The reason the tag half survives is the same reason the shape half dies.
    [__forall_l_tagged] DROPS its own ε (conclusion [Ψ], premise [Ψ ∪ Ψ']) —
    instantiating a quantifier never SOLVES its tag — so it cannot put a tag
    into the conclusion either; it just hands the whole tag set down.  Tags
    reach the conclusion only through rules that MATCH a quantifier of the
    subject against a quantifier of the counterpart, and a [bskl_monoish]
    counterpart has none.  So this witness bounds the shape of the subject and
    nothing else. *)
