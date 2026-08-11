(** ⚠️ RETRACTED 2026-08-11 — AND THAT IS THE POINT.

    THIS FILE USED TO REFUTE TWO BRIDGES.  Read without the paper's
    presupposition on skeleton consistency, declarative skeleton inference
    derives

        x : ∀X.◇  ⊢ˢ[TI]  x  ⦂  ∀ˢX.X                        (cap_d_pat)

    which [ad_pat] rejects outright ([cap_not_reachable],
    cex/cex_ad_pat_join_not_leaf_valid.v §3a).  From that this file proved

      - [d_pat_bridges_false]      — the pointwise [d_pat] -> [ad_pat] bridge
                                     is FALSE, so the completeness bridge that
                                     carried it as a hypothesis was VACUOUS;
      - [d_pat_app_package_false]  — and [App]'s EXISTENTIALLY quantified
                                     skeleton does not repair it: at
                                     [Γ = x:∀X.◇], [e₂ = ⌈x⌉], [B₁ = ∀ⁱX.X]
                                     no [P'] satisfies both the leaf datum and
                                     the App refinement, because the two read
                                     the same binder in opposite directions.

    ⭐ THE DIAGNOSIS THOSE TWO FORCED.  The leaf datum is not a mech invention:
    declarative.tex:2074 states it — *"skeleton consistency … requires
    well-formedness of syn{S} and bid{P} under Γ AS WELL AS the refinement
    judgement Γ ⊢ ⌊S⌋ ⊳ P"* — and docs/WF-SIDE-CONDITIONS.md §2 had recorded
    the mechanisation's deferral of it as "it has not bitten yet".  It bit
    here.  The repair was to stop deferring: [d_pat_sub]'s three
    consistency-bearing rows now carry the presupposition, exactly as
    [ad_pat_sub_gv] always did (decl/def_extra.v).

    SO BOTH REFUTATIONS ARE RETRACTED, at the very configuration that produced
    them — [cap_d_pat] is no longer derivable ([cap_d_pat_excluded] below), so
    neither statement can even be formed.  Their proof text is in this file's
    git history.

    ⚠️ WHAT IS **NOT** RETRACTED, and is the reason the presupposition may not
    be dropped again: [cap_consis] + [cap_no_refine]
    (cex/cex_ad_pat_join_not_leaf_valid.v §1-§2).  Those are statements about
    the paper's own consistency and refinement RULES — the rules derive a pair
    that refinement rejects — so they show the presupposition is a genuine
    restriction and not derivable.  They stand unchanged.

    Author-facing write-up: docs/ghost-capture.tex. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.prop_coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.algo.def_extra.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.algo.pat.prop_soundness_pat.   (* a_wf_exp *)
Require Import src.frost.decorated_algo.prop_conserv.
Require Import src.cex.cex_ad_pat_join_not_leaf_valid.

(** ⚙ NO [Set Implicit Arguments] — prop_conserv.v is compiled without it
    (see its header), so its lemmas take every argument explicitly here. *)

(** the one-entry context carrying the ghosty skeleton *)
Definition capΓ (x : atom) : denv := (x ~ dbind_skl capP) ++ nil.

Lemma cap_denv_to_aenv : forall x,
  denv_to_aenv (capΓ x) = (x ~ abind_var_skl capP) ++ nil.
Proof. reflexivity. Qed.

(** A ghost skeleton is still a legal context entry — the repair does not
    touch skeleton well-formedness, only what consistency may do with it. *)
Lemma cap_denv_wf : forall x, d_wf_denv (capΓ x).
Proof.
  intros x. apply d_wf_denv__skl;
    [ apply d_wf_denv__nil | simpl; fsetdec | ].
  unfold capP. apply d_wf_pskl__all with (L := empty).
  intros α Hα. simpl. apply d_wf_pskl__hole.
Qed.

Lemma cap_wf_exp : forall x, a_wf_exp (denv_to_aenv (capΓ x)) (exp_var_f x).
Proof. intros x. apply a_wf_exp__var. Qed.

(* ===================================================================== *)
(*  THE REPAIR, CHECKED AT THE CONFIGURATION THAT REFUTED THE BRIDGE.     *)
(* ===================================================================== *)

(** ⭐ The declarative side of the capture is GONE.  [P-Var] is the only rule
    for a variable, the singleton context pins the bound skeleton to [∀X.◇],
    [Infer] is the only skeleton-subtyping rule at [M = TI] — and its
    presupposition is now on the rule, where §2 of the sibling file refutes
    it.  The two systems no longer disagree here. *)
Theorem cap_d_pat_excluded : forall x,
  ~ ({{ (capΓ x) ⊢ˢ[ mode_ti ] (exp_var_f x) ⦂ capQ }}d).
Proof.
  intros x H.
  inversion H as [ Γ0 m0 Q0 Hwfq Hjoin
                 | Γ0 m0 x0 P0 d0 Q0 Hb Hd Hwfq Hjoin | | | | | | | ]; subst.
  (* the singleton context pins the entry *)
  assert (Hd0 : d0 = dbind_skl capP)
    by (clear - Hb; simpl in Hb; destruct Hb as [ Heq | Habs ];
        [ congruence | contradiction ]).
  subst d0. simpl in Hd. inversion Hd; subst.
  (* at [TI] only [Infer] concludes; its presupposition is the refuted one *)
  inversion Hjoin; subst; try congruence.
  match goal with Hr : d_refine_pskl _ _ _ _ |- _ =>
    apply d_refine_pskl_to_ad_closed in Hr end.
  eapply cap_no_refine. rewrite <- cap_erase. eassumption.
Qed.

(** …and therefore the pointwise bridge it refuted can no longer be refuted
    THIS way: [d_pat] and [ad_pat] agree at the configuration.  The positive
    statement is [d_pat_to_ad] (decorated_algo/prop_conserv.v §15), which is
    now a theorem with no hypothesis at all. *)
Theorem cap_bridge_holds : forall x,
  {{ (capΓ x) ⊢ˢ[ mode_ti ] (exp_var_f x) ⦂ capQ }}d ->
  {{ ((x ~ abind_var_skl capP) ++ nil) ⊢ˢ[ mode_ti ] (exp_var_f x) ⦂ capQ }}ad.
Proof.
  intros x H. exact (d_pat_to_ad mode_ti (capΓ x) (exp_var_f x) capQ H).
Qed.
