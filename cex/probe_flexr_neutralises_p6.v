(** ⭐⭐ THE `SolE-FlexR` REPAIR NEUTRALISES TWO OF THE MECH'S P6-LEVEL
    COUNTEREXAMPLES (2026-08-05).  Machine-checked, Qed, axiom-free, and
    SELF-CONTAINED — it rests on nothing but [algo/def_extra.v], so it stays
    checkable independently of the completeness cluster.

    Both retracted counterexamples turned on the SAME step: the OLD
    [SolE-FlexR] read [P ∼ α̂ ⤳ α̂], DISCARDING the accumulated pattern, so
    the solve's answer at a flexible counterpart was forced to be the
    flexible itself — and the enclosing precision obligation then compared
    that flexible's κ-image against the ideal guess, which is where both
    refutations bit.  The authors' repaired row returns [guess^TY(P)]
    instead, and at both configurations [P] is GHOST-FREE, so [guess^TY]
    invents nothing and the answer IS the pattern.

    ── (1) [cex_p6_flex_counterpart.v] ──────────────────────────────────
    There [P_i = c → ⟨⟩] faces [P_0 = β̂] with [κ β̂ = ⟨⟩ → ⟨⟩], and the old
    rule forced [P_a = β̂], leaving the underivable obligation
    [(⟨⟩→⟨⟩) ⊑ᵖ (c → ⟨⟩)] (its argument side is [⟨⟩ ⊑ᵖ c] with [c] RIGID).
    Under the repair the answer is [c → ⟨⟩] and the obligation is
    reflexivity at the very same skeleton.

    ── (2) [cex_p6sv_forall_flex.v] ─────────────────────────────────────
    There the body solve is [β→β ≼[TC] f̂], the old rule forced [f̂], the
    close then re-bound a VACUOUS binder [∀_.f̂] and no instantiation of [f̂]
    could mention the bound [β].  Under the repair the body answer is
    [β→β], so the close re-binds a REAL occurrence and yields [∀β.β→β].

    ⚠️ WHAT THIS DOES AND DOES NOT SETTLE.  It settles that the two
    CONFIGURATIONS no longer refute anything.  It does NOT by itself
    establish the paper's P6-Sv, nor that the mech's [sub_shield] premise
    can be dropped — that is Step 3 of docs/HANDOFF-solve-flexr-repair.md,
    and it has to be decided by re-proving the statements without the
    premise, not by observing that one witness died.  The two files are
    retracted (their Coq text is recoverable at the pre-repair commit
    `d5f9169`); every consumer that still CITES them as the reason for
    [sub_shield] is flagged there. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  (1)  the flexible-counterpart configuration                           *)
(* ===================================================================== *)

(** The repaired [SolE-FlexR] returns the PATTERN, [c → ⟨⟩], where the old
    row returned the flexible [β̂].  [guess^TY] invents nothing: the pattern
    is ghost-free, so the emitted block is empty. *)
Lemma flexctp_solve_returns_the_pattern : forall (c beta : atom) (Θ0 : aenv),
  binds beta abind_flex_mono Θ0 ->
  Θ0 ⊢ₑ (pskl_arrow (pskl_var_f c) pskl_unit) ∼ (pskl_var_f beta)
       ⤳ nil ⨾ (pskl_arrow (pskl_var_f c) pskl_unit).
Proof.
  intros c beta Θ0 Hb.
  replace (pskl_arrow (pskl_var_f c) pskl_unit)
    with (ptyp_to_pskl (ptyp_arrow (ptyp_var_f c) ptyp_unit))
    at 2 by reflexivity.
  apply a_solve_eq__flex_r;
    [ left; exact Hb
    | split; [ apply lc_pskl_arrow; auto | intros Hf; inversion Hf ]
    | apply nonghost_pskl__arrow
    | ].
  replace (@nil (atom * abind)) with (nil ++ nil : aenv) by reflexivity.
  apply a_guess_mono__arrow;
    [ apply a_guess_mono__var | apply a_guess_mono__unit ].
Qed.

(** …and the obligation that used to be underivable is now REFLEXIVITY at
    the pattern: [(c → ⟨⟩) ⊑ᵖ[∅] (c → ⟨⟩)], with [c] a rigid of the context.
    (The old obligation was [(⟨⟩→⟨⟩) ⊑ᵖ (c → ⟨⟩)], whose argument side
    [⟨⟩ ⊑ᵖ c] has no rule.) *)
Lemma flexctp_precision_now_holds : forall (c : atom) (Θ : aenv) Δ,
  binds c abind_tvar Θ ->
  Θ ⨟ Δ ⊢ (pskl_arrow (pskl_var_f c) pskl_unit)
        ⊑ᵖ[ empty ] (uskl_arrow (uskl_var_f c) uskl_unit).
Proof.
  intros c Θ Δ Hb.
  (* ⚠️ PIN the two tag sets.  [eapply] would leave them EVARS, and the
     [Ψ [=] ∅] side conditions of the var/unit rows are then [fsetdec] goals
     with a set metavariable — which does not terminate.  Third occurrence of
     this trap in the campaign; see the hand-off's §7 hazards. *)
  apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
    [ apply ad_ppre__var; [ clear; fsetdec | right; left; exact Hb ]
    | apply ad_ppre__unit; clear; fsetdec
    | clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  (2)  the P6-Sv ∀-over-flexible configuration                          *)
(* ===================================================================== *)

(** The body solve [β→β ≼[TC] f̂] returns [β→β], not [f̂].  SolS-Check
    bridges into the repaired SolE-FlexR, whose [guess^TY] again invents
    nothing. *)
Lemma p6sv_body_returns_the_pattern : forall (f b : atom) (Θ0 : aenv),
  binds f abind_flex_mono Θ0 ->
  Θ0 ⊢ₛ (pskl_arrow (pskl_var_f b) (pskl_var_f b)) ≼[ mode_tc ]
        (pskl_var_f f)
       ⤳ nil ⨾ (pskl_arrow (pskl_var_f b) (pskl_var_f b)).
Proof.
  intros f b Θ0 Hb.
  apply a_solve_sub__check;
    [ exact I | apply guarded_pskl__arrow; auto | apply guarded_pskl__var | ].
  replace (pskl_arrow (pskl_var_f b) (pskl_var_f b))
    with (ptyp_to_pskl (ptyp_arrow (ptyp_var_f b) (ptyp_var_f b)))
    at 2 by reflexivity.
  apply a_solve_eq__flex_r;
    [ left; exact Hb
    | split; [ apply lc_pskl_arrow; auto | intros Hf; inversion Hf ]
    | apply nonghost_pskl__arrow
    | ].
  replace (@nil (atom * abind)) with (nil ++ nil : aenv) by reflexivity.
  apply a_guess_mono__arrow; apply a_guess_mono__var.
Qed.

(** The binder really is re-bound: [close b (β→β) = (0)→(0)]. *)
Remark p6sv_close_is_the_real_binder : forall b : atom,
  close_pskl_wrt_pskl b (pskl_arrow (pskl_var_f b) (pskl_var_f b))
  = pskl_arrow (pskl_var_b 0) (pskl_var_b 0).
Proof.
  intros b. unfold close_pskl_wrt_pskl; cbn [close_pskl_wrt_pskl_rec].
  (* ⚙️ grab the ACTUAL scrutinee — a bare [destruct (b == b)] does not
     reduce the [if], the notation elaborating to a different head *)
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    solve [ reflexivity | exfalso; auto ].
Qed.

(** ⭐ …so SolS-ForallL closes over a REAL occurrence: the whole run on
    [∀β.β→β ≼[TC] f̂] yields [∀. close β (β→β)], which
    [p6sv_close_is_the_real_binder] computes to [∀β.β→β] — where the OLD rule
    yielded the vacuous-binder [∀_.f̂].  This is the shape the paper's P6-Sv
    asks for. *)
Lemma p6sv_forall_returns_the_pattern : forall (f b : atom) (Θ0 : aenv),
  binds f abind_flex_mono Θ0 ->
  b `notin` ftvar_in_aenv Θ0 `union` singleton f ->
  Θ0 ⊢ₛ (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
        ≼[ mode_tc ] (pskl_var_f f)
       ⤳ nil ⨾ (pskl_all_syn
                  (close_pskl_wrt_pskl b
                     (pskl_arrow (pskl_var_f b) (pskl_var_f b)))).
Proof.
  intros f b Θ0 Hb Hfr.
  apply a_solve_sub__forall_l with (β := b);
    [ cbn [ftvar_in_pskl]; clear - Hfr; solve_notin | ].
  unfold open_pskl_wrt_pskl; cbn [open_pskl_wrt_pskl_rec].
  apply p6sv_body_returns_the_pattern.
  apply binds_app_3; exact Hb.
Qed.

Print Assumptions flexctp_solve_returns_the_pattern.
Print Assumptions flexctp_precision_now_holds.
Print Assumptions p6sv_forall_returns_the_pattern.
