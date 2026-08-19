(** PROBE (2026-08-19): ⚠️ THE LIFT [a_extract] ⟹ [e_extract] IS **FALSE**,
    and this file is the configuration.  It is the obstruction
    docs/HANDOFF-extractable-algo-encoding.md §8c.25 predicted from the
    rules; here it is machine-checked.

    ⚠️ WHAT GOES WRONG.  [LE-Arrow] runs BOTH halves at the SAME [Θ], and
    the collection has no supply, so an atom the LEFT half leaks as a ∀
    OPENER and an atom the RIGHT half INVENTS as a flexible may be THE SAME
    ATOM: the two side conditions are

      LE-ForallInh   β ∉ add α (ftvar Θ ∪ ftvar P ∪ ftvar P')
      LE-FlexR       γ ∉ add α (add β̂ (ftvar Θ ∪ ftvar P))

    and at the terms below BOTH read [∉ {α, β̂}].  Nothing separates them.
    The supply-threaded encoding always does separate them — the opener is
    drawn at [S0] and the flexible at [S1 ⊇ add opener S0] — so where the
    a-side has ONE atom the e-side has TWO.

    ⚠️ AND THE CONFLATION IS LOAD-BEARING, not cosmetic.  §1's collection
    returns block [γ̂] and constraints [≐1, ≐γ, ≐γ], where the FIRST [γ] is
    the invented flexible and the SECOND is the leaked opener.  §2 then
    shows the two folds disagree:

      §2a  at the conflated names the fold RUNS — the leaked [γ] is
           flexible, because the sibling put it in [Ξ], so SolE-FlexR fires;
      §2b  de-conflate the opener to any [δ] the context does not bind —
           which is exactly what threading does — and the fold is STUCK:
           [1 ∼ δ] matches NO [a_solve_eq] row.  Not SolE-Unit (the target
           is not [1]), not SolE-Var (the subject is not a variable), not
           SolE-FlexR ([δ] is not hatted), not SolE-GhostL / SolE-VacuousR
           (neither side is [◇]), and no ⫯ / ∀ / → row.

    ⇒ There is no [flex_agree_rel] between the a-side's [Ξ ++ Θ0] and the
    e-side's [Ξ2 ++ Θ2], which is precisely the premise the fold transport
    ([prop_lift.v] §7) needs.  The extract row cannot be lifted as stated.

    ⭐ WHAT IT PINS.  The fact the lift is missing is exactly

        a leaked opener that OCCURS IN 𝒞 is not one of the collection's
        own block names

    — §1 realizes its negation.  ⚙ Note the "occurs in 𝒞" qualifier is not
    slack: [rel_a_cstrs] never consults a pair whose left atom is absent
    from [ftvar_in_a_cstrs 𝒞], so a leaked opener that never surfaces in a
    constraint is harmless and the guard need not exclude it.

    ⭐ THE REPAIR the probe therefore supports is a side condition on the
    collection's TWO ARROW ROWS, in the shape the tree has already used for
    the five dispatch guards and the three [uniq] prose-completions:

        ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty

    It is a THEOREM of the threaded encoding ([e_looksub_lookeq_cstr_ftvar]
    bounds [ftvar C1 ⊆ S1] under coverage, and [dom Ξ2 ∩ S1 = ∅]), so the
    reference implementation — one global counter, never reused — cannot
    violate it and completeness costs nothing.  docs/PAPER-GAPS.md. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.

From src Require Import frost.notations.
From src Require Import frost.ltac_utils.
From src Require Import frost.coercions.
From src Require Import frost.def_shapes.
From src Require Import frost.algo.def_rules.
From src Require Import frost.ext_algo.notations.
From src Require Import frost.ext_algo.def_supply.
From src Require Import frost.ext_algo.def_look.
From src Require Import frost.ext_algo.def_solve.
From src Require Import frost.ext_algo.prop_solve.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  THE COLLECTION CONFLATES — one atom, two roles                    *)
(*                                                                        *)
(*  Θ0 = β̂                                                                *)
(*  subject   (α → (α → α))  →  ∀. α                                      *)
(*  target    (1 → β̂)        →  ∀. 0                                      *)
(*                                                                        *)
(*  LEFT half  (LE-Arrow):   LE-Var emits [≐1]; LE-FlexR INVENTS γ̂,       *)
(*                           emitting [≐γ] and the block [γ̂].             *)
(*  RIGHT half (LE-ForallInh): opens BOTH sides at γ — the SAME atom —     *)
(*                           and LE-Var emits [≐γ], the LEAK.             *)
(* ===================================================================== *)

Lemma probe_collection_conflates : forall (α β γ : atom),
  α <> β -> α <> γ -> β <> γ ->
  {{ ((β ~ abind_flex_mono) ++ nil)
     ⊢ (pskl_arrow
          (pskl_arrow (pskl_var_f α)
                      (pskl_arrow (pskl_var_f α) (pskl_var_f α)))
          (pskl_all_syn (pskl_var_f α)))
       ∼[ α ]
       (pskl_arrow
          (pskl_arrow pskl_unit (pskl_var_f β))
          (pskl_all_syn (pskl_var_b 0)))
     ⤳ ((γ ~ abind_flex_mono) ++ nil)
     ⨾ (a_cstr_eq pskl_unit
        :: a_cstr_eq (pskl_var_f γ)
        :: a_cstr_eq (pskl_var_f γ) :: nil) }}a.
Proof.
  intros α β γ Hαβ Hαγ Hβγ.
  apply a_lookeq__arrow with
    (Ξ1 := nil ++ ((γ ~ abind_flex_mono) ++ nil)) (Ξ2 := nil)
    (C1 := (a_cstr_eq pskl_unit :: nil)
           ++ (a_cstr_eq (pskl_var_f γ) :: nil))
    (C2 := a_cstr_eq (pskl_var_f γ) :: nil).
  - (* the LEFT half: LE-Var, then LE-FlexR — which invents γ̂ *)
    apply a_lookeq__arrow.
    + apply a_lookeq__var.
    + apply a_lookeq__flex_r with (β := β).
      * simpl. solve_notin_auto.
      * left. simpl. auto.
      * intros Heq. inversion Heq.
      * simpl. fsetdec.
  - (* the RIGHT half: LE-ForallInh opens at γ — the SAME atom — and the
       opener LEAKS into the constraint LE-Var emits *)
    apply a_lookeq__forall_inh with (β := γ).
    + simpl. solve_notin_auto.
    + simpl. fsetdec.
    + simpl. apply a_lookeq__var.
Qed.

(* ===================================================================== *)
(*  §2  THE FOLD DEPENDS ON THE CONFLATION                                *)
(* ===================================================================== *)

(** §2a — at the conflated names the fold RUNS.  The leaked [γ] is
    flexible, because the SIBLING half put it in [Ξ], so SolE-FlexR fires
    on it exactly as it does on the invented one. *)
Lemma probe_fold_runs_conflated : forall (β γ : atom), β <> γ ->
  exists Ξs Q,
  {{ (((γ ~ abind_flex_mono) ++ nil) ++ ((β ~ abind_flex_mono) ++ nil))
     ⊩ (a_cstr_eq pskl_unit
        :: a_cstr_eq (pskl_var_f γ)
        :: a_cstr_eq (pskl_var_f γ) :: nil) ⨾ pskl_hole ⤳ Ξs ⨾ Q }}a.
Proof.
  intros β γ Hβγ.
  eexists. eexists.
  eapply a_solve_cstr__eq; [ apply a_solve_eq__hole_l | ].
  eapply a_solve_cstr__eq.
  { apply a_solve_eq__flex_r with (A := ptyp_unit).
    - left. simpl. auto.
    - split; [ constructor | intros Hf; inversion Hf; subst;
               match goal with H : binds _ _ _ |- _ => inversion H end ].
    - constructor.
    - apply a_guess_mono__unit. }
  simpl.
  eapply a_solve_cstr__eq.
  { apply a_solve_eq__flex_r with (A := ptyp_unit).
    - left. simpl. auto.
    - split; [ constructor | intros Hf; inversion Hf; subst;
               match goal with H : binds _ _ _ |- _ => inversion H end ].
    - constructor.
    - apply a_guess_mono__unit. }
  simpl. apply a_solve_cstr__empty.
Qed.

(** §2b — ⚠️ DE-CONFLATE THE OPENER AND THE FOLD IS STUCK.  Threading is
    exactly this de-conflation: the e-side draws the opener before the
    flexible and never reuses it, so the third constraint's variable is one
    the context does not bind — and then NO [a_solve_eq] row applies. *)
Lemma probe_fold_stuck_deconflated : forall (β γ δ : atom),
  δ <> β -> δ <> γ ->
  ~ (exists Ξs Q,
     {{ (((γ ~ abind_flex_mono) ++ nil) ++ ((β ~ abind_flex_mono) ++ nil))
        ⊩ (a_cstr_eq pskl_unit
           :: a_cstr_eq (pskl_var_f γ)
           :: a_cstr_eq (pskl_var_f δ) :: nil) ⨾ pskl_hole ⤳ Ξs ⨾ Q }}a).
Proof.
  intros β γ δ Hδβ Hδγ [Ξs [Q Hd]].
  (* constraint 1, [◇ ∼ 1]: SolE-GhostL is the only row, and it yields [1] *)
  inversion Hd as [ | | ? ? ? ? ? ? ? ? Heq1 Hrest1 ]; subst.
  inversion Heq1; subst.
  simpl in Hrest1.
  (* constraint 2, [1 ∼ γ]: SolE-FlexR is the only row, and the guess of
     [1] is [1], so the pattern is unchanged *)
  inversion Hrest1 as [ | | ? ? ? ? ? ? ? ? Heq2 Hrest2 ]; subst.
  inversion Heq2; subst.
  match goal with
  | Hg : a_guess_mono _ pskl_unit _ _ |- _ => inversion Hg; subst
  end.
  simpl in Hrest2.
  (* constraint 3, [1 ∼ δ]: SolE-FlexR is again the only candidate, and it
     needs [δ] HATTED — which it is not *)
  inversion Hrest2 as [ | | ? ? ? ? ? ? ? ? Heq3 Hrest3 ]; subst.
  inversion Heq3; subst.
  match goal with
  | Hf : a_flex_tvar _ δ |- _ =>
      destruct Hf as [Hb | [τ Hb]]; inversion Hb as [Hin | Hin];
        try (inversion Hin; subst; congruence);
        simpl in Hin; intuition (try congruence)
  end.
Qed.

(* ===================================================================== *)
(*  §3  THE THREADED COLLECTION AT THE SAME INPUTS — TWO ATOMS, NOT ONE   *)
(*                                                                        *)
(*  Same [Θ0], same subject, same target.  The supply draws the flexible  *)
(*  at [S0] and the opener at [add γ1 S0], so the answer's third          *)
(*  constraint names an atom the block does NOT contain.                  *)
(* ===================================================================== *)

Lemma probe_threaded_collection_separates :
  forall (α β γ1 γ2 : atom) (S0 : supply),
  γ1 `notin` S0 -> γ2 `notin` add γ1 S0 -> β `in` S0 ->
  {{ S0 ↝ (add γ2 (add γ1 S0))
     ⊨ ((β ~ abind_flex_mono) ++ nil)
     ⊢ (pskl_arrow
          (pskl_arrow (pskl_var_f α)
                      (pskl_arrow (pskl_var_f α) (pskl_var_f α)))
          (pskl_all_syn (pskl_var_f α)))
       ∼[ α ]
       (pskl_arrow
          (pskl_arrow pskl_unit (pskl_var_f β))
          (pskl_all_syn (pskl_var_b 0)))
     ⤳ ((γ1 ~ abind_flex_mono) ++ nil)
     ⨾ (a_cstr_eq pskl_unit
        :: a_cstr_eq (pskl_var_f γ1)
        :: a_cstr_eq (pskl_var_f γ2) :: nil) }}e.
Proof.
  intros α β γ1 γ2 S0 Hγ1 Hγ2 Hβ.
  apply e_lookeq__arrow with (S1 := add γ1 S0)
    (Ξ1 := nil ++ ((γ1 ~ abind_flex_mono) ++ nil)) (Ξ2 := nil)
    (C1 := (a_cstr_eq pskl_unit :: nil)
           ++ (a_cstr_eq (pskl_var_f γ1) :: nil))
    (C2 := a_cstr_eq (pskl_var_f γ2) :: nil).
  - apply e_lookeq__arrow with (S1 := S0).
    + apply e_lookeq__var.
    + apply e_lookeq__flex_r with (β := β).
      * exact Hγ1.
      * left. simpl. auto.
      * intros Heq. inversion Heq.
      * simpl. fsetdec.
  - apply e_lookeq__forall_inh with (β := γ2).
    + exact Hγ2.
    + simpl. fsetdec.
    + simpl. apply e_lookeq__var.
Qed.

(* ===================================================================== *)
(*  §4  ⚠️ THE CONCLUSION — the a-side extract's fold RUNS and the         *)
(*      threaded one CANNOT, at one and the same configuration            *)
(*                                                                        *)
(*  ⚙ The threaded fold is refuted through [e_solve_cstr_sound]: a        *)
(*  threaded fold would give an unthreaded one at the same context and    *)
(*  constraints, and §2b says there is none.  Its coverage side condition *)
(*  is discharged from the supply hypotheses.                             *)
(* ===================================================================== *)

Theorem probe_extract_lift_false :
  forall (α β γ γ1 γ2 : atom) (S0 : supply),
  α <> β -> α <> γ -> β <> γ ->
  γ1 `notin` S0 -> γ2 `notin` add γ1 S0 -> β `in` S0 ->
  (* the collection derives on BOTH sides, and the threaded answer's third
     constraint names an atom its block does not contain *)
  {{ ((β ~ abind_flex_mono) ++ nil)
     ⊢ (pskl_arrow
          (pskl_arrow (pskl_var_f α)
                      (pskl_arrow (pskl_var_f α) (pskl_var_f α)))
          (pskl_all_syn (pskl_var_f α)))
       ∼[ α ]
       (pskl_arrow
          (pskl_arrow pskl_unit (pskl_var_f β))
          (pskl_all_syn (pskl_var_b 0)))
     ⤳ ((γ ~ abind_flex_mono) ++ nil)
     ⨾ (a_cstr_eq pskl_unit :: a_cstr_eq (pskl_var_f γ)
        :: a_cstr_eq (pskl_var_f γ) :: nil) }}a
  /\ {{ S0 ↝ (add γ2 (add γ1 S0))
        ⊨ ((β ~ abind_flex_mono) ++ nil)
        ⊢ (pskl_arrow
             (pskl_arrow (pskl_var_f α)
                         (pskl_arrow (pskl_var_f α) (pskl_var_f α)))
             (pskl_all_syn (pskl_var_f α)))
          ∼[ α ]
          (pskl_arrow
             (pskl_arrow pskl_unit (pskl_var_f β))
             (pskl_all_syn (pskl_var_b 0)))
        ⤳ ((γ1 ~ abind_flex_mono) ++ nil)
        ⨾ (a_cstr_eq pskl_unit :: a_cstr_eq (pskl_var_f γ1)
           :: a_cstr_eq (pskl_var_f γ2) :: nil) }}e
  (* the a-side fold on the a-side answer RUNS … *)
  /\ (exists Ξs Q,
        {{ (((γ ~ abind_flex_mono) ++ nil) ++ ((β ~ abind_flex_mono) ++ nil))
           ⊩ (a_cstr_eq pskl_unit :: a_cstr_eq (pskl_var_f γ)
              :: a_cstr_eq (pskl_var_f γ) :: nil) ⨾ pskl_hole ⤳ Ξs ⨾ Q }}a)
  (* … and the threaded fold on the threaded answer CANNOT *)
  /\ ~ (exists S1 Ξs Q,
          {{ (add γ2 (add γ1 S0)) ↝ S1
             ⊨ (((γ1 ~ abind_flex_mono) ++ nil)
                ++ ((β ~ abind_flex_mono) ++ nil))
             ⊩ (a_cstr_eq pskl_unit :: a_cstr_eq (pskl_var_f γ1)
                :: a_cstr_eq (pskl_var_f γ2) :: nil)
             ⨾ pskl_hole ⤳ Ξs ⨾ Q }}e).
Proof.
  intros α β γ γ1 γ2 S0 Hαβ Hαγ Hβγ Hγ1 Hγ2 Hβ.
  assert (Hγ12 : γ2 <> γ1) by (clear - Hγ2; fsetdec).
  assert (Hγ2β : γ2 <> β) by (clear - Hγ2 Hβ; fsetdec).
  split; [ apply probe_collection_conflates; assumption | ].
  split; [ apply probe_threaded_collection_separates; assumption | ].
  split; [ apply probe_fold_runs_conflated; clear - Hβγ; auto | ].
  intros [S1 [Ξs [Q He]]].
  apply (probe_fold_stuck_deconflated β γ1 γ2 Hγ2β Hγ12).
  exists Ξs, Q.
  eapply e_solve_cstr_sound; [ exact He | ].
  simpl. clear - Hγ1 Hγ2 Hβ. fsetdec.
Qed.
