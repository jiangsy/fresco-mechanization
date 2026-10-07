(** PROBE (2026-08-19): ⚠️ THE CONFIGURATION THE COLLECTION'S **CROSS-HALF
    FRESHNESS GUARD** EXCLUDES — and the record of why that guard had to be
    added (fresco/algo/def_rules.v, [a_looksub__arrow] / [a_lookeq__arrow];
    docs/PAPER-GAPS.md; hand-off §8c.25).

    ⚠️ WHAT THE UNGUARDED RULE ADMITTED.  [LE-Arrow] runs BOTH halves at the
    SAME [Θ], and the collection has no supply, so an atom the LEFT half
    leaks as a ∀ OPENER and an atom the RIGHT half INVENTS as a flexible may
    be THE SAME ATOM: the two side conditions are

      LE-ForallInh   β ∉ add α (ftvar Θ ∪ ftvar P ∪ ftvar P')
      LE-FlexR       γ̂ ∉ add α (add β̂ (ftvar Θ ∪ ftvar P))

    and at the terms below BOTH read [∉ {α, β̂}].  Nothing separated them.
    The supply-threaded encoding always does separate them — the opener is
    drawn at [S0] and the flexible at [S1 ⊇ add opener S0] — so where the
    a-side had ONE atom the e-side has TWO.

    ⚠️ AND THE COLLISION WAS LOAD-BEARING, not cosmetic.  §1's two halves
    return block [γ̂] and constraints [≐1, ≐γ] on the left and [≐γ] on the
    right, where the left [γ] is the invented flexible and the right one is
    the leaked opener.  §2 shows the two folds then disagree:

      §2a  at the conflated names the fold RUNS — the leaked [γ] is
           flexible, because the SIBLING put it in [Ξ], so SolE-FlexR fires;
      §2b  de-conflate the opener to any [δ] the context does not bind —
           which is exactly what threading does — and the fold is STUCK:
           [1 ∼ δ] matches NO [a_solve_eq] row.  Not SolE-Unit (the target
           is not [1]), not SolE-Var (the subject is not a variable), not
           SolE-FlexR ([δ] is not hatted), not SolE-GhostL / SolE-VacuousR
           (neither side is [◇]), and no ⫯ / ∀ / → row.

    ⇒ There was no [flex_agree_rel] between the a-side's [Ξ ++ Θ0] and the
    e-side's [Ξ2 ++ Θ2], which is precisely the premise the fold transport
    (ext_algo/prop_lift.v §7) needs — so [a_extract] ⟹ [e_extract] was FALSE
    as a lift.

    ✅ **WHAT THE GUARD DOES.**  §1c is the point of the file: at these two
    halves the guard's second conjunct

        ftvar_in_a_cstrs 𝒞₂ ∩ dom Ξ₁ [=] empty

    is FALSE — both sides are [{γ}] — so [LE-Arrow] no longer combines them.
    ⭐ The guard costs completeness NOTHING: it is a THEOREM of the
    supply-threaded encoding ([e_looksub_lookeq_cstr_old], prop_look.v §2c),
    so the reference implementation — one global counter, never reused —
    cannot violate it, and [e_looksub_sound] discharges both conjuncts.  §3
    is that fact made concrete: the threaded collection at the SAME inputs
    returns two distinct atoms. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.

From src Require Import fresco.notations.
From src Require Import fresco.ltac_utils.
From src Require Import fresco.coercions.
From src Require Import fresco.def_shapes.
From src Require Import fresco.algo.def_rules.
From src Require Import fresco.ext_algo.notations.
From src Require Import fresco.ext_algo.def_supply.
From src Require Import fresco.ext_algo.def_look.
From src Require Import fresco.ext_algo.def_solve.
From src Require Import fresco.ext_algo.prop_solve.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  THE TWO HALVES, AND THE GUARD THAT NOW KEEPS THEM APART           *)
(*                                                                        *)
(*  Θ0 = β̂                                                                *)
(*  LEFT   (α → (α → α))  ∼[α]  (1 → β̂)   ⤳ γ̂  ⨾ [≐1, ≐γ]                *)
(*         LE-Var emits [≐1]; LE-FlexR INVENTS γ̂, emitting [≐γ].          *)
(*  RIGHT  ∀. α          ∼[α]  ∀. 0       ⤳ ·  ⨾ [≐γ]                    *)
(*         LE-ForallInh opens BOTH sides at γ — the SAME atom — and        *)
(*         LE-Var emits [≐γ], the LEAK.                                    *)
(* ===================================================================== *)

Definition Θconf (β : atom) : aenv := (β ~ abind_flex_mono) ++ nil.

Lemma probe_half_left : forall (α β γ : atom),
  α <> β -> α <> γ -> β <> γ ->
  {{ (Θconf β)
     ⊢ (pskl_arrow (pskl_var_f α)
                   (pskl_arrow (pskl_var_f α) (pskl_var_f α)))
       ∼[ α ]
       (pskl_arrow pskl_unit (pskl_var_f β))
     ⤳ (nil ++ ((γ ~ abind_flex_mono) ++ nil))
     ⨾ ((a_cstr_eq pskl_unit :: nil)
        ++ (a_cstr_eq (pskl_var_f γ) :: nil)) }}a.
Proof.
  intros α β γ Hαβ Hαγ Hβγ. unfold Θconf.
  apply a_lookeq__arrow.
  - (* the guard, LEFT conjunct: [≐1] mentions no atom at all *)
    simpl. clear. fsetdec.
  - (* the guard, RIGHT conjunct: the LEFT half here generates nothing *)
    simpl. clear. fsetdec.
  - apply a_lookeq__var.
  - apply a_lookeq__flex_r with (β := β).
    + simpl. solve_notin_auto.
    + left. simpl. auto.
    + intros Heq. inversion Heq.
    + simpl. fsetdec.
Qed.

Lemma probe_half_right : forall (α β γ : atom),
  α <> β -> α <> γ -> β <> γ ->
  {{ (Θconf β)
     ⊢ (pskl_all_syn (pskl_var_f α)) ∼[ α ] (pskl_all_syn (pskl_var_b 0))
     ⤳ nil ⨾ (a_cstr_eq (pskl_var_f γ) :: nil) }}a.
Proof.
  intros α β γ Hαβ Hαγ Hβγ. unfold Θconf.
  apply a_lookeq__forall_inh with (β := γ).
  - simpl. solve_notin_auto.
  - simpl. fsetdec.
  - simpl. apply a_lookeq__var.
Qed.

(** ⭐ §1c — THE GUARD IS EXACTLY THE EXCLUSION.  [LE-Arrow] would combine
    the two halves above into a single collection returning block [γ̂] and
    constraints [≐1, ≐γ, ≐γ] — one atom in two roles.  Its second conjunct
    forbids that, and nothing weaker does: the offending atom is a LEAKED
    OPENER, so it is not in either block and no [uniq Ξ] condition can see
    it. *)
Lemma probe_cross_half_guard_excludes_it : forall (γ : atom),
  ~ (ftvar_in_a_cstrs (a_cstr_eq (pskl_var_f γ) :: nil)
     ∩ dom (nil ++ ((γ ~ abind_flex_mono) ++ nil)) [=] empty).
Proof.
  intros γ Heq. simpl in Heq.
  assert (Hin : γ `in` empty) by (rewrite <- Heq; clear; fsetdec).
  clear - Hin. fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  WHY IT HAD TO BE EXCLUDED — the fold DEPENDS on the collision     *)
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
(*  constraint names an atom the block does NOT contain.  ⭐ This is why   *)
(*  the guard costs nothing: the implementation could not have produced   *)
(*  the excluded configuration in the first place.                        *)
(* ===================================================================== *)

Lemma probe_threaded_collection_separates :
  forall (α β γ1 γ2 : atom) (S0 : supply),
  γ1 `notin` S0 -> γ2 `notin` add γ1 S0 -> β `in` S0 ->
  {{ S0 ↝ (add γ2 (add γ1 S0))
     ⊨ (Θconf β)
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
  intros α β γ1 γ2 S0 Hγ1 Hγ2 Hβ. unfold Θconf.
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
(*  §4  ⭐ THE CONCLUSION — the guard is NECESSARY, and it is FREE         *)
(* ===================================================================== *)

Theorem probe_cross_half_guard_is_necessary :
  forall (α β γ γ1 γ2 : atom) (S0 : supply),
  α <> β -> α <> γ -> β <> γ ->
  γ1 `notin` S0 -> γ2 `notin` add γ1 S0 -> β `in` S0 ->
  (* the two halves derive … *)
  {{ (Θconf β)
     ⊢ (pskl_arrow (pskl_var_f α)
                   (pskl_arrow (pskl_var_f α) (pskl_var_f α)))
       ∼[ α ] (pskl_arrow pskl_unit (pskl_var_f β))
     ⤳ (nil ++ ((γ ~ abind_flex_mono) ++ nil))
     ⨾ ((a_cstr_eq pskl_unit :: nil)
        ++ (a_cstr_eq (pskl_var_f γ) :: nil)) }}a
  /\ {{ (Θconf β)
        ⊢ (pskl_all_syn (pskl_var_f α)) ∼[ α ] (pskl_all_syn (pskl_var_b 0))
        ⤳ nil ⨾ (a_cstr_eq (pskl_var_f γ) :: nil) }}a
  (* … and ONLY the CROSS-HALF GUARD stops [LE-Arrow] combining them *)
  /\ ~ (ftvar_in_a_cstrs (a_cstr_eq (pskl_var_f γ) :: nil)
        ∩ dom (nil ++ ((γ ~ abind_flex_mono) ++ nil)) [=] empty)
  (* had it combined them, the fold on the answer would RUN … *)
  /\ (exists Ξs Q,
        {{ (((γ ~ abind_flex_mono) ++ nil) ++ ((β ~ abind_flex_mono) ++ nil))
           ⊩ (a_cstr_eq pskl_unit :: a_cstr_eq (pskl_var_f γ)
              :: a_cstr_eq (pskl_var_f γ) :: nil) ⨾ pskl_hole ⤳ Ξs ⨾ Q }}a)
  (* … while the THREADED collection separates the two atoms … *)
  /\ {{ S0 ↝ (add γ2 (add γ1 S0))
        ⊨ (Θconf β)
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
  (* … and on THAT answer the threaded fold cannot run at all *)
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
  split; [ apply probe_half_left; assumption | ].
  split; [ apply probe_half_right; assumption | ].
  split; [ apply probe_cross_half_guard_excludes_it | ].
  split; [ apply probe_fold_runs_conflated; clear - Hβγ; auto | ].
  split; [ apply probe_threaded_collection_separates; assumption | ].
  intros [S1 [Ξs [Q He]]].
  apply (probe_fold_stuck_deconflated β γ1 γ2 Hγ2β Hγ12).
  exists Ξs, Q.
  eapply e_solve_cstr_sound; [ exact He | ].
  simpl. clear - Hγ1 Hγ2 Hβ. fsetdec.
Qed.
