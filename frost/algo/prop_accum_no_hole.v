(** ACCUMULATED-SKELETON INVARIANT (Task A, docs/DESIGN-completeness-subtyping.md §7).

    "Every counterpart skeleton the algorithm feeds to [solve] is [□] or
    hole-free."  This discharges the [P0 = pskl_hole \/ pskl_no_hole P0]
    side-condition of the P6 completeness cluster
    (a_solve_eq_complete_var, algo/prop_look_complete_var.v;
    WF-SIDE-CONDITIONS.md, "pskl_no_hole P0 on P6-Cv").

    Four algo-level results, all Qed / axiom-free:
      A1  a_guess_hnh                    — guess^TY returns a paint (hole-free),
                                           guess^SK is the identity.
      A2  a_look_payload_hnh             — lookeq/looksub emit □-or-hole-free
                                           constraint payloads (mutual).
      A3  a_solve_cstr_hnh (+ _hole_start) — solving a constraint list from a
                                           □-or-hole-free accumulator against
                                           □-or-hole-free payloads stays so;
                                           generalises a_solve_eq_no_hole_p0
                                           (prop_look_complete.v) to the mutual
                                           sub/eq/cstr block.
      A4  a_sub_a_sub_flex_no_hole_p0    — a_sub / a_sub_flex outputs are
                                           hole-free when the counterpart P0 is
                                           (SUBJECT-FREE: holes come only from
                                           the counterpart, so ForallL merely
                                           threads P0 and the ∀-body
                                           instantiation is irrelevant; Infer /
                                           UnivGhostR have P0 = □ and are
                                           excluded by [pskl_no_hole P0]).
    Supporting: a_consis output preservation (a_consis_out_no_hole /
    a_consis_out_no_hole_q).

    No completeness kit is used — these are pure structural inductions over the
    algorithmic judgments.  [pskl_no_hole], [a_solve_eq_no_hole_p0] and the
    open/msubst reflection lemmas are reused from prop_look_complete.v. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_look_complete.

(* ===================================================================== *)
(*  The disjunctive invariant predicate: "□ or hole-free".               *)
(* ===================================================================== *)

Definition pskl_hnh (P : pskl) : Prop := P = pskl_hole \/ pskl_no_hole P.

Lemma pskl_hnh_hole : pskl_hnh pskl_hole.
Proof. left; reflexivity. Qed.

Lemma pskl_nh_hnh : forall P, pskl_no_hole P -> pskl_hnh P.
Proof. intros; right; assumption. Qed.

Lemma pskl_hnh_arrow_inv : forall P1 P2,
  pskl_hnh (pskl_arrow P1 P2) -> pskl_no_hole P1 /\ pskl_no_hole P2.
Proof. intros P1 P2 [H|H]; [discriminate | simpl in H; exact H]. Qed.

Lemma pskl_hnh_tophole_inv : forall P,
  pskl_hnh (pskl_tophole P) -> pskl_no_hole P.
Proof. intros P [H|H]; [discriminate | simpl in H; exact H]. Qed.

Lemma pskl_hnh_all_inv : forall P,
  pskl_hnh (pskl_all_syn P) -> pskl_no_hole P.
Proof. intros P [H|H]; [discriminate | simpl in H; exact H]. Qed.

Lemma guarded_pskl_hnh_nh : forall P,
  guarded_pskl P -> pskl_hnh P -> pskl_no_hole P.
Proof.
  intros P Hg [Heq|Hnh]; [subst; inversion Hg | exact Hnh].
Qed.

(* ===================================================================== *)
(*  A3 (strict, from counterpart): nh counterpart => nh output.          *)
(*  a_solve_eq_no_hole_p0 (prop_look_complete) is the eq half; here sub.  *)
(* ===================================================================== *)

Lemma a_solve_sub_no_hole_q : forall Θ m P Q P',
  Θ ⊢ₛ P ≼[ m ] Q ⤳ P' -> pskl_no_hole Q -> pskl_no_hole P'.
Proof.
  intros Θ m P Q P' H; induction H; intros Hnh; simpl in *; auto.
  - (* forall_l *)
    pick fresh β for L.
    apply (pskl_no_hole_open_inv P' (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | exact Hnh ].
  - (* vacuous: Q = □ *) contradiction.
  - (* check: eq P ∼ Q *) eapply a_solve_eq_no_hole_p0; eauto.
  - (* forall_r: Q = all_syn B *)
    pick fresh β for L.
    apply (H0 β); [ clear - Fr; fsetdec | ].
    apply pskl_no_hole_open_rec; simpl; auto.
  - (* arrow *)
    destruct Hnh as [Hq1 Hq2]; split; [ eapply a_solve_eq_no_hole_p0; eauto | auto ].
  - (* ghost_l_fn: Q = arrow Q1 Q2 *)
    destruct Hnh as [Hq1 Hq2]; split; [ eapply a_solve_eq_no_hole_p0; eauto | auto ].
Qed.

(* ===================================================================== *)
(*  A3 (strict, from subject): nh subject + hnh counterpart => nh output. *)
(*  (□-subject rules hole_l / ghost_l / ghost_l_fn are excluded by nh P.) *)
(* ===================================================================== *)

Lemma a_solve_eq_from_subj_no_hole : forall Θ P Q P',
  Θ ⊢ₑ P ∼ Q ⤳ P' -> pskl_no_hole P -> pskl_hnh Q -> pskl_no_hole P'.
Proof.
  intros Θ P Q P' H Hp Hq. destruct Hq as [HQ | HQ].
  - subst Q. inversion H; subst; simpl in *;
      first [ exact I | assumption | contradiction
            | match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end ].
  - eapply a_solve_eq_no_hole_p0; eauto.
Qed.

Lemma a_solve_sub_from_subj_no_hole : forall Θ m P Q P',
  Θ ⊢ₛ P ≼[ m ] Q ⤳ P' -> pskl_no_hole P -> pskl_hnh Q -> pskl_no_hole P'.
Proof.
  intros Θ m P Q P' H; induction H; intros Hp Hq; simpl in Hp |- *.
  - (* var *) exact I.
  - (* forall_l: subject all_syn P *)
    pick fresh β for L.
    apply (pskl_no_hole_open_inv P' (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | apply pskl_no_hole_open_rec; simpl; auto | exact Hq ].
  - (* univ_ghost_l *)
    apply IHa_solve_sub; [ exact Hp | exact Hq ].
  - (* vacuous: P' = P *) exact Hp.
  - (* check: eq P ∼ Q, guarded Q *)
    eapply a_solve_eq_no_hole_p0; [ eassumption | apply guarded_pskl_hnh_nh; assumption ].
  - (* forall_r: counterpart all_syn B *)
    pick fresh β for L.
    apply (H0 β); [ clear - Fr; fsetdec | exact Hp | ].
    apply pskl_nh_hnh, pskl_no_hole_open_rec; [ apply (pskl_hnh_all_inv _ Hq) | simpl; auto ].
  - (* arrow: counterpart arrow Q1 Q2 *)
    apply pskl_hnh_arrow_inv in Hq as [Hq1 Hq2]; destruct Hp as [Hp1 Hp2]; split.
    + eapply a_solve_eq_no_hole_p0; [ eassumption | exact Hq1 ].
    + apply IHa_solve_sub; [ exact Hp2 | apply pskl_nh_hnh; exact Hq2 ].
  - (* ghost_l_fn: subject □ *) contradiction.
  - (* ghost_l: subject □ *) contradiction.
Qed.

(* ===================================================================== *)
(*  A3 (disjunctive): hnh subject + hnh counterpart => hnh output;       *)
(*  then the constraint-list corollary (the □-start form a_extract uses). *)
(* ===================================================================== *)

Lemma a_solve_eq_hnh : forall Θ P Q P',
  Θ ⊢ₑ P ∼ Q ⤳ P' -> pskl_hnh P -> pskl_hnh Q -> pskl_hnh P'.
Proof.
  intros Θ P Q P' H Hp Hq. destruct Hq as [HQ | HQ].
  - (* counterpart □ *) subst Q. inversion H; subst;
      first [ left; reflexivity | right; exact I | exact Hp
            | match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end ].
  - (* counterpart nh: output nh regardless of subject *)
    right; eapply a_solve_eq_no_hole_p0; eauto.
Qed.

Lemma a_solve_sub_hnh : forall Θ m P Q P',
  Θ ⊢ₛ P ≼[ m ] Q ⤳ P' -> pskl_hnh P -> pskl_hnh Q -> pskl_hnh P'.
Proof.
  intros Θ m P Q P' H; induction H; intros Hp Hq.
  - (* var *) right; exact I.
  - (* forall_l: subject all_syn P -> nh; strict from-subject on the body *)
    pick fresh β for L.
    assert (Fr' : β `notin` L) by (clear - Fr; fsetdec).
    specialize (H β Fr').
    right; simpl; apply (pskl_no_hole_open_inv P' (pskl_var_f β)).
    eapply a_solve_sub_from_subj_no_hole;
      [ exact H
      | apply pskl_no_hole_open_rec; [ apply (pskl_hnh_all_inv _ Hp) | simpl; auto ]
      | exact Hq ].
  - (* univ_ghost_l *)
    right; simpl.
    eapply a_solve_sub_from_subj_no_hole;
      [ eassumption | apply (pskl_hnh_tophole_inv _ Hp) | exact Hq ].
  - (* vacuous: out = subject P *) exact Hp.
  - (* check *) right.
    eapply a_solve_eq_no_hole_p0; [ eassumption | apply guarded_pskl_hnh_nh; assumption ].
  - (* forall_r: out P' via IH *)
    pick fresh β for L.
    assert (Fr' : β `notin` L) by (clear - Fr; fsetdec).
    specialize (H0 β Fr'); apply H0; [ exact Hp | ].
    apply pskl_nh_hnh, pskl_no_hole_open_rec; [ apply (pskl_hnh_all_inv _ Hq) | simpl; auto ].
  - (* arrow *)
    apply pskl_hnh_arrow_inv in Hq as [Hq1 Hq2]; apply pskl_hnh_arrow_inv in Hp as [Hp1 Hp2].
    right; simpl; split;
      [ eapply a_solve_eq_no_hole_p0; [ eassumption | exact Hq1 ]
      | eapply a_solve_sub_no_hole_q; [ eassumption | exact Hq2 ] ].
  - (* ghost_l_fn: subject □, counterpart arrow Q1 Q2 *)
    apply pskl_hnh_arrow_inv in Hq as [Hq1 Hq2].
    right; simpl; split;
      [ eapply a_solve_eq_no_hole_p0; [ eassumption | exact Hq1 ]
      | eapply a_solve_sub_no_hole_q; [ eassumption | exact Hq2 ] ].
  - (* ghost_l: subject □, counterpart B guarded *)
    right; simpl; apply guarded_pskl_hnh_nh; assumption.
Qed.

Definition a_cstr_hnh (c : a_cstr) : Prop :=
  match c with
  | a_cstr_sub _ Q => pskl_hnh Q
  | a_cstr_eq Q => pskl_hnh Q
  end.

(** A3 main: solving a constraint list from a □-or-hole-free accumulator
    against □-or-hole-free payloads yields a □-or-hole-free result. *)
Lemma a_solve_cstr_hnh : forall Θ C P Q,
  Θ ⊩ C ⨾ P ⤳ Q -> pskl_hnh P -> Forall a_cstr_hnh C -> pskl_hnh Q.
Proof.
  intros Θ C P Q H; induction H; intros Hp Hc.
  - (* empty *) exact Hp.
  - (* sub *) inversion Hc as [| ? ? Hhead ?]; subst; simpl in Hhead.
    eapply a_solve_sub_hnh; [ eassumption | exact Hp | exact Hhead ].
  - (* eq *) inversion Hc as [| ? ? Hhead Htail]; subst; simpl in Hhead.
    apply IHa_solve_cstr; [ | exact Htail ].
    eapply a_solve_eq_hnh; [ eassumption | exact Hp | exact Hhead ].
Qed.

(** The exact form a_extract feeds to guess: solve from □. *)
Corollary a_solve_cstr_hole_start_hnh : forall Θ C Q,
  Θ ⊩ C ⨾ pskl_hole ⤳ Q -> Forall a_cstr_hnh C -> pskl_hnh Q.
Proof.
  intros Θ C Q H Hc. eapply a_solve_cstr_hnh; [ exact H | apply pskl_hnh_hole | exact Hc ].
Qed.

(* ===================================================================== *)
(*  A2: look payloads are □-or-hole-free when the counterpart is.         *)
(* ===================================================================== *)

(* derive hnh of the recursion counterpart from the conclusion counterpart *)
Ltac hnh_open Hpp :=
  apply pskl_nh_hnh, pskl_no_hole_open_rec;
    [ first [ apply (pskl_hnh_all_inv _ Hpp) | exact Hpp ] | simpl; auto ].

Lemma a_look_payload_hnh :
  (forall α m P P' Ξ C, a_looksub α m P P' Ξ C -> pskl_hnh P' -> Forall a_cstr_hnh C)
  /\ (forall α P P' Ξ C, a_lookeq α P P' Ξ C -> pskl_hnh P' -> Forall a_cstr_hnh C).
Proof.
  apply a_looksub_lookeq_mutind; intros.
  - (* LS-var: [sub m P'] *) simpl; constructor; [ assumption | constructor ].
  - (* LS-absent *) constructor.
  - (* LS-vacuous *) constructor.
  - (* LS-check: lookeq A ∼ B, counterpart B = P' *)
    match goal with IH : pskl_hnh _ -> Forall _ _ |- _ => apply IH; assumption end.
  - (* LS-forall_r: counterpart all_syn B; body at (open B β) *)
    match goal with
    | IH : forall b, b `notin` ?L -> pskl_hnh _ -> Forall _ _,
      Hpp : pskl_hnh (pskl_all_syn _) |- _ =>
        pick fresh β for L; apply (IH β); [ clear - Fr; fsetdec | hnh_open Hpp ]
    end.
  - (* LS-arrow: C1 (lookeq P1∼P1') ++ C2 (looksub P2≼P2') *)
    match goal with Hpp : pskl_hnh (pskl_arrow _ _) |- _ =>
      apply pskl_hnh_arrow_inv in Hpp as [Hq1 Hq2] end.
    apply Forall_app; split;
      match goal with IH : pskl_hnh ?X -> Forall _ _ |- _ =>
        apply IH; apply pskl_nh_hnh; assumption end.
  - (* LS-forall_l: counterpart P' unchanged; body at (open P β) *)
    match goal with
    | IH : forall b, b `notin` ?L -> pskl_hnh _ -> Forall _ _,
      Hpp : pskl_hnh _ |- _ =>
        pick fresh β for L; apply (IH β); [ clear - Fr; fsetdec | exact Hpp ]
    end.
  - (* LS-univ_ghost_l: counterpart P'; body P ≼ P' *)
    match goal with IH : pskl_hnh _ -> Forall _ _, Hpp : pskl_hnh _ |- _ =>
      apply IH; exact Hpp end.
  - (* LE-var: [eq P'] *) simpl; constructor; [ assumption | constructor ].
  - (* LE-absent *) constructor.
  - (* LE-vacuous *) constructor.
  - (* LE-flex_r: [eq (var γ)] *) simpl; constructor; [ right; exact I | constructor ].
  - (* LE-arrow *)
    match goal with Hpp : pskl_hnh (pskl_arrow _ _) |- _ =>
      apply pskl_hnh_arrow_inv in Hpp as [Hq1 Hq2] end.
    apply Forall_app; split;
      match goal with IH : pskl_hnh ?X -> Forall _ _ |- _ =>
        apply IH; apply pskl_nh_hnh; assumption end.
  - (* LE-forall_inh: counterpart all_syn P'; body (open P)∼(open P') *)
    match goal with
    | IH : forall b, b `notin` ?L -> pskl_hnh _ -> Forall _ _,
      Hpp : pskl_hnh (pskl_all_syn _) |- _ =>
        pick fresh β for L; apply (IH β); [ clear - Fr; fsetdec | hnh_open Hpp ]
    end.
  - (* LE-forall_syn: counterpart ⊤◇P' unchanged *)
    match goal with
    | IH : forall b, b `notin` ?L -> pskl_hnh _ -> Forall _ _,
      Hpp : pskl_hnh (pskl_tophole _) |- _ =>
        pick fresh β for L; apply (IH β); [ clear - Fr; fsetdec | exact Hpp ]
    end.
  - (* LE-univ_ghost: counterpart ⊤◇P'; body P ∼ P' *)
    match goal with IH : pskl_hnh _ -> Forall _ _, Hpp : pskl_hnh (pskl_tophole _) |- _ =>
      apply IH; apply pskl_nh_hnh; apply (pskl_hnh_tophole_inv _ Hpp) end.
  - (* LE-univ_ghost1: counterpart all_syn P'; body ⊤◇P ∼ (open P') *)
    match goal with
    | IH : forall b, b `notin` ?L -> pskl_hnh _ -> Forall _ _,
      Hpp : pskl_hnh (pskl_all_syn _) |- _ =>
        pick fresh β for L; apply (IH β); [ clear - Fr; fsetdec | hnh_open Hpp ]
    end.
  - (* LE-univ_ghost2: counterpart P' guarded; body P ∼ P' *)
    match goal with IH : pskl_hnh _ -> Forall _ _, Hpp : pskl_hnh _ |- _ =>
      apply IH; exact Hpp end.
  - (* LE-univ_ghost_r: counterpart ⊤◇P'; body P ∼ P' *)
    match goal with IH : pskl_hnh _ -> Forall _ _, Hpp : pskl_hnh (pskl_tophole _) |- _ =>
      apply IH; apply pskl_nh_hnh; apply (pskl_hnh_tophole_inv _ Hpp) end.
Qed.

(* ===================================================================== *)
(*  A1: guess output is □-or-hole-free.                                   *)
(*  guess^TY returns a paint (hole-free); guess^SK is the identity.       *)
(* ===================================================================== *)

Lemma a_guess_hnh : forall NM Q Ξ' Q',
  a_guess NM Q Ξ' Q' -> pskl_hnh Q -> pskl_hnh Q'.
Proof.
  intros NM Q Ξ' Q' H Hq. inversion H; subst.
  - (* sk: identity *) exact Hq.
  - (* ty: readback of a ptyp — hole-free *) right; apply ptyp_to_pskl_no_hole.
Qed.

(* ===================================================================== *)
(*  a_consis output preservation (strict): nh counterpart + nh subject    *)
(*  => nh output.  (Ghost has □ subject, GhostR has □ counterpart — both   *)
(*  excluded by the nh premises.)  Support for A4's arrow case.           *)
(* ===================================================================== *)

Lemma a_consis_out_no_hole : forall F Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis F Δ1 Δ2 Θ0 P0 P Q Θ1 ->
  pskl_no_hole P0 -> pskl_no_hole P -> pskl_no_hole Q.
Proof.
  intros F Δ1 Δ2 Θ0 P0 P Q Θ1 H; induction H; intros Hp0 Hp; simpl in *.
  - (* ghost: out = P0 *) exact Hp0.
  - (* unit *) exact I.
  - (* rigid *) exact I.
  - (* arrow *) destruct Hp0 as [Hp0a Hp0b]; destruct Hp as [Hpa Hpb]; split;
      match goal with
      | IH : pskl_no_hole _ -> pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
          apply IH; assumption
      end.
  - (* forall_inh *) pick fresh β for L.
    apply (pskl_no_hole_open_inv Q (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec
              | apply pskl_no_hole_open_rec; [ exact Hp0 | simpl; auto ]
              | apply pskl_no_hole_open_rec; [ exact Hp  | simpl; auto ] ].
  - (* forall_syn: counterpart ⊤◇P0, subject all_syn P *)
    pick fresh β for L.
    apply (pskl_no_hole_open_inv Q (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec
              | simpl; exact Hp0
              | apply pskl_no_hole_open_rec; [ exact Hp | simpl; auto ] ].
  - (* univ_ghost: ⊤◇P0 / ⊤◇P / ⊤◇Q *)
    match goal with IH : pskl_no_hole _ -> pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q => apply IH; assumption end.
  - (* univ_ghost1: counterpart all_syn P0, subject ⊤◇P *)
    pick fresh β for L.
    apply (pskl_no_hole_open_inv Q (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec
              | apply pskl_no_hole_open_rec; [ exact Hp0 | simpl; auto ]
              | simpl; exact Hp ].
  - (* univ_ghost2: counterpart P0, subject ⊤◇P *)
    match goal with IH : pskl_no_hole _ -> pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q => apply IH; assumption end.
  - (* flex: out var *) exact I.
  - (* flex_l: out var *) exact I.
  - (* flex_r: out var *) exact I.
  - (* ghost_r: out = subject P *) exact Hp.
  - (* univ_ghost_r: counterpart ⊤◇P0, subject P guarded *)
    match goal with IH : pskl_no_hole _ -> pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q => apply IH; assumption end.
Qed.

(* ===================================================================== *)
(*  a_consis output (counterpart-only): nh counterpart => nh output.      *)
(*  Subject-free — holes in the output come only from the counterpart.    *)
(* ===================================================================== *)

Lemma a_consis_out_no_hole_q : forall F Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis F Δ1 Δ2 Θ0 P0 P Q Θ1 -> pskl_no_hole P0 -> pskl_no_hole Q.
Proof.
  intros F Δ1 Δ2 Θ0 P0 P Q Θ1 H; induction H; intros Hp0; simpl in *.
  - (* ghost: out = P0 *) exact Hp0.
  - (* unit *) exact I.
  - (* rigid *) exact I.
  - (* arrow *) destruct Hp0 as [Hp0a Hp0b]; split;
      match goal with IH : pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
        apply IH; assumption end.
  - (* forall_inh: counterpart all_syn P0 *) pick fresh β for L.
    apply (pskl_no_hole_open_inv Q (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | apply pskl_no_hole_open_rec; [ exact Hp0 | simpl; auto ] ].
  - (* forall_syn: counterpart ⊤◇P0 (unchanged in body) *) pick fresh β for L.
    apply (pskl_no_hole_open_inv Q (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | simpl; exact Hp0 ].
  - (* univ_ghost: counterpart ⊤◇P0 -> body P0 *)
    match goal with IH : pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
      apply IH; exact Hp0 end.
  - (* univ_ghost1: counterpart all_syn P0 -> body (open P0) *) pick fresh β for L.
    apply (pskl_no_hole_open_inv Q (pskl_var_f β)).
    apply H0; [ clear - Fr; fsetdec | apply pskl_no_hole_open_rec; [ exact Hp0 | simpl; auto ] ].
  - (* univ_ghost2: counterpart P0 -> body P0 *)
    match goal with IH : pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
      apply IH; exact Hp0 end.
  - (* flex *) exact I.
  - (* flex_l *) exact I.
  - (* flex_r *) exact I.
  - (* ghost_r: counterpart □ — excluded *) contradiction.
  - (* univ_ghost_r: counterpart ⊤◇P0 -> body P0 *)
    match goal with IH : pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
      apply IH; exact Hp0 end.
Qed.

(* ===================================================================== *)
(*  A4: a_sub / a_sub_flex output is hole-free when the counterpart is.   *)
(*  SUBJECT-FREE: holes in the output come only from the counterpart P0,  *)
(*  so ForallL just threads P0 (the ∀-body instantiation is irrelevant),  *)
(*  and Infer / UnivGhostR (P0 = □) are excluded by [pskl_no_hole P0].    *)
(* ===================================================================== *)

Lemma subst_pskl_no_hole : forall V x P,
  pskl_no_hole V -> pskl_no_hole P -> pskl_no_hole (subst_pskl_in_pskl V x P).
Proof.
  intros V x P HV; induction P; intros HP; simpl in *.
  - (* unit *) exact I.
  - (* var_b *) exact I.
  - (* var_f *) match goal with |- context [if ?c then _ else _] => destruct c end;
      [ exact HV | exact I ].
  - (* arrow *) destruct HP as [HP1 HP2]; split;
      match goal with IH : pskl_no_hole ?P -> pskl_no_hole (subst_pskl_in_pskl _ _ ?P) |- _ =>
        apply IH; assumption end.
  - (* all_syn *)
    match goal with IH : pskl_no_hole ?P -> pskl_no_hole (subst_pskl_in_pskl _ _ ?P) |- _ =>
      apply IH; assumption end.
  - (* hole: nh □ = False *) contradiction.
  - (* tophole *)
    match goal with IH : pskl_no_hole ?P -> pskl_no_hole (subst_pskl_in_pskl _ _ ?P) |- _ =>
      apply IH; assumption end.
Qed.

Scheme a_sub_mut_nh := Induction for a_sub Sort Prop
  with a_sub_flex_mut_nh := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_mut_nh from a_sub_mut_nh, a_sub_flex_mut_nh.

Lemma a_sub_a_sub_flex_no_hole_p0 :
  (forall NM M P0 Θ0 P Q Θ1, a_sub NM M P0 Θ0 P Q Θ1 ->
     pskl_no_hole P0 -> pskl_no_hole Q)
  /\ (forall NM M P0 Θ0 Ξ α A Θ1, a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
     pskl_no_hole P0 -> pskl_no_hole A).
Proof.
  apply a_sub_sub_flex_mut_nh; intros; simpl in *.
  all: try contradiction.                       (* Infer, UnivGhostR: counterpart □ *)
  all: try assumption.                           (* Check, ForallR, Ghost: Q = counterpart *)
  all: try (match goal with H : pskl_no_hole _ /\ pskl_no_hole _ |- _ =>
              destruct H as [Hp0a Hp0b] end; split;
            [ solve [ eapply a_consis_out_no_hole_q; [ eassumption | eassumption ]
                    | match goal with IH : _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
                        apply IH; assumption end ]
            | match goal with IH : _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
                apply IH; assumption end ]).   (* Arrow *)
  all: try (match goal with IH : pskl_no_hole _ -> pskl_no_hole ?Q |- pskl_no_hole ?Q =>
              apply IH; assumption end).         (* ForallL, UnivGhostL, FlexMono, FlexSolve/Depend/Skip *)
  all: try (match goal with IH : pskl_no_hole _ -> pskl_no_hole ?A |- pskl_no_hole ?A =>
              apply IH; apply subst_pskl_no_hole;
                [ apply ptyp_to_pskl_no_hole | assumption ] end).  (* FlexAssign *)
Qed.
