(** ext_algo — the supply invariants of the solving layer, and its bridge.

    §1  supply growth
    §2  the generated block, as SET ARITHMETIC (the M3a lesson): in the output
        supply, out of the input supply, [uniq], and mentioning only its own
        domain
    §3  the bridge

    ⚙ §2's fourth conjunct ([ftvar_in_aenv Ξ [<=] dom Ξ]) is new here and it
    is what the CONTEXT threading forces: an arrow row's second premise runs
    at [Ξ1 ++ Θ], so the bridge must move that context into the supply, and
    for the [Ξ1] half it can only do so by knowing the block mentions nothing
    beyond its own names. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.

Set Implicit Arguments.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The supply only grows                                             *)
(* ===================================================================== *)

Lemma e_solve_sub_eq_supply_grows :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1).
Proof.
  apply (e_solve_sub_eq_mutind
           (fun S0 Θ m P Q S1 Ξ P' _ => S0 [<=] S1)
           (fun S0 Θ P Q S1 Ξ P' _ => S0 [<=] S1));
    intros;
    try (match goal with
         | Hg : e_guess_mono _ _ _ _ _ |- _ =>
             exact (e_guess_mono_supply_grows Hg)
         end);
    fsetdec.
Qed.

Corollary e_solve_sub_supply_grows : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1.
Proof. apply e_solve_sub_eq_supply_grows. Qed.

Corollary e_solve_eq_supply_grows : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1.
Proof. apply e_solve_sub_eq_supply_grows. Qed.

Lemma e_solve_cstr_supply_grows : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e -> S0 [<=] S1.
Proof.
  intros * H; induction H;
    try (match goal with
         | Hs : e_solve_sub _ _ _ _ _ _ _ _ |- _ =>
             pose proof (e_solve_sub_supply_grows Hs)
         end);
    try (match goal with
         | He : e_solve_eq _ _ _ _ _ _ _ |- _ =>
             pose proof (e_solve_eq_supply_grows He)
         end);
    fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  The generated block                                               *)
(* ===================================================================== *)

#[local] Ltac solve_grow_facts :=
  repeat match goal with
  | H : e_solve_sub ?S0 _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_solve_sub_supply_grows H)
      end
  | H : e_solve_eq ?S0 _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_solve_eq_supply_grows H)
      end
  | H : e_solve_cstr ?S0 _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_solve_cstr_supply_grows H)
      end
  | H : e_guess_mono ?S0 _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_guess_mono_supply_grows H)
      end
  end.

(** SE-FlexR's block comes straight from [guess^TY], so all four conjuncts are
    M1's, imported rather than re-derived. *)
#[local] Ltac guess_block_facts :=
  repeat match goal with
  | H : e_guess_mono _ _ _ ?X _ |- _ =>
      lazymatch goal with
      | _ : dom X [<=] _ |- _ => fail
      | _ => pose proof (e_guess_mono_generated_in_supply H);
             pose proof (e_guess_mono_block_fresh H);
             pose proof (e_guess_mono_uniq H);
             pose proof (e_guess_mono_generated_ftvar H)
      end
  end.

Lemma e_solve_sub_eq_block :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply (e_solve_sub_eq_mutind
           (fun S0 Θ m P Q S1 Ξ P' _ =>
              dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
              /\ ftvar_in_aenv Ξ [<=] dom Ξ)
           (fun S0 Θ P Q S1 Ξ P' _ =>
              dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
              /\ ftvar_in_aenv Ξ [<=] dom Ξ));
    intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    solve_grow_facts; guess_block_facts;
    repeat (rewrite dom_app in * || rewrite ftvar_in_aenv_app in * );
    simpl in *;
    repeat split;
    try solve [ fsetdec ];
    try solve [ solve_uniq ];
    (* the arrow rows: the second block is fresh for a supply that already
       holds the first *)
    try solve [ apply uniq_app_4;
                [ assumption | assumption | unfold disjoint; fsetdec ] ].
Qed.

Corollary e_solve_sub_block_in_supply : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> dom Ξ [<=] S1.
Proof. intros * H. apply (proj1 e_solve_sub_eq_block) in H. tauto. Qed.

Corollary e_solve_eq_block_in_supply : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> dom Ξ [<=] S1.
Proof. intros * H. apply (proj2 e_solve_sub_eq_block) in H. tauto. Qed.

Corollary e_solve_sub_block_ftvar : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros * H. apply (proj1 e_solve_sub_eq_block) in H. tauto. Qed.

Corollary e_solve_eq_block_ftvar : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros * H. apply (proj2 e_solve_sub_eq_block) in H. tauto. Qed.

Corollary e_solve_sub_uniq : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> uniq Ξ.
Proof. intros * H. apply (proj1 e_solve_sub_eq_block) in H. tauto. Qed.

Corollary e_solve_eq_uniq : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> uniq Ξ.
Proof. intros * H. apply (proj2 e_solve_sub_eq_block) in H. tauto. Qed.

(** The context an arrow row's second premise runs at is still covered by the
    supply.  ⭐ This is the whole reason §2 carries its fourth conjunct, and it
    is the step the CONTEXT threading makes necessary. *)
Lemma e_solve_ctx_cov : forall (Ξ Θ : aenv) (S0 S1 : supply),
  ftvar_in_aenv Θ [<=] S0 ->
  S0 [<=] S1 ->
  dom Ξ [<=] S1 ->
  ftvar_in_aenv Ξ [<=] dom Ξ ->
  ftvar_in_aenv (Ξ ++ Θ) [<=] S1.
Proof. intros * H1 H2 H3 H4. rewrite ftvar_in_aenv_app. fsetdec. Qed.

(** Bound every opened skeleton, and pin every closed one.  Guards keyed on
    the POSED fact's own shape, so the [repeat]s terminate. *)
#[local] Ltac binder_facts :=
  repeat match goal with
  | H : context [ ftvar_in_pskl (open_pskl_wrt_pskl ?X (pskl_var_f ?b)) ] |- _ =>
      lazymatch goal with
      | _ : ftvar_in_pskl (open_pskl_wrt_pskl X (pskl_var_f b)) [<=] _ |- _ =>
          fail
      | _ => pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X (pskl_var_f b))
      end
  end;
  repeat match goal with
  | |- context [ ftvar_in_pskl (close_pskl_wrt_pskl ?b ?X) ] =>
      lazymatch goal with
      | _ : ftvar_in_pskl (close_pskl_wrt_pskl b X) [=] _ |- _ => fail
      | _ => pose proof (ftvar_in_pskl_close_pskl_wrt_pskl X b)
      end
  end.

(** ⭐ WHAT THE SOLVED PATTERN CAN MENTION.  Needed because the constraint
    fold hands one row's OUTPUT [P''] to the next row as its input, so the
    pipeline's bridge has to bound it.  ⚙ Hypothesis-free, in the §7.9 shape:
    the subjects sit on the right, and coverage collapses it at the use site. *)
Lemma e_solve_sub_eq_out_ftvar :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_pskl P' [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_pskl P' [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q).
Proof.
  apply (e_solve_sub_eq_mutind
           (fun S0 Θ m P Q S1 Ξ P' _ =>
              ftvar_in_pskl P' [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q)
           (fun S0 Θ P Q S1 Ξ P' _ =>
              ftvar_in_pskl P' [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q));
    intros; solve_grow_facts;
    (* SE-FlexR: the output is the GUESS's, so M1 bounds it *)
    repeat match goal with
    | H : e_guess_mono _ _ _ _ _ |- _ =>
        lazymatch goal with
        | _ : ftvar_in_ptyp _ [<=] _ |- _ => fail
        | _ => pose proof (e_guess_mono_ftv H);
               pose proof (e_guess_mono_generated_in_supply H)
        end
    end;
    (* ⚠️ [simpl] MUST come before [binder_facts]: the ∀ rows wrap their
       output in [pskl_all_syn], so the [close] subterm the tactic looks for
       is not visible until the wrapper is reduced away *)
    simpl in *; binder_facts;
    (* and again after: the posed [open] bounds mention
       [ftvar_in_pskl (pskl_var_f β)], which [fsetdec] must see as [{β}] to
       connect it to the growth fact [add β S0 [<=] S1] *)
    simpl in *;
    try fsetdec.
  (* SE-FlexR — the only row [fsetdec] cannot finish, because relating the
     guessed TYPE to its [pskl] reading is a rewrite, not set arithmetic *)
  all: rewrite ftvar_ptyp_to_pskl; fsetdec.
Qed.

Corollary e_solve_eq_out_ftvar : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  ftvar_in_pskl P' [<=] S1.
Proof.
  intros * H Hcov. pose proof (e_solve_eq_supply_grows H) as Hgrow.
  apply (proj2 e_solve_sub_eq_out_ftvar) in H. clear - H Hcov Hgrow. fsetdec.
Qed.

(* ===================================================================== *)
(*  §3  The bridge                                                        *)
(* ===================================================================== *)

Lemma e_solve_sub_eq_sound :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
     {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
     {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a).
Proof.
  apply (e_solve_sub_eq_mutind
    (fun S0 Θ m P Q S1 Ξ P' _ =>
       ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
       {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a)
    (fun S0 Θ P Q S1 Ξ P' _ =>
       ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
       {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a)).

  (* ---- solve_sub ---- *)
  - (* SS-Var *) intros. apply a_solve_sub__var.
  - (* SS-ForallL *)
    intros S0 S1 Θ m P Q Ξ P' β Hβ Hs IH Hcov.
    apply a_solve_sub__forall_l with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *. clear - H1 Hcov. fsetdec.
  - (* SS-UnivGhostL *)
    intros S0 S1 Θ m P Q Ξ P' Hs IH Hcov.
    apply a_solve_sub__univ_ghost_l. apply IH. simpl in Hcov.
    clear - Hcov. fsetdec.
  - (* SS-Vacuous *) intros. apply a_solve_sub__vacuous.
  - (* SS-Check *)
    intros S0 S1 Θ P Q Ξ P' Hgf Hg1 Hg2 He IH Hcov.
    apply a_solve_sub__check; auto.
  - (* SS-ForallR *)
    intros S0 S1 Θ P B Ξ P' β Hgf Hβ Hs IH Hcov.
    apply a_solve_sub__forall_r with (β := β); [ assumption | | ].
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *. clear - H1 Hcov. fsetdec.
  - (* SS-Arrow — the second premise runs at [Ξ1 ++ Θ] and [S1] *)
    intros S0 S1 S2 Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' He IH1 Hs IH2 Hcov.
    simpl in Hcov.
    pose proof (e_solve_eq_supply_grows He) as Hgrow.
    pose proof (e_solve_eq_block_in_supply He) as Hbin.
    pose proof (e_solve_eq_block_ftvar He) as Hbftv.
    apply a_solve_sub__arrow.
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      clear - Hctx Hcov Hgrow. fsetdec.
  - (* SS-GhostLF *)
    intros S0 S1 S2 Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' He IH1 Hs IH2 Hcov.
    simpl in Hcov.
    pose proof (e_solve_eq_supply_grows He) as Hgrow.
    pose proof (e_solve_eq_block_in_supply He) as Hbin.
    pose proof (e_solve_eq_block_ftvar He) as Hbftv.
    apply a_solve_sub__ghost_l_fn.
    + apply IH1. simpl. clear - Hcov. fsetdec.
    + apply IH2.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      simpl. clear - Hctx Hcov Hgrow. fsetdec.
  - (* SS-GhostL *) intros. apply a_solve_sub__ghost_l; assumption.

  (* ---- solve_eq ---- *)
  - (* SE-Unit *) intros. apply a_solve_eq__unit.
  - (* SE-Var *) intros. apply a_solve_eq__var.
  - (* SE-FlexR — the layer's generating row: M1's bridge does the work *)
    intros S0 S1 Θ α P Ξ A Hf Hnf Hng Hg Hcov.
    apply a_solve_eq__flex_r; try assumption.
    eapply e_guess_mono_sound;
      [ exact Hg | clear - Hcov; fsetdec | clear - Hcov; fsetdec ].
  - (* SE-GhostL *) intros. apply a_solve_eq__hole_l.
  - (* SE-VacuousR *) intros. apply a_solve_eq__hole_r.
  - (* SE-Arrow *)
    intros S0 S1 S2 Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' He1 IH1 He2 IH2 Hcov.
    simpl in Hcov.
    pose proof (e_solve_eq_supply_grows He1) as Hgrow.
    pose proof (e_solve_eq_block_in_supply He1) as Hbin.
    pose proof (e_solve_eq_block_ftvar He1) as Hbftv.
    apply a_solve_eq__arrow.
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      clear - Hctx Hcov Hgrow. fsetdec.
  - (* SE-Forall *)
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH Hcov.
    apply a_solve_eq__forall with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)) as H2.
      simpl in H1, H2, Hcov |- *. clear - H1 H2 Hcov. fsetdec.
  - (* SE-UnivGhost *)
    intros S0 S1 Θ P Q Ξ P' He IH Hcov.
    apply a_solve_eq__tophole_both. apply IH. simpl in Hcov.
    clear - Hcov. fsetdec.
  - (* SE-GhostForall *)
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH Hcov.
    apply a_solve_eq__tophole_l_all with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)) as H2.
      simpl in H2, Hcov |- *. clear - H2 Hcov. fsetdec.
  - (* SE-GhostGuarded *)
    intros S0 S1 Θ P Q Ξ P' Hg He IH Hcov.
    apply a_solve_eq__tophole_l_guarded; [ assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
  - (* SE-ForallGhost *)
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH Hcov.
    apply a_solve_eq__all_l_tophole with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *. clear - H1 Hcov. fsetdec.
  - (* SE-GuardedGhost *)
    intros S0 S1 Θ P Q Ξ P' Hg He IH Hcov.
    apply a_solve_eq__tophole_r_guarded; [ assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
Qed.

Corollary e_solve_sub_sound : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a.
Proof. intros. eapply (proj1 e_solve_sub_eq_sound); eassumption. Qed.

Corollary e_solve_eq_sound : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a.
Proof. intros. eapply (proj2 e_solve_sub_eq_sound); eassumption. Qed.

(* ===================================================================== *)
(*  §4  The constraint fold                                               *)
(*                                                                        *)
(*  Not mutual with §1-§3, so a plain induction — but the same three       *)
(*  statements, because [a_extract] consumes all three: the block it       *)
(*  deposits, what its result can mention, and the bridge.                *)
(* ===================================================================== *)

Lemma e_solve_cstr_block : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
  /\ ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros * H; induction H as
    [ S Θ P | S0 S1 Θ m Q P Ξ P' Hs | S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'' He Hc IH ].
  - simpl. repeat split; try apply uniq_nil; fsetdec.
  - (* the conjunction is verbatim §2's *)
    exact ((proj1 e_solve_sub_eq_block) _ _ _ _ _ _ _ _ Hs).
  - destruct IH as [Hin2 [Hfr2 [Hu2 Hft2]]].
    pose proof (e_solve_eq_block_in_supply He) as Hin1.
    pose proof (e_solve_eq_block_ftvar He) as Hft1.
    pose proof (e_solve_eq_uniq He) as Hu1.
    pose proof ((proj2 e_solve_sub_eq_block) _ _ _ _ _ _ _ He) as Hall.
    destruct Hall as [_ [Hfr1 _]].
    pose proof (e_solve_eq_supply_grows He) as Hg1.
    pose proof (e_solve_cstr_supply_grows Hc) as Hg2.
    repeat rewrite dom_app in *; repeat rewrite ftvar_in_aenv_app in *.
    repeat split; try solve [ fsetdec ].
    apply uniq_app_4; [ assumption | assumption | unfold disjoint; fsetdec ].
Qed.

Lemma e_solve_cstr_out_ftvar : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  ftvar_in_pskl Q [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C.
Proof.
  intros * H; induction H as
    [ S Θ P | S0 S1 Θ m Q P Ξ P' Hs | S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'' He Hc IH ];
    simpl in *.
  - fsetdec.
  - pose proof ((proj1 e_solve_sub_eq_out_ftvar) _ _ _ _ _ _ _ _ Hs).
    fsetdec.
  - pose proof ((proj2 e_solve_sub_eq_out_ftvar) _ _ _ _ _ _ _ He).
    pose proof (e_solve_cstr_supply_grows Hc) as Hg2.
    fsetdec.
Qed.

Lemma e_solve_cstr_sound : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_a_cstrs C ∪ ftvar_in_pskl P [<=] S0 ->
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}a.
Proof.
  intros * H; induction H as
    [ S Θ P | S0 S1 Θ m Q P Ξ P' Hs | S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'' He Hc IH ];
    intros Hcov; simpl in Hcov.
  - apply a_solve_cstr__empty.
  - apply a_solve_cstr__sub. eapply e_solve_sub_sound;
      [ exact Hs | clear - Hcov; fsetdec ].
  - (* the tail solves on the head's YIELD, at the head's OUTPUT context and
       supply — so the bridge needs BOTH §3's output bound and §2's block *)
    pose proof (e_solve_eq_supply_grows He) as Hg1.
    pose proof (e_solve_eq_block_in_supply He) as Hbin.
    pose proof (e_solve_eq_block_ftvar He) as Hbftv.
    pose proof (e_solve_eq_out_ftvar He ltac:(clear - Hcov; fsetdec)) as Hout.
    apply a_solve_cstr__eq with (P'' := P'').
    + eapply e_solve_eq_sound; [ exact He | clear - Hcov; fsetdec ].
    + apply IH.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      clear - Hctx Hout Hcov Hg1. fsetdec.
Qed.
