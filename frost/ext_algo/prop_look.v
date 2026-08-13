(** ext_algo — the supply invariants of the collection cluster, and its bridge.

    §1  supply growth
    §2  the block is generated: it lands in the output supply, and it was not
        in the input one — hence ⭐ [uniq Ξ]
    §3  the bridge, and ⭐ the [a_sub__forall_l] payoff

    ⚙ The shape is [prop_guess.v]'s, not [prop_consis.v]'s, because the
    collection has no output context (see def_look.v's header).  All four
    invariants are therefore hypothesis-free, and they fit in one mutual
    induction each. *)

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
Require Import src.frost.ext_algo.def_look.

Set Implicit Arguments.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The supply only grows                                             *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_supply_grows :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1).
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ => S0 [<=] S1)
           (fun S0 Θ α P P' S1 Ξ C _ => S0 [<=] S1));
    intros; fsetdec.
Qed.

Corollary e_looksub_supply_grows : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1.
Proof. apply e_looksub_lookeq_supply_grows. Qed.

Corollary e_lookeq_supply_grows : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1.
Proof. apply e_looksub_lookeq_supply_grows. Qed.

(** Turn every collection derivation in context into its §1 growth fact,
    name-free (the [Combined Scheme] rationale of prop_consis.v §2). *)
#[local] Ltac look_grow_facts :=
  repeat match goal with
  | H : e_looksub ?S0 _ _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_looksub_supply_grows H)
      end
  | H : e_lookeq ?S0 _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_lookeq_supply_grows H)
      end
  end.

(* ===================================================================== *)
(*  §2  The generated block — in the output supply, out of the input      *)
(*      supply, and therefore DUPLICATE-FREE                              *)
(*                                                                        *)
(*  ⭐ ONE induction for all three, because the third needs the first two: *)
(*  the arrow rows' [uniq (Ξ1 ++ Ξ2)] is exactly: the left block is        *)
(*  inside S1 and the right block misses S1.  Stating the freshness        *)
(*  as SET ARITHMETIC ([dom Ξ ∩ S0 [=] empty]) rather than as             *)
(*  [∀ γ ∈ dom Ξ, γ ∉ S0] is what lets one [fsetdec] close every row.      *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_block :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ =>
              dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
              /\ ftvar_in_aenv Ξ [<=] dom Ξ)
           (fun S0 Θ α P P' S1 Ξ C _ =>
              dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
              /\ ftvar_in_aenv Ξ [<=] dom Ξ));
    intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    look_grow_facts;
    repeat (rewrite dom_app in * || rewrite ftvar_in_aenv_app in * );
    simpl in *;
    repeat split;
    try solve [ fsetdec ];
    try solve [ solve_uniq ];
    (* the two ARROW rows: the blocks are disjoint because the right one is
       fresh for a supply that already contains the left one *)
    try solve [ apply uniq_app_4;
                [ assumption | assumption | unfold disjoint; fsetdec ] ].
Qed.

Corollary e_looksub_generated_in_supply : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> dom Ξ [<=] S1.
Proof. intros * H. apply (proj1 e_looksub_lookeq_block) in H. tauto. Qed.

Corollary e_lookeq_generated_in_supply : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> dom Ξ [<=] S1.
Proof. intros * H. apply (proj2 e_looksub_lookeq_block) in H. tauto. Qed.

(** The freshness fact in the ∀γ shape a consumer reads it in. *)
Corollary e_looksub_generated_fresh : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  forall γ, γ `in` dom Ξ -> γ `notin` S0.
Proof.
  intros * H γ Hγ. apply (proj1 e_looksub_lookeq_block) in H.
  destruct H as [_ [Hd _]]. clear - Hd Hγ. fsetdec.
Qed.

Corollary e_lookeq_generated_fresh : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  forall γ, γ `in` dom Ξ -> γ `notin` S0.
Proof.
  intros * H γ Hγ. apply (proj2 e_looksub_lookeq_block) in H.
  destruct H as [_ [Hd _]]. clear - Hd Hγ. fsetdec.
Qed.

(** ⭐ THE BLOCK IS DUPLICATE-FREE — the fact the collection cannot supply
    unthreaded, and half of what [a_sub__forall_l]'s prose-completed premise
    [uniq (Ξ ++ Θ0)] asks for (§4). *)
Corollary e_looksub_uniq : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> uniq Ξ.
Proof. intros * H. apply (proj1 e_looksub_lookeq_block) in H. tauto. Qed.

Corollary e_lookeq_uniq : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> uniq Ξ.
Proof. intros * H. apply (proj2 e_looksub_lookeq_block) in H. tauto. Qed.

Corollary e_looksub_block_ftvar : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros * H. apply (proj1 e_looksub_lookeq_block) in H. tauto. Qed.

Corollary e_lookeq_block_ftvar : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros * H. apply (proj2 e_looksub_lookeq_block) in H. tauto. Qed.

(** Bound every opened skeleton in sight.  The [lazymatch] guard is keyed on
    the POSED fact's own shape, which is what makes the [repeat] terminate. *)
#[local] Ltac open_upper_facts :=
  repeat match goal with
  | H : context [ ftvar_in_pskl (open_pskl_wrt_pskl ?X (pskl_var_f ?b)) ] |- _ =>
      lazymatch goal with
      | _ : ftvar_in_pskl (open_pskl_wrt_pskl X (pskl_var_f b)) [<=] _ |- _ =>
          fail
      | _ => pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X (pskl_var_f b))
      end
  end.

(** ⭐ WHAT THE COLLECTED CONSTRAINTS CAN MENTION.  Needed because [a_extract]
    feeds [C] to the SOLVING layer at a LATER supply, so the pipeline's bridge
    has to bound it — and unlike the block [Ξ], that is not a statement about
    [dom].

    ⚙ Stated with the subjects on the right rather than as [[<=] S1], which
    would need the input-coverage hypothesis and so could not live in this
    hypothesis-free section.  At the use site coverage turns it into the
    simpler form in one [fsetdec] step. *)
Lemma e_looksub_lookeq_cstr_ftvar :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P').
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ =>
              ftvar_in_a_cstrs C [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P')
           (fun S0 Θ α P P' S1 Ξ C _ =>
              ftvar_in_a_cstrs C [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P'));
    intros; look_grow_facts; open_upper_facts;
    repeat rewrite ftvar_in_a_cstrs_app in *;
    simpl in *; fsetdec.
Qed.

Corollary e_looksub_cstr_ftvar : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
  ftvar_in_a_cstrs C [<=] S1.
Proof.
  intros * H Hcov. pose proof (e_looksub_supply_grows H) as Hgrow.
  apply (proj1 e_looksub_lookeq_cstr_ftvar) in H. clear - H Hcov Hgrow. fsetdec.
Qed.

(* ===================================================================== *)
(*  §3  The bridge                                                        *)
(*                                                                        *)
(*  As at M1 and M2: inputs fixed POINTWISE, and the outputs [Ξ] and [C]  *)
(*  carried across unchanged.  The supply must cover the SUBJECT'S        *)
(*  VARIABLE [α] as well as the context and both skeletons — LE-FlexR's   *)
(*  side condition names it, and it is not reachable from the rest.       *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_sound :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
     {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
     {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a).
Proof.
  apply (e_looksub_lookeq_mutind
    (fun S0 Θ α m P P' S1 Ξ C _ =>
       add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
       {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a)
    (fun S0 Θ α P P' S1 Ξ C _ =>
       add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
       {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a)).

  - (* LS-Var *) intros. apply a_looksub__var.
  - (* LS-Absent *) intros. apply a_looksub__absent; assumption.
  - (* LS-Vacuous *) intros. apply a_looksub__vacuous.
  - (* LS-Check *)
    intros S0 S1 Θ α A B Ξ C Hgf Hne Hg1 Hg2 Hl IH Hcov.
    apply a_looksub__check; auto.
  - (* LS-ForallR — the witness enters BOTH the supply and the context *)
    intros S0 S1 Θ α A B Ξ C β Hgf Hβ Hl IH Hcov.
    apply a_looksub__forall_r with (β := β).
    + assumption.
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β)) as Hup.
      simpl in Hup, Hcov |- *.
      clear - Hup Hcov. fsetdec.
  - (* LS-Arrow — the right half runs at [S1], so coverage travels by §1 *)
    intros S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He IH1 Hs IH2 Hcov.
    simpl in Hcov.
    pose proof (e_lookeq_supply_grows He) as Hgrow.
    apply a_looksub__arrow.
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2. clear - Hcov Hgrow. fsetdec.
  - (* LS-ForallL *)
    intros S0 S1 Θ α m P P' Ξ C β Hβ Hl IH Hcov.
    apply a_looksub__forall_l with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
      simpl in Hup, Hcov |- *.
      clear - Hup Hcov. fsetdec.
  - (* LS-UnivGhostL *)
    intros S0 S1 Θ α m P P' Ξ C Hl IH Hcov.
    apply a_looksub__univ_ghost_l. apply IH. simpl in Hcov.
    clear - Hcov. fsetdec.

  - (* LE-Var *) intros. apply a_lookeq__var.
  - (* LE-Absent *) intros. apply a_lookeq__absent; assumption.
  - (* LE-Vacuous *) intros. apply a_lookeq__vacuous.
  - (* LE-FlexR — ⭐ the generating row: [α1 ∉ S] covers all four names the
       paper's side condition lists, [β] included (it is [P']'s only ftv) *)
    intros S Θ α P β α1 Hα1 Hne Hin Hcov.
    apply a_lookeq__flex_r; auto.
    simpl in Hcov. clear - Hα1 Hcov. fsetdec.
  - (* LE-Arrow *)
    intros S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He1 IH1 He2 IH2 Hcov.
    simpl in Hcov.
    pose proof (e_lookeq_supply_grows He1) as Hgrow.
    apply a_lookeq__arrow.
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2. clear - Hcov Hgrow. fsetdec.
  - (* LE-ForallInh *)
    intros S0 S1 Θ α P P' Ξ C β Hβ He IH Hcov.
    apply a_lookeq__forall_inh with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β)) as H2.
      simpl in H1, H2, Hcov |- *.
      clear - H1 H2 Hcov. fsetdec.
  - (* LE-ForallSyn *)
    intros S0 S1 Θ α P P' Ξ C β Hβ He IH Hcov.
    apply a_lookeq__forall_syn with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *.
      clear - H1 Hcov. fsetdec.
  - (* LE-UnivGhost *)
    intros S0 S1 Θ α P P' Ξ C He IH Hcov.
    apply a_lookeq__univ_ghost. apply IH. simpl in Hcov. clear - Hcov. fsetdec.
  - (* LE-UnivGhost1 *)
    intros S0 S1 Θ α P P' Ξ C β Hβ He IH Hcov.
    apply a_lookeq__univ_ghost1 with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β)) as H2.
      simpl in H2, Hcov |- *.
      clear - H2 Hcov. fsetdec.
  - (* LE-UnivGhost2 *)
    intros S0 S1 Θ α P P' Ξ C Hg He IH Hcov.
    apply a_lookeq__univ_ghost2; [ assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
  - (* LE-UnivGhostR *)
    intros S0 S1 Θ α P P' Ξ C Hne Hg He IH Hcov.
    apply a_lookeq__univ_ghost_r; [ assumption | assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
Qed.

Corollary e_looksub_sound : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a.
Proof. intros. eapply (proj1 e_looksub_lookeq_sound); eassumption. Qed.

Corollary e_lookeq_sound : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a.
Proof. intros. eapply (proj2 e_looksub_lookeq_sound); eassumption. Qed.

(* ===================================================================== *)
(*  §4  ⭐ THE PAYOFF — [a_sub__forall_l]'s [uniq (Ξ ++ Θ0)] is DERIVABLE  *)
(*                                                                        *)
(*  frost/algo/def_rules.v:1253-1256 states it as a prose-completion — the *)
(*  paper's `fresh` Ξ, needed there because (in that comment's words)      *)
(*  [a_lookeq]'s LE-FlexR and [a_guess_mono]'s hole rule pick arbitrary    *)
(*  names, so re-attaching Ξ needs the freshness stated.                   *)
(*  Threaded, both halves are theorems: §2 gives [uniq Ξ] and              *)
(*  the block's disjointness from anything the supply already covers.      *)
(*  This is M1's [AT-Abs] payoff at the second of the two sites the        *)
(*  comment names.                                                        *)
(* ===================================================================== *)

Corollary e_looksub_uniq_app : forall S0 Θ α m P P' S1 Ξ C Θ0,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  ftvar_in_aenv Θ0 [<=] S0 ->
  uniq Θ0 ->
  uniq (Ξ ++ Θ0).
Proof.
  intros * Hl Hcov Hu.
  apply uniq_app_4; [ eapply e_looksub_uniq; eassumption | assumption | ].
  unfold disjoint. intros y Hy.
  assert (Hy1 : y `in` dom Ξ) by (clear - Hy; fsetdec).
  assert (Hy2 : y `in` dom Θ0) by (clear - Hy; fsetdec).
  pose proof (e_looksub_generated_fresh Hl Hy1) as Hout.
  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdom.
  assert (Hin : y `in` S0) by (clear - Hy2 Hdom Hcov; fsetdec).
  contradiction.
Qed.
