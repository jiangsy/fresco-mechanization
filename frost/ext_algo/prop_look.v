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
Require Import src.frost.prop_tag.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_swap.
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
(*  §2c  ⭐⭐ WHAT THE ABSENCE-FIRST GUARD BUYS — an α-free subject pins    *)
(*  the WHOLE answer, SUPPLY INCLUDED                                     *)
(*                                                                        *)
(*  The a-side has half of this already ([a_looksub_subject_absent],      *)
(*  prop_look_equiv.v §2): at an α-free subject every derivation returns  *)
(*  [Ξ = ·] and [𝒞 = ·], because the only EMITTING rows need an           *)
(*  α-occurrence.  What it cannot say is anything about the supply — and  *)
(*  the supply is the whole content of the drift.                         *)
(*                                                                        *)
(*  ⛔ THE THIRD CONJUNCT IS FALSE WITHOUT THE GUARD, and that is the      *)
(*  point: [cex/probe_extract_supply_drift.v] is precisely a derivation   *)
(*  at an α-free subject with [S1 = add β S0].  Guarded, the five rows    *)
(*  that could spend cannot fire at such a subject, so the only rows left *)
(*  are no-ops and the supply comes back untouched — HYPOTHESIS-FREE.     *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_absent_pins :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     α `notin` ftvar_in_pskl P ->
     Ξ = nil /\ C = nil /\ S1 [=] S0) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     α `notin` ftvar_in_pskl P ->
     Ξ = nil /\ C = nil /\ S1 [=] S0).
Proof.
  (* ⚠️ NOT [repeat split]: [S1 [=] S0] unfolds to an [iff], which
     [repeat split] happily dives into.  Every split below is spelled out. *)
  apply (e_looksub_lookeq_mutind
    (fun S0 Θ α m P P' S1 Ξ C _ =>
       α `notin` ftvar_in_pskl P -> Ξ = nil /\ C = nil /\ S1 [=] S0)
    (fun S0 Θ α P P' S1 Ξ C _ =>
       α `notin` ftvar_in_pskl P -> Ξ = nil /\ C = nil /\ S1 [=] S0)).

  - (* LS-Var — the subject IS α *)
    intros S Θ α m P Habs. exfalso. simpl in Habs. clear - Habs. fsetdec.
  - (* LS-Absent *)
    intros S Θ α m P P' Hn Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  - (* LS-Vacuous *)
    intros S Θ α m P Hne Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  - (* LS-Check — same subject, one layer down *)
    intros S0 S1 Θ α A B Ξ C Hgf Hne Hg1 Hg2 He IH Habs. exact (IH Habs).
  - (* LS-ForallR — ⭐ GUARDED, so it cannot fire here *)
    intros S0 S1 Θ α A B Ξ C β Hgf Hβ Hocc Hnv He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  - (* LS-Arrow — both halves are α-free, and the supplies compose *)
    intros S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He IH1 Hs IH2 Habs.
    simpl in Habs.
    destruct (IH1 ltac:(clear - Habs; fsetdec)) as [-> [-> HS1]].
    destruct (IH2 ltac:(clear - Habs; fsetdec)) as [-> [-> HS2]].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    clear - HS1 HS2. fsetdec.
  - (* LS-ForallL — ⭐ GUARDED *)
    intros S0 S1 Θ α m P P' Ξ C β Hβ Hocc Hnh Hfr He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  - (* LS-UnivGhostL *)
    intros S0 S1 Θ α m P P' Ξ C Hnh Hfr He IH Habs.
    apply IH. simpl in Habs. exact Habs.

  - (* LE-Var — the subject IS α *)
    intros S Θ α P Habs. exfalso. simpl in Habs. clear - Habs. fsetdec.
  - (* LE-Absent *)
    intros S Θ α P P' Hn Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  - (* LE-Vacuous *)
    intros S Θ α P Hne Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  - (* LE-FlexR — the one row that already carried the guard *)
    intros S Θ α P β α1 Hα1 Hflx Hne Hin Habs.
    exfalso. clear - Hin Habs. fsetdec.
  - (* LE-Arrow *)
    intros S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He1 IH1 He2 IH2 Habs.
    simpl in Habs.
    destruct (IH1 ltac:(clear - Habs; fsetdec)) as [-> [-> HS1]].
    destruct (IH2 ltac:(clear - Habs; fsetdec)) as [-> [-> HS2]].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    clear - HS1 HS2. fsetdec.
  - (* LE-ForallInh — ⭐ GUARDED *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  - (* LE-ForallSyn — ⭐ GUARDED *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  - (* LE-UnivGhost *)
    intros S0 S1 Θ α P P' Ξ C He IH Habs.
    apply IH. simpl in Habs. exact Habs.
  - (* LE-UnivGhost1 — ⭐ GUARDED *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  - (* LE-UnivGhost2 *)
    intros S0 S1 Θ α P P' Ξ C Hg Hfx He IH Habs.
    apply IH. simpl in Habs. exact Habs.
  - (* LE-UnivGhostR — the subject is unchanged by the ⫯ on the RIGHT *)
    intros S0 S1 Θ α P P' Ξ C Hne Hg He IH Habs. exact (IH Habs).
Qed.

Corollary e_looksub_absent_pins : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil /\ S1 [=] S0.
Proof. intros. eapply (proj1 e_looksub_lookeq_absent_pins); eassumption. Qed.

Corollary e_lookeq_absent_pins : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil /\ S1 [=] S0.
Proof. intros. eapply (proj2 e_looksub_lookeq_absent_pins); eassumption. Qed.

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
  - (* LS-Vacuous *) intros. apply a_looksub__vacuous. assumption.
  - (* LS-Check *)
    intros S0 S1 Θ α A B Ξ C Hgf Hne Hg1 Hg2 Hl IH Hcov.
    apply a_looksub__check; auto.
  - (* LS-ForallR — the witness enters BOTH the supply and the context *)
    intros S0 S1 Θ α A B Ξ C β Hgf Hβ Hocc Hnv Hl IH Hcov.
    apply a_looksub__forall_r with (β := β).
    + assumption.
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + exact Hnv.
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
    intros S0 S1 Θ α m P P' Ξ C β Hβ Hocc Hnh Hfr Hl IH Hcov.
    apply a_looksub__forall_l with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + exact Hnh.
    + exact Hfr.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
      simpl in Hup, Hcov |- *.
      clear - Hup Hcov. fsetdec.
  - (* LS-UnivGhostL *)
    intros S0 S1 Θ α m P P' Ξ C Hnh Hfr Hl IH Hcov.
    apply a_looksub__univ_ghost_l; [ exact Hnh | exact Hfr | ].
    apply IH. simpl in Hcov.
    clear - Hcov. fsetdec.

  - (* LE-Var *) intros. apply a_lookeq__var.
  - (* LE-Absent *) intros. apply a_lookeq__absent; assumption.
  - (* LE-Vacuous *) intros. apply a_lookeq__vacuous. assumption.
  - (* LE-FlexR — ⭐ the generating row: [α1 ∉ S] covers all four names the
       paper's side condition lists, [β] included (it is [P']'s only ftv) *)
    intros S Θ α P β α1 Hα1 Hflx Hne Hin Hcov.
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
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Hcov.
    apply a_lookeq__forall_inh with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β)) as H2.
      simpl in H1, H2, Hcov |- *.
      clear - H1 H2 Hcov. fsetdec.
  - (* LE-ForallSyn *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Hcov.
    apply a_lookeq__forall_syn with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *.
      clear - H1 Hcov. fsetdec.
  - (* LE-UnivGhost *)
    intros S0 S1 Θ α P P' Ξ C He IH Hcov.
    apply a_lookeq__univ_ghost. apply IH. simpl in Hcov. clear - Hcov. fsetdec.
  - (* LE-UnivGhost1 *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Hcov.
    apply a_lookeq__univ_ghost1 with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β)) as H2.
      simpl in H2, Hcov |- *.
      clear - H2 Hcov. fsetdec.
  - (* LE-UnivGhost2 *)
    intros S0 S1 Θ α P P' Ξ C Hg Hfx He IH Hcov.
    apply a_lookeq__univ_ghost2; [ assumption | assumption | ].
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

(* ===================================================================== *)
(*  §5  SUPPLY RESPECT — the two supply indexes transport along [=]       *)
(*                                                                        *)
(*  ⚙ MOVED here 2026-08-17 from prop_look_pair.v §1b: prop_solve.v and    *)
(*  prop_extract.v need it for their own supply-respect statements, and    *)
(*  they are BELOW prop_look_pair.v in the [Require] graph.               *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_supply_respect :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e).
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ =>
              forall S0', S0' [=] S0 ->
              exists S1', S1' [=] S1 /\
                {{ S0' ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e)
           (fun S0 Θ α P P' S1 Ξ C _ =>
              forall S0', S0' [=] S0 ->
              exists S1', S1' [=] S1 /\
                {{ S0' ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e)).
  - (* LS-Var *)
    intros * Heq. eexists. split; [ exact Heq | ].
    apply e_looksub__var.
  - (* LS-Absent *)
    intros * Habs * Heq. eexists. split; [ exact Heq | ].
    apply e_looksub__absent. exact Habs.
  - (* LS-Vacuous *)
    intros * Hne * Heq. eexists. split; [ exact Heq | ].
    apply e_looksub__vacuous. exact Hne.
  - (* LS-Check *)
    intros * Hgf Hne HgA HgB Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__check; assumption.
  - (* LS-ForallR *)
    intros * Hgf Hβ Hocc Hnv Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__forall_r with (β := β);
      [ assumption | rewrite Heq; assumption | exact Hocc | exact Hnv
      | exact Hd' ].
  - (* LS-Arrow *)
    intros * Hd1 IH1 Hd2 IH2 S0' Heq.
    destruct (IH1 S0' Heq) as [S1' [Heq1 Hd1']].
    destruct (IH2 S1' Heq1) as [S2' [Heq2 Hd2']].
    exists S2'. split; [ exact Heq2 | ].
    eapply e_looksub__arrow; [ exact Hd1' | exact Hd2' ].
  - (* LS-ForallL *)
    intros * Hβ Hocc Hnh Hfr Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__forall_l with (β := β);
      [ rewrite Heq; assumption | exact Hocc | exact Hnh | exact Hfr
      | exact Hd' ].
  - (* LS-UnivGhostL *)
    intros * Hnh Hfr Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_looksub__univ_ghost_l; [ exact Hnh | exact Hfr | exact Hd' ].
  - (* LE-Var *)
    intros * Heq. eexists. split; [ exact Heq | ].
    apply e_lookeq__var.
  - (* LE-Absent *)
    intros * Habs * Heq. eexists. split; [ exact Heq | ].
    apply e_lookeq__absent. exact Habs.
  - (* LE-Vacuous *)
    intros * Hne * Heq. eexists. split; [ exact Heq | ].
    apply e_lookeq__vacuous. exact Hne.
  - (* LE-FlexR *)
    intros * Hα1 Hflx Hne Hocc S0' Heq.
    exists (add α1 S0'). split; [ rewrite Heq; reflexivity | ].
    apply e_lookeq__flex_r;
      [ rewrite Heq; assumption | assumption | assumption | assumption ].
  - (* LE-Arrow *)
    intros * Hd1 IH1 Hd2 IH2 S0' Heq.
    destruct (IH1 S0' Heq) as [S1' [Heq1 Hd1']].
    destruct (IH2 S1' Heq1) as [S2' [Heq2 Hd2']].
    exists S2'. split; [ exact Heq2 | ].
    eapply e_lookeq__arrow; [ exact Hd1' | exact Hd2' ].
  - (* LE-ForallInh *)
    intros * Hβ Hocc Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__forall_inh with (β := β);
      [ rewrite Heq; assumption | exact Hocc | exact Hd' ].
  - (* LE-ForallSyn *)
    intros * Hβ Hocc Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__forall_syn with (β := β);
      [ rewrite Heq; assumption | exact Hocc | exact Hd' ].
  - (* LE-UnivGhost *)
    intros * Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost. exact Hd'.
  - (* LE-UnivGhost1 *)
    intros * Hβ Hocc Hd IH S0' Heq.
    destruct (IH (add β S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost1 with (β := β);
      [ rewrite Heq; assumption | exact Hocc | exact Hd' ].
  - (* LE-UnivGhost2 *)
    intros * Hg Hfx Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost2; [ assumption | assumption | exact Hd' ].
  - (* LE-UnivGhostR *)
    intros * Hne Hg Hd IH S0' Heq.
    destruct (IH S0' Heq) as [S1' [Heq1 Hd']].
    exists S1'. split; [ exact Heq1 | ].
    apply e_lookeq__univ_ghost_r; [ assumption | assumption | exact Hd' ].
Qed.


(* ===================================================================== *)
(*  §6  EQUIVARIANCE                                                      *)
(*                                                                        *)
(*  algo/prop_swap.v §10's [a_looksub_lookeq_swap], rule for rule, in the  *)
(*  ∃-form the supply forces (prop_guess.v §8's reason: [swap_atoms] is    *)
(*  not a Leibniz homomorphism on the opaque [atoms], so the OUTPUT supply *)
(*  is fixed only up to [=]).  ⚙ The four LEAKING rows draw their opener   *)
(*  from the supply, so their freshness moves by [swap_notin_eq] and the   *)
(*  premise's supply by [eq_swap_atoms_add]; the two ARROW rows thread, so *)
(*  their ∃-witnesses chain.                                              *)
(*                                                                        *)
(*  Its consumer is §8c.11's level, through [e_extract_swap] and           *)
(*  [e_sub_sub_flex_swap]: a derivation opens a binder at ANY fresh atom   *)
(*  and the runner opens it at [supply_fresh], so the two agree only up to *)
(*  a transposition.                                                      *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_swap : forall a b,
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
          ≼[ (swap_atom a b α) , m ] (swap_pskl a b P')
          ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
          ∼[ (swap_atom a b α) ] (swap_pskl a b P')
          ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e).
Proof.
  intros a b.
  apply (e_looksub_lookeq_mutind
    (fun S0 Θ α m P P' S1 Ξ C _ =>
       forall S0', S0' [=] swap_atoms a b S0 ->
       exists S1', S1' [=] swap_atoms a b S1 /\
         {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
            ≼[ (swap_atom a b α) , m ] (swap_pskl a b P')
            ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e)
    (fun S0 Θ α P P' S1 Ξ C _ =>
       forall S0', S0' [=] swap_atoms a b S0 ->
       exists S1', S1' [=] swap_atoms a b S1 /\
         {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
            ∼[ (swap_atom a b α) ] (swap_pskl a b P')
            ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e)).

  (* ------------------------- e_looksub ------------------------- *)
  - (* LS-Var *)
    intros S Θ α m P S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_looksub__var ].
  - (* LS-Absent *)
    intros S Θ α m P P' Hni S0' Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_looksub__absent. auto using swap_pskl_ftv_notin.
  - (* LS-Vacuous *)
    intros S Θ α m P Hne S0' Heq. simpl.
    exists S0'. split;
      [ exact Heq | apply e_looksub__vacuous; apply swap_pskl_neq_var; exact Hne ].
  - (* LS-Check *)
    intros S0 S1 Θ α A B Ξ C Hgf Hne Hg1 Hg2 Hl IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_looksub__check;
      auto using swap_pskl_neq_var, guarded_pskl_swap, pskl_ghost_free_swap.
  - (* LS-ForallR — LEAKS *)
    intros S0 S1 Θ α A B Ξ C β Hgf Hβ Hocc Hnv Hl IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_looksub__forall_r with (β := swap_atom a b β);
      [ apply pskl_ghost_free_swap; exact Hgf
      | eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc
      | apply swap_pskl_neq_var; exact Hnv | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  - (* LS-Arrow — threaded, so the two ∃-witnesses chain *)
    intros S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He IH1 Hs IH2 S0' Heq.
    simpl.
    destruct (IH1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IH2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app, swap_cstrs_app.
    eapply e_looksub__arrow; eassumption.
  - (* LS-ForallL — LEAKS *)
    intros S0 S1 Θ α m P P' Ξ C β Hβ Hocc Hnh Hfr Hl IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_looksub__forall_l with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc
      | apply swap_pskl_neq_hole; exact Hnh
      | apply forall_r_off_swap; exact Hfr | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  - (* LS-UnivGhostL *)
    intros S0 S1 Θ α m P P' Ξ C Hnh Hfr Hl IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split;
      [ exact HS1
      | apply e_looksub__univ_ghost_l;
          [ apply swap_pskl_neq_hole; exact Hnh
          | apply forall_r_off_swap; exact Hfr | exact Hd ] ].

  (* ------------------------- e_lookeq -------------------------- *)
  - (* LE-Var *)
    intros S Θ α P S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_lookeq__var ].
  - (* LE-Absent *)
    intros S Θ α P P' Hni S0' Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_lookeq__absent. auto using swap_pskl_ftv_notin.
  - (* LE-Vacuous *)
    intros S Θ α P Hne S0' Heq. simpl.
    exists S0'. split;
      [ exact Heq | apply e_lookeq__vacuous; apply swap_pskl_neq_var; exact Hne ].
  - (* LE-FlexR — the cluster's ONE generating row *)
    intros S Θ α P β α1 Hα1 Hflx Hne Hin S0' Heq. simpl.
    exists (add (swap_atom a b α1) S0'). split;
      [ apply eq_swap_atoms_add; exact Heq | ].
    apply e_lookeq__flex_r;
      [ eapply swap_notin_eq; eassumption
      | auto using a_flex_tvar_swap
      | auto using swap_pskl_neq_var
      | auto using swap_pskl_ftv_in ].
  - (* LE-Arrow — threaded *)
    intros S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He1 IH1 He2 IH2 S0' Heq.
    simpl.
    destruct (IH1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IH2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app, swap_cstrs_app.
    eapply e_lookeq__arrow; eassumption.
  - (* LE-ForallInh — LEAKS *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__forall_inh with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc | ].
    rewrite !swap_pskl_open_var in Hd. exact Hd.
  - (* LE-ForallSyn — LEAKS *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__forall_syn with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  - (* LE-UnivGhost *)
    intros S0 S1 Θ α P P' Ξ C He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_lookeq__univ_ghost; exact Hd ].
  - (* LE-UnivGhost1 — LEAKS *)
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__univ_ghost1 with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  - (* LE-UnivGhost2 *)
    intros S0 S1 Θ α P P' Ξ C Hg Hfx He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__univ_ghost2;
      auto using guarded_pskl_swap, flex_r_off_swap.
  - (* LE-UnivGhostR *)
    intros S0 S1 Θ α P P' Ξ C Hne Hg He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__univ_ghost_r;
      auto using swap_pskl_neq_var, guarded_pskl_swap.
Qed.

Corollary e_looksub_swap : forall a b S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
       ≼[ (swap_atom a b α) , m ] (swap_pskl a b P')
       ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e.
Proof. intros a b. apply e_looksub_lookeq_swap. Qed.

Corollary e_lookeq_swap : forall a b S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
       ∼[ (swap_atom a b α) ] (swap_pskl a b P')
       ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e.
Proof. intros a b. apply e_looksub_lookeq_swap. Qed.
