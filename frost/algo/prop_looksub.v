(** BASICS for the constraint-collection layer
    ([a_looksub]/[a_lookeq]/[a_extract]) — docs/DESIGN-subtyping.md P2.

    The declaration-shape facts every re-attachment of a look output [Ξ] to
    a context needs: look only ever generates FLEXIBLE declarations (the
    single generative rule is LE-FlexR), and [a_extract] appends [guess]'s
    declarations ([a_guess_mono_decls]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_consis_sound.

Set Implicit Arguments.

Scheme a_looksub_mutind := Induction for a_looksub Sort Prop
  with a_lookeq_mutind := Induction for a_lookeq Sort Prop.

Combined Scheme a_looksub_lookeq_mutind
  from a_looksub_mutind, a_lookeq_mutind.

(* ===================================================================== *)
(*  §1  Look outputs are declaration-only contexts                        *)
(* ===================================================================== *)

Lemma a_looksub_lookeq_decls :
  (forall α m P P' Ξ 𝒞, P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ) /\
  (forall α P P' Ξ 𝒞, P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ 𝒞 _ => a_decls Ξ)
           (fun α P P' Ξ 𝒞 _ => a_decls Ξ));
    intros; try solve [ assumption ]; try solve [ apply a_decls__nil ];
    try solve [ apply a_decls_app; assumption ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ].
  (* LE-FlexR : the single generative rule *)
  econstructor; apply a_decls__nil.
Qed.

Lemma a_looksub_decls : forall α m P P' Ξ 𝒞,
  P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_decls); eauto. Qed.

Lemma a_lookeq_decls : forall α P P' Ξ 𝒞,
  P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_decls); eauto. Qed.

(** [guess] generates only declarations ([SK]: none; [TY]: the fresh mono
    flexibles of [a_guess_mono]). *)
Lemma a_guess_decls : forall NM P Ξ P',
  a_guess NM P Ξ P' -> a_decls Ξ.
Proof.
  intros NM P Ξ P' H; destruct H;
    [ apply a_decls__nil | eapply a_guess_mono_decls; eauto ].
Qed.

Lemma a_extract_decls : forall NM α m P P' Ξ P0,
  P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ P0 -> a_decls Ξ.
Proof.
  intros NM α m P P' Ξ P0 H; destruct H.
  apply a_decls_app;
    [ eapply a_looksub_decls; eauto | eapply a_guess_decls; eauto ].
Qed.

(* ===================================================================== *)
(*  §2  Free variables of the collected constraints                       *)
(*                                                                        *)
(*  Every variable in a collected constraint comes from the RHS being     *)
(*  compared against, or is one of the freshly-generated flexibles in Ξ   *)
(*  (LE-FlexR).  Needed for freshness bookkeeping when re-attaching Ξ.     *)
(* ===================================================================== *)

Definition ftvar_in_cstr (c : a_cstr) : atoms :=
  match c with
  | a_cstr_sub _ P => ftvar_in_pskl P
  | a_cstr_eq P     => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_cstrs (C : a_cstrs) : atoms :=
  match C with
  | nil     => empty
  | c :: C' => ftvar_in_cstr c `union` ftvar_in_cstrs C'
  end.

Lemma ftvar_in_cstrs_app : forall C1 C2,
  ftvar_in_cstrs (C1 ++ C2) [=] ftvar_in_cstrs C1 `union` ftvar_in_cstrs C2.
Proof. induction C1; intros; simpl; [ fsetdec | rewrite IHC1; fsetdec ]. Qed.

Lemma a_looksub_lookeq_ftv :
  (forall α m P P' Ξ 𝒞, P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     ftvar_in_cstrs 𝒞 [<=] ftvar_in_pskl P' `union` dom Ξ) /\
  (forall α P P' Ξ 𝒞, P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     ftvar_in_cstrs 𝒞 [<=] ftvar_in_pskl P' `union` dom Ξ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ 𝒞 _ =>
              ftvar_in_cstrs 𝒞 [<=] ftvar_in_pskl P' `union` dom Ξ)
           (fun α P P' Ξ 𝒞 _ =>
              ftvar_in_cstrs 𝒞 [<=] ftvar_in_pskl P' `union` dom Ξ));
    intros;
    try rewrite ftvar_in_cstrs_app; try rewrite dom_app;
    simpl in *;
    try solve [ fsetdec ].
  all: (* cofinite cases: fresh β (fresh for 𝒞 too), IH + open ftv upper *)
    match goal with
    | IH : forall a, a `notin` ?L -> _ |- ftvar_in_cstrs ?𝒞 [<=] _ =>
        pick fresh β for (L `union` ftvar_in_cstrs 𝒞);
        specialize (IH β ltac:(auto))
    end;
    try match goal with
    | H : _ [<=] ftvar_in_pskl (open_pskl_wrt_pskl ?B _) `union` _ |- _ =>
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β))
    end;
    simpl in *; fsetdec.
Qed.

Lemma a_looksub_ftv : forall α m P P' Ξ 𝒞,
  P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  ftvar_in_cstrs 𝒞 [<=] ftvar_in_pskl P' `union` dom Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_ftv); eauto. Qed.

(* ===================================================================== *)
(*  §3  Look freshness (lemma:look-output-fresh, subtyping-proofs:522)    *)
(*                                                                        *)
(*  The extract output's free variables come from the input skeleton      *)
(*  [P0] and the collected/guessed flexibles [Ξ] only — in particular     *)
(*  the looked-for variable α (or any variable fresh for [P0] and [Ξ])    *)
(*  does not survive into the instantiation candidate.                    *)
(* ===================================================================== *)

Lemma a_solve_cstr_ftv : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' ->
  ftvar_in_pskl P' [<=] ftvar_in_pskl P `union` ftvar_in_cstrs 𝒞.
Proof.
  intros Θ 𝒞 P P' H; induction H; simpl.
  - fsetdec.
  - pose proof (a_solve_sub_ftv H). simpl. fsetdec.
  - pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ H). clear - H1 IHa_solve_cstr. fsetdec.
Qed.

Lemma ptyp_to_pskl_ftv : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [<=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

Lemma a_extract_output_fresh : forall NM α M P P0 Ξ P1 γ,
  P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 ->
  γ `notin` ftvar_in_pskl P0 ->
  γ `notin` dom Ξ ->
  γ `notin` ftvar_in_pskl P1.
Proof.
  intros * Hex Hγ0 HγΞ. inversion Hex; subst.
  simpl_env in HγΞ.
  match goal with
  | Hlk : _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ , Hsc : _ ⊩ _ ⨾ _ ⤳ _ |- _ =>
      pose proof (a_looksub_ftv Hlk) as Hb1;
      pose proof (a_solve_cstr_ftv Hsc) as Hb2
  end.
  match goal with
  | Hg : a_guess _ _ _ _ |- _ => inversion Hg; subst
  end.
  - (* SK : output = solve output *)
    simpl in Hb2. clear - Hb1 Hb2 Hγ0 HγΞ. fsetdec.
  - (* TY : output = guessed monotype *)
    match goal with
    | Hgm : a_guess_mono _ _ _ _ |- _ =>
        pose proof (a_guess_mono_ftv Hgm) as Hb3
    end.
    pose proof (ptyp_to_pskl_ftv A) as Hb4.
    simpl in Hb2. clear - Hb1 Hb2 Hb3 Hb4 Hγ0 HγΞ. fsetdec.
Qed.

(* ===================================================================== *)
(*  §4  Stability of constraint collection under substitution             *)
(*  (lemma:constraint-collection-stable-substitution, tex:504-520,        *)
(*  forward direction).  Substituting an α-free [Q] for β ≠ α preserves   *)
(*  the collected constraints; when the substitution destroys a           *)
(*  guardedness side condition the source has become α-free, so the       *)
(*  derivation switches to the Absent rule (the paper's remark).          *)
(* ===================================================================== *)

(** An α-free source collects nothing. *)
Lemma a_looksub_lookeq_absent_nil :
  (forall α m P P' Ξ 𝒞, P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil) /\
  (forall α P P' Ξ 𝒞, P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ 𝒞 _ =>
              α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil)
           (fun α P P' Ξ 𝒞 _ =>
              α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil));
    intros; simpl in *;
    try solve [ auto ];
    try solve [ exfalso; fsetdec ];
    try match goal with
        | IH1 : _ -> ?Ξ1 = nil /\ ?C1 = nil,
          IH2 : _ -> ?Ξ2 = nil /\ ?C2 = nil
          |- ?Ξ1 ++ ?Ξ2 = nil /\ ?C1 ++ ?C2 = nil =>
            destruct IH1 as [-> ->]; [ fsetdec | ];
            destruct IH2 as [-> ->]; [ fsetdec | ];
            auto
        end;
    try match goal with
        | Hn : ?a `notin` ftvar_in_pskl ?Px ,
          IH : forall β, β `notin` ?L -> _ |- _ =>
            pick fresh β for (L `union` singleton a);
            apply (IH β ltac:(auto));
            match goal with
            | |- _ `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?Pb _) =>
                pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                              Pb (pskl_var_f β));
                simpl in *; fsetdec
            end
        end;
    (* target-cofinite rules : the source is unchanged *)
    try match goal with
        | IH : forall β, β `notin` ?L -> _ |- _ =>
            pick fresh β for L;
            apply (IH β ltac:(auto)); assumption
        end.
Qed.

Lemma guarded_pskl_subst : forall P P' β,
  guarded_pskl P ->
  lc_pskl P' ->
  P <> pskl_var_f β ->
  guarded_pskl (subst_pskl_in_pskl P' β P).
Proof.
  intros P P' β Hg Hlc Hne; inversion Hg; subst; simpl.
  - constructor.
  - destruct_if; [ exfalso; congruence | constructor ].
  - constructor; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

Lemma a_looksub_lookeq_subst_stable :
  (forall α m P P' Ξ 𝒞, P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall α P P' Ξ 𝒞, P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ 𝒞 _ =>
              forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
              (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun α P P' Ξ 𝒞 _ =>
              forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
              (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞));
    intros; simpl.
  - (* LS-Var *)
    destruct_if; [ exfalso; congruence | apply a_looksub__var ].
  - (* LS-Absent *)
    apply a_looksub__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β).
    fsetdec.
  - (* LS-Vacuous *)
    apply a_looksub__vacuous.
  - (* LS-Check : switch to Absent when the source was the substituted var *)
    match goal with Hg : guarded_pskl A |- _ => inversion Hg; subst end;
      simpl.
    + (* unit *)
      apply a_looksub__check;
        [ intro Hc; discriminate Hc | constructor | assumption | auto ].
    + (* var X *)
      destruct_if as [-> | HneX].
      * (* X = β : the source became α-free — switch to Absent *)
        match goal with
        | Hl : _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
            destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ Hl)
              as [-> ->]; [ simpl; fsetdec | ]
        end.
        apply a_looksub__absent. assumption.
      * apply a_looksub__check;
          [ assumption | constructor | assumption | auto ].
    + (* arrow *)
      apply a_looksub__check;
        [ intro Hc; discriminate Hc
        | constructor; apply subst_pskl_in_pskl_lc_pskl; auto
        | assumption
        | match goal with
          | IH : forall (b : atom) (q : pskl), _ |- _ =>
              let HI := fresh "HI" in
              pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                            ltac:(eassumption)) as HI;
              simpl in HI; exact HI
          end ].
  - (* LS-ForallR *)
    apply a_looksub__forall_r with (L := L). intros γ Hγ. auto.
  - (* LS-Arrow *)
    apply a_looksub__arrow; auto.
  - (* LS-ForallL *)
    apply a_looksub__forall_l
      with (L := L `union` singleton β `union` ftvar_in_pskl P0).
    intros γ Hγ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hγ; fsetdec | assumption ].
    auto.
  - (* LS-UnivGhostL *)
    apply a_looksub__univ_ghost_l. auto.
  - (* LE-Var *)
    destruct_if; [ exfalso; congruence | apply a_lookeq__var ].
  - (* LE-Absent *)
    apply a_lookeq__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β).
    fsetdec.
  - (* LE-Vacuous *)
    apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    apply a_lookeq__flex_r.
    + intro Hc. destruct P; simpl in Hc; try discriminate Hc.
      revert Hc.
      destruct_if as [-> | HneX]; intro Hc.
      * (* X = β : then α ∈ ftv (var β) forces α = β, contradiction *)
        simpl in *. fsetdec.
      * inversion Hc; subst. congruence.
    + match goal with
      | |- _ `in` ftvar_in_pskl (subst_pskl_in_pskl ?Qx ?bx ?Px) =>
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Px Qx bx)
      end.
      fsetdec.
  - (* LE-Arrow *)
    apply a_lookeq__arrow; auto.
  - (* LE-ForallInh *)
    apply a_lookeq__forall_inh
      with (L := L `union` singleton β `union` ftvar_in_pskl P0).
    intros γ Hγ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hγ; fsetdec | assumption ].
    auto.
  - (* LE-ForallSyn *)
    apply a_lookeq__forall_syn
      with (L := L `union` singleton β `union` ftvar_in_pskl P0).
    intros γ Hγ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hγ; fsetdec | assumption ].
    auto.
  - (* LE-UnivGhost *)
    apply a_lookeq__univ_ghost. auto.
  - (* LE-UnivGhost1 *)
    apply a_lookeq__univ_ghost1 with (L := L). intros γ Hγ.
    match goal with
    | IH : forall b : atom, _ |- _ =>
        let HI := fresh "HI" in
        pose proof (IH γ Hγ _ _ ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption)) as HI;
        simpl in HI; exact HI
    end.
  - (* LE-UnivGhost2 *)
    apply a_lookeq__univ_ghost2; auto.
  - (* LE-UnivGhostR : switch to Absent when the source was β *)
    match goal with Hg : guarded_pskl P |- _ => inversion Hg; subst end;
      simpl.
    + (* unit *)
      apply a_lookeq__univ_ghost_r;
        [ intro Hc; discriminate Hc | constructor | auto ].
    + (* var X *)
      destruct_if as [-> | HneX].
      * (* X = β : the source became α-free — switch to Absent *)
        match goal with
        | Hl : _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
            destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ Hl)
              as [-> ->]; [ simpl; fsetdec | ]
        end.
        apply a_lookeq__absent. assumption.
      * apply a_lookeq__univ_ghost_r;
          [ assumption | constructor | auto ].
    + (* arrow *)
      apply a_lookeq__univ_ghost_r;
        [ intro Hc; discriminate Hc
        | constructor; apply subst_pskl_in_pskl_lc_pskl; auto
        | match goal with
          | IH : forall (b : atom) (q : pskl), _ |- _ =>
              let HI := fresh "HI" in
              pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                            ltac:(eassumption)) as HI;
              simpl in HI; exact HI
          end ].
Qed.

Lemma a_looksub_subst_stable : forall α m P P' Ξ 𝒞 β P0,
  P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
  (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof. intros; eapply (proj1 a_looksub_lookeq_subst_stable); eauto. Qed.

(* ===================================================================== *)
(*  §5  Renaming the looked-for variable                                  *)
(*                                                                        *)
(*  Collected constraints mention only input residuals, never the looked  *)
(*  variable itself, so the look run is stable under renaming it — the    *)
(*  Barendregt device that keeps the KEY decoration's substitution        *)
(*  variable clear of guessed flexible names.                             *)
(* ===================================================================== *)

Lemma ftv_subst_var_in : forall P α α',
  α `in` ftvar_in_pskl P ->
  α' `in` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P as [ | | γ | | | | ]; intros α α' Hin; simpl in *;
    try solve [ exfalso; fsetdec ].
  - destruct_if as [-> | Hne]; simpl; [ fsetdec | exfalso; fsetdec ].
  - destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P1)) as [Hi | Hni];
      [ pose proof (IHP1 _ α' Hi) | ];
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P2)) as [Hi2 | Hni2];
      try pose proof (IHP2 _ α' Hi2); try fsetdec.
  - eauto.
  - eauto.
Qed.

Lemma a_looksub_lookeq_rename_var :
  (forall α m P P' Ξ 𝒞, P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α', α' `notin` ftvar_in_pskl P ->
     (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall α P P' Ξ 𝒞, P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α', α' `notin` ftvar_in_pskl P ->
     (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ 𝒞 _ =>
              forall α', α' `notin` ftvar_in_pskl P ->
              (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun α P P' Ξ 𝒞 _ =>
              forall α', α' `notin` ftvar_in_pskl P ->
              (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞));
    intros; simpl.
  - (* LS-Var *)
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    apply a_looksub__var.
  - (* LS-Absent *)
    rewrite subst_pskl_in_pskl_fresh_eq; [ | assumption ].
    apply a_looksub__absent. assumption.
  - (* LS-Vacuous *)
    apply a_looksub__vacuous.
  - (* LS-Check *)
    apply a_looksub__check.
    + intro Hc. destruct A; simpl in Hc; try discriminate Hc.
      revert Hc.
      destruct_if as [-> | HneX]; intro Hc; [ congruence | ].
      inversion Hc; subst. simpl in *. fsetdec.
    + apply guarded_pskl_subst_var; assumption.
    + assumption.
    + auto.
  - (* LS-ForallR *)
    apply a_looksub__forall_r with (L := L). intros γ Hγ. auto.
  - (* LS-Arrow *)
    apply a_looksub__arrow;
      [ match goal with IH : forall a, a `notin` _ -> _ |- _ => idtac end | ];
      simpl in *;
      [ match goal with
        | IH : context [ _ ∼[ _ ] _ ⤳ _ ⨾ _ ] |- _ => apply IH; fsetdec
        end
      | match goal with
        | IH : context [ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ ] |- _ => apply IH; fsetdec
        end ].
  - (* LS-ForallL *)
    apply a_looksub__forall_l
      with (L := L `union` singleton α `union` singleton α').
    intros γ Hγ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hγ; fsetdec | constructor ].
    match goal with
    | IH : forall β, β `notin` _ -> _ |- _ =>
        apply IH; [ clear - Hγ; fsetdec | ]
    end.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ)).
    simpl in *. fsetdec.
  - (* LS-UnivGhostL *)
    apply a_looksub__univ_ghost_l. auto.
  - (* LE-Var *)
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    apply a_lookeq__var.
  - (* LE-Absent *)
    rewrite subst_pskl_in_pskl_fresh_eq; [ | assumption ].
    apply a_lookeq__absent. assumption.
  - (* LE-Vacuous *)
    apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    apply a_lookeq__flex_r.
    + intro Hc. destruct P; simpl in Hc; try discriminate Hc.
      match goal with
      | Hin : α `in` ftvar_in_pskl (pskl_var_f ?X) |- _ =>
          simpl in Hin;
          assert (HXα : X = α) by (clear - Hin; fsetdec);
          subst; congruence
      end.
    + apply ftv_subst_var_in. assumption.
  - (* LE-Arrow *)
    apply a_lookeq__arrow; simpl in *;
      match goal with
      | IH1 : context [ subst_pskl_in_pskl _ _ ?Pa ∼[ _ ] ?Qa ⤳ _ ⨾ _ ] ,
        IH2 : context [ subst_pskl_in_pskl _ _ ?Pb ∼[ _ ] ?Qb ⤳ _ ⨾ _ ] |- _ =>
          idtac
      end;
      [ match goal with
        | IH : forall a, a `notin` ftvar_in_pskl ?Px -> _ |-
            (subst_pskl_in_pskl _ _ ?Px) ∼[ _ ] _ ⤳ _ ⨾ _ =>
            apply IH; fsetdec
        end
      | match goal with
        | IH : forall a, a `notin` ftvar_in_pskl ?Px -> _ |-
            (subst_pskl_in_pskl _ _ ?Px) ∼[ _ ] _ ⤳ _ ⨾ _ =>
            apply IH; fsetdec
        end ].
  - (* LE-ForallInh *)
    apply a_lookeq__forall_inh
      with (L := L `union` singleton α `union` singleton α').
    intros γ Hγ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hγ; fsetdec | constructor ].
    match goal with
    | IH : forall β, β `notin` _ -> _ |- _ =>
        apply IH; [ clear - Hγ; fsetdec | ]
    end.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ)).
    simpl in *. fsetdec.
  - (* LE-ForallSyn *)
    apply a_lookeq__forall_syn
      with (L := L `union` singleton α `union` singleton α').
    intros γ Hγ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hγ; fsetdec | constructor ].
    match goal with
    | IH : forall β, β `notin` _ -> _ |- _ =>
        apply IH; [ clear - Hγ; fsetdec | ]
    end.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ)).
    simpl in *. fsetdec.
  - (* LE-UnivGhost *)
    apply a_lookeq__univ_ghost. simpl in *. auto.
  - (* LE-UnivGhost1 *)
    apply a_lookeq__univ_ghost1 with (L := L). intros γ Hγ.
    match goal with
    | IH : forall β, β `notin` _ -> forall a, _ |- _ =>
        specialize (IH γ Hγ α' ltac:(assumption)); simpl in IH; exact IH
    end.
  - (* LE-UnivGhost2 *)
    apply a_lookeq__univ_ghost2; [ assumption | ]. simpl in *. auto.
  - (* LE-UnivGhostR *)
    apply a_lookeq__univ_ghost_r.
    + intro Hc. destruct P; simpl in Hc; try discriminate Hc.
      revert Hc.
      destruct_if as [-> | HneX]; intro Hc; [ congruence | ].
      inversion Hc; subst. simpl in *. fsetdec.
    + apply guarded_pskl_subst_var; assumption.
    + auto.
Qed.

Lemma a_looksub_rename_var : forall α m P P' Ξ 𝒞 α',
  P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  α' `notin` ftvar_in_pskl P ->
  (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof. intros; eapply (proj1 a_looksub_lookeq_rename_var); eauto. Qed.
