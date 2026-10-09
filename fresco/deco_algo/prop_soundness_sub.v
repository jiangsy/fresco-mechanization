(** ⭐ THE PAPER'S thm:sound-subtyping — [a_sub_sound], assembled here (§17).

    §14 the KEY subtyping-decoration lemma, §15 decorating constraint solving,
    §16 MAIN (decorating an algorithmic subtyping run), §17 the assembled
    theorem: [a_sub_sound] = L-A ∘ L-B, where L-A is the decoration built in
    §14–§16 and L-B is [a_subtag_sound_bundle]
    (algo/sub/prop_soundness_subtag.v).

    ⚙ Second half of a pair with [prop_decorate_sub.v], which holds the
    bottom-up auxiliaries; the split is for BUILD TIME (the heavy earlier
    sections are not re-checked on every iteration), not for topic. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_mod_compat.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.prop_ctx_mono.   (* ad_pat_sub_of_fuel, _fuel_le *)
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_metasubst.
Require Import src.fresco.algo.prop_precise.
Require Import src.fresco.algo.consis.prop_soundness_consis.
(* cluster 4: [a_consis_decorate] moved to prop_consis_rename.v §10 *)
Require Import src.fresco.algo.consis.prop_consis_rename.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_pat_sub.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.algo.sub.prop_looksub.
Require Import src.fresco.algo.sub.prop_soundness_subtag.
Require Import src.fresco.deco_algo.prop_decorate_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §14  Subtyping decoration (lemma:subtyping-decoration, KEY,           *)
(*  subtyping-proofs.tex:541-959): a decorated subtyping run on           *)
(*  R[⌊ψa⌋/α] replays on R[ψa/α], additionally solving ψa's tags Ψa as    *)
(*  computed by the solvetag run on the constraints collected at α's      *)
(*  occurrences.  Induction on the decorated subtyping premise            *)
(*  (generalizing the look run): the paper's WLOG reorderings become      *)
(*  a_looksub_open_target (ForallR) and per-case inversions; the looked   *)
(*  variable is renamed on the fly (a_looksub_rename_var) to keep it      *)
(*  clear of guessed flexible names (Barendregt prose-completion).        *)
(* ===================================================================== *)

Lemma subst_uskl_in_uskl_decompose : forall ψ α α' R,
  α `notin` ftvar_in_uskl ψ ->
  α' `notin` ftvar_in_uskl R ->
  α' <> α ->
  subst_uskl_in_uskl ψ α' (subst_uskl_in_uskl (uskl_var_f α') α R)
  = subst_uskl_in_uskl ψ α R.
Proof.
  intros ψ α α' R Hαψ Hα'S Hne.
  rewrite subst_uskl_in_uskl_subst_uskl_in_uskl;
    [ | assumption | auto ].
  simpl.
  destruct_if as [_ | Hc];
      [ | exfalso; congruence ].
  rewrite (subst_uskl_in_uskl_fresh_eq R); [ reflexivity | assumption ].
Qed.

Lemma pskl_to_uskl_not_tag : forall P ε ψ,
  pskl_to_uskl P <> uskl_all_tag ε ψ.
Proof. destruct P; simpl; discriminate. Qed.

Lemma pskl_to_uskl_not_holeg : forall P,
  pskl_to_uskl P <> uskl_holeg.
Proof. destruct P; simpl; discriminate. Qed.

Lemma pskl_to_uskl_not_topholeg : forall P ψ,
  pskl_to_uskl P <> uskl_topholeg ψ.
Proof. destruct P; simpl; discriminate. Qed.

(** Rename-composition for the decorated substitution: substituting at a
    RE-FRESHENED variable composes back — [αv' ∉ ftv R0] and the value's
    [αv]-freshness make the detour invisible.  (The exists-fresh ForallR
    case below re-freshens its substitution variable away from the rule's
    Barendregt binder.) *)
Lemma subst_uskl_in_uskl_rename_compose : forall ψ αv αv' R0,
  αv `notin` ftvar_in_uskl ψ ->
  αv' `notin` ftvar_in_uskl R0 ->
  αv <> αv' ->
  subst_uskl_in_uskl ψ αv' (subst_uskl_in_uskl (uskl_var_f αv') αv R0)
  = subst_uskl_in_uskl ψ αv R0.
Proof.
  intros ψ αv αv' R0 Hψ HR Hne.
  rewrite subst_uskl_in_uskl_subst_uskl_in_uskl;
    [ | exact Hψ | exact Hne ].
  simpl. destruct_if; [ | congruence ].
  rewrite (subst_uskl_in_uskl_fresh_eq R0); [ reflexivity | exact HR ].
Qed.

Lemma a_subtag_decoration : forall NM M P0 Ψ Θ0 R' P Θ1,
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] R' ⩽ P ⊣ Θ1 }}da ->
  (* The look run carries its OWN context [Θl], universally quantified INSIDE
     the induction: the lemma only ever CONSUMES the run, so there is no
     alignment constraint with the subtag judgment's [Θ0], and the ForallL
     rows genuinely need a different one (their recursive call hands on a run
     that lives under the look rule's own binder).  Cluster 3. *)
  forall Θl R0 ψa Ψa αv Ξc 𝒞,
    R' = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ->
    {{ Θl ⊢ ⌊ R0 ⌋ˢ ≼[ αv , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a ->
    {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
    αv `notin` ftvar_in_uskl ψa ->
    αv `notin` ftvar_in_pskl P0 ->
    lc_uskl ψa ->
    lc_uskl R0 ->
    {{ ⊢ Θ0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ R' ⌋ˢ }}a ->
    (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
    {{ Θ0 ⊢[ NM | M | P0 | (Ψ `union` Ψa) ]
      (subst_uskl_in_uskl ψa αv R0) ⩽ P ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Ψ Θ0 R' P Θ1 Hsub.
  induction Hsub;
    intros Θl R0 ψa Ψa αv Ξc C HeqT HD Hst Hαψ HαP0 Hlcψ HlcS0 Hwf
      HwfP0 HwfT Hmod.
  - (* Infer : P0 = ◇ solves nothing; the run is erasure-determined *)
    assert (Hemp : Ψa [=] empty)
      by (eapply a_looksub_hole_solvetag_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite <- erase_swap_subst.
    apply a_subtag__infer; assumption.
  - (* Check : dispatch on the look run *)
    inversion HD; subst.
    + (* LS-Var : R0 = αv; the decoration-var lemma at ρ = nil *)
      match goal with
      | He : pskl_var_f αv = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in *.
      revert HwfT Hmod.
      destruct_if as [_ | Hc];
          [ | exfalso; congruence ].
      intros HwfT Hmod.
      inversion Hst; subst.
      change ψa with (msubst_uskl nil ψa).
      eapply a_subtag_decoration_var;
        [ eapply a_subtag__check; eassumption
        | reflexivity
        | eassumption
        | intros α1 g Hb; inversion Hb
        | exact Hlcψ
        | exact Hwf
        | apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    + (* LS-Absent : both substitutions are the identity *)
      assert (HαR : αv `notin` ftvar_in_uskl R0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). assumption. }
      rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR ].
      match goal with
      | Hg1 : guarded_uskl _, Hc : {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
          rewrite subst_uskl_in_uskl_fresh_eq in Hg1, Hc; try exact HαR
      end.
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ eapply a_subtag__check; eassumption
        | fsetdec_empty ].
    + (* LS-Vacuous : the Check target is guarded, not ◇ *)
      inv_guarded_hole.
    + (* LS-Check : decorate the consistency premise *)
      eapply a_subtag__check.
      * assumption.
      * apply guarded_subst_decorate; assumption.
      * assumption.
      * eapply a_consistag_decoration;
          [ eassumption | exact Hst | reflexivity | exact Hαψ
          | exact Hlcψ | exact HlcS0 | eassumption | exact Hwf
          | exact HwfP0 | exact HwfT
          | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ].
    + (* LS-ForallR : a guarded ∀ target is absurd *)
      match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
        inversion Hg end.
    + (* LS-ForallL : the source is ∀-headed, not guarded *)
      match goal with
      | He : pskl_all_syn _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
    + (* LS-UnivGhostL : the source is ∀◇-headed, not guarded *)
      match goal with
      | He : pskl_tophole _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
  - (* ForallR : transport the look run under the opened target.
       EXISTS-FRESH (2026-07-31): the substitution variable αv is first
       RE-FRESHENED to αv' away from the rule's Barendregt binder α (which
       is in scope here — this is exactly what the single-binder encoding
       requires of consumers): [a_looksub_rename_var] moves the look run to
       αv', [a_looksub_open_target_at] opens its ∀-target AT α, and the
       rename-composition collapses the detour in the conclusion. *)
    match goal with
    | Hn : ?a `notin` union (dom (_ ++ _)) _ |- _ => rename Hn into Hfr
    end.
    match goal with
    | Hn : a_suffix _ |- _ => rename Hn into Hsuf
    end.
    match goal with
    | Hn : uniq _ |- _ => rename Hn into Huq
    end.
    match goal with
    (* the IH now leads with the look run's own context [Θl] *)
    | Hn : forall _ : aenv, _ |- _ => rename Hn into IHprem
    end.
    rewrite dom_app in Hfr.
    (* the subject's ftv, read through the erasure *)
    assert (HeqE : ⌊ R ⌋ˢ = subst_pskl_in_pskl ⌊ ψa ⌋ˢ αv ⌊ R0 ⌋ˢ)
      by (rewrite HeqT; rewrite uskl_to_pskl_subst;
          rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    assert (HαR0 : forall γ, γ `notin` ftvar_in_uskl R -> γ <> αv ->
              γ `notin` ftvar_in_uskl R0).
    { intros γ Hγ Hγv Hc.
      apply Hγ. rewrite HeqT.
      pose proof (ftvar_in_uskl_subst_uskl_in_uskl_lower
                    R0 (pskl_to_uskl (uskl_to_pskl ψa)) αv) as Hlo.
      clear - Hlo Hγv Hc. fsetdec. }
    (* the re-freshened substitution variable *)
    destruct (atom_fresh (singleton α `union` singleton αv
                `union` ftvar_in_uskl R0 `union` ftvar_in_uskl ψa
                `union` ftvar_in_pskl B
                (* cluster 3: the var rename now carries an OUTPUT-freshness
                   premise — a binder that ESCAPED into [Ξc ⨾ 𝒞] cannot be
                   renamed onto, so the new looked-for variable must differ
                   from every name the run produced *)
                `union` dom Ξc `union` ftvar_in_a_cstrs C)) as [αv' Hαv'].
    assert (HeqT' : R = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                          αv' (subst_uskl_in_uskl (uskl_var_f αv') αv R0)).
    { rewrite subst_uskl_in_uskl_rename_compose;
        [ exact HeqT
        | pose proof Hαψ as Hαψ0;
          rewrite <- (ftvar_in_pskl_uskl_to_pskl ψa) in Hαψ0;
          rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl ⌊ ψa ⌋ˢ));
          rewrite uskl_to_pskl_pskl_to_uskl;
          exact Hαψ0
        | clear - Hαv'; fsetdec
        | intros ->; clear - Hαv'; fsetdec ]. }
    (* the look run, moved to αv' *)
    assert (HD1 : {{ Θl ⊢ ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                    ≼[ αv' , mode_tc ] (pskl_all_syn B) ⤳ Ξc ⨾ C }}a).
    { rewrite uskl_to_pskl_subst. simpl.
      apply a_looksub_rename_var;
        [ exact HD
        | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Hαv'; fsetdec
        | clear - Hαv'; fsetdec
        | clear - Hαv'; fsetdec ]. }
    (* …and opened at the rule's binder α *)
    assert (HαR0' : α `notin`
              ftvar_in_uskl (subst_uskl_in_uskl (uskl_var_f αv') αv R0)).
    { pose proof (ftvar_in_uskl_subst_uskl_in_uskl_upper
                    R0 (uskl_var_f αv') αv) as Hup.
      simpl in Hup.
      assert (HαRR : α `notin` ftvar_in_uskl R)
        by (clear - Hfr; fsetdec).
      assert (Hααv' : α <> αv') by (intros ->; clear - Hαv'; fsetdec).
      destruct (α == αv) as [-> | Hααv].
      - clear - Hup Hααv'. fsetdec.
      - intro Hc.
        assert (HinR0 : α `in` ftvar_in_uskl R0)
          by (clear - Hup Hc Hααv'; fsetdec).
        exact (HαR0 α HαRR Hααv HinR0). }
    assert (HαB : α `notin` ftvar_in_pskl (pskl_all_syn B))
      by (cbn; clear - Hfr; fsetdec).
    (* ⭐ THE RUN'S OWN CONTEXT IS IRRELEVANT HERE — the lemma only consumes
       the run — so shrink it, which makes the opener's [ftvar_in_aenv]
       condition vacuous.  ⚠️ UNDER THE FlexR-PRIORITY GUARD IT CANNOT BE
       SHRUNK TO [·] (2026-08-18): the eq layer reads its context for
       HATTEDNESS, and dropping every entry would turn a flexible counterpart
       rigid.  [flex_restrict] keeps exactly the flexibles the COUNTERPART
       mentions, with their payloads dropped — enough for the guard, whose
       condition is scoped to [ftv P'], and its [ftvar_in_aenv] still lands
       inside [ftv (∀B)], which is what the shrink was for. *)
    assert (Hmono0 : ftvar_in_aenv
                       (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                     [<=] ftvar_in_aenv Θl)
      by (apply flex_restrict_dom).
    pose proof (@a_looksub_ctx_ftv_mono _ _ _ _ _ _ _
                  (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                  HD1 Hmono0
                  (fun β Hβ => @flex_restrict_iff _ Θl β Hβ)) as HD1n.
    clear HD1 Hmono0; rename HD1n into HD1.
    (* α is the [a_subtag] rule's OWN Barendregt binder; nothing relates it to
       the run's generated names, so freshen the run away from it first
       (cluster 3: the same two-independent-generators gap as §8) *)
    assert (HαP : α `notin` ftvar_in_pskl
                    ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ).
    { pose proof (ftvar_in_pskl_uskl_to_pskl
                    (subst_uskl_in_uskl (uskl_var_f αv') αv R0)) as Hepq.
      clear - HαR0' Hepq; fsetdec. }
    assert (Hααv' : α <> αv') by (intros ->; clear - Hαv'; fsetdec).
    pose proof (flex_restrict_ftvar (ftvar_in_pskl (pskl_all_syn B)) Θl)
      as HΘlr.
    destruct (atom_fresh (singleton α `union` singleton αv'
                `union` ftvar_in_pskl
                    ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                `union` ftvar_in_pskl B `union` dom Ξc
                `union` ftvar_in_a_cstrs C)) as [δ Hδ].
    (* every side condition is ASSERTED and passed BY NAME: an [ltac:] inside a
       partially-applied lemma is elaborated while [β]/[δ] are still evars *)
    assert (Hδαv' : δ <> αv') by (intros ->; clear - Hδ; fsetdec).
    assert (Hδα : δ <> α) by (intros ->; clear - Hδ; fsetdec).
    assert (Hβin : α `notin` ftvar_in_aenv
                       (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                     `union` ftvar_in_pskl
                         ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                     `union` ftvar_in_pskl (pskl_all_syn B))
      by (cbn in HαB |- *; clear - HαP HαB HΘlr; fsetdec).
    assert (Hδin : δ `notin` ftvar_in_aenv
                       (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                     `union` ftvar_in_pskl
                         ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                     `union` ftvar_in_pskl (pskl_all_syn B)
                     `union` dom Ξc `union` ftvar_in_a_cstrs C)
      by (cbn in HΘlr |- *; clear - Hδ HΘlr; fsetdec).
    destruct (a_looksub_avoid_atom HD1 Hst Hααv' Hδαv' Hδα Hβin Hδin)
      as (Ξf & Cf & HDf & Hstf & Hαf).
    assert (Hopen : α `notin` ftvar_in_aenv
                        (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                      `union` ftvar_in_pskl
                          ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                      `union` ftvar_in_pskl B
                      `union` dom Ξf `union` ftvar_in_a_cstrs Cf)
      by (cbn in HαB, HΘlr |- *; clear - HαP HαB Hαf HΘlr; fsetdec).
    destruct (a_looksub_open_target_at ltac:(eassumption) HDf Hstf Hααv' Hopen)
      as [C' [HD2 Hst2]].
    (* the transported premise, via the IH at the re-freshened variable *)
    assert (Htrans :
        {{ ((α ~ abind_tvar) ++ Θ0)
          ⊢[ a_sub_mode_ty | mode_tc
            | (open_pskl_wrt_pskl B (pskl_var_f α)) | (Ψ `union` Ψa) ]
          (subst_uskl_in_uskl ψa αv'
             (subst_uskl_in_uskl (uskl_var_f αv') αv R0))
          ⩽ (open_pskl_wrt_pskl B (pskl_var_f α))
          ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}da).
    { eapply IHprem.
      { exact HeqT'. }
      { exact HD2. }
      { exact Hst2. }
      { clear - Hαv'; fsetdec. }
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      B (pskl_var_f α)) as Hup.
        simpl in Hup. clear - Hαv' Hup. fsetdec. }
      { exact Hlcψ. }
      { apply subst_uskl_in_uskl_lc_uskl;
          [ exact HlcS0 | constructor ]. }
      { apply a_wf_aenv__tvar; [ clear - Hfr; fsetdec | exact Hwf ]. }
      { eapply a_wf_pskl_all_syn_open_tvar;
          [ exact HwfP0 | clear - Hfr; fsetdec ]. }
      { eapply a_wf_pskl_weaken;
          [ intros x b Hb; unfold binds; simpl; right; exact Hb
          | exact HwfT ]. }
      { intros Hsk; discriminate Hsk. } }
    (* collapse the detour in the transported subject *)
    assert (Hcollapse : subst_uskl_in_uskl ψa αv'
                          (subst_uskl_in_uskl (uskl_var_f αv') αv R0)
                        = subst_uskl_in_uskl ψa αv R0).
    { apply subst_uskl_in_uskl_rename_compose;
        [ exact Hαψ
        | clear - Hαv'; fsetdec
        | intros ->; clear - Hαv'; fsetdec ]. }
    rewrite Hcollapse in Htrans.
    (* assemble the exists-fresh node at the same binder *)
    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ assumption | exact Hsuf | exact Huq | | exact Htrans ].
    rewrite dom_app.
    assert (Hfteq : ftvar_in_uskl (subst_uskl_in_uskl ψa αv R0)
                    [=] ftvar_in_uskl R).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl
                    (subst_uskl_in_uskl ψa αv R0)).
      rewrite <- (ftvar_in_pskl_uskl_to_pskl R).
      rewrite uskl_to_pskl_subst. rewrite HeqE. reflexivity. }
    clear - Hfr Hfteq. fsetdec.
  - (* UnivGhostR : P0 = ◇ solves nothing *)
    assert (Hemp : Ψa [=] empty)
      by (eapply a_looksub_hole_solvetag_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite <- erase_swap_subst.
    apply a_subtag__univ_ghost_r;
      [ | assumption ].
    apply guarded_subst_decorate; try assumption.
    rewrite <- HeqT. assumption.
  - (* Arrow : split the constraints; decorate left via consistency,
       right via the IH threaded across the mid context *)
    inversion HD; subst.
    + (* LS-Var : R0 = αv *)
      match goal with
      | He : pskl_var_f αv = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in HeqT |- *.
      revert HeqT HwfT.
      destruct_if as [_ | Hc];
          [ | exfalso; congruence ].
      intros HeqT HwfT.
      inversion Hst; subst.
      change ψa with (msubst_uskl nil ψa).
      eapply a_subtag_decoration_var;
        [ eapply a_subtag__arrow; eassumption
        | simpl; exact HeqT
        | eassumption
        | intros α1 g Hb; inversion Hb
        | exact Hlcψ
        | exact Hwf
        | rewrite HeqT;
          apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    + (* LS-Absent *)
      assert (HαR : αv `notin` ftvar_in_uskl R0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). assumption. }
      rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR ].
      rewrite subst_uskl_in_uskl_fresh_eq in HeqT; [ | exact HαR ].
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ first [ rewrite HeqT | idtac ]; eapply a_subtag__arrow; eassumption
        | fsetdec_empty ].
    + (* LS-Arrow : the structural pair *)
      match goal with
      | He : pskl_arrow _ _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in HeqT.
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HαP0.
      simpl in HwfT.
      apply a_wf_pskl_arrow_inv in HwfT as [HwfT1 HwfT2].
      apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b].
      destruct (a_solvetag_split _ _ Hst) as [Ψa1 [Ψa2 [Hst1 [Hst2 HΨs]]]].
      simpl.
      match goal with
      | Hc1 : {{ _ ⊢[ _ | _ | ?P0a | ?Ψ1 ] _ ∼ ?Q1 ⊣ ?Θm }}da,
        Hs2 : {{ ?Θm ⊢[ _ | _ | ?P0b | ?Ψ2 ] _ ⩽ ?Q2 ⊣ _ }}da,
        HΨc : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
          destruct (a_consistag_sound_aux Hc1 Hwf
                      ltac:(apply subst_uskl_in_uskl_lc_uskl;
                            [ assumption
                            | apply pskl_to_uskl_lc;
                              apply lc_uskl_to_pskl; assumption ])
                      HwfP0a HwfT1
                      (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
            as [Hle [HwfΘm _]];
          eapply a_subtag__arrow
            with (Ψ1 := Ψ1 `union` Ψa1) (Ψ2 := Ψ2 `union` Ψa2) (Θ1 := Θm);
          [ eapply a_consistag_decoration;
            [ eassumption | exact Hst1 | reflexivity | exact Hαψ
            | exact Hlcψ | assumption | exact Hc1 | exact Hwf
            | exact HwfP0a | exact HwfT1
            | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ]
          | match goal with
            (* the IH now leads with the look run's own context *)
        | IH : forall R1 : aenv, _ |- _ =>
                eapply IH;
                  [ reflexivity | eassumption | exact Hst2 | exact Hαψ
                  | clear - HαP0; fsetdec
                  | exact Hlcψ | assumption
                  | exact HwfΘm
                  | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
                  | eapply a_wf_pskl_isub; [ exact HwfT2 | exact Hle ]
                  | intros Hsk; specialize (Hmod Hsk); simpl in Hmod;
                    inversion Hmod; subst; assumption ]
            end
          | clear - HΨc HΨs; fsetdec ]
      end.
    + (* LS-ForallL : shape clash with the arrow subject *)
      match goal with
      | He : pskl_all_syn _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
    + (* LS-UnivGhostL : shape clash *)
      match goal with
      | He : pskl_tophole _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
  - (* ForallL (tagged) : the source is a tagged ∀; the looked variable is
       renamed away from the guessed names before the family rebuild *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip is never a tagged ∀ *)
      revert HeqT.
      destruct_if as [_ | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_tag; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* R0 = all_tag ε0 R0 *)
      match goal with
      | He : uskl_all_tag _ _ = uskl_all_tag ?e (subst_uskl_in_uskl _ _ ?Rb)
        |- _ => idtac
      end.
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_all_tag ε0 R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_all_tag ε0 R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        assert (Hnode : {{ Θ0 ⊢[ NM | M | P0 | Ψ ]
                          (uskl_all_tag ε0
                             (subst_uskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽ Q ⊣ Θ1 }}da)
          by (eapply a_subtag__forall_l_tagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        rewrite subst_uskl_in_uskl_fresh_eq in Hnode; [ | exact HαR' ].
        simpl. rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR' ].
        inversion Hst; subst.
        eapply a_subtag_psi_cong;
          [ exact Hnode
          | fsetdec_empty ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        assert (Hnode : {{ Θ0 ⊢[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_tag ε0
                             (subst_uskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽ Q ⊣ Θ1 }}da)
          by (eapply a_subtag__forall_l_tagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply subst_uskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl ⌊ _ ⌋ˢ |- _ => simpl in Hg; inversion Hg
        end.
      * (* LS-ForallR : a ∀ input contradicts guarded-or-hole *)
        match goal with
        | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
        end.
      * (* LS-ForallL : the structural crux *)
      (* EXISTS-FRESH (cluster 3).  LS-ForallL now fires at ONE binder [b], so
         the row can no longer pick a representative fresh for the node's
         guess [P1]: it must substitute [P1] for the binder it is GIVEN.  §8's
         [a_looksub_subst_gen] is what makes that legal without a Barendregt
         premise the caller cannot supply — it re-picks any binder that
         collides with [P1] and hands back RENAMED outputs, so [Ξc ⨾ C] are
         replaced by [Ξg ⨾ Cg] and the solvetag rides across with them. *)
      match goal with
      | Hp : {{ _ ⊢ (open_pskl_wrt_pskl _ _) ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
          rename Hp into Dbody
      end.
      match goal with
      | Hb : _ `notin` add αv _ |- _ => rename Hb into Hbfr
      end.
      assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
        by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ).
      assert (HlcP1 : lc_pskl P1)
        by (eapply a_wf_pskl_lc; eauto).
      match type of Dbody with
      | {{ ((?b ~ abind_tvar) ++ _) ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a =>
        destruct (atom_fresh (singleton αv `union` ftvar_in_uskl ψa
                    `union` ftvar_in_uskl R0
                    `union` ftvar_in_pskl ⌊ R0 ⌋ˢ
                    `union` ftvar_in_pskl P0
                    `union` ftvar_in_pskl P1
                    `union` singleton b `union` dom Ξc
                    `union` ftvar_in_a_cstrs C)) as [αt Hαt];
        assert (Hbne : b <> αt) by (intros ->; clear - Hαt; fsetdec);
        assert (Hαvb : αv <> b) by (intros ->; clear - Hbfr; fsetdec);
        assert (HbR0 : b `notin` ftvar_in_pskl ⌊ R0 ⌋ˢ)
          by (clear - Hbfr; fsetdec);
        (* (1) move the looked-for variable off the guess's names *)
        apply a_looksub_rename_var with (α' := αt) in Dbody;
          [ | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            ⌊ R0 ⌋ˢ (pskl_var_f b)) as Hup;
              simpl in Hup; clear - Hαt Hup; fsetdec
            | clear - Hαt; fsetdec
            | clear - Hαt; fsetdec ];
        rewrite <- subst_pskl_in_pskl_open_pskl_wrt_pskl_var in Dbody;
          [ | clear - Hαvb; congruence | constructor ];
        (* (2) substitute the node's guess for the binder we were GIVEN *)
        assert (HαtP1 : αt `notin` ftvar_in_pskl P1)
          by (clear - Hαt; fsetdec);
        destruct (a_looksub_subst_gen Dbody Hst Hbne HαtP1 HlcP1)
          as (Ξg & Cg & Dsub & Hstg);
        rewrite <- subst_pskl_in_pskl_intro in Dsub;
          [ | pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            ⌊ R0 ⌋ˢ (pskl_var_f αt) αv) as Hup2;
              simpl in Hup2; clear - Hbne HbR0 Hup2; fsetdec ]
      end.
      rename Dsub into Dβ0.
      (* freshness facts for the rebuilt family *)
      assert (Hαtψa : αt `notin` ftvar_in_uskl ψa)
        by (clear - Hαt; fsetdec).
      assert (HαvStrip : αv `notin` ftvar_in_uskl
                           (pskl_to_uskl (uskl_to_pskl ψa))).
      { intro Hin.
        pose proof (ftvar_in_pskl_uskl_to_pskl
                      (pskl_to_uskl (uskl_to_pskl ψa))) as Hf1.
        rewrite uskl_to_pskl_pskl_to_uskl in Hf1.
        pose proof (ftvar_in_pskl_uskl_to_pskl ψa) as Hf2.
        clear - Hin Hf1 Hf2 Hαψ. fsetdec. }
      destruct (atom_fresh L) as [α0 Hα0].
      assert (Hdecls : a_decls Ξ)
        by (eapply a_extract_decls; eauto).
      assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
      { apply a_wf_aenv_prepend_decls; auto.
        - match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu; solve_uniq end.
        - intros α1 Hα1.
          match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu Hα1; destruct_uniq;
            unfold disjoint in *; fsetdec end. }
      assert (Hmono : forall x (b : abind),
                 binds x b Θ0 -> binds x b (Ξ ++ Θ0))
        by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
      assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
        by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
      simpl.
      eapply a_subtag__forall_l_tagged
        (* [LD] is gone with the cofinite look family (cluster 3) *)
        with (L := L `union` singleton αv `union` singleton αt
                   `union` ftvar_in_pskl P1)
             (Ξ := Ξ) (P1 := P1);
        [ assumption | assumption | | assumption | assumption | ].
      { intros α1 Hα1.
        replace (⌊ open_uskl_wrt_uskl
                     (subst_uskl_in_uskl ψa αv R0) (uskl_var_f α1) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl
                    (subst_uskl_in_uskl
                       (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                    (uskl_var_f α1) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open;
              rewrite ! uskl_to_pskl_subst;
              rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        match goal with
        | Hex : forall a, a `notin` _ -> a_extract _ _ _ _ _ _ _ _ |- _ =>
            apply Hex; clear - Hα1; fsetdec
        end. }
        intros Ψg' ψg' Hfr Hsort Hera.
        assert (Hlcg : lc_uskl ψg')
          by (apply is_tskl_lc; inversion Hsort; assumption).
        assert (Hαtg : αt `notin` ftvar_in_uskl ψg').
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg'). rewrite Hera.
          clear - Hαt; fsetdec. }
        assert (Hsubject :
            subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αt
              (open_uskl_wrt_uskl
                 (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl
                (subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                ψg').
        { rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcstrip ].
          rewrite subst_uskl_in_uskl_decompose;
            [ | exact HαvStrip | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_uskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (Hresult :
            subst_uskl_in_uskl ψa αt
              (open_uskl_wrt_uskl
                 (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl (subst_uskl_in_uskl ψa αv R0) ψg').
        { rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcψ ].
          rewrite subst_uskl_in_uskl_decompose;
            [ | exact Hαψ | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_uskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        (* the run now lives under the look rule's OWN binder, and carries the
           outputs §8 handed back — read the context off the derivation, since
           the binder is the rule's and has no name of ours *)
        match type of Dβ0 with
        | {{ ?Θb ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a =>
            assert (HDg : {{ Θb ⊢
                ⌊ open_uskl_wrt_uskl
                    (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg' ⌋ˢ
                ≼[ αt , M ] P0 ⤳ Ξg ⨾ Cg }}a)
              by (rewrite uskl_to_pskl_open_gen;
                  rewrite uskl_to_pskl_subst; simpl;
                  rewrite Hera; exact Dβ0)
        end.
        assert (HlcSg : lc_uskl
            (open_uskl_wrt_uskl
               (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          match goal with
          | |- body_uskl_wrt_uskl _ =>
              eapply lc_body_uskl_all_tag_2
                with (ε1 := ε0);
              change (uskl_all_tag ε0
                        (subst_uskl_in_uskl (uskl_var_f αt) αv R0))
                with (subst_uskl_in_uskl (uskl_var_f αt) αv
                        (uskl_all_tag ε0 R0));
              apply subst_uskl_in_uskl_lc_uskl;
                [ exact HlcS0 | constructor ]
          end. }
        assert (HwfSg : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
            ⌊ open_uskl_wrt_uskl
                (subst_uskl_in_uskl
                   (pskl_to_uskl (uskl_to_pskl ψa)) αv R0) ψg' ⌋ˢ }}a).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ subst_uskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ subst_uskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall α, α `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros α Hα;
                  eapply a_wf_pskl_weaken;
                    [ exact (@binds_sub_cons _ _ _ Hmono) | apply Hbody; auto ]
                | assumption ]
          end. }
        rewrite <- Hresult.
        eapply a_subtag_psi_cong;
          [ match goal with
            | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
                eapply (IHfam Ψg' ψg' ltac:(clear - Hfr; solve_notin_auto) Hsort Hera
                          _
                          (open_uskl_wrt_uskl
                             (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
                          ψa Ψa αt Ξg Cg);
                [ rewrite Hsubject; reflexivity
                | exact HDg
                | exact Hstg
                | exact Hαtψa
                | clear - Hαt; fsetdec
                | exact Hlcψ
                | exact HlcSg
                | exact HwfΞΘ
                | exact HwfP0'
                | exact HwfSg
                | exact Hmod ]
            end
          | clear; fsetdec ].

  - (* ForallL (untagged) *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip itself is the ∀ source *)
      revert HeqT HwfT.
      destruct_if as [-> | Hc]; intros HeqT HwfT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : the decoration-var route *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ eapply a_subtag__forall_l_untagged
              with (L := L) (Ξ := Ξ) (P1 := P1); eassumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ eapply a_subtag__forall_l_untagged
              with (L := L) (Ξ := Ξ) (P1 := P1); eassumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
      * (* LS-Check : the source is the looked variable *)
        match goal with
        | Hne : pskl_var_f αv <> pskl_var_f αv |- _ => congruence
        end.
      * (* LS-ForallR : a ∀ input contradicts guarded-or-hole *)
        match goal with
        | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
        end.
    + (* R0 = all_syn R0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_all_syn R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_all_syn R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        assert (Hnode : {{ Θ0 ⊢[ NM | M | P0 | Ψ ]
                          (uskl_all_syn
                             (subst_uskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽ Q ⊣ Θ1 }}da)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        rewrite subst_uskl_in_uskl_fresh_eq in Hnode; [ | exact HαR' ].
        simpl. rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR' ].
        inversion Hst; subst.
        eapply a_subtag_psi_cong;
          [ exact Hnode
          | fsetdec_empty ].
      * (* LS-Vacuous *)
        assert (Hnode : {{ Θ0 ⊢[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_syn
                             (subst_uskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽ Q ⊣ Θ1 }}da)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply subst_uskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl ⌊ _ ⌋ˢ |- _ => simpl in Hg; inversion Hg
        end.
      * (* LS-ForallR : a ∀ input contradicts guarded-or-hole *)
        match goal with
        | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
        end.
      * (* LS-ForallL : the structural crux *)
      (* EXISTS-FRESH (cluster 3) — the untagged twin of the row above; see
         its comment.  [a_looksub_subst_gen] substitutes the node's guess for
         the ONE binder LS-ForallL gives us, re-picking anything that collides
         with [P1] and renaming the outputs. *)
      match goal with
      | Hp : {{ _ ⊢ (open_pskl_wrt_pskl _ _) ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
          rename Hp into Dbody
      end.
      match goal with
      | Hb : _ `notin` add αv _ |- _ => rename Hb into Hbfr
      end.
      assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
        by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ).
      assert (HlcP1 : lc_pskl P1)
        by (eapply a_wf_pskl_lc; eauto).
      match type of Dbody with
      | {{ ((?b ~ abind_tvar) ++ _) ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a =>
        destruct (atom_fresh (singleton αv `union` ftvar_in_uskl ψa
                    `union` ftvar_in_uskl R0
                    `union` ftvar_in_pskl ⌊ R0 ⌋ˢ
                    `union` ftvar_in_pskl P0
                    `union` ftvar_in_pskl P1
                    `union` singleton b `union` dom Ξc
                    `union` ftvar_in_a_cstrs C)) as [αt Hαt];
        assert (Hbne : b <> αt) by (intros ->; clear - Hαt; fsetdec);
        assert (Hαvb : αv <> b) by (intros ->; clear - Hbfr; fsetdec);
        assert (HbR0 : b `notin` ftvar_in_pskl ⌊ R0 ⌋ˢ)
          by (clear - Hbfr; fsetdec);
        apply a_looksub_rename_var with (α' := αt) in Dbody;
          [ | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                            ⌊ R0 ⌋ˢ (pskl_var_f b)) as Hup;
              simpl in Hup; clear - Hαt Hup; fsetdec
            | clear - Hαt; fsetdec
            | clear - Hαt; fsetdec ];
        rewrite <- subst_pskl_in_pskl_open_pskl_wrt_pskl_var in Dbody;
          [ | clear - Hαvb; congruence | constructor ];
        assert (HαtP1 : αt `notin` ftvar_in_pskl P1)
          by (clear - Hαt; fsetdec);
        destruct (a_looksub_subst_gen Dbody Hst Hbne HαtP1 HlcP1)
          as (Ξg & Cg & Dsub & Hstg);
        rewrite <- subst_pskl_in_pskl_intro in Dsub;
          [ | pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                            ⌊ R0 ⌋ˢ (pskl_var_f αt) αv) as Hup2;
              simpl in Hup2; clear - Hbne HbR0 Hup2; fsetdec ]
      end.
      rename Dsub into Dβ0.
      (* freshness facts for the rebuilt family *)
      assert (Hαtψa : αt `notin` ftvar_in_uskl ψa)
        by (clear - Hαt; fsetdec).
      assert (HαvStrip : αv `notin` ftvar_in_uskl
                           (pskl_to_uskl (uskl_to_pskl ψa))).
      { intro Hin.
        pose proof (ftvar_in_pskl_uskl_to_pskl
                      (pskl_to_uskl (uskl_to_pskl ψa))) as Hf1.
        rewrite uskl_to_pskl_pskl_to_uskl in Hf1.
        pose proof (ftvar_in_pskl_uskl_to_pskl ψa) as Hf2.
        clear - Hin Hf1 Hf2 Hαψ. fsetdec. }
      destruct (atom_fresh L) as [α0 Hα0].
      assert (Hdecls : a_decls Ξ)
        by (eapply a_extract_decls; eauto).
      assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
      { apply a_wf_aenv_prepend_decls; auto.
        - match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu; solve_uniq end.
        - intros α1 Hα1.
          match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu Hα1; destruct_uniq;
            unfold disjoint in *; fsetdec end. }
      assert (Hmono : forall x (b : abind),
                 binds x b Θ0 -> binds x b (Ξ ++ Θ0))
        by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
      assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
        by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
      simpl.
      eapply a_subtag__forall_l_untagged
        (* [LD] is gone with the cofinite look family (cluster 3) *)
        with (L := L `union` singleton αv `union` singleton αt
                   `union` ftvar_in_pskl P1)
             (Ξ := Ξ) (P1 := P1);
        [ assumption | assumption | | assumption | assumption | ].
      { intros α1 Hα1.
        replace (⌊ open_uskl_wrt_uskl
                     (subst_uskl_in_uskl ψa αv R0) (uskl_var_f α1) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl
                    (subst_uskl_in_uskl
                       (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                    (uskl_var_f α1) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open;
              rewrite ! uskl_to_pskl_subst;
              rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        match goal with
        | Hex : forall a, a `notin` _ -> a_extract _ _ _ _ _ _ _ _ |- _ =>
            apply Hex; clear - Hα1; fsetdec
        end. }
        intros Ψg' ψg' Hfr Hsort Hera.
        assert (Hlcg : lc_uskl ψg')
          by (apply is_tskl_lc; inversion Hsort; assumption).
        assert (Hαtg : αt `notin` ftvar_in_uskl ψg').
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg'). rewrite Hera.
          clear - Hαt; fsetdec. }
        assert (Hsubject :
            subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αt
              (open_uskl_wrt_uskl
                 (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl
                (subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                ψg').
        { rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcstrip ].
          rewrite subst_uskl_in_uskl_decompose;
            [ | exact HαvStrip | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_uskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (Hresult :
            subst_uskl_in_uskl ψa αt
              (open_uskl_wrt_uskl
                 (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl (subst_uskl_in_uskl ψa αv R0) ψg').
        { rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcψ ].
          rewrite subst_uskl_in_uskl_decompose;
            [ | exact Hαψ | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_uskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        match type of Dβ0 with
        | {{ ?Θb ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a =>
            assert (HDg : {{ Θb ⊢
                ⌊ open_uskl_wrt_uskl
                    (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg' ⌋ˢ
                ≼[ αt , M ] P0 ⤳ Ξg ⨾ Cg }}a)
              by (rewrite uskl_to_pskl_open_gen;
                  rewrite uskl_to_pskl_subst; simpl;
                  rewrite Hera; exact Dβ0)
        end.
        assert (HlcSg : lc_uskl
            (open_uskl_wrt_uskl
               (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          match goal with
          | |- body_uskl_wrt_uskl _ =>
              eapply lc_body_uskl_all_syn_1;
              change (uskl_all_syn
                        (subst_uskl_in_uskl (uskl_var_f αt) αv R0))
                with (subst_uskl_in_uskl (uskl_var_f αt) αv
                        (uskl_all_syn R0));
              apply subst_uskl_in_uskl_lc_uskl;
                [ exact HlcS0 | constructor ]
          end. }
        assert (HwfSg : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
            ⌊ open_uskl_wrt_uskl
                (subst_uskl_in_uskl
                   (pskl_to_uskl (uskl_to_pskl ψa)) αv R0) ψg' ⌋ˢ }}a).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ subst_uskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ subst_uskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall α, α `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros α Hα;
                  eapply a_wf_pskl_weaken;
                    [ exact (@binds_sub_cons _ _ _ Hmono) | apply Hbody; auto ]
                | assumption ]
          end. }
        rewrite <- Hresult.
        eapply a_subtag_psi_cong;
          [ match goal with
            | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
                eapply (IHfam Ψg' ψg' ltac:(clear - Hfr; solve_notin_auto) Hsort Hera
                          _
                          (open_uskl_wrt_uskl
                             (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
                          ψa Ψa αt Ξg Cg);
                [ rewrite Hsubject; reflexivity
                | exact HDg
                | exact Hstg
                | exact Hαtψa
                | clear - Hαt; fsetdec
                | exact Hlcψ
                | exact HlcSg
                | exact HwfΞΘ
                | exact HwfP0'
                | exact HwfSg
                | exact Hmod ]
            end
          | clear; fsetdec ].

  - (* Ghost : source ◇ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var *)
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : decoration-var at ρ = nil *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__ghost; assumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__ghost; assumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
      * (* LS-Check : the source is the looked variable *)
        match goal with
        | Hne : pskl_var_f αv <> pskl_var_f αv |- _ => congruence
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
    + (* R0 = ◇ : nothing to decorate *)
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ HD
                  ltac:(simpl; clear; solve_notin_auto)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghost; assumption
        | fsetdec_empty ].
  - (* GhostG : source ◈ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip is never dotted *)
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_holeg; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* R0 = ◈ : P0 = ◇ is pinned by the rule *)
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ HD
                  ltac:(simpl; clear; solve_notin_auto)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghostg; assumption
        | fsetdec_empty ].
  - (* UnivGhostL : source ∀◇.R̄ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var *)
      revert HeqT HwfT.
      destruct_if as [-> | Hc]; intros HeqT HwfT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : decoration-var at ρ = nil *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__univ_ghost_l; eassumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_l; eassumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
      * (* LS-Check : the source is the looked variable *)
        match goal with
        | Hne : pskl_var_f αv <> pskl_var_f αv |- _ => congruence
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
    + (* R0 = ∀◇.R0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_tophole R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_tophole R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        inversion Hst; subst.
        simpl. rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR' ].
        match goal with
        | Hs' : {{ _ ⊢[ _ | _ | _ | _ ]
                  (subst_uskl_in_uskl _ _ _) ⩽ _ ⊣ _ }}da |- _ =>
            rewrite subst_uskl_in_uskl_fresh_eq in Hs'; [ | exact HαR' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_l; eassumption
          | fsetdec_empty ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_l; eassumption
          | reflexivity
          | apply subst_uskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀◇-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
      * (* LS-UnivGhostL : the structural mirror *)
        simpl.
        apply a_subtag__univ_ghost_l; [ assumption | ].
        match goal with
        (* the IH now leads with the look run's own context *)
        | IH : forall R1 : aenv, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_tophole_inv in HwfT as [_ HwfT];
                exact HwfT
              | exact Hmod ]
        end.
  - (* UnivGhostLG : source ∀◈.R̄ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip is never dotted *)
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_topholeg; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* R0 = ∀◈.R0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_topholeg R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_topholeg R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        inversion Hst; subst.
        simpl. rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR' ].
        match goal with
        | Hs' : {{ _ ⊢[ _ | _ | _ | _ ]
                  (subst_uskl_in_uskl _ _ _) ⩽ _ ⊣ _ }}da |- _ =>
            rewrite subst_uskl_in_uskl_fresh_eq in Hs'; [ | exact HαR' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_lg; eassumption
          | fsetdec_empty ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_lg; eassumption
          | reflexivity
          | apply subst_uskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀◇-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
      * (* LS-UnivGhostL : the structural mirror *)
        simpl.
        apply a_subtag__univ_ghost_lg; [ assumption | ].
        match goal with
        (* the IH now leads with the look run's own context *)
        | IH : forall R1 : aenv, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_tophole_inv in HwfT as [_ HwfT];
                exact HwfT
              | exact Hmod ]
        end.
  - (* FlexMono : source α̂₀ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    revert HeqT.
    destruct_if as [-> | Hc]; intro HeqT.
    + (* eq : the strip is the flexible variable — decoration-var *)
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__flex_mono; eassumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__flex_mono; eassumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
    + (* neq : the subject is an untouched variable *)
      inversion HeqT; subst.
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ HD
                  ltac:(simpl; clear - Hc; solve_notin_auto)) as [-> ->].
      inversion Hst; subst.
      simpl.
      destruct_if as [Habs | _];
          [ exfalso; congruence | ].
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__flex_mono; eassumption
        | fsetdec_empty ].
Qed.

(* ===================================================================== *)
(*  §15  Decorating constraint solving                                    *)
(*  (lemma:decorate-constraint-solving, subtyping-proofs.tex:95-127)      *)
(*                                                                        *)
(*  a_extract_decorate is Qed, proved the PAPER's way: induction on the   *)
(*  constraint solving [solve C □ Ps], building [solvetag C ψa Ψa] by     *)
(*  the tag/ghost PROVENANCE relation [dec_ext] — every tagged quantifier *)
(*  of ψa comes from a quantifier of an intermediate skeleton (or is      *)
(*  ABSORBED against a ∀◇ by SE-GhostForall), every dotted ghost (SK)     *)
(*  from a ghost, and every DROPPED ∀◇ sits over a GUARDED erasure.       *)
(*  Coverage is SET MEMBERSHIP (Ψa = ⋃ per-constraint contributions, ⊆    *)
(*  squeezed against solvetag soundness), NOT a per-step growth identity  *)
(*  — so the idempotent re-collection of ∀-tags is harmless.  The only    *)
(*  side condition is the TY prose-wf "against a TYPE (ghost-free)",      *)
(*  which feeds [pskl_top_guarded] of the TY solve output (the guess-drop *)
(*  anchor); SK needs no condition at all.                                *)
(*                                                                        *)
(*  Reusable helpers below (kept from the walk): d_tags_skl congruence /  *)
(*  determinism / is_tskl, guarded+ghost-free skeleton-var rename, and    *)
(*  a_solvetag_sub_eq_rename_var (the ∀-case output uniformity).          *)
(* ===================================================================== *)

(** Determinism of the tag reading (up to set-equality). *)
Lemma d_tags_skl_det : forall Ψ1 Ψ' ψ,
  d_tags_skl Ψ1 ψ -> d_tags_skl Ψ' ψ -> Ψ1 [=] Ψ'.
Proof.
  intros Ψ1 Ψ' ψ H; revert Ψ'; induction H; intros Ψ' HB; inversion HB; subst.
  - (* unit *) fsetdec.
  - (* var *) fsetdec.
  - (* arrow : pin the second derivation's components via [Ψ'] union eqn *)
    match goal with
    | Hd1 : d_tags_skl ?Ψa R1, Hd2 : d_tags_skl ?Ψb R2,
      _ : Ψ' [=] union ?Ψa ?Ψb |- _ =>
        pose proof (IHd_tags_skl1 _ Hd1) as He1;
        pose proof (IHd_tags_skl2 _ Hd2) as He2
    end.
    fsetdec.
  - (* all_tag : match the IH by shape; pin the second body via [Ψ']=add ε _ *)
    match goal with
    | HIH : forall α, α `notin` ?La -> forall Ψx, d_tags_skl Ψx _ -> _ [=] Ψx,
      Hbody : forall α, α `notin` ?Lb -> d_tags_skl ?Ψb _,
      _ : Ψ' [=] add ε ?Ψb |- _ =>
        destruct (atom_fresh (La `union` Lb)) as [α Hα];
        pose proof (HIH α ltac:(clear - Hα; solve_notin_auto)
                      Ψb (Hbody α ltac:(clear - Hα; solve_notin_auto))) as He
    end.
    fsetdec.
  - (* holeg *) fsetdec.
  - (* topholeg *) apply IHd_tags_skl; assumption.
Qed.

(** Guardedness / ghost-freeness survive a skeleton-variable rename. *)
Lemma guarded_uskl_subst_var : forall ψ α β,
  guarded_uskl ψ -> guarded_uskl (subst_uskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H; inversion H; subst; simpl.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - apply guarded_uskl__arrow;
      apply subst_uskl_in_uskl_lc_uskl; auto; apply lc_uskl_var_f.
Qed.

Lemma uskl_ghost_free_subst_var : forall ψ α β,
  uskl_ghost_free ψ ->
  uskl_ghost_free (subst_uskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H; induction H; simpl.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - auto with fresco.
  - apply uskl_ghost_free__all_tag with (L := L `union` singleton α);
      intros α2 Hα2;
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
        [ apply H0; clear - Hα2; fsetdec
        | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
  - apply uskl_ghost_free__all_syn with (L := L `union` singleton α);
      intros α2 Hα2;
      rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
        [ apply H0; clear - Hα2; fsetdec
        | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
Qed.

(** [solvetag] is invariant under a simultaneous skeleton-variable rename of
    subject and target (the tags are ε-markers, untouched). *)
Lemma a_solvetag_sub_eq_rename_var :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da ->
     forall α β0, {{ (subst_uskl_in_uskl (uskl_var_f β0) α ψ) ≼[ M ]
                 (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da ->
     forall α β0, {{ (subst_uskl_in_uskl (uskl_var_f β0) α ψ) ∼
                 (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da).
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M P Ψ _ => forall α β0,
              {{ (subst_uskl_in_uskl (uskl_var_f β0) α ψ) ≼[ M ]
              (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da)
           (fun ψ P Ψ _ => forall α β0,
              {{ (subst_uskl_in_uskl (uskl_var_f β0) α ψ) ∼
              (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da));
    intros; simpl.
  - (* SSub-Var *)
    destruct_if;
      apply a_solvetag_sub__var; assumption.
  - (* SSub-ForallL *)
    apply a_solvetag_sub__forall_l with (L := L `union` singleton α); intros β Hβ.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end.
  - (* SSub-UnivGhostLG *)
    apply a_solvetag_sub__univ_ghost_lg; auto.
  - (* SSub-Vacuous *)
    apply a_solvetag_sub__vacuous; assumption.
  - (* SSub-Check *)
    apply a_solvetag_sub__check;
      [ apply pskl_ghost_free_subst_var; assumption
      | apply guarded_uskl_subst_var; assumption
      | apply guarded_pskl_subst_var; assumption | auto ].
  - (* SSub-ForallR *)
    apply a_solvetag_sub__forall_r with (L := L `union` singleton α);
      [ apply pskl_ghost_free_subst_var; assumption | ]; intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ].
    match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end.
  - (* SSub-Arrow *)
    eapply a_solvetag_sub__arrow; [ auto | auto | eassumption ].
  - (* SEq-Unit *)
    apply a_solvetag_eq__unit; assumption.
  - (* SEq-Var *)
    destruct_if;
      apply a_solvetag_eq__var; assumption.
  - (* SEq-Vacuous *)
    apply a_solvetag_eq__vacuous; assumption.
  - (* SEq-Arrow *)
    eapply a_solvetag_eq__arrow; [ auto | auto | eassumption ].
  - (* SEq-ForallInh *)
    eapply a_solvetag_eq__forall_inh with (L := L `union` singleton α);
      [ intros β Hβ;
        rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ];
        rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
          [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ];
        match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end
      | eassumption ].
  - (* SEq-UnivGhostG *)
    apply a_solvetag_eq__univ_ghostg; auto.
  - (* SEq-ForallSyn *)
    apply a_solvetag_eq__forall_syn with (L := L `union` singleton α); intros β Hβ.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall b, _ |- _ =>
      specialize (IH β ltac:(clear - Hβ; solve_notin_auto) α β0); simpl in IH; exact IH end.
  - (* SEq-UnivGhostR *)
    apply a_solvetag_eq__univ_ghost_r;
      [ rewrite uskl_to_pskl_subst; simpl;
        apply guarded_pskl_subst_var; assumption
      | auto ].
  - (* SEq-FlexR : the target var may itself be renamed *)
    destruct_if;
      apply a_solvetag_eq__flex_r;
      first [ apply uskl_ghost_free_subst_var; assumption | assumption ].
Qed.

(** Renaming the TARGET alone.  The solvetag judgments never inspect a target
    VARIABLE — only the target's SHAPE (unit / arrow / ∀ / ∀◇ / guarded), and
    the one rule with a variable target (SEq-FlexR) accepts any variable — so
    a rename touching the target only is admissible.

    Needed since the freshness campaign (DESIGN.md §4.3): SolS-ForallR hands
    its consumer ITS OWN binder, and that binder LEAKS into the output, hence
    may occur free in the output's decoration ψ.  The two-sided
    [a_solvetag_sub_eq_rename_var] would move it inside ψ as well, so it
    cannot manufacture SSub-ForallR's cofinite family from the one instance
    the rule provides; this one can. *)

(** A tag reading witnesses that its subject is a decorated skeleton. *)
Lemma d_tags_skl_is_tskl : forall Ψ ψ, d_tags_skl Ψ ψ -> is_tskl ψ.
Proof.
  intros Ψ ψ H; induction H; eauto with fresco.
Qed.

(** SOUNDNESS (paper coverage, direction ⊆): a decorated solvetag collects
    only tags that ψ actually carries.  Mutual over [≼[ M ]] / [∼] in [}}da]. *)
Lemma a_solvetag_sub_eq_sound :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da ->
     forall Ψtot, d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da ->
     forall Ψtot, d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot).
Proof.
  apply a_solvetag_sub_eq_mutind.
  - (* SSub-Var *) intros α M P Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SSub-ForallL : subject all_tag ε ψ *)
    intros L ε ψ M P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψ0 _,
      Heq : Ψtot [=] add ?e ?Ψ0 |- _ =>
        destruct (atom_fresh (L `union` L1)) as [β Hβ];
        pose proof (IH β ltac:(clear - Hβ; solve_notin_auto) Ψ0
                      (Hb β ltac:(clear - Hβ; solve_notin_auto))) as Hs;
        clear - Hs Heq; fsetdec
    end.
  - (* SSub-UnivGhostLG : subject topholeg ψ *)
    intros ψ M P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with Hd : d_tags_skl ?T ψ |- _ => exact (IH T Hd) end.
  - (* SSub-Vacuous *) intros ψ M Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SSub-Check *) intros ψ B Ψ Hgf Hgψ HgB Hprem IH Ψtot Hdt; exact (IH Ψtot Hdt).
  - (* SSub-ForallR *) intros L ψ B Ψ Hgf Hprem IH Ψtot Hdt;
      destruct (atom_fresh L) as [β Hβ]; exact (IH β ltac:(clear - Hβ; solve_notin_auto) Ψtot Hdt).
  - (* SSub-Arrow : subject arrow ψ1 ψ2 *)
    intros ψ1 ψ2 M Q1 Q2 Ψ Ψ1 Ψ2 Hp1 IH1 Hp2 IH2 He Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Ha : d_tags_skl ?T1 ψ1, Hbb : d_tags_skl ?T2 ψ2 |- _ =>
        pose proof (IH1 T1 Ha); pose proof (IH2 T2 Hbb)
    end.
    match goal with Heq : Ψtot [=] _ |- _ => clear - He Heq H H0; fsetdec end.
  - (* SEq-Unit *) intros Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SEq-Var *) intros α P Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SEq-Vacuous *) intros ψ Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SEq-Arrow *) intros ψ1 ψ2 Q1 Q2 Ψ Ψ1 Ψ2 Hp1 IH1 Hp2 IH2 He Ψtot Hdt;
      inversion Hdt; subst.
    match goal with
    | Ha : d_tags_skl ?T1 ψ1, Hbb : d_tags_skl ?T2 ψ2 |- _ =>
        pose proof (IH1 T1 Ha); pose proof (IH2 T2 Hbb)
    end.
    match goal with Heq : Ψtot [=] _ |- _ => clear - He Heq H H0; fsetdec end.
  - (* SEq-ForallInh : subject all_tag ε ψ, Ψ = add ε Ψ0 *)
    intros L ε ψ P Ψ Ψ0 Hprem IH He Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heq : Ψtot [=] add ?e ?Ψt0 |- _ =>
        destruct (atom_fresh (L `union` L1)) as [β Hβ];
        pose proof (IH β ltac:(clear - Hβ; solve_notin_auto) Ψt0
                      (Hb β ltac:(clear - Hβ; solve_notin_auto))) as Hs;
        clear - Hs Heq He; fsetdec
    end.
  - (* SEq-UnivGhostG : subject topholeg ψ *)
    intros ψ P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with Hd : d_tags_skl ?T ψ |- _ => exact (IH T Hd) end.
  - (* SEq-ForallSyn : subject all_tag ε ψ *)
    intros L ε ψ P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heq : Ψtot [=] add ?e ?Ψt0 |- _ =>
        destruct (atom_fresh (L `union` L1)) as [β Hβ];
        pose proof (IH β ltac:(clear - Hβ; solve_notin_auto) Ψt0
                      (Hb β ltac:(clear - Hβ; solve_notin_auto))) as Hs;
        clear - Hs Heq; fsetdec
    end.
  - (* SEq-UnivGhostR : subject ψ, target ∀◇P *)
    intros ψ P Ψ Hg Hprem IH Ψtot Hdt; exact (IH Ψtot Hdt).
  - (* SEq-FlexR *) intros ψ α Ψ Hgf He Ψtot Hdt; clear - He; fsetdec.
Qed.

(** The list-level solvetag collects only ψ's tags (per-constraint ⊆ + union). *)
Lemma a_solvetag_sound : forall 𝒞 ψ Ψ Ψtot,
  {{ 𝒞 ⊩ ψ ⤳ Ψ }}da -> d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot.
Proof.
  intros 𝒞 ψ Ψ Ψtot Hc; revert Ψtot; induction Hc; intros Ψtot Hdt.
  - (* empty *) fsetdec_empty.
  - (* sub *) match goal with H : {{ _ ≼[ _ ] _ ⤳ _ }}da |- _ =>
      pose proof ((proj1 a_solvetag_sub_eq_sound) _ _ _ _ H Ψtot Hdt) end; fsetdec.
  - (* eq *)
    match goal with
    | Hs : {{ _ ∼ _ ⤳ ?Ψ1 }}da, He : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
        pose proof ((proj2 a_solvetag_sub_eq_sound) _ _ _ Hs Ψtot Hdt) as Hae;
        pose proof (IHHc Ψtot Hdt) as Hai;
        clear - He Hae Hai; fsetdec
    end.
Qed.

(* --------------------------------------------------------------------- *)
(*  PAPER COVERAGE (subtyping-proofs.tex:110-127): [dec_ext P ψ Ψ] is the
    ψ↔skeleton relation making the paper's "provenance observation"
    explicit — ψ (the decoration of the guess output) EXTENDS the
    intermediate solve skeleton P; Ψ = ψ's tags at positions the skeleton
    does not yet account for.  Coverage is SET-MEMBERSHIP (⊆), NOT a
    per-step growth identity, so the idempotent re-collection of ∀-tags
    is harmless.  The ∀◇ constructors are FAITHFUL (no side conditions on
    the against-skeleton P0 anywhere — the paper's lemma has none):
      · topholeg     — SK: the ∀◇ survives to the output, ψ dotted;
      · skip_tophole — the ∀◇ is dropped LATER (by a guarded-target solve
        step, or by the TY guess); in both droppings the subject erasure
        is GUARDED, which is exactly what SEq-UnivGhostR needs;
      · absorb_all   — a ∀ of ψ CREATED against the ∀◇ by SE-GhostForall
        (the skeleton stays ∀◇P0 under the binder, mirroring
        SEq-ForallSyn); its tag ε stays REMAINING (the skeleton has no
        matching quantifier), and SEq-ForallSyn indeed does not collect it. *)
(* --------------------------------------------------------------------- *)

Inductive dec_ext : pskl -> uskl -> atoms -> Prop :=
| dec_ext__hole : forall ψ Ψ,               (* P = ◇ : every tag of ψ remains *)
    is_tskl ψ ->
    d_tags_skl Ψ ψ ->
    dec_ext pskl_hole ψ Ψ
| dec_ext__unit : forall Ψ,
    Ψ [=] empty ->
    dec_ext pskl_unit uskl_unit Ψ
| dec_ext__var : forall α Ψ,
    Ψ [=] empty ->
    dec_ext (pskl_var_f α) (uskl_var_f α) Ψ
| dec_ext__arrow : forall P1 P2 ψ1 ψ2 Ψ Ψ1 Ψ2,
    dec_ext P1 ψ1 Ψ1 ->
    dec_ext P2 ψ2 Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    dec_ext (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) Ψ
| dec_ext__all : forall L P0 ψ0 ε Ψ,         (* P's ∀ ; ε accounted, not remaining *)
    (forall α, α `notin` L ->
       dec_ext (open_pskl_wrt_pskl P0 (pskl_var_f α))
               (open_uskl_wrt_uskl ψ0 (uskl_var_f α)) Ψ) ->
    dec_ext (pskl_all_syn P0) (uskl_all_tag ε ψ0) Ψ
| dec_ext__skip_tophole : forall P0 ψ Ψ,     (* P's ∀◇ dropped later; ψ guarded *)
    guarded_pskl ⌊ ψ ⌋ˢ ->
    dec_ext P0 ψ Ψ ->
    dec_ext (pskl_tophole P0) ψ Ψ
| dec_ext__topholeg : forall P0 ψ0 Ψ,        (* SK keeps ∀◇ ; ψ = ∀◈.ψ0 *)
    dec_ext P0 ψ0 Ψ ->
    dec_ext (pskl_tophole P0) (uskl_topholeg ψ0) Ψ
| dec_ext__absorb_all : forall L P0 ψ0 ε Ψ Ψ0,  (* ψ's ∀ created against the ∀◇
                                                   (SE-GhostForall); ε REMAINS *)
    (forall α, α `notin` L ->
       dec_ext (pskl_tophole P0)
               (open_uskl_wrt_uskl ψ0 (uskl_var_f α)) Ψ0) ->
    Ψ [=] add ε Ψ0 ->
    dec_ext (pskl_tophole P0) (uskl_all_tag ε ψ0) Ψ
| dec_ext__flex_forget : forall P α Ψ,       (* P resolved to flex α̂ (untagged) *)
    Ψ [=] empty ->
    dec_ext P (uskl_var_f α) Ψ.

#[export] Hint Constructors dec_ext : fresco.

(** SK anchor / self-extension: a decorated skeleton extends its own erasure
    with no remaining tags. *)
Lemma dec_ext_erase_refl : forall ψ,
  is_tskl ψ ->
  dec_ext (uskl_to_pskl ψ) ψ empty.
Proof.
  intros ψ H; induction H; simpl.
  - apply dec_ext__unit; fsetdec.
  - apply dec_ext__var; fsetdec.
  - eapply dec_ext__arrow; [ exact IHis_tskl1 | exact IHis_tskl2 | fsetdec ].
  - apply dec_ext__all with (L := L). intros α Hα.
    rewrite <- uskl_to_pskl_open.
    match goal with
    | IH : forall α, α `notin` L -> dec_ext _ _ empty |- _ =>
        exact (IH α ltac:(clear - Hα; solve_notin_auto))
    end.
  - apply dec_ext__hole; [ apply is_tskl__holeg | apply d_tags_skl__holeg; fsetdec ].
  - auto with fresco.
Qed.

(** A guarded skeleton is locally closed. *)
(** Head-shape predicate: the skeleton's head is unit/var/arrow (the shapes
    [guarded_pskl] admits, without its lc payload; bound vars included so the
    predicate is stable under opening). *)
Definition pskl_guarded_head (P : pskl) : Prop :=
  match P with
  | pskl_unit | pskl_var_f _ | pskl_var_b _ | pskl_arrow _ _ => True
  | _ => False
  end.

Lemma lc_head_guarded : forall P,
  lc_pskl P -> pskl_guarded_head P -> guarded_pskl P.
Proof.
  intros P Hlc Hh; destruct P; simpl in Hh; try contradiction.
  - auto with fresco.
  - inversion Hlc.
  - auto with fresco.
  - inversion Hlc; subst; auto with fresco.
Qed.

Lemma guarded_pskl_head : forall P, guarded_pskl P -> pskl_guarded_head P.
Proof. intros P H; inversion H; subst; simpl; exact I. Qed.

(** The TY guess preserves guarded heads (◇ ↦ var, ∀◇ stripped, ∀ kept —
    but a guarded-headed input has no ∀ head). *)
Lemma a_guess_mono_head : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> pskl_guarded_head P ->
  pskl_guarded_head (ptyp_to_pskl A).
Proof.
  intros Θ P Ξ A Hg Hh; inversion Hg; subst; simpl in Hh;
    try contradiction; simpl; exact I.
Qed.

(** [pskl_top_guarded P]: every universal ghost ∀◇ in P heads a guarded-headed
    body.  TY-mode solve outputs satisfy this (the eq-phase against ghost-free
    targets keeps the skeleton ∀◇-free; the terminal sub step only creates ∀◇
    over guarded bodies, SS-GhostL / SS-GhostLF) — it is what lets the TY
    guess-drop anchor use the GUARDED [skip_tophole]. *)
Fixpoint pskl_top_guarded (P : pskl) : Prop :=
  match P with
  | pskl_tophole P0 => pskl_guarded_head P0 /\ pskl_top_guarded P0
  | pskl_arrow P1 P2 => pskl_top_guarded P1 /\ pskl_top_guarded P2
  | pskl_all_syn P0 => pskl_top_guarded P0
  | _ => True
  end.

Lemma pskl_guarded_head_open_rec : forall P α' k,
  pskl_guarded_head P <-> pskl_guarded_head (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof.
  intros P α' k; destruct P; simpl; try tauto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto.
Qed.

(* CLOSE-stability of the same predicates — the solve ∀ rules re-bind their
   output now (DESIGN.md §4.3), so the consumers see [close β P'] where they
   used to see an opened body. *)
Lemma pskl_guarded_head_close_rec : forall P β k,
  pskl_guarded_head P -> pskl_guarded_head (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  - destruct (lt_ge_dec n k); simpl; auto.
  - destruct (β == α); simpl; auto.
Qed.

Lemma pskl_top_guarded_open_rec : forall P α' k,
  pskl_top_guarded P <-> pskl_top_guarded (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof.
  induction P; intros α' k; simpl; try tauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto.
  - rewrite (IHP1 α' k), (IHP2 α' k); tauto.
  - rewrite (IHP α' (S k)); tauto.
  - rewrite (IHP α' k), (pskl_guarded_head_open_rec P α' k); tauto.
Qed.

Lemma pskl_top_guarded_close_rec : forall P β k,
  pskl_top_guarded P -> pskl_top_guarded (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  - destruct (lt_ge_dec n k); simpl; auto.
  - destruct (β == α); simpl; auto.
  - destruct H; split; auto.
  - destruct H as [Hh Ht]; split;
      [ apply pskl_guarded_head_close_rec; exact Hh | auto ].
Qed.

Lemma pskl_top_guarded_close : forall P β,
  pskl_top_guarded P -> pskl_top_guarded (close_pskl_wrt_pskl β P).
Proof.
  intros P β H; unfold close_pskl_wrt_pskl;
    apply pskl_top_guarded_close_rec; exact H.
Qed.

(** WELL-FORMEDNESS ⟹ [pskl_top_guarded]: [a_wf_pskl__tophole] admits a ∀◇
    ONLY over a [guarded_pskl] body, so every ∀◇ in a wf skeleton heads a
    guarded body.  This is the paper's implicit source-skeleton discipline —
    it supplies exactly what the coverage needs (no [ghost_free]/[no_top]
    hypothesis: a ∀◇ in [P0] is fine, it just wraps a guarded type). *)
Lemma a_wf_pskl_top_guarded : forall Θ Δ P,
  a_wf_pskl Θ Δ P -> pskl_top_guarded P.
Proof.
  intros Θ Δ P H; induction H; simpl; try exact I.
  - (* arrow *) auto.
  - (* all : strip the fresh opener via the open_rec congruence *)
    destruct (atom_fresh L) as [α Hα].
    apply (proj2 (pskl_top_guarded_open_rec P α 0)).
    match goal with IH : forall α, α `notin` L -> pskl_top_guarded _ |- _ =>
      exact (IH α Hα) end.
  - (* tophole : guarded body ⟹ guarded_head + IH *)
    auto using guarded_pskl_head.
Qed.

(** ghost-free (no ghosts at all) ⟹ top-guarded (no ∀◇ to check). *)
Lemma pskl_ghost_free_top_guarded : forall P, pskl_ghost_free P -> pskl_top_guarded P.
Proof. induction P; simpl; intuition. Qed.

(** [pskl_top_guarded] survives monotype substitution (a mono has no ∀/∀◇, so
    it keeps guarded heads and creates no new ∀◇) — for the Flex-Assign case. *)
Lemma pskl_guarded_head_ptyp_mono : forall τ,
  mono_ptyp τ -> pskl_guarded_head (ptyp_to_pskl τ).
Proof. intros τ Hm; induction Hm; simpl; exact I. Qed.

Lemma pskl_guarded_head_subst_mono : forall P τ β,
  pskl_guarded_head P -> mono_ptyp τ ->
  pskl_guarded_head (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros P τ β Hg Hm; destruct P; simpl in Hg |- *; try contradiction; try exact I.
  destruct_if; auto using pskl_guarded_head_ptyp_mono.
Qed.

Lemma pskl_top_guarded_subst_mono : forall P τ β,
  pskl_top_guarded P -> mono_ptyp τ ->
  pskl_top_guarded (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  induction P; intros τ β Hg Hm; simpl in Hg |- *; try exact I.
  - (* var_f : β↦τ or itself, both top_guarded *)
    destruct_if; auto using pskl_ghost_free_top_guarded, ptyp_to_pskl_ghost_free.
  - (* arrow *) destruct Hg as [Hg1 Hg2]; auto using IHP1, IHP2.
  - (* all *) auto using IHP.
  - (* tophole *) destruct Hg as [Hgh Ht];
      auto using pskl_guarded_head_subst_mono, IHP.
Qed.

(** TY anchor: the [a_guess_mono] output painting's decoration extends the
    pre-guess skeleton (◇ ↦ fresh var, ∀◇ dropped onto a guarded remainder —
    supplied by [pskl_top_guarded] of the solve output). *)
(* SIZE INDUCTION (freshness campaign): [a_guess_mono] is exists-fresh
   while the target [dec_ext] is still cofinite, so the ∀ case must turn ONE
   guess instance into a family via [a_guess_mono_open_at] — whose output
   is no sub-derivation, hence no derivation-IH.  See
   [a_guess_mono_rename_tvar_size] (algo/prop_basic.v) for the recipe. *)
Lemma dec_ext_guess_mono_anchor_size : forall n Θ P' Ξ' A ψa,
  size_pskl P' <= n ->
  a_guess_mono Θ P' Ξ' A ->
  pskl_top_guarded P' ->
  is_tskl ψa ->
  uskl_ghost_free ψa ->
  ⌊ ψa ⌋ˢ = ptyp_to_pskl A ->
  dec_ext P' ψa empty.
Proof.
  induction n as [| n IHn]; intros Θ P' Ξ' A ψa Hsz Hg;
    [ destruct Hg; cbn in Hsz; lia | ].
  destruct Hg as [ Θ' α Hα | Θ' Pb Ξb Ab Hgb | Θ' α | Θ'
                 | Θ' Pa Pb Ξa Ξb Aa Ab Hga Hgb
                 | Θ' Pb Ξb Ab b0 Hfr Hgb ];
    cbn in Hsz; intros Htg Histk Hgf Hera.
  - (* hole ↦ fresh α̂ : A = var α *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__hole; [ exact Histk | apply d_tags_skl__var; fsetdec ].
  - (* tophole P ↦ guess P : drop the ∀◇ ; the guess output is guarded *)
    simpl in Htg; destruct Htg as [Hhd Htg0].
    apply dec_ext__skip_tophole;
      [ rewrite Hera; apply lc_head_guarded;
          [ rewrite <- Hera; apply lc_uskl_to_pskl; apply is_tskl_lc;
            exact Histk
          | eapply a_guess_mono_head; eassumption ]
      | eapply IHn; [ lia | exact Hgb | exact Htg0 | exact Histk | exact Hgf
                    | exact Hera ] ].
  - (* var α ↦ var α *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst. apply dec_ext__var; fsetdec.
  - (* unit ↦ unit *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__unit; fsetdec.
  - (* arrow ↦ arrow *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst.
    simpl in Htg; destruct Htg as [Htg1 Htg2].
    inversion Histk; subst. inversion Hgf; subst.
    eapply dec_ext__arrow;
      [ eapply IHn with (P' := Pa); [ lia | exact Hga | .. ]
      | eapply IHn with (P' := Pb); [ lia | exact Hgb | .. ]
      | fsetdec ]; assumption.
  - (* forall P ↦ all A0 : the ghost-free [is_tskl] ∀-decoration is [all_tag].
       EXISTS-FRESH source, COFINITE target: re-open the guess at each α. *)
    destruct ψa; simpl in Hera; try discriminate Hera;
      try (inversion Histk; fail).          (* kill the non-[is_tskl] all_syn survivor *)
    injection Hera as Hera0.
    simpl in Htg.
    inversion Histk; subst. inversion Hgf; subst.
    match goal with
    | Hib : forall α, α `notin` ?Li -> is_tskl (open_uskl_wrt_uskl ?bd _),
      Hgfb : forall α, α `notin` ?Lg -> uskl_ghost_free (open_uskl_wrt_uskl ?bd _)
      |- _ =>
        apply dec_ext__all
          with (L := Li `union` Lg `union` dom Ξb `union` ftvar_in_pskl Pb
                       `union` ftvar_in_ptyp Ab
                       `union` ftvar_in_aenv Θ');
        intros α Hα;
        eapply IHn with (P' := open_pskl_wrt_pskl Pb (pskl_var_f α))
                        (A := open_ptyp_wrt_ptyp
                                (close_ptyp_wrt_ptyp b0 Ab) (ptyp_var_f α));
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | apply a_guess_mono_open_at;
              [ apply a_guess_mono__forall with (β := b0);
                  [ exact Hfr | exact Hgb ]
              | clear - Hα; fsetdec ]
          | apply (proj1 (pskl_top_guarded_open_rec Pb α 0)); exact Htg
          | apply Hib; clear - Hα; fsetdec
          | apply Hgfb; clear - Hα; fsetdec
          | rewrite uskl_to_pskl_open; rewrite Hera0;
            rewrite <- ptyp_to_pskl_open; reflexivity ]
    end.
Qed.

Corollary dec_ext_guess_mono_anchor : forall Θ P' Ξ' A ψa,
  a_guess_mono Θ P' Ξ' A ->
  pskl_top_guarded P' ->
  is_tskl ψa ->
  uskl_ghost_free ψa ->
  ⌊ ψa ⌋ˢ = ptyp_to_pskl A ->
  dec_ext P' ψa empty.
Proof.
  intros. eapply dec_ext_guess_mono_anchor_size; eauto.
Qed.

(** ANCHOR: a decoration of the guess output extends the pre-guess skeleton,
    with NO remaining tags — the guess places untagged fresh flex vars at
    every ◇, so all of ψa's tags sit in the structure of [Q]. *)
Lemma dec_ext_guess_anchor : forall Θ NM P Ξ' P' Ψa ψa,
  a_guess Θ NM P Ξ' P' ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P) ->
  a_tags_sort NM Ψa ψa ->
  ⌊ ψa ⌋ˢ = P' ->
  dec_ext P ψa empty.
Proof.
  intros Θ NM P Ξ' P' Ψa ψa Hg Htg Htags Hera; inversion Hg; subst.
  - (* SK : P' = P ; subst already rewrote P to ⌊ψa⌋ˢ *)
    inversion Htags; subst.
    apply dec_ext_erase_refl; assumption.
  - (* TY : P' = ptyp_to_pskl A ; the solve output is top-guarded *)
    inversion Htags; subst.
    eapply dec_ext_guess_mono_anchor; [ eassumption | apply Htg; reflexivity | .. ];
      eauto.
Qed.

(** Skeleton-variable rename lemmas (for the ∀ case's cofinite reconstruction). *)
Lemma is_tskl_rename_var : forall ψ α β,
  is_tskl ψ -> is_tskl (subst_uskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H; induction H; simpl.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - auto with fresco.
  - apply is_tskl__all_tag with (L := L `union` singleton α); intros α2 Hα2.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH α2 ltac:(clear - Hα2; solve_notin_auto)) end.
  - auto with fresco.
  - auto with fresco.
Qed.

Lemma d_tags_skl_rename_var : forall Ψ ψ α β,
  d_tags_skl Ψ ψ -> d_tags_skl Ψ (subst_uskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros Ψ ψ α β H; induction H; simpl.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - eauto with fresco.
  - eapply d_tags_skl__all_tag with (L := L `union` singleton α) (Ψ0 := Ψ0);
      [ intros α2 Hα2 | assumption | assumption ].
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH α2 ltac:(clear - Hα2; solve_notin_auto)) end.
  - auto with fresco.
  - auto with fresco.
Qed.

Lemma dec_ext_rename_var : forall P ψ Ψ,
  dec_ext P ψ Ψ ->
  forall α β, dec_ext (subst_pskl_in_pskl (pskl_var_f β) α P)
                      (subst_uskl_in_uskl (uskl_var_f β) α ψ) Ψ.
Proof.
  intros P ψ Ψ H; induction H; intros αr βr; simpl.
  - auto using is_tskl_rename_var, d_tags_skl_rename_var with fresco.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - eapply dec_ext__arrow; [ apply IHdec_ext1 | apply IHdec_ext2 | assumption ].
  - apply dec_ext__all with (L := L `union` singleton αr); intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall a, a `notin` L -> forall b c, _ |- _ =>
      apply (IH α2 ltac:(clear - Hα2; solve_notin_auto)) end.
  - apply dec_ext__skip_tophole;
      [ rewrite uskl_to_pskl_subst; apply guarded_pskl_subst_var; assumption
      | apply IHdec_ext ].
  - apply dec_ext__topholeg; apply IHdec_ext.
  - eapply dec_ext__absorb_all with (L := L `union` singleton αr);
      [ intros α2 Hα2;
        rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ];
        match goal with IH : forall a, a `notin` L -> forall b c, _ |- _ =>
          apply (IH α2 ltac:(clear - Hα2; solve_notin_auto)) end
      | assumption ].
  - destruct_if; auto with fresco.
Qed.

(** A [dec_ext] subject is a decorated skeleton. *)
Lemma dec_ext_is_tskl : forall P ψ Ψ, dec_ext P ψ Ψ -> is_tskl ψ.
Proof.
  intros P ψ Ψ H; induction H; eauto with fresco.
Qed.

(** ⚠️⚠️ THE GUARDED-**TARGET** VERSION IS NOW FALSE (2026-08-04, the
    SolE-FlexR repair).  It used to read

      [Θ ⊢ₑ P ∼ P0 ⤳ P' -> guarded_pskl P0 -> pskl_guarded_head P']

    and its whole content was SE-FlexR: a guarded target could only be a
    (flexible) VARIABLE, and the old row returned that variable, whose head
    is guarded whatever the subject was.  The repaired row returns the
    ACCUMULATED PATTERN instead, so at [∀γ.γ→γ ∼ β̂] — target guarded, since
    [β̂] is a variable — the output is [∀γ.γ→γ] and its head is NOT guarded.

    ⭐ The GUARDED-SUBJECT version survives, and it is the one the
    consumers should have used: [a_guess_mono_guarded] (prop_solve_sub.v)
    says guess^TY is structural on the three guarded shapes, so a guarded
    subject still guesses to a guarded result.  The one call site that
    wanted the target version (SEq-UnivGhostR's twin, the SE-GhostGuarded
    row of [dec_ext_solve_eq_step_size]) is re-routed through the SUBJECT,
    where the needed head-guardedness is exactly what
    [pskl_top_guarded (∀◇P)] supplies — i.e. the paper's own implicit
    source-skeleton discipline ([a_wf_pskl_top_guarded]: a ∀◇ is well-formed
    only over a guarded body).  docs/PAPER-GAPS.md. *)
Lemma solve_eq_guarded_l_head : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> guarded_pskl P -> pskl_guarded_head P'.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Hg; simpl;
    try exact I; try (inversion Hg; fail).
  - (* flex_r : guess^TY is structural on the guarded shapes *)
    apply guarded_pskl_head. eapply a_guess_mono_guarded; eassumption.
  - (* hole_r : P'=P *) inversion Hg; subst; simpl; auto.
  - (* tophole_r_guarded *) apply IHa_solve_eq; assumption.
Qed.

(** A decoration of a guarded-headed skeleton has a GUARDED erasure —
    exactly the [SEq-UnivGhostR] premise, supplied when a solve step drops
    a ∀◇ onto a guarded remainder. *)
Lemma dec_ext_head_guarded_erase : forall P ψ Ψ,
  dec_ext P ψ Ψ -> pskl_guarded_head P -> guarded_pskl ⌊ ψ ⌋ˢ.
Proof.
  intros P ψ Ψ H Hh; inversion H; subst; simpl in Hh; try contradiction; simpl.
  - auto with fresco.
  - auto with fresco.
  - apply guarded_pskl__arrow;
      apply lc_uskl_to_pskl; apply is_tskl_lc;
      eapply dec_ext_is_tskl; eassumption.
  - auto with fresco.
Qed.

(** COVERAGE (unconditional — the paper's provenance, with NO side condition
    on the target Q): matching ψ against the skeleton it extends collects a
    Ψi with ψ's full tags Ψtot ⊆ Ψ' ∪ Ψi.  A surviving ∀◇ is matched by a
    dotted ghost (SEq-UnivGhostG); a dropped ∀◇ sits over a GUARDED erasure
    (SEq-UnivGhostR); a ∀ created against a ∀◇ recurses through
    SEq-ForallSyn (whose un-collected ε is REMAINING in [absorb_all]). *)
Lemma dec_ext_cover_eq : forall P ψ Ψ' Ψtot,
  dec_ext P ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi, {{ ψ ∼ P ⤳ Ψi }}da /\ Ψtot [<=] Ψ' `union` Ψi.
Proof.
  intros P ψ Ψ' Ψtot H; revert Ψtot; induction H; intros Ψtot Hdt.
  - (* hole : SEq-Vacuous, Ψ' = d_tags ψ = Ψtot *)
    exists empty. split; [ apply a_solvetag_eq__vacuous; fsetdec | ].
    match goal with Hh : d_tags_skl ?β2 ψ |- Ψtot [<=] union ?β2 empty =>
      pose proof (d_tags_skl_det Hh Hdt) as Hd; clear - Hd; fsetdec end.
  - (* unit *) exists empty. split; [ apply a_solvetag_eq__unit; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  - (* var *) exists empty. split; [ apply a_solvetag_eq__var; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  - (* arrow *)
    inversion Hdt; subst.
    match goal with
    | Ha : d_tags_skl ?T1 ψ1, Hbb : d_tags_skl ?T2 ψ2, Heq : Ψtot [=] _ |- _ =>
        destruct (IHdec_ext1 T1 Ha) as [Ψi1 [Hs1 Hsub1]];
        destruct (IHdec_ext2 T2 Hbb) as [Ψi2 [Hs2 Hsub2]];
        exists (Ψi1 `union` Ψi2); split;
        [ eapply a_solvetag_eq__arrow; [ exact Hs1 | exact Hs2 | fsetdec ]
        | clear - H1 Heq Hsub1 Hsub2; fsetdec ]
    end.
  - (* all : P=∀P0, ψ=all_tag ε ψ0, Ψtot=add ε Ψt0 *)
    inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heq : Ψtot [=] add ?e ?Ψt0,
      IH : forall α, α `notin` ?Lh -> forall Ψ2, _ -> _ |- _ =>
        destruct (atom_fresh (L `union` L1 `union` ftvar_in_uskl ψ0
                    `union` ftvar_in_pskl P0)) as [α0 HX0];
        destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Ψt0
                    (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
                  as [Ψi0 [Hs0 Hsub0]];
        exists (add ε Ψi0); split;
        [ eapply a_solvetag_eq__forall_inh with
            (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P0
                  `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ];
          intros β Hβ;
          rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                     ltac:(clear - HX0; solve_notin_auto));
          rewrite (subst_pskl_in_pskl_intro α0 P0 (pskl_var_f β)
                     ltac:(clear - HX0; solve_notin_auto));
          exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β)
        | clear - Heq Hsub0; fsetdec ]
    end.
  - (* skip_tophole : P=∀◇P0, guarded ⌊ψ⌋ ; SEq-UnivGhostR *)
    destruct (IHdec_ext Ψtot Hdt) as [Ψi [Hs Hsub]].
    exists Ψi. split;
      [ apply a_solvetag_eq__univ_ghost_r; [ assumption | exact Hs ] | exact Hsub ].
  - (* topholeg : P=∀◇P0, ψ=∀◈ψ0 ; SEq-UnivGhostG *)
    inversion Hdt; subst.
    match goal with Hd0 : d_tags_skl Ψtot ?p0 |- _ =>
      destruct (IHdec_ext Ψtot Hd0) as [Ψi [Hs Hsub]] end.
    exists Ψi. split; [ apply a_solvetag_eq__univ_ghostg; exact Hs | exact Hsub ].
  - (* absorb_all : P=∀◇P0, ψ=all_tag ε ψ0 ; SEq-ForallSyn (ε stays remaining) *)
    inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heqt : Ψtot [=] add ?e ?Ψt0,
      IH : forall α, α `notin` ?Lh -> forall Ψ2, _ -> _ |- _ =>
        destruct (atom_fresh (L `union` L1 `union` ftvar_in_uskl ψ0
                    `union` ftvar_in_pskl P0)) as [α0 HX0];
        destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Ψt0
                    (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
                  as [Ψi0 [Hs0 Hsub0]];
        exists Ψi0; split;
        [ apply a_solvetag_eq__forall_syn with
            (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P0
                  `union` singleton α0);
          intros β Hβ;
          rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                     ltac:(clear - HX0; solve_notin_auto));
          rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P0)
                       (pskl_var_f β) α0 ltac:(simpl; clear - HX0; solve_notin_auto));
          exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β)
        | match goal with Heq0 : Ψ [=] add ε _ |- _ =>
            clear - Heqt Heq0 Hsub0; fsetdec end ]
    end.
  - (* flex_forget : ψ = var *) exists empty. split;
      [ apply a_solvetag_eq__var; fsetdec
      | inversion Hdt; subst; fsetdec ].
Qed.

(* ===================================================================== *)
(*  ⭐⭐ A DECORATION OF THE GUESS IS A DECORATION OF THE SOURCE            *)
(*  (2026-08-04 — the soundness obligation the SolE-FlexR repair creates). *)
(*                                                                        *)
(*  Before the repair this was VACUOUS: SE-FlexR returned the bare          *)
(*  flexible, so [dec_ext α̂ ψ Ψ'] forced ψ to be a variable and             *)
(*  [dec_ext__flex_forget] rebuilt the subject side for free.  The row now  *)
(*  returns [guess^TY(P)], so the decoration arrives against the GUESS and  *)
(*  has to be transported back to the PATTERN it came from.                *)
(*                                                                        *)
(*  It transports because guess^TY only ever LOSES information: a ghost     *)
(*  becomes a fresh flexible (and [dec_ext__hole] lets a ghost decorate ANY *)
(*  tagged skeleton, so the step backwards is free), and a universal ghost  *)
(*  is dropped (rebuilt by [dec_ext__skip_tophole]).  Nothing is invented,  *)
(*  so no tag is invented either — whence the coverage [Ψp ⊆ Ψ'].           *)
(*                                                                        *)
(*  ⚠️ THE ∀◇ CASE NEEDS [pskl_top_guarded P] — [dec_ext__skip_tophole]     *)
(*  demands a guarded erasure.  That is not a new side condition: it is the *)
(*  paper's own implicit source-skeleton discipline, since                  *)
(*  [a_wf_pskl__tophole] admits a ∀◇ ONLY over a guarded body               *)
(*  ([a_wf_pskl_top_guarded]).  The SAME condition is what re-routes the    *)
(*  SE-GhostGuarded row below, now that [solve_eq_guarded_r_head] is false. *)
(*                                                                        *)
(*  SIZE induction, not derivation induction: the ∀ case must read the      *)
(*  cofinite [dec_ext__all] family at an α0 fresh for the DECORATION ψ0 as  *)
(*  well, and [a_guess_mono] is exists-fresh — so the guess instance is     *)
(*  moved to that α0 by [a_guess_mono_open_at] (algo/prop_basic.v, THE decl/algo   *)
(*  boundary bridge), whose output is no sub-derivation.                    *)
(* ===================================================================== *)

Lemma dec_ext_guess_source_size : forall n Θ P Ξ A ψ Ψ',
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  pskl_top_guarded P ->
  dec_ext (ptyp_to_pskl A) ψ Ψ' ->
  exists Ψp, dec_ext P ψ Ψp /\ Ψp [<=] Ψ'.
Proof.
  intros n; induction n as [| n IHn];
    intros Θ P Ξ A ψ Ψ' Hsz Hg Htg Hd;
    [ exfalso; pose proof (size_pskl_min P); lia | ].
  pose proof Hg as Hg0.
  destruct Hg as
    [ Θ α Hfr                                   (* ◇  ↦ a fresh flexible *)
    | Θ P0 Ξ A0 Hg                              (* ∀◇ ↦ dropped *)
    | Θ α                                       (* α  ↦ α *)
    | Θ                                         (* 1  ↦ 1 *)
    | Θ P1 P2 Ξ1 Ξ2 A1 A2 Hg1 Hg2               (* arrow *)
    | Θ P0 Ξ A0 β Hfr Hg ];                     (* ∀ *)
    cbn [ptyp_to_pskl] in Hd.
  - (* ◇ : the guess is a VARIABLE, and both rows that decorate a variable
       ([dec_ext__var] / [dec_ext__flex_forget]) make ψ a variable — which a
       ghost decorates with no remaining tags *)
    exists empty. split; [ | clear; fsetdec ].
    inversion Hd; subst;
      apply dec_ext__hole;
      solve [ apply is_tskl__var | apply d_tags_skl__var; clear; fsetdec ].
  - (* ∀◇ : dropped by the guess, rebuilt by the guarded skip *)
    cbn in Htg. destruct Htg as [Hh Ht].
    assert (Hsz0 : size_pskl P0 <= n) by (cbn in Hsz; lia).
    destruct (IHn _ _ _ _ _ _ Hsz0 Hg Ht Hd) as [Ψp [Hdp Hsub]].
    exists Ψp. split; [ | exact Hsub ].
    apply dec_ext__skip_tophole;
      [ eapply dec_ext_head_guarded_erase; [ exact Hdp | exact Hh ]
      | exact Hdp ].
  - (* α : the guess is the identity *) exists Ψ'; split; [ exact Hd | clear; fsetdec ].
  - (* 1 : the guess is the identity *) exists Ψ'; split; [ exact Hd | clear; fsetdec ].
  - (* arrow *)
    cbn in Htg. destruct Htg as [Ht1 Ht2].
    inversion Hd as [ | | | P1' P2' ψ1 ψ2 Ψ0 Ψ1 Ψ2 Hd1 Hd2 Heq
                    | | | | | P0' α0 Ψ0 Heq ]; subst.
    + assert (Hsz1 : size_pskl P1 <= n) by (cbn in Hsz; lia).
      assert (Hsz2 : size_pskl P2 <= n) by (cbn in Hsz; lia).
      destruct (IHn _ _ _ _ _ _ Hsz1 Hg1 Ht1 Hd1) as [Ψp1 [Hp1 Hs1]].
      destruct (IHn _ _ _ _ _ _ Hsz2 Hg2 Ht2 Hd2) as [Ψp2 [Hp2 Hs2]].
      exists (Ψp1 `union` Ψp2). split;
        [ eapply dec_ext__arrow; [ exact Hp1 | exact Hp2 | clear; fsetdec ]
        | clear - Hs1 Hs2 Heq; fsetdec ].
    + (* flex_forget : ψ is a variable, which decorates anything *)
      exists empty; split;
        [ apply dec_ext__flex_forget; clear; fsetdec
        | clear; fsetdec ].
  - (* ∀ *)
    cbn in Htg.
    inversion Hd as [ | | | | L' Q0 ψ0 ε Ψ0 Hfam
                    | | | | P0' α0 Ψ0 Heq ]; subst.
    + (* dec_ext__all : ψ = ∀^ε ψ0.  Read the family at an α0 fresh for the
         DECORATION too, and move the guess instance there. *)
      destruct (atom_fresh (L' `union` ftvar_in_aenv Θ `union` ftvar_in_pskl P0
                              `union` dom Ξ `union` ftvar_in_uskl ψ0))
        as [α0 Hα0].
      assert (Hα0g : α0 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P0
                        `union` dom Ξ) by (clear - Hα0; fsetdec).
      assert (Hα0L : α0 `notin` L') by (clear - Hα0; fsetdec).
      pose proof (a_guess_mono_open_at Hg0 Hα0g) as Hgα.
      pose proof (Hfam α0 Hα0L) as Hdα.
      rewrite <- ptyp_to_pskl_open in Hdα.
      assert (Hszα : size_pskl (open_pskl_wrt_pskl P0 (pskl_var_f α0)) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia).
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P0 (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P0 α0 0)); exact Htg).
      destruct (IHn _ _ _ _ _ _ Hszα Hgα Htgα Hdα) as [Ψp [Hdp Hsub]].
      exists Ψp. split; [ | exact Hsub ].
      (* ONE instance ⟹ the cofinite family: [dec_ext_rename_var] is
         UNCONDITIONAL, and α0 was chosen apart from both P0 and ψ0 *)
      apply dec_ext__all with
        (L := ftvar_in_pskl P0 `union` ftvar_in_uskl ψ0 `union` singleton α0)
        (ε := ε).
      intros α1 Hα1.
      rewrite (subst_pskl_in_pskl_intro α0 P0 (pskl_var_f α1))
        by (clear - Hα0; fsetdec).
      rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α1))
        by (clear - Hα0; fsetdec).
      exact (dec_ext_rename_var Hdp α0 α1).
    + (* flex_forget *)
      exists empty; split;
        [ apply dec_ext__flex_forget; clear; fsetdec | clear; fsetdec ].
Qed.

(** A GHOST-FREE skeleton decorates only to a ghost-free ψ: every [dec_ext]
    row that could introduce a ghost into ψ ([topholeg], and the rows whose
    subject is ◇ or ∀◇) needs a ghost IN THE SKELETON.  Supplies SEq-FlexR's
    premise, since [ptyp_to_pskl] emits no ghost. *)
Lemma dec_ext_ghost_free : forall P ψ Ψ,
  dec_ext P ψ Ψ -> pskl_ghost_free P -> uskl_ghost_free ψ.
Proof.
  intros P ψ Ψ H; induction H; intros Hgf; cbn in Hgf;
    (* ◇ and the three ∀◇ rows need a ghost IN THE SKELETON *)
    try contradiction;
    (* unit / var / flex_forget *)
    try solve [ constructor ].
  - (* arrow *)
    destruct Hgf as [Hgf1 Hgf2]. constructor; auto.
  - (* ψ's ∀ : ghost-freeness transports through the opening, and ONE
       instance re-grows the cofinite family *)
    match goal with
    | |- uskl_ghost_free (uskl_all_tag _ ?psi0) =>
        pick fresh α0 for (L `union` ftvar_in_uskl psi0);
        apply uskl_ghost_free__all_tag with (L := ftvar_in_uskl psi0);
        intros α1 Hα1;
        rewrite (subst_uskl_in_uskl_intro α0 psi0 (uskl_var_f α1))
          by (clear - Fr; fsetdec);
        apply uskl_ghost_free_subst_var
    end.
    match goal with
    | IH : forall α, α `notin` L -> pskl_ghost_free _ -> _ |- _ =>
        apply (IH α0 ltac:(clear - Fr; solve_notin_auto));
        apply pskl_ghost_free_open_rec; exact Hgf
    end.
Qed.

Corollary dec_ext_guess_source : forall Θ P Ξ A ψ Ψ',
  a_guess_mono Θ P Ξ A ->
  pskl_top_guarded P ->
  dec_ext (ptyp_to_pskl A) ψ Ψ' ->
  exists Ψp, dec_ext P ψ Ψp /\ Ψp [<=] Ψ'.
Proof. intros; eapply dec_ext_guess_source_size; eauto. Qed.

(** FORWARD STEP (eq): one [eq Q] constraint, threaded through
    [solve_eq P ∼ Q ⤳ P'] — UNCONDITIONAL (no side condition on P or Q;
    the paper's lemma has none).  Produces the per-constraint solvetag
    [{{ ψ ∼ Q ⤳ Ψi }}da] and re-relates ψ to the pre-step P with COVERAGE
    [Ψp ⊆ Ψ' ∪ Ψi] (⊆, set membership).  ∀◇ solve steps decompose by the
    subject's relation to the output: dotted (topholeg ↦ SEq-UnivGhostG),
    guarded-skip (↦ SEq-UnivGhostR), absorbed-∀ (↦ SEq-ForallSyn), flex. *)
(* SIZE induction (freshness campaign, DESIGN.md §4.3).  The solve ∀ rules
   are exists-fresh, so each hands over ITS OWN binder — but the decoration
   ψ is an input and may mention that binder (a ◇ under the ∀ decorates to
   an arbitrary tagged skeleton), so the cofinite [dec_ext] / [d_tags_skl] /
   [a_solvetag] families cannot be re-built by renaming from it.  The fix is
   to move the SOLVE derivation instead: SWAP its binder to a genuinely
   fresh α0 ([a_solve_eq_move_binder], over the equivariance kit) and read
   the families there.  A moved premise is no sub-derivation, whence the
   measure. *)
Lemma dec_ext_solve_eq_step_size : forall n Θ P P3 Ξ P' ψ Ψ' Ψtot,
  2 * (size_pskl P + size_pskl P3) <= n ->
  {{ Θ ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
  (* ⚠️ NEW PREMISE (2026-08-04).  Two rows now need it, both for the same
     reason and both discharged by the paper's own implicit source-skeleton
     discipline ([a_wf_pskl_top_guarded]: a ∀◇ is well-formed only over a
     guarded body): SE-FlexR, whose output [guess^TY(P)] must be pushed back
     to P through a dropped ∀◇, and SE-GhostGuarded, which drops a ∀◇ onto
     the output and therefore needs a GUARDED erasure — the old route via
     [solve_eq_guarded_r_head] is gone, that lemma being false now. *)
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ∼ P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  induction n as [| n IHn];
    [ intros Θ P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs;
      pose proof (size_pskl_min P); pose proof (size_pskl_min P3); lia | ].
  intros Θ P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs Htg; revert ψ Ψ' Ψtot.
  destruct Hs as
    [ Θ                                         (* SE-Unit *)
    | Θ α Q                                     (* SE-Var *)
    | Θ α P Ξ A Hflex Hnf Hng Hgu               (* SE-FlexR *)
    | Θ Q                                       (* SE-GhostL *)
    | Θ P                                       (* SE-VacuousR *)
    | Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2       (* SE-Arrow *)
    | Θ P Q Ξ P' b Hfr Hp                       (* SE-Forall *)
    | Θ P Q Ξ P' Hp                             (* SE-UnivGhost *)
    | Θ P Q Ξ P' b Hfr Hp                       (* SE-GhostForall *)
    | Θ P Q Ξ P' Hg Hp                          (* SE-GhostGuarded *)
    | Θ P Q Ξ P' b Hfr Hp                       (* SE-ForallGhost *)
    | Θ P Q Ξ P' Hg Hp ];                       (* SE-GuardedGhost *)
    intros ψ Ψ' Ψtot Hdec Hdt; cbn in Hsz; cbn in Htg.
  - (* unit *) inversion Hdec; subst.
    + exists empty, empty; split;
        [ apply a_solvetag_eq__unit; fsetdec
        | split; [ apply dec_ext__unit; fsetdec | fsetdec ] ].
    + exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* var : P=P'=var α, Q arbitrary *) inversion Hdec; subst.
    + exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__var; fsetdec | fsetdec ] ].
    + exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* ⭐ SE-FlexR (2026-08-04).  The output is no longer the bare flexible
       but [guess^TY(P)], so the decoration arrives against the GUESS and is
       transported back to the pattern by [dec_ext_guess_source].  The
       decorated row is SEq-FlexR — it exists already — and its
       ghost-freeness premise holds because [ptyp_to_pskl] emits no ghost. *)
    destruct (dec_ext_guess_source Hgu Htg Hdec) as [Ψp [Hdp Hsub]].
    exists empty, Ψp; split;
      [ apply a_solvetag_eq__flex_r;
          [ eapply dec_ext_ghost_free;
              [ exact Hdec | apply ptyp_to_pskl_ghost_free ]
          | clear; fsetdec ]
      | split; [ exact Hdp | clear - Hsub; fsetdec ] ].
  - (* hole_l : P=◇, P'=Q ; the coverage sub-lemma *)
    destruct (dec_ext_cover_eq Hdec Hdt) as [Ψi [Hsi Hsub]].
    exists Ψi, Ψtot; split; [ exact Hsi | split;
      [ apply dec_ext__hole; [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
      | exact Hsub ] ].
  - (* hole_r : Q=◇, P'=P ; SEq-Vacuous *)
    exists empty, Ψ'; split;
      [ apply a_solvetag_eq__vacuous; fsetdec
      | split; [ exact Hdec | fsetdec ] ].
  - (* arrow *)
    inversion Hdec; subst.
    + (* ψ = arrow ψ1 ψ2 *)
      inversion Hdt; subst.
      assert (Hsz1 : 2 * (size_pskl P1 + size_pskl Q1) <= n) by lia.
      assert (Hsz2 : 2 * (size_pskl P2 + size_pskl Q2) <= n) by lia.
      destruct Htg as [Htg1 Htg2].
      edestruct IHn as [Ψi1 [Ψp1 [Hsa [Hd1 Hu1]]]];
        [ exact Hsz1 | exact Hp1 | exact Htg1 | eassumption | eassumption | ].
      edestruct IHn as [Ψi2 [Ψp2 [Hsb [Hd2 Hu2]]]];
        [ exact Hsz2 | exact Hp2 | exact Htg2 | eassumption | eassumption | ].
      exists (Ψi1 `union` Ψi2), (Ψp1 `union` Ψp2); split;
        [ eapply a_solvetag_eq__arrow; [ exact Hsa | exact Hsb | fsetdec ]
        | split; [ eapply dec_ext__arrow; [ exact Hd1 | exact Hd2 | fsetdec ]
                 | match goal with Heq : Ψ' [=] _ `union` _ |- _ =>
                     clear - Heq Hu1 Hu2; fsetdec end ] ].
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* forall : P=∀P0, Q=∀Q0, P'=∀P0' *)
    inversion Hdec; subst.
    + (* ψ = all_tag ε ψ0 ; dec_ext cofin = H2, d_tags cofin = H4 (tags Ψ0).
         The rule's own binder b may occur in ψ0, so the SOLVE premise is
         renamed b ⤳ α0 (fresh for everything) and the two families are
         instantiated there. *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                  `union` ftvar_in_pskl P' `union` dom Θ `union` singleton b))
        as [α0 HX0].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b))
        as HupP.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b))
        as HupQ.
      (* ⚠️ the witness-move is a SWAP now, not a rename: [b] sits IN the
         premise's context, so no rename side condition can hold *)
      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_eq_move_binder _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ) as Hr.
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P α0 0)); exact Htg).
      assert (Hszr : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f α0))
                          + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f α0)))
                     <= n)
        by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ Hszr Hr Htgα Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists (add ε Ψi0), Ψp0; split.
      * (* solvetag : SEq-ForallInh, rename α0 ⤳ β *)
        eapply a_solvetag_eq__forall_inh with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ].
        intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite (subst_pskl_in_pskl_intro α0 Q (pskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- (* dec_ext : dec_ext__all, rename α0 ⤳ α2 *)
           apply dec_ext__all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0).
           intros α2 Hα2.
           rewrite (subst_pskl_in_pskl_intro α0 P (pskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_both : ∀◇P ∼ ∀◇Q ⤳ ∀◇P' ; inner induction on the ψ↔∀◇P'
       relation (the subject may keep absorbing ∀s against the ghost) *)
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    remember (pskl_tophole P') as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole : guarded erasure ; SEq-UnivGhostR *)
      injection HeqW as HeqP; subst P0.
      match goal with Hin : dec_ext P' _ _ |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hdt)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_eq__univ_ghost_r; [ assumption | exact Hsi ]
        | split; [ apply dec_ext__skip_tophole; [ assumption | exact Hdp ]
                 | exact Hsub ] ].
    + (* topholeg : SEq-UnivGhostG *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with
      | Hin : dec_ext P' ?p0 _, Hd0 : d_tags_skl _ ?p0 |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hd0)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_eq__univ_ghostg; exact Hsi
        | split; [ apply dec_ext__topholeg; exact Hdp | exact Hsub ] ].
    + (* absorb_all : SEq-ForallSyn (ε stays remaining on both sides) *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]]
      end.
      exists Ψi0, (add ε Ψp0); split.
      * apply a_solvetag_eq__forall_syn with
          (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0).
        intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q)
                     (pskl_var_f β) α0 ltac:(simpl; clear - HX0; solve_notin_auto)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- eapply dec_ext__absorb_all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P)
                        (pskl_var_f α2) α0 ltac:(simpl; clear - HX0; solve_notin_auto)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - HeqAbs Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_l_all : ∀◇P ∼ ∀Q ⤳ ∀P' (SE-GhostForall) ; the subject's ∀ is
       CREATED against the ghost — absorb_all backward, SEq-ForallInh forward *)
    inversion Hdec; subst.
    + (* ψ = all_tag ε ψ0 — as SE-Forall: rename the solve premise b ⤳ α0
         (the ∀◇ subject is b-free, so only the opened target moves) *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                  `union` ftvar_in_pskl P' `union` dom Θ `union` singleton b))
        as [α0 HX0].
      (* witness-move by SWAP (the ∀◇ subject is b-free, so it rides along) *)
      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_eq_move_binder_tophole_l _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ)
        as Hr.
      assert (Hszr : 2 * (size_pskl (pskl_tophole P)
                          + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f α0)))
                     <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ Hszr Hr Htg Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists (add ε Ψi0), (add ε Ψp0); split.
      * eapply a_solvetag_eq__forall_inh with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ].
        intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite (subst_pskl_in_pskl_intro α0 Q (pskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- eapply dec_ext__absorb_all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P)
                        (pskl_var_f α2) α0 ltac:(simpl; clear - HX0; solve_notin_auto)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_l_guarded : ∀◇P ∼ Q (guarded) ⤳ P' ; the ∀◇ is DROPPED onto a
       guarded output — guarded skip backward *)
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hdec Hdt)
      as [Ψi [Ψp [Hsi [Hdp Hsub]]]].
    exists Ψi, Ψp; split;
      [ exact Hsi
      | split;
        [ apply dec_ext__skip_tophole;
            [ (* ⚠️ the target route ([solve_eq_guarded_r_head]) is GONE — that
                 lemma is false under the repair.  The subject route: [∀◇P]
                 well-formed means P is guarded-headed, which is exactly
                 [pskl_top_guarded]'s first component. *)
              eapply dec_ext_head_guarded_erase;
                [ exact Hdp | exact (proj1 Htg) ]
            | exact Hdp ]
        | exact Hsub ] ].
  - (* all_l_tophole : ∀P ∼ ∀◇Q ⤳ ∀P' (SE-ForallGhost) ; SEq-ForallSyn keeps
       the ∀◇ target whole, the skeleton ∀ matches the subject ∀ *)
    inversion Hdec; subst.
    + (* ψ = all_tag ε ψ0 — as SE-Forall: rename the solve premise b ⤳ α0
         (the ∀◇ target is b-free, so only the opened subject moves) *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                  `union` ftvar_in_pskl P' `union` dom Θ `union` singleton b))
        as [α0 HX0].
      (* witness-move by SWAP (the ∀◇ target is b-free, so it rides along) *)
      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_eq_move_binder_tophole_r _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ)
        as Hr.
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P α0 0)); exact Htg).
      assert (Hszr : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f α0))
                          + size_pskl (pskl_tophole Q)) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ Hszr Hr Htgα Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists Ψi0, Ψp0; split.
      * apply a_solvetag_eq__forall_syn with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0).
        intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q)
                     (pskl_var_f β) α0 ltac:(simpl; clear - HX0; solve_notin_auto)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- apply dec_ext__all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0).
           intros α2 Hα2.
           rewrite (subst_pskl_in_pskl_intro α0 P (pskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_r_guarded : P (guarded) ∼ ∀◇Q ⤳ P' ; SEq-UnivGhostR *)
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp Htg Hdec Hdt)
      as [Ψi [Ψp [Hsi [Hdp Hsub]]]].
    exists Ψi, Ψp; split;
      [ apply a_solvetag_eq__univ_ghost_r;
          [ eapply dec_ext_head_guarded_erase;
              [ exact Hdec | eapply solve_eq_guarded_l_head; eassumption ]
          | exact Hsi ]
      | split; [ exact Hdp | exact Hsub ] ].
Qed.

Lemma dec_ext_solve_eq_step : forall Θ P P3 Ξ P' ψ Ψ' Ψtot,
  {{ Θ ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ∼ P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros Θ P P3 Ξ P' ψ Ψ' Ψtot Hs Htg Hdec Hdt.
  exact (dec_ext_solve_eq_step_size
           (n := 2 * (size_pskl P + size_pskl P3))
           (le_n _) Hs Htg Hdec Hdt).
Qed.

(** At a ◇-hole, dec_ext's remaining tags are exactly all of ψ's tags. *)
Lemma dec_ext_hole_tags : forall ψ Ψp Ψtot,
  dec_ext pskl_hole ψ Ψp -> d_tags_skl Ψtot ψ -> Ψp [=] Ψtot.
Proof.
  intros ψ Ψp Ψtot H Hdt; inversion H; subst.
  - eapply d_tags_skl_det; eassumption.
  - inversion Hdt; subst; fsetdec.
Qed.

(** A decoration of a guarded skeleton is guarded (unit/var/arrow). *)
Lemma dec_ext_guarded_uskl : forall P ψ Ψ,
  dec_ext P ψ Ψ -> guarded_pskl P -> is_tskl ψ -> guarded_uskl ψ.
Proof.
  intros P ψ Ψ H Hg Hik; inversion H; subst; try (inversion Hg; fail).
  - auto with fresco.
  - auto with fresco.
  - apply is_tskl_lc in Hik; inversion Hik; subst; auto with fresco.
  - auto with fresco.
Qed.

(** FORWARD STEP (sub): the terminal [sub m Q] constraint — UNCONDITIONAL.
    SIZE induction, for the same reason as the eq step (DESIGN.md §4.3). *)
Lemma dec_ext_solve_sub_step_size : forall n Θ m P P3 Ξ P' ψ Ψ' Ψtot,
  2 * (size_pskl P + size_pskl P3) <= n ->
  {{ Θ ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a ->
  (* the same premise the EQ step gained, and for the same reason: SS-Check
     hands the subject straight to the eq step *)
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ≼[ m ] P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  induction n as [| n IHn];
    [ intros Θ m P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs;
      pose proof (size_pskl_min P); pose proof (size_pskl_min P3); lia | ].
  intros Θ m P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs Htg; revert ψ Ψ' Ψtot.
  destruct Hs as
    [ Θ m α Q                                   (* SS-Var *)
    | Θ m P Q Ξ P' b Hfr Hp                     (* SS-ForallL *)
    | Θ m P Q Ξ P' Hp                           (* SS-UnivGhostL *)
    | Θ m P Hoff                                (* SS-Vacuous *)
    | Θ P Q Ξ P' Hgf0 H H0 H1                   (* SS-Check *)
    | Θ A B Ξ P' b Hgf0 Hoff Hfr Hp             (* SS-ForallR *)
    | Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' H H0        (* SS-Arrow *)
    | Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' H H0              (* SS-GhostLF *)
    | Θ B Hgf0 H ];                             (* SS-GhostL *)
    intros ψ Ψ' Ψtot Hdec Hdt; cbn in Hsz; cbn in Htg.
  - (* var : P=P'=var α *)
    inversion Hdec; subst;
      (exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ solve [ apply dec_ext__var; fsetdec
                         | apply dec_ext__flex_forget; fsetdec ] | fsetdec ] ]).
  - (* forall_l : subject ∀P, output ∀(close b P').  The rule's own binder b
       may occur in ψ0, so the SOLVE premise is renamed b ⤳ α0 (fresh) and
       the cofinite dec_ext / d_tags families are instantiated there. *)
    inversion Hdec; subst.
    + (* all_tag ε ψ0 *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
                  `union` ftvar_in_pskl Q `union` dom Θ `union` singleton b))
        as [α0 HX0].
      (* witness-move by SWAP: b sits in the premise's context now *)
      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_sub_move_binder_l _ _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ)
        as Hr.
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P α0 0)); exact Htg).
      assert (Hszr : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f α0))
                          + size_pskl Q) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ _ Hszr Hr Htgα Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists Ψi0, Ψp0; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` singleton α0). intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq Q (pskl_var_f β) α0
                     ltac:(clear - HX0; solve_notin_auto)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split.
        -- apply dec_ext__all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P `union` singleton α0).
           intros α2 Hα2.
           rewrite (subst_pskl_in_pskl_intro α0 P (pskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* univ_ghost_l : ∀◇P ≼[m] Q ⤳ ∀◇P' ; inner induction on the ψ↔∀◇P'
       relation — the target Q is untouched by the ghost *)
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    remember (pskl_tophole P') as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole *)
      injection HeqW as HeqP; subst P0.
      match goal with Hin : dec_ext P' _ _ |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hdt)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ exact Hsi
        | split; [ apply dec_ext__skip_tophole; [ assumption | exact Hdp ]
                 | exact Hsub ] ].
    + (* topholeg : SSub-UnivGhostLG *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with
      | Hin : dec_ext P' ?p0 _, Hd0 : d_tags_skl _ ?p0 |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hd0)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_sub__univ_ghost_lg; exact Hsi
        | split; [ apply dec_ext__topholeg; exact Hdp | exact Hsub ] ].
    + (* absorb_all : SSub-ForallL *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]]
      end.
      exists Ψi0, (add ε Ψp0); split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q `union` singleton α0).
        intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq Q (pskl_var_f β) α0
                     ltac:(clear - HX0; solve_notin_auto)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split.
        -- eapply dec_ext__absorb_all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; solve_notin_auto)).
           rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P)
                        (pskl_var_f α2) α0 ltac:(simpl; clear - HX0; solve_notin_auto)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - HeqAbs Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* vacuous : Q=◇, P'=P ; SSub-Vacuous *)
    exists empty, Ψ'; split;
      [ apply a_solvetag_sub__vacuous; fsetdec
      | split; [ exact Hdec | fsetdec ] ].
  - (* check : guarded P (H), guarded Q (H0), solve_eq (H1) → eq_step + SSub-Check *)
    edestruct dec_ext_solve_eq_step as [Ψi [Ψp [Hste [Hdp Hup]]]];
      [ exact H1 | exact Htg | exact Hdec | exact Hdt | ].
    exists Ψi, Ψp; split;
      [ apply a_solvetag_sub__check;
          [ assumption
          | eapply dec_ext_guarded_uskl;
              [ exact Hdp | assumption | eapply d_tags_skl_is_tskl; exact Hdt ]
          | assumption
          | exact Hste ]
      | split; [ exact Hdp | exact Hup ] ].
  - (* forall_r : Q=∀B ; the output passes through UNCHANGED, so the IH
       applies at the rule's OWN binder b with [Hdec]/[Hdt] as they stand.
       But b LEAKS, so it may occur free in ψ — the family is therefore
       built with the TARGET-ONLY rename. *)
    assert (Hsz0 : 2 * (size_pskl A
                        + size_pskl (open_pskl_wrt_pskl B (pskl_var_f b)))
                   <= n)
      by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
    destruct (IHn _ _ _ _ _ _ _ _ _ Hsz0 Hp Htg Hdec Hdt)
              as [Ψi0 [Ψp0 [Hst0 [Hd0 Hu0]]]].
    exists Ψi0, Ψp0; split.
    + apply a_solvetag_sub__forall_r with
        (L := ftvar_in_pskl B `union` singleton b);
        [ assumption | ].
      intros β Hβ.
      rewrite (subst_pskl_in_pskl_intro b B (pskl_var_f β)
                 ltac:(clear - Hfr; solve_notin_auto)).
      exact ((proj1 a_solvetag_sub_eq_target_rename) _ _ _ _ Hst0 b β).
    + split; [ exact Hd0 | exact Hu0 ].
  - (* arrow : domain via eq_step, codomain via sub IH *)
    inversion Hdec; subst.
    + (* arrow ψ1 ψ2 *)
      inversion Hdt; subst.
      destruct Htg as [Htg1 Htg2].
      edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
        [ exact H | exact Htg1 | eassumption | eassumption | ].
      assert (Hsz2 : 2 * (size_pskl P2 + size_pskl Q2) <= n) by lia.
      edestruct IHn as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
        [ exact Hsz2 | exact H0 | exact Htg2 | eassumption | eassumption | ].
      exists (Ψi1 `union` Ψi2), (Ψp1 `union` Ψp2); split;
        [ eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
        | split; [ eapply dec_ext__arrow; [ exact Hd1 | exact Hd2 | reflexivity ]
                 | match goal with Heq : Ψ' [=] _ `union` _ |- _ =>
                     clear - Heq Hu1 Hu2; fsetdec end ] ].
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* ghost_l_fn : ◇ ≼[fn m] (arrow Q1 Q2) ⤳ ∀◇(arrow P1' P2') ; the pre-step
       skeleton is ◇ (any subject) — inner induction on the ψ↔∀◇(arrow) relation
       for the solvetag, hole for the backward relation *)
    assert (Hsz2 : 2 * (size_pskl pskl_hole + size_pskl Q2) <= n)
      by (cbn; lia).
    remember (pskl_tophole (pskl_arrow P1' P2')) as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole : dec_ext (arrow P1' P2') ψ _ *)
      injection HeqW as HeqP; subst P0.
      match goal with Hde : dec_ext (pskl_arrow P1' P2') _ _ |- _ =>
        inversion Hde; subst end.
      * (* ψ = arrow ψ1 ψ2 *)
        inversion Hdt; subst.
        (* SS-GhostLF: the subject is ◇, whose [pskl_top_guarded] is [I] *)
        edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
          [ exact H | exact I | eassumption | eassumption | ].
        edestruct IHn as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
          [ exact Hsz2 | exact H0 | exact I | eassumption | eassumption | ].
        match goal with Ha : d_tags_skl _ ψ1, Hb : d_tags_skl _ ψ2 |- _ =>
          pose proof (dec_ext_hole_tags Hd1 Ha) as He1;
          pose proof (dec_ext_hole_tags Hd2 Hb) as He2 end.
        exists (Ψi1 `union` Ψi2), Ψtot; split;
          [ eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
          | split;
            [ apply dec_ext__hole; [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
            | match goal with Heqt : Ψtot [=] _ |- Ψtot [<=] ?β2 `union` _ =>
                match goal with Heqp : β2 [=] _ |- _ =>
                  clear - Heqt Heqp He1 He2 Hu1 Hu2; fsetdec end end ] ].
      * (* ψ = var (flex_forget under skip) *)
        exists empty, empty; split;
          [ apply a_solvetag_sub__var; fsetdec
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt
                       | inversion Hdt; subst; apply d_tags_skl__var; fsetdec ]
                   | inversion Hdt; subst; fsetdec ] ].
    + (* topholeg : ψ = ∀◈ψ0, dec_ext (arrow P1' P2') ψ0 *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with Hde : dec_ext (pskl_arrow P1' P2') ?p0 _,
                      Hd0t : d_tags_skl Ψtot ?p0 |- _ =>
        inversion Hde; subst end.
      * (* ψ0 = arrow ψ1 ψ2 *)
        match goal with Hd0t : d_tags_skl Ψtot (uskl_arrow _ _) |- _ =>
          inversion Hd0t; subst end.
        (* SS-GhostLF: the subject is ◇, whose [pskl_top_guarded] is [I] *)
        edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
          [ exact H | exact I | eassumption | eassumption | ].
        edestruct IHn as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
          [ exact Hsz2 | exact H0 | exact I | eassumption | eassumption | ].
        match goal with Ha : d_tags_skl _ ψ1, Hb : d_tags_skl _ ψ2 |- _ =>
          pose proof (dec_ext_hole_tags Hd1 Ha) as He1;
          pose proof (dec_ext_hole_tags Hd2 Hb) as He2 end.
        exists (Ψi1 `union` Ψi2), Ψtot; split;
          [ apply a_solvetag_sub__univ_ghost_lg;
            eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
          | split;
            [ apply dec_ext__hole; [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
            | match goal with Heqt : Ψtot [=] _ |- Ψtot [<=] ?β2 `union` _ =>
                match goal with Heqp : β2 [=] _ |- _ =>
                  clear - Heqt Heqp He1 He2 Hu1 Hu2; fsetdec end end ] ].
      * (* ψ0 = var *)
        exists empty, empty; split;
          [ apply a_solvetag_sub__univ_ghost_lg; apply a_solvetag_sub__var; fsetdec
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt
                       | apply d_tags_skl__topholeg; apply d_tags_skl__var; fsetdec ]
                   | fsetdec ] ].
    + (* absorb_all : SSub-ForallL down the created ∀-prefix *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl Q1 `union` ftvar_in_pskl Q2)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]];
          pose proof (dec_ext_hole_tags Hd0 (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
            as He0
      end.
      exists Ψi0, Ψtot; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q1 `union` ftvar_in_pskl Q2
                `union` singleton α0).
        intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_arrow Q1 Q2)
                     (pskl_var_f β) α0 ltac:(simpl; clear - HX0; solve_notin_auto)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split;
          [ apply dec_ext__hole;
              [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
          | match goal with Heqt : Ψtot [=] add _ _ |- _ =>
              clear - Heqt HeqAbs He0 Hu0; fsetdec end ].
    + (* flex_forget : ψ = var *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__hole;
                     [ eapply d_tags_skl_is_tskl; exact Hdt
                     | inversion Hdt; subst; apply d_tags_skl__var; fsetdec ]
                 | inversion Hdt; subst; fsetdec ] ].
  - (* ghost_l : ◇ ≼[tc] B ⤳ ∀◇B, guarded B = H ; inner induction, the target
       B is matched by the coverage lemma (SSub-Check) *)
    remember (pskl_tophole B) as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole : dec_ext B ψ _ *)
      injection HeqW as HeqP; subst P0.
      match goal with Hde : dec_ext B _ _ |- _ =>
        destruct (dec_ext_cover_eq Hde Hdt) as [Ψi [Hsi Hsub]];
        exists Ψi, Ψtot; split;
          [ apply a_solvetag_sub__check;
              [ exact Hgf0
              | eapply dec_ext_guarded_uskl;
                  [ exact Hde | exact H | eapply d_tags_skl_is_tskl; exact Hdt ]
              | exact H | exact Hsi ]
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
                   | exact Hsub ] ]
      end.
    + (* topholeg : ψ = ∀◈ψ0, dec_ext B ψ0 _ *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with Hde : dec_ext B ?p0 _, Hd0 : d_tags_skl Ψtot ?p0 |- _ =>
        destruct (dec_ext_cover_eq Hde Hd0) as [Ψi [Hsi Hsub]];
        exists Ψi, Ψtot; split;
          [ apply a_solvetag_sub__univ_ghost_lg; apply a_solvetag_sub__check;
              [ exact Hgf0
              | eapply dec_ext_guarded_uskl;
                  [ exact Hde | exact H | eapply d_tags_skl_is_tskl; exact Hd0 ]
              | exact H | exact Hsi ]
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
                   | exact Hsub ] ]
      end.
    + (* absorb_all : SSub-ForallL down the created ∀-prefix *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl B)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]];
          pose proof (dec_ext_hole_tags Hd0 (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
            as He0
      end.
      exists Ψi0, Ψtot; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl B `union` singleton α0).
        intros β Hβ.
        rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; solve_notin_auto)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq B (pskl_var_f β) α0
                     ltac:(clear - HX0; solve_notin_auto)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split;
          [ apply dec_ext__hole;
              [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
          | match goal with Heqt : Ψtot [=] add _ _ |- _ =>
              clear - Heqt HeqAbs He0 Hu0; fsetdec end ].
    + (* flex_forget : ψ = var *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__hole;
                     [ eapply d_tags_skl_is_tskl; exact Hdt
                     | inversion Hdt; subst; apply d_tags_skl__var; fsetdec ]
                 | inversion Hdt; subst; fsetdec ] ].
Qed.

Lemma dec_ext_solve_sub_step : forall Θ m P P3 Ξ P' ψ Ψ' Ψtot,
  {{ Θ ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ≼[ m ] P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros Θ m P P3 Ξ P' ψ Ψ' Ψtot Hs Htg Hdec Hdt.
  exact (dec_ext_solve_sub_step_size
           (n := 2 * (size_pskl P + size_pskl P3))
           (le_n _) Hs Htg Hdec Hdt).
Qed.

(* --------------------------------------------------------------------- *)
(*  TY-mode prose-wf invariant (paper: in TY mode the against-side P0 is a
    TYPE, hence ghost-free — the mode discipline stated in prose; registry
    docs/WF-SIDE-CONDITIONS.md).  Consequence chain: the look targets are
    ∀◇-free ⟹ the eq-phase skeleton stays ∀◇-free ⟹ every ∀◇ of the final
    solve output was created by SS-GhostL / SS-GhostLF over a GUARDED body
    ⟹ [pskl_top_guarded], which feeds the TY guess-drop anchor.  SK mode
    needs NONE of this.                                                     *)
(* --------------------------------------------------------------------- *)

(** [pskl_no_top P]: no universal ghost ∀◇ anywhere (holes ◇ allowed). *)
Fixpoint pskl_no_top (P : pskl) : Prop :=
  match P with
  | pskl_tophole _ => False
  | pskl_arrow P1 P2 => pskl_no_top P1 /\ pskl_no_top P2
  | pskl_all_syn P0 => pskl_no_top P0
  | _ => True
  end.

Lemma pskl_no_top_top_guarded : forall P, pskl_no_top P -> pskl_top_guarded P.
Proof. induction P; simpl; intuition. Qed.

(** [guess^TY]'s result, read back into [pskl], has NO universal ghost at all
    — [ptyp] has no ghost constructor.  This is what keeps the ∀◇-tracking
    invariants true at the repaired SE-FlexR row, whose output is that
    result rather than the bare flexible. *)
Lemma ptyp_to_pskl_no_top : forall A, pskl_no_top (ptyp_to_pskl A).
Proof. induction A; simpl; intuition. Qed.

(* ===================================================================== *)
(*  [top_guarded]-INPUT propagation chain (replaces the [no_top] chain):   *)
(*  a wf [P0] may carry ∀◇ (over GUARDED bodies, a_wf_pskl__tophole), so   *)
(*  the coverage anchor's [pskl_top_guarded Q] must flow from              *)
(*  [pskl_top_guarded P0] (⟸ wf), NOT from [ghost_free]/[no_top].          *)
(* ===================================================================== *)

(** A guarded-headed subject stays guarded-headed through eq-solving. *)
Lemma solve_eq_guarded_head_l : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> pskl_guarded_head P -> pskl_guarded_head P'.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Hg; simpl in Hg;
    try contradiction; simpl; try exact I;
    (* flex_r : guess^TY is structural on the guarded shapes *)
    try solve [ eapply a_guess_mono_head; eassumption ].
  - (* hole_r : P'=P *) exact Hg.
  - (* tophole_r_guarded : P guarded, P∼P0⤳P' *) apply IHa_solve_eq; exact Hg.
Qed.

(** A guarded-headed subject stays guarded-headed through sub-solving. *)
Lemma solve_sub_guarded_head_l : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> pskl_guarded_head P -> pskl_guarded_head P'.
Proof.
  intros Θ m P P0 Ξ P' Hs; induction Hs; intros Hg; simpl in Hg;
    try contradiction; simpl; try exact I.
  - (* vacuous : P'=P *) exact Hg.
  - (* check : eq preserves *) eapply solve_eq_guarded_head_l; eassumption.
  - (* forall_r : same subject/result, recurse *)
    apply IHHs; exact Hg.
Qed.

(** [top_guarded] is preserved by eq-solving (∀◇ over guarded stays so). *)
Lemma solve_eq_top_guarded : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P -> pskl_top_guarded P0 -> pskl_top_guarded P'.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  - (* unit *) exact I.
  - (* var *) exact I.
  - (* flex_r : guess^TY emits no ∀◇, a fortiori all of them are guarded *)
    apply pskl_no_top_top_guarded; apply ptyp_to_pskl_no_top.
  - (* hole_l : P'=Q *) exact Hgf.
  - (* hole_r : P'=P *) exact Hnt.
  - (* arrow *) destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2];
      split; [ apply IHa_solve_eq1 | apply IHa_solve_eq2 ]; assumption.
  - (* forall : the rule closes its output *)
    apply pskl_top_guarded_close.
    apply IHa_solve_eq;
      [ apply (proj1 (pskl_top_guarded_open_rec P _ 0)); exact Hnt
      | apply (proj1 (pskl_top_guarded_open_rec Q _ 0)); exact Hgf ].
  - (* tophole_both : ∀◇P∼∀◇Q⤳∀◇P' *)
    destruct Hnt as [HgP HtP]; destruct Hgf as [HgQ HtQ].
    split; [ eapply solve_eq_guarded_head_l; [ eassumption | exact HgP ]
           | apply IHa_solve_eq; assumption ].
  - (* tophole_l_all : ∀◇P∼∀Q⤳∀(close β P') *)
    destruct Hnt as [HgP HtP].
    apply pskl_top_guarded_close.
    apply IHa_solve_eq;
      [ simpl; split; assumption
      | apply (proj1 (pskl_top_guarded_open_rec Q _ 0)); exact Hgf ].
  - (* tophole_l_guarded : ∀◇P∼(guarded Q)⤳P' *)
    destruct Hnt as [HgP HtP]; apply IHa_solve_eq; assumption.
  - (* all_l_tophole : ∀P∼∀◇Q⤳∀(close β P') *)
    destruct Hgf as [HgQ HtQ].
    apply pskl_top_guarded_close.
    apply IHa_solve_eq;
      [ apply (proj1 (pskl_top_guarded_open_rec P _ 0)); exact Hnt
      | simpl; split; assumption ].
  - (* tophole_r_guarded : (guarded P)∼∀◇Q⤳P' *)
    destruct Hgf as [HgQ HtQ]; apply IHa_solve_eq; assumption.
Qed.

(** [top_guarded] is preserved by sub-solving. *)
Lemma solve_sub_top_guarded_tg : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P -> pskl_top_guarded P0 -> pskl_top_guarded P'.
Proof.
  intros Θ m P P0 Ξ P' Hs; induction Hs; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  - (* var *) exact I.
  - (* forall_l : the rule closes its output *)
    apply pskl_top_guarded_close.
    apply IHHs;
      [ apply (proj1 (pskl_top_guarded_open_rec P _ 0)); exact Hnt | exact Hgf ].
  - (* univ_ghost_l : ∀◇P ≼ P0 ⤳ ∀◇P' *)
    destruct Hnt as [HgP HtP].
    split; [ eapply solve_sub_guarded_head_l; [ eassumption | exact HgP ]
           | apply IHHs; assumption ].
  - (* vacuous : P'=P *) exact Hnt.
  - (* check : eq preserves top_guarded *)
    eapply solve_eq_top_guarded; [ eassumption | exact Hnt | exact Hgf ].
  - (* forall_r : the output passes through *)
    apply IHHs;
      [ exact Hnt | apply (proj1 (pskl_top_guarded_open_rec B _ 0)); exact Hgf ].
  - (* arrow *)
    destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2].
    split;
      [ eapply solve_eq_top_guarded; [ eassumption | exact Hnt1 | exact Hgf1 ]
      | apply IHHs; assumption ].
  - (* ghost_l_fn : ∀◇(arrow P1' P2') *)
    destruct Hgf as [Hgf1 Hgf2].
    split; [ exact I | split;
      [ eapply solve_eq_top_guarded; [ eassumption | exact I | exact Hgf1 ]
      | apply IHHs; [ exact I | exact Hgf2 ] ] ].
  - (* ghost_l : ∀◇B, B guarded *)
    split; [ apply guarded_pskl_head; assumption | exact Hgf ].
Qed.

(** Every constraint target is [top_guarded]. *)
Definition a_cstr_tg (c : a_cstr) : Prop :=
  match c with
  | a_cstr_sub _ Q => pskl_top_guarded Q
  | a_cstr_eq Q => pskl_top_guarded Q
  end.

(** The look's targets are sub-skeletons of P0 — all [top_guarded] when P0 is. *)
Lemma a_look_top_guarded :
  (forall Θ α m P P0 Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P0 ⤳ Ξ ⨾ 𝒞 }}a ->
     pskl_top_guarded P0 -> List.Forall a_cstr_tg 𝒞) /\
  (forall Θ α P P0 Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P0 ⤳ Ξ ⨾ 𝒞 }}a ->
     pskl_top_guarded P0 -> List.Forall a_cstr_tg 𝒞).
Proof.
  apply a_looksub_lookeq_mutind; intros; simpl in *;
    (* [simpl] already unfolded top_guarded of ∀◇/arrow into conjunctions;
       split them (fresh names, don't clobber IHs) *)
    repeat match goal with
           | H : _ /\ _ |- _ =>
               let Hg := fresh "Hg" in let Ht := fresh "Ht" in destruct H as [Hg Ht]
           end;
    try (apply List.Forall_nil; fail);                        (* nil constraints *)
    try (apply List.Forall_app; split; [ apply H | apply H0 ]; tauto);  (* arrow *)
    try (repeat apply List.Forall_cons;
         solve [ assumption | exact I | apply List.Forall_nil ]);  (* [sub/eq _] *)
    try (apply H; assumption);                                (* same/∀◇-strip recursion *)
    (* EXISTS-FRESH (cluster 3): the ∀ rows' IH is the premise's own *)
    try (apply H;
         solve [ assumption
               | apply (proj1 (pskl_top_guarded_open_rec _ _ _)); assumption
               | simpl; split; assumption ]).
Qed.

(** The TY solve output is top-guarded (walk the constraints; ∀◇ targets OK). *)
Lemma solve_cstr_top_guarded_tg : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a -> pskl_top_guarded P -> List.Forall a_cstr_tg 𝒞 ->
  pskl_top_guarded P'.
Proof.
  intros Θ 𝒞 P Ξ P' Hs; induction Hs; intros Hnt Hntc.
  - exact Hnt.
  - inversion Hntc as [ | ? ? Hnt0 ]; subst; simpl in Hnt0.
    eapply solve_sub_top_guarded_tg; [ exact H | exact Hnt | exact Hnt0 ].
  - inversion Hntc as [ | ? ? Hnt0 HntC ]; subst; simpl in Hnt0.
    apply IHHs;
      [ eapply solve_eq_top_guarded; [ exact H | exact Hnt | exact Hnt0 ] | exact HntC ].
Qed.

(** ASSEMBLY: walk the constraint list — UNCONDITIONAL; [dec_ext] re-grows
    toward P with COVERAGE Ψp ⊆ Ψpost ∪ Ψc. *)
(* ⚠️ TWO PREMISES BEYOND THE PAPER (2026-08-04), both inherited from the
   per-constraint steps: the SUBJECT is top-guarded, and so is every
   constraint TARGET.  Both are wf consequences ([a_wf_pskl_top_guarded]),
   and the target one is needed only to re-establish the subject condition
   for the TAIL — the eq row folds its yield into the pattern the rest of
   the list solves on ([solve_eq_top_guarded]). *)
Lemma solve_cstr_decorate : forall Θ 𝒞 P Ξ P' ψ Ψpost Ψtot,
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P -> List.Forall a_cstr_tg 𝒞 ->
  dec_ext P' ψ Ψpost -> d_tags_skl Ψtot ψ ->
  exists Ψc Ψp, {{ 𝒞 ⊩ ψ ⤳ Ψc }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψpost `union` Ψc.
Proof.
  intros Θ 𝒞 P Ξ P' ψ Ψpost Ψtot Hsolve Htg Htgc Hdec Hdt;
    revert Ψpost Hdec; revert Htg Htgc;
    induction Hsolve; intros Htg Htgc Ψpost Hdec.
  - (* empty *) exists empty, Ψpost; split;
      [ apply a_solvetag__empty; fsetdec | split; [ exact Hdec | fsetdec ] ].
  - (* sub *)
    destruct (dec_ext_solve_sub_step H Htg Hdec Hdt)
      as [Ψi [Ψp [Hs [Hd Hu]]]].
    exists Ψi, Ψp; split;
      [ apply a_solvetag__sub; exact Hs | split; [ exact Hd | exact Hu ] ].
  - (* eq *)
    inversion Htgc as [ | ? ? Htg0 HtgC ]; subst; simpl in Htg0.
    assert (Htg'' : pskl_top_guarded P'')
      by (eapply solve_eq_top_guarded; [ exact H | exact Htg | exact Htg0 ]).
    destruct (IHHsolve Htg'' HtgC Ψpost Hdec)
      as [Ψc' [Ψp'' [Hstc [Hd'' Hu'']]]].
    destruct (dec_ext_solve_eq_step H Htg Hd'' Hdt)
      as [Ψi [Ψp [Hste [Hd Hu]]]].
    exists (Ψi `union` Ψc'), Ψp; split;
      [ eapply a_solvetag__eq; [ exact Hste | exact Hstc | reflexivity ]
      | split; [ exact Hd | clear - Hu Hu''; fsetdec ] ].
Qed.

(** DECORATING CONSTRAINT SOLVING (lemma:decorate-constraint-solving,
    subtyping-proofs.tex:95-127) — the paper's statement, proved via the ⊆
    set-membership coverage machinery and squeezed against solvetag
    soundness.  Sole hypothesis beyond the paper's: the TY mode discipline
    "the against-side is a TYPE (ghost-free)" — prose-level wf in the paper
    (docs/WF-SIDE-CONDITIONS.md); it is vacuous in SK mode. *)
Lemma a_extract_decorate : forall Θ0 NM αv M P P0 Ξ P1,
  {{ Θ0 ⊢ P ⊳[ NM , αv , M ] P0 ⤳ Ξ ↪ P1 }}a ->
  (* ⚠️ UNGUARDED since 2026-08-04 (was [NM = TY -> …]).  The decoration of
     the SOLVE now needs the constraint targets to be top-guarded in BOTH
     modes, because [solve_cstr_decorate] must re-establish its subject
     condition for the tail.  It is the same wf consequence
     ([a_wf_pskl_top_guarded]) the TY branch already relied on. *)
  pskl_top_guarded P0 ->
  forall Ψa ψa,
    a_tags_sort NM Ψa ψa ->
    ⌊ ψa ⌋ˢ = P1 ->
    exists Ξc 𝒞,
      {{ Θ0 ⊢ P ≼[ αv , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a /\
      {{ 𝒞 ⊩ ψa ⤳ Ψa }}da.
Proof.
  intros Θ0 NM αv M P P0 Ξ P1 Hext Htg0 Ψa ψa Htags Hera.
  inversion Hext; subst.
  (* H : look ;  H0 : solve 𝒞 □ Q ;  H1 : guess (output ⌊ψa⌋ˢ) *)
  eexists; eexists; split; [ exact H | ].
  assert (Hda : d_tags_skl Ψa ψa) by (inversion Htags; assumption).
  assert (Htgc : List.Forall a_cstr_tg C)
    by (eapply (proj1 a_look_top_guarded); [ exact H | exact Htg0 ]).
  assert (HtgQ : pskl_top_guarded Q)
    by (eapply solve_cstr_top_guarded_tg;
        [ exact H0 | exact I | exact Htgc ]).
  assert (Htg : NM = a_sub_mode_ty -> pskl_top_guarded Q)
    by (intros _; exact HtgQ).
  assert (Hanchor : dec_ext Q ψa empty)
    by (eapply dec_ext_guess_anchor;
        [ exact H1 | exact Htg | exact Htags | reflexivity ]).
  destruct (solve_cstr_decorate H0 I Htgc Hanchor Hda)
    as [Ψc [Ψp [Hstag [Hhole Hsub]]]].
  (* dec_ext □ ψa Ψp pins Ψp = d_tags = Ψa; soundness gives Ψc ⊆ Ψa; squeeze *)
  assert (Hsnd : Ψc [<=] Ψa) by (eapply a_solvetag_sound; [ exact Hstag | exact Hda ]).
  inversion Hhole; subst.
  - (* dec_ext__hole : Ψp = d_tags ψa = Ψa *)
    match goal with Hdtag : d_tags_skl _ ψa |- _ =>
      pose proof (d_tags_skl_det Hda Hdtag) as Hdet end.
    eapply a_solvetag_psi_cong; [ exact Hstag | clear - Hsub Hsnd Hdet; fsetdec ].
  - (* dec_ext__flex_forget : ψa a bare var ⇒ Ψa = ∅ *)
    eapply a_solvetag_psi_cong; [ exact Hstag | ].
    inversion Hda; subst;
      match goal with He : Ψa [=] empty |- _ => clear - Hsnd He; fsetdec end.
Qed.

(* ===================================================================== *)
(*  §16  MAIN: decorating algorithmic subtyping                           *)
(*  (lemma:decorating-algorithmic-subtyping, subtyping-proofs.tex:1019)   *)
(* ===================================================================== *)

Scheme a_sub_mut := Induction for a_sub Sort Prop
  with a_sub_flex_mut := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_mutind from a_sub_mut, a_sub_flex_mut.

Definition sub_decorate_concl NM M P0 Θ0 P Q Θ1 : Prop :=
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P0) ->
  {{ Θ0 ⊢[ NM | M | P0 | empty ] (pskl_to_uskl P) ⩽ Q ⊣ Θ1 }}da.

Definition sub_flex_decorate_concl NM M P0 Θ0 Ξw αf Q Θ1 : Prop :=
  a_decls Ξw ->
  {{ ⊢ (Ξw ++ Θ0) }}a ->
  {{ (Ξw ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar αf (Ξw ++ Θ0) ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) (mode_fn M)) ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P0) ->
  a_subtag_flex NM M P0 Θ0 Ξw αf Q Θ1.

(** MAIN (lemma:decorating-algorithmic-subtyping) — fully Qed.  The side
    conditions are exactly the sound-bundle's (P3): wf, the SK mode
    compatibility, and the TY "against a TYPE" ghost-freeness — the two
    mode disciplines the paper states in prose (docs/WF-SIDE-CONDITIONS.md).
    The ForallL case consumes [a_extract_decorate] (§15, Qed). *)
Theorem a_sub_decorate_bundle :
  (forall NM M P0 Θ0 P P' Θ1,
     a_sub NM M P0 Θ0 P P' Θ1 ->
     sub_decorate_concl NM M P0 Θ0 P P' Θ1) /\
  (forall NM M P0 Θ0 Ξw αf P' Θ1,
     a_sub_flex NM M P0 Θ0 Ξw αf P' Θ1 ->
     sub_flex_decorate_concl NM M P0 Θ0 Ξw αf P' Θ1).
Proof.
  apply (a_sub_sub_flex_mutind
           (fun NM M P0 Θ0 P P' Θ1 _ =>
              sub_decorate_concl NM M P0 Θ0 P P' Θ1)
           (fun NM M P0 Θ0 Ξw αf P' Θ1 _ =>
              sub_flex_decorate_concl NM M P0 Θ0 Ξw αf P' Θ1));
    unfold sub_decorate_concl, sub_flex_decorate_concl.
  - (* Infer *)
    intros NM P Θ0 Hwf HwfP0 HwfP Hmod Hgf0.
    replace P with (⌊ pskl_to_uskl P ⌋ˢ) at 2
      by apply uskl_to_pskl_pskl_to_uskl.
    apply a_subtag__infer. fsetdec.
  - (* Check : audit-F2 CLOSED — the decorated [a_subtag__check] no longer
       pins the consistency output to [B] (it existentialises it, matching the
       plain [a_consis_chk] and the paper's "output not used / ≡ B"
       convention), so we simply decorate the plain consistency premise. *)
    intros Θ0 Θ1 A B Hgfa Hgfb HgA HgB Hchk Hwf HwfP0 HwfP Hmod Hgf0.
    destruct Hchk as [P' Hcns].
    eapply a_subtag__check;
      [ exact Hgfb
      | apply pskl_to_uskl_guarded; exact HgA
      | exact HgB
      | exact (a_consis_decorate Hcns (a_wf_aenv_uniq Hwf)) ].
  - (* ForallR (exists-fresh 2026-07-31: the rule's own binder serves) *)
    intros α Θ0 Θ1 Ξ A B Hgfb Hsuf Huq Hfr Hprem IHprem Hwf HwfP0 HwfP Hmod Hgf0.
    rewrite dom_app in Hfr.
    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ exact Hgfb | exact Hsuf | exact Huq
      | rewrite dom_app;
        pose proof (ftvar_in_uskl_pskl A) as Hfa;
        clear - Hfr Hfa; fsetdec
      | ].
    eapply IHprem.
    { apply a_wf_aenv__tvar; [ clear - Hfr; fsetdec | exact Hwf ]. }
    { eapply a_wf_pskl_all_syn_open_tvar;
        [ exact HwfP0 | clear - Hfr; fsetdec ]. }
    { eapply a_wf_pskl_weaken;
        [ intros x b Hb; unfold binds; simpl; right; exact Hb
        | exact HwfP ]. }
    { intros Hsk; discriminate Hsk. }
    { intros Hty; specialize (Hgf0 Hty); simpl in Hgf0.
      unfold open_pskl_wrt_pskl; apply (proj1 (pskl_top_guarded_open_rec _ _ _)); exact Hgf0. }
  - (* UnivGhostR *)
    intros Θ0 P Hg Hwf HwfP0 HwfP Hmod Hgf0.
    replace (pskl_tophole P)
      with (pskl_tophole ⌊ pskl_to_uskl P ⌋ˢ)
      by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    apply a_subtag__univ_ghost_r;
      [ apply pskl_to_uskl_guarded; exact Hg | fsetdec ].
  - (* FlexMono *)
    intros NM M P0 Θ0 Θ1 α A Hflex IHflex Hwf HwfP0 HwfP Hmod Hgf0.
    simpl.
    apply a_subtag__flex_mono; [ | fsetdec ].
    apply IHflex.
    { constructor. }
    { simpl. exact Hwf. }
    { simpl. exact HwfP0. }
    { simpl.
      pose proof (a_wf_pskl_ftv_binds HwfP (α := α)
                  ltac:(simpl; clear; solve_notin_auto)) as Htx; exact Htx. }
    { exact Hmod. }
    { simpl. exact Hgf0. }
  - (* Arrow *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs2 IH2 Hwf HwfP0 HwfP Hmod Hgf0.
    apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b].
    apply a_wf_pskl_arrow_inv in HwfP as [HwfP1 HwfP2].
    pose proof (a_consis_decorate Hc (a_wf_aenv_uniq Hwf)) as Hct.
    destruct (a_consistag_sound_aux Hct Hwf
                ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto)
                HwfP0a
                ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP1)
                (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
      as [Hle [HwfΘm _]].
    simpl.
    eapply a_subtag__arrow with (Ψ1 := empty) (Ψ2 := empty) (Θ1 := Θ1);
      [ exact Hct
      | apply IH2;
        [ exact HwfΘm
        | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
        | eapply a_wf_pskl_isub; [ exact HwfP2 | exact Hle ]
        | intros Hsk; specialize (Hmod Hsk); simpl in Hmod;
          inversion Hmod; subst; assumption
        | intros Hty; specialize (Hgf0 Hty); simpl in Hgf0; tauto ]
      | fsetdec ].
  - (* ForallL : look-decoration + decorate-constraint-solving + KEY *)
    (* [a_sub__forall_l] is EXISTS-FRESH (campaign cluster 5), while the
       decorated [a_subtag__forall_l_*] is still cofinite, so this row
       rebuilds the family from the run's ONE opener [α0]
       ([a_extract_family_of_instance], prop_looksub.v §11) and then picks
       its own [α] for the decoration exactly as before. *)
    intros α0 NM M P0 Θ0 Θ1 P P' Ξ P1 Hne Hgor Hfr0 Hex Huq HwfP1 Hsub IHsub
      Hwf HwfP0 HwfP Hmod Hgf0.
    destruct (@a_extract_family_of_instance Θ0 NM M α0 P P0 Ξ P1 Hex
                ltac:(clear - Hfr0; solve_notin_auto)) as [L Hfam].
    assert (Hdecls : a_decls Ξ) by (eapply a_extract_decls; eauto).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros α1 Hα1. clear - Huq Hα1. destruct_uniq.
        unfold disjoint in *. fsetdec. }
    assert (Hmono : forall x (b : abind),
               binds x b Θ0 -> binds x b (Ξ ++ Θ0))
      by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
    assert (HlcP1 : lc_pskl P1) by (eapply a_wf_pskl_lc; eauto).
    simpl.
    eapply a_subtag__forall_l_untagged
      with (L := L `union` singleton α0 `union` dom Ξ `union` dom Θ0
                 `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P1)
           (Ξ := Ξ) (P1 := P1);
      [ exact Hne | exact Hgor | | exact Huq | exact HwfP1 | ].
    { intros α Hα.
      replace (⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ)
        with (open_pskl_wrt_pskl P (pskl_var_f α))
        by (rewrite uskl_to_pskl_open;
            rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      apply Hfam. clear - Hα. fsetdec. }
    intros Ψg ψg Hfr Hsort Hera.
    assert (Hlcg : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Hsort; assumption).
    destruct (atom_fresh
                (L `union` singleton α0 `union` dom Ξ `union` dom Θ0
                 `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P1)) as [α Hα].
    (* the premise is UNGUARDED now; it is a wf consequence, so it comes
       straight from [HwfP0] rather than from the mode-guarded [Hgf0] *)
    assert (HtgP0 : pskl_top_guarded P0)
      by (eapply a_wf_pskl_top_guarded; exact HwfP0).
    destruct (a_extract_decorate (Hfam α ltac:(clear - Hα; solve_notin_auto))
                HtgP0 Hsort Hera) as [Ξc [C [HDlk Hst]]].
    assert (Hαg : α `notin` ftvar_in_uskl ψg).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg). rewrite Hera.
      clear - Hα. fsetdec. }
    assert (HeqSubj :
        pskl_to_uskl (open_pskl_wrt_pskl P P1)
        = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψg)) α
            (open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α))).
    { rewrite pskl_to_uskl_open.
      rewrite (subst_uskl_in_uskl_intro α);
        [ | rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl P));
            rewrite uskl_to_pskl_pskl_to_uskl; clear - Hα; fsetdec ].
      rewrite Hera. reflexivity. }
    assert (HDsrc : {{ Θ0 ⊢
        ⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ
        ≼[ α , M ] P0 ⤳ Ξc ⨾ C }}a).
    { replace (⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ)
        with (open_pskl_wrt_pskl P (pskl_var_f α))
        by (rewrite uskl_to_pskl_open;
            rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      exact HDlk. }
    assert (Hresult :
        subst_uskl_in_uskl ψg α
          (open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α))
        = open_uskl_wrt_uskl (pskl_to_uskl P) ψg).
    { symmetry. apply subst_uskl_in_uskl_intro.
      rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl P)).
      rewrite uskl_to_pskl_pskl_to_uskl. clear - Hα. fsetdec. }
    assert (HwfOpen : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ open_pskl_wrt_pskl P P1 }}a).
    { inversion HwfP as [ | | | LP ΘP ΔP PP HbodyP HeqP | | ]; subst.
      eapply a_wf_pskl_open with (L := LP);
        [ intros α2 Hα2; eapply a_wf_pskl_weaken;
          [ exact (@binds_sub_cons _ _ _ Hmono) | apply HbodyP; auto ]
        | exact HwfP1 ]. }
    rewrite <- Hresult.
    eapply a_subtag_psi_cong;
      [ eapply a_subtag_decoration;
        [ apply IHsub;
          [ exact HwfΞΘ
          | exact HwfP0'
          | exact HwfOpen
          | exact Hmod
          | exact Hgf0 ]
        | exact HeqSubj
        | exact HDsrc
        | exact Hst
        | exact Hαg
        | clear - Hα; fsetdec
        | exact Hlcg
        | apply lc_body_uskl_wrt_uskl;
          [ eapply lc_body_uskl_all_syn_1;
            change (uskl_all_syn (pskl_to_uskl P))
              with (pskl_to_uskl (pskl_all_syn P));
            apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; exact HwfP
          | constructor ]
        | exact HwfΞΘ
        | exact HwfP0'
        | rewrite uskl_to_pskl_pskl_to_uskl; exact HwfOpen
        | exact Hmod ]
      | clear; fsetdec ].
  - (* Ghost *)
    intros M Θ0 P0 Hmghost Hwf HwfP0 HwfP Hmod Hgf0.
    simpl. apply a_subtag__ghost. fsetdec.
  - (* UnivGhostL *)
    intros M Θ0 Θ1 P0 P P' Hne Hs IH Hwf HwfP0 HwfP Hmod Hgf0.
    simpl.
    apply a_subtag__univ_ghost_l; [ exact Hne | ].
    apply IH;
      [ exact Hwf | exact HwfP0
      | apply a_wf_pskl_tophole_inv in HwfP as [_ HwfP];
        eapply a_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]
      | exact Hmod
      | exact Hgf0 ].
  - (* Flex-Solve : deposit α̂0 := α̂→β̂ and recurse on the arrow; the
       hypotheses lift into the deposited context by ⊴ (mirrors the
       corresponding a_subtag_sound_bundle case). *)
    intros NM M P0 Θ0 Θ1 Ξw α0 α β A Hne Hα Hβ Hs IH
      Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξw ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    assert (Huq : uniq (Ξw ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact HwfΞ).
    assert (Hwf0 : {{ ⊢ Θ0 }}a).
    { eapply a_wf_aenv_strip_prefix with (Ξ := Ξw ++ (α0 ~ abind_flex_mono)).
      simpl_env. exact HwfΞ. }
    assert (Hbα : binds α abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; right; left; reflexivity).
    assert (Hbβ : binds β abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; left; reflexivity).
    assert (Hwfmid : {{ ⊢ Θmid }}a).
    { unfold Θmid. apply a_wf_aenv__flex.
      { simpl. clear - Hβ Hne. simpl_env in *. fsetdec. }
      apply a_wf_aenv__flex;
        [ clear - Hα; simpl_env in *; fsetdec | exact Hwf0 ]. }
    assert (Hwfdef : {{ ⊢ ((α0 ~ abind_flex_mono_def τab) ++ Θmid) }}a).
    { apply a_wf_aenv__flex_def.
      - unfold Θmid. simpl. clear - Hα Hβ Huq. simpl_env in *. solve_uniq.
      - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var;
          [ right; left; exact Hbα | right; left; exact Hbβ ].
      - repeat constructor.
      - exact Hwfmid. }
    assert (HwfΘ' : {{ ⊢ Θ' }}a).
    { unfold Θ'. apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros α1 Hα1. unfold Θmid. simpl_env.
        clear - Huq Hα Hβ Hα1. destruct_uniq.
        unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (Hbase : Θ0 ⊴ Θ').
    { unfold Θ', Θmid.
      replace (Ξw ++ (α0 ~ abind_flex_mono_def τab)
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
        with ((Ξw ++ (α0 ~ abind_flex_mono_def τab)
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)) ++ Θ0)
        by (simpl_env; reflexivity).
      apply a_isub_weaken_suffix;
        [ apply a_wf_aenv_lc_aenv; exact Hwf0 | ].
      apply a_suffix_app; [ auto using a_decls_suffix | ].
      apply (a_suffix__cons α0);
        [ apply (a_suffix__cons β);
            [ apply (a_suffix__cons α);
                [ apply a_suffix__nil | constructor ]
            | constructor ]
        | constructor ]. }
    assert (Hbα0' : binds α0 (abind_flex_mono_def τab) Θ').
    { unfold Θ'. unfold binds. apply in_or_app. right. left. reflexivity. }
    assert (Hlift : (Ξw ++ (α0 ~ abind_flex_mono) ++ Θ0) ⊴ Θ').
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb. right; left.
        unfold Θ'. unfold binds. apply in_or_app. left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α0); apply a_decls__nil | | exact Hbase ].
      intros α1 Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> _] | Hb'];
        [ right; right; exists τab; exact Hbα0' | inversion Hb' ]. }
    assert (HwfP0' : {{ Θ' ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_isub; eauto).
    assert (Hwfarr : {{ Θ' ⨟ empty ⊢ₚₛ
                       pskl_arrow (pskl_var_f α) (pskl_var_f β) }}a).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var;
        right; left;
        (unfold Θ'; unfold binds; apply in_or_app; right; simpl;
         right; auto). }
    eapply a_subtag_flex__solve;
      [ exact Hne | exact Hα | exact Hβ | ].
    exact (IH HwfΘ' HwfP0' Hwfarr Hmod Hgf0).
  - (* Flex-Assign : merge and re-enter the decorated MAIN judgment with
       the substituted subject (audit F1; mirrors the sound-bundle case's
       hypothesis transport). *)
    intros NM M P0 Θ0 Θ1 Ξw α β τ A Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    assert (Hwfcons : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; eauto).
    inversion Hwfcons as [ | | βz τz Θz HβΘ0 Hwfτ Hm Hwf0 | | | ]; subst.
    assert (HβΞΘ0 : β `notin` dom (Ξw ++ Θ0)).
    { pose proof (a_wf_aenv_uniq HwfΞ) as Huq.
      clear - Huq. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (HwfΞΘ0 : {{ ⊢ (Ξw ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hwfpaint : {{ (Ξw ++ Θ0) ⨟ empty ⊢ₚₛ ptyp_to_pskl τ }}a).
    { apply a_scope_pskl_of_ptyp_vis;
        [ apply mono_ptyp_lc; exact Hm | ].
      intros α0 Hα0.
      pose proof (a_wf_ptyp_ftv_tvarish Hwfτ Hα0) as Ht.
      destruct Ht as [Hb | [Hb | [τ1 Hb]]];
        [ left | right; left | right; right; exists τ1 ];
        unfold binds in *; apply in_or_app; auto. }
    assert (HwfP0' : {{ (Ξw ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β P0 }}a).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ exact HwfP0 | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint
        | clear; fsetdec ]. }
    assert (Hwfvarsub : {{ (Ξw ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α) }}a).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ apply a_wf_pskl__var; exact Hαb
        | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint
        | clear; fsetdec ]. }
    apply a_subtag_flex__assign; [ exact Hβ1 | ].
    apply (IH HwfΞΘ0 HwfP0' Hwfvarsub);
      [ intro HSK; specialize (Hmod HSK);
        rewrite <- pskl_to_bskl_inh_subst_mono;
          [ apply mod_comp_sk_subst_mono; [ exact Hmod | exact Hm ]
          | exact Hm ]
      | intros Hty; specialize (Hgf0 Hty);
        apply pskl_top_guarded_subst_mono; [ exact Hgf0 | exact Hm ] ].
  - (* Flex-Depend : β̂ joins the suffix at the Θ0-adjacent end; the
       premise context is the conclusion's up to associativity. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hin Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__depend; [ exact Hne | exact Hin | ].
    apply IH.
    { apply a_decls_app;
        [ exact Hsuf | apply (a_decls__cons β); apply a_decls__nil ]. }
    { simpl_env. simpl_env in HwfΞ. exact HwfΞ. }
    { simpl_env. simpl_env in HwfP0. exact HwfP0. }
    { simpl_env. simpl_env in Hαb. exact Hαb. }
    { exact Hmod. }
    { exact Hgf0. }
  - (* Flex-Skip : strip the walked entry (P0 avoids it) and re-cons it
       on the output. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__skip;
      [ exact Hne | exact Hnin | exact Hβ1 | ].
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; eauto. }
    { eapply a_binds_tvar_strip_mid;
        [ exact Hαb
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]. }
    { exact Hmod. }
    { exact Hgf0. }
  - (* Flex-SkipRigid : as Flex-Skip with a rigid head. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__skip_rigid;
      [ exact Hne | exact Hnin | exact Hβ1 | ].
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; eauto. }
    { eapply a_binds_tvar_strip_mid;
        [ exact Hαb
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]. }
    { exact Hmod. }
    { exact Hgf0. }
  - (* Flex-SkipTmVar : the head is a TERM entry, so the strip lemmas'
       disequalities are all [discriminate]. *)
    intros NM M P0 Θ0 Θ1 Ξw α x Q A Hnin Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    (* a TERM entry is never [a_binds_tvar], so [P0] cannot mention it — that
       is what supplies [a_wf_pskl_strip_mid]'s freshness, which the rule does
       not carry (nor does the twin walk's [Assign-SkipTmVar]). *)
    assert (Hxfr : x `notin` ftvar_in_pskl P0).
    { intro Hin.
      assert (Huq : uniq (Ξw ++ (x ~ abind_var_typ Q) ++ Θ0))
        by (apply a_wf_aenv_uniq; exact HwfΞ).
      assert (Hbx : binds x (abind_var_typ Q) (Ξw ++ (x ~ abind_var_typ Q) ++ Θ0))
        by (apply binds_app_3; apply binds_app_2;
            unfold binds; simpl; left; reflexivity).
      pose proof (a_wf_pskl_ftv_binds HwfP0 Hin) as Hbt.
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hbx Hb Huq) as Hc;
        discriminate Hc. }
    apply a_subtag_flex__skip_tm_var.
    { exact Hnin. }
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ]. }
    { eapply a_binds_tvar_strip_mid;
        [ exact Hαb
        | intro He; discriminate He
        | intro He; discriminate He
        | intros τ1 He; discriminate He ]. }
    { exact Hmod. }
    { exact Hgf0. }
  - (* Flex-SkipTmVar (skl) *)
    intros NM M P0 Θ0 Θ1 Ξw α x Q A Hnin Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    (* a TERM entry is never [a_binds_tvar], so [P0] cannot mention it — that
       is what supplies [a_wf_pskl_strip_mid]'s freshness, which the rule does
       not carry (nor does the twin walk's [Assign-SkipTmVar]). *)
    assert (Hxfr : x `notin` ftvar_in_pskl P0).
    { intro Hin.
      assert (Huq : uniq (Ξw ++ (x ~ abind_var_skl Q) ++ Θ0))
        by (apply a_wf_aenv_uniq; exact HwfΞ).
      assert (Hbx : binds x (abind_var_skl Q) (Ξw ++ (x ~ abind_var_skl Q) ++ Θ0))
        by (apply binds_app_3; apply binds_app_2;
            unfold binds; simpl; left; reflexivity).
      pose proof (a_wf_pskl_ftv_binds HwfP0 Hin) as Hbt.
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hbx Hb Huq) as Hc;
        discriminate Hc. }
    apply a_subtag_flex__skip_tm_skl.
    { exact Hnin. }
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ]. }
    { eapply a_binds_tvar_strip_mid;
        [ exact Hαb
        | intro He; discriminate He
        | intro He; discriminate He
        | intros τ1 He; discriminate He ]. }
    { exact Hmod. }
    { exact Hgf0. }
Qed.

(** L-A corollary: NO TY side condition — [pskl_top_guarded P0] is DERIVED
    from the wf hypothesis [HwfP0] ([a_wf_pskl__tophole] admits ∀◇ only over a
    guarded body), exactly as the paper's [thm:sound-subtyping] carries no P0
    condition beyond well-formedness.  SK uses the paper's [P0 :sk M]. *)
Lemma a_sub_decorate : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  {{ Θ0 ⊢[ NM | M | P0 | empty ] (pskl_to_uskl P) ⩽ P' ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Θ0 P P' Θ1 Hrun Hwf HwfP0 HwfP Hmod.
  eapply (proj1 a_sub_decorate_bundle); try eassumption.
  - intros HSK; apply a_sk_mode_compat_mod_comp_sk; apply Hmod; exact HSK.
  - intros _; eapply a_wf_pskl_top_guarded; exact HwfP0.
Qed.

(* ===================================================================== *)
(*  §17  thm:sound-subtyping = L-A ∘ L-B                                  *)
(*                                                                        *)
(*  An algorithmic subtyping run yields a (refinement-valid) solution to  *)
(*  its subtyping problem: the output context extends the input, the      *)
(*  input skeleton fills into the output, and the declarative typsub      *)
(*  holds in the output context.  Stated against refinement-valid         *)
(*  solutions per docs/PAPER-GAPS.md (the 2-condition solution notion is  *)
(*  false under capture; soundness yields the refinement conjunct).       *)
(* ===================================================================== *)

Theorem a_sub_sound : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* paper's [P0 :sk M] *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* paper's [P0 :ty M] *)
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt,
    bskl_to_pskl Qt = P' /\
    ({{ empty ⨟ Θ1 ⊢ˢ[ NM | M ] (pskl_to_uskl P) ⩽ Qt }}ad) /\
    {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad.
Proof.
  intros NM M P0 Θ0 P P' Θ1 Hrun Hwf HwfP0 HwfP Hmod Hgf.
  pose proof (a_sub_decorate Hrun Hwf HwfP0 HwfP Hmod) as Htag.
  destruct ((proj1 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
              Hwf
              ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto)
              HwfP0
              ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP)
              ltac:(intros HSK; apply a_sk_mode_compat_mod_comp_sk;
                    apply Hmod; exact HSK)
              Hgf)
    as (Hisub & Hwf1 & Qt & HeQt & Hjoin & Hrs).
  (* ⚙ the bundle now concludes the LEAF-VALID join (hand-off §6.2); this
     theorem's own statement keeps the PLAIN one, recovered here.  When
     [ad_pat] / [ad_sd_typing] switch to [_gv], this is where the [_gv]
     is handed on instead. *)
  destruct Hjoin as [njoin Hjoin]; apply ad_pat_sub_of_fuel in Hjoin.
  exact (conj Hisub (conj Hwf1
           (ex_intro _ Qt (conj HeQt (conj Hjoin
              Hrs))))).
Qed.

(** ⭐ THE LEAF-VALID COMPANION (hand-off §6.2).  Identical to
    [a_sub_sound] except that it hands the bundle's join on as
    [ad_pat_sub_v] instead of forgetting it — which is what [ad_pat] /
    [ad_sd_typing]'s base rows now demand, and hence what [a_pat_sound] /
    [a_typing_sound] consume.  The PLAIN version stays for the ~10 consumers
    that only need a declarative subtyping derivation. *)
Theorem a_sub_sound_v : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt,
    bskl_to_pskl Qt = P' /\
    {{ empty ⨟ Θ1 ⊢ˢ[ NM | M ] (pskl_to_uskl P) ⩽ Qt }}ad /\
    {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad.
Proof.
  intros NM M P0 Θ0 P P' Θ1 Hrun Hwf HwfP0 HwfP Hmod Hgf.
  pose proof (a_sub_decorate Hrun Hwf HwfP0 HwfP Hmod) as Htag.
  destruct ((proj1 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
              Hwf
              ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto)
              HwfP0
              ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP)
              ltac:(intros HSK; apply a_sk_mode_compat_mod_comp_sk;
                    apply Hmod; exact HSK)
              Hgf)
    as (Hisub & Hwf1 & Qt & HeQt & Hjoin & Hrs).
  destruct Hjoin as [ njoin Hjoin ].
  exact (conj Hisub (conj Hwf1
           (ex_intro _ Qt (conj HeQt (conj (ad_pat_sub_of_fuel Hjoin)
              Hrs))))).
Qed.
