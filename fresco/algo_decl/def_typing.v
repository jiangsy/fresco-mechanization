Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.

Set Implicit Arguments.

Open Scope fresco_ad_scope.

Reserved Notation "{{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad"
  (at level 0, M at level 0, e at level 74, Q at level 74,
   format "'{{'  Θ  ⊢ˢ[  M  ]  e  ⦂  Q  '}}ad'").
Reserved Notation "{{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad"
  (at level 0, M at level 0, e at level 74, B at level 74,
   format "'{{'  Θ  ⊢ˢᵈ[  M  ]  e  ⦂  B  '}}ad'").

Inductive ad_pat : mode -> aenv -> exp -> bskl -> Prop :=
| ad_pat__unit : forall Θ m Q,
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    ad_pat_sub a_sub_mode_sk m empty Θ uskl_unit Q ->
    {{ Θ ⊢ˢ[ m ] exp_unit ⦂ Q }}ad
| ad_pat__var : forall Θ m x (P : pskl) b Q,

    binds x b Θ ->
    abind_to_pskl b = Some P ->
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    ad_pat_sub a_sub_mode_sk m empty Θ
      (bskl_to_uskl (pskl_to_bskl_syn P)) Q ->
    {{ Θ ⊢ˢ[ m ] (exp_var_f x) ⦂ Q }}ad
| ad_pat__anno : forall Θ m e (A : ptyp) Q,

    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    ad_pat_sub a_sub_mode_sk m empty Θ
      (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl A))) Q ->
    {{ Θ ⊢ˢ[ m ] (exp_anno e A) ⦂ Q }}ad
| ad_pat__freeze : forall Θ e P,
    {{ Θ ⊢ˢ[ mode_ti ] e ⦂ (pskl_to_bskl_syn P) }}ad ->
    {{ Θ ⊢ˢ[ mode_tc ] (exp_freeze e) ⦂ (pskl_to_bskl_syn P) }}ad
| ad_pat__abs : forall L Θ m e P Q,
    m <> mode_tc ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    mod_comp_sk (bskl_arrow (pskl_to_bskl_inh P) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_skl P) ++ Θ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}ad) ->
    {{ Θ ⊢ˢ[ m ] (exp_abs e) ⦂ (bskl_arrow (pskl_to_bskl_inh P) Q) }}ad
| ad_pat__abs_anno : forall L Θ m e (A : ptyp) (B : btyp) Q,
    m <> mode_tc ->
    a_wf_ptyp Θ A ->
    btyp_to_ptyp B = A ->
    mod_comp_sk (bskl_arrow (btyp_to_bskl B) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}ad) ->
    {{ Θ ⊢ˢ[ m ] (exp_abs_anno A e) ⦂ (bskl_arrow (btyp_to_bskl B) Q) }}ad
| ad_pat__app : forall Θ m e1 e2 P (Q1 Q2 : bskl),
    {{ Θ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q1 }}ad ->
    {{ Θ ⊢ˢ[ mode_fn m ] e1 ⦂ (bskl_arrow Q1 Q2) }}ad ->
    {{ Θ ⊢ˢ[ m ] (exp_app e1 e2) ⦂ Q2 }}ad
| ad_pat__abs_check : forall L Θ e P,
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_skl pskl_ghost) ++ Θ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}ad) ->
    {{ Θ ⊢ˢ[ mode_tc ] (exp_abs e)
      ⦂ (bskl_univ_ghost (bskl_arrow bskl_ghost (pskl_to_bskl_syn P))) }}ad
| ad_pat__abs_anno_check : forall L Θ e A P,
    a_wf_ptyp Θ A ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}ad) ->
    {{ Θ ⊢ˢ[ mode_tc ] (exp_abs_anno A e)
      ⦂ (bskl_univ_ghost (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A))
                                  (pskl_to_bskl_syn P))) }}ad
where "{{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad" := (ad_pat M Θ e Q) : fresco_ad_scope.

Inductive ad_sd_typing : mode -> aenv -> exp -> btyp -> Prop :=
| ad_sd_typing__unit : forall Θ m B,
    ad_pat_sub a_sub_mode_ty m empty Θ
      (ptyp_to_uskl_syn ptyp_unit) (btyp_to_bskl B) ->
    {{ Θ ⊢ˢᵈ[ m ] exp_unit ⦂ B }}ad
| ad_sd_typing__var : forall Θ m x A B,
    binds x (abind_var_typ A) Θ ->
    ad_pat_sub a_sub_mode_ty m empty Θ
      (ptyp_to_uskl_syn A) (btyp_to_bskl B) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_var_f x) ⦂ B }}ad
| ad_sd_typing__anno : forall Θ m e A B,
    a_wf_ptyp Θ A ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) }}ad ->
    ad_pat_sub a_sub_mode_ty m empty Θ
      (ptyp_to_uskl_syn A) (btyp_to_bskl B) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_anno e A) ⦂ B }}ad
| ad_sd_typing__freeze : forall Θ e A B,
    {{ Θ ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn B) }}ad ->
    {{ Θ ⊢ B ≡ᵗ A }}a ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A) }}ad
| ad_sd_typing__abs_check_step : forall L Θ e B,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⊢ˢᵈ[ mode_tc ] (exp_abs e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B) }}ad
| ad_sd_typing__abs_check_base : forall L Θ e A B,
    a_wf_ptyp Θ A ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}ad
| ad_sd_typing__abs_anno_check_step : forall L Θ A e B,

    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B) }}ad
| ad_sd_typing__abs_anno_check_base : forall L Θ e A A' B,
    a_wf_ptyp Θ A ->
    {{ Θ ⊢ A ≡ᵗ A' }}a ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e)
      ⦂ (btyp_arrow (ptyp_to_btyp_inh A') B) }}ad
| ad_sd_typing__abs : forall L Θ m e A B,
    m <> mode_tc ->
    a_wf_ptyp Θ A ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}ad) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}ad
| ad_sd_typing__abs_anno : forall L Θ m e A A' B1 B2,
    m <> mode_tc ->
    a_wf_ptyp Θ A ->
    {{ Θ ⊢ A ≡ᵗ A' }}a ->
    btyp_to_ptyp B1 = A' ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2 }}ad) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2) }}ad
| ad_sd_typing__app : forall Θ m e1 e2 P A2 B1 B2,
    {{ Θ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) }}ad ->
    {{ Θ ⊢ˢᵈ[ (mode_fn m) ] e1 ⦂ (btyp_arrow B1 B2) }}ad ->
    {{ Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ A2 }}a ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh A2) }}ad ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_app e1 e2) ⦂ B2 }}ad
where "{{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad" := (ad_sd_typing M Θ e B) : fresco_ad_scope.
