(** Frost algorithmic-system definitions — RESTARTED against the finalized
    paper (appendices/full-algo-spec.tex, sections/algorithmic.tex).

    The algorithmic system is UNCOLOURED: every judgment ranges over
    [ptyp] / [pskl] — never the coloured [btyp] / [bskl], which belong to the
    declarative system.  Painting to the coloured sorts happens only at the
    soundness/completeness bridge.

    Flexible variables [α̂] are atoms bound [abind_flex_mono] /
    [abind_flex_mono_def τ] in the ordered algorithmic context [Θ] (paper
    entries [α̂] / [α̂ := τ]); rigid variables are [abind_tvar].  The paper's
    [Θ, e] cons-on-the-right is the list HEAD here (contexts grow at the
    head). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.

Set Implicit Arguments.

Reserved Notation "Θ ⊢ₐ[ P0 ] P '~ᴬ' Q ⊣ Θ'"
  (at level 70, P0 at level 0, P at level 0, Q at level 0, Θ' at level 0,
   no associativity).
Reserved Notation "Θ ⊢ₐ[ N | m | P0 ] P ⊑ᴬ Q ⊣ Θ'"
  (at level 70, N at level 0, m at level 0, P0 at level 0, P at level 0,
   Q at level 0, Θ' at level 0, no associativity).
Reserved Notation "Θ ⊢ₐ[ m ; P0 ] e ⇨ Q ⊣ Θ'"
  (at level 70, m at level 0, P0 at level 0, e at level 0, Q at level 0,
   Θ' at level 0, no associativity).
Reserved Notation "Θ ⊢ₐ[ m ; P0 ] e ⦂ B ⊣ Θ'"
  (at level 70, m at level 0, P0 at level 0, e at level 0, B at level 0,
   Θ' at level 0, no associativity).

(* ===================================================================== *)
(*  Contexts (paper entries  e ::= α | x:P | α̂ | α̂ := τ)                *)
(* ===================================================================== *)

Inductive abind : Set :=
| abind_tvar : abind
| abind_var_typ : ptyp -> abind
(* Term variable bound with a SKELETON (paper entry [x : P]; skeleton
   inference binds skeletons, typing binds types — both are the paper's
   single [x:P] entry with types embedded). *)
| abind_var_skl : pskl -> abind
| abind_flex_mono : abind
| abind_flex_mono_def : ptyp -> abind.

Definition aenv : Set := list (atom * abind).

(** Suffixes  Ξ ::= · | Ξ,α̂ | Ξ,α̂:=τ  (paper alg-syntax). *)
Inductive a_suffix_binding : abind -> Prop :=
| a_suffix_binding__flex_mono :
    a_suffix_binding abind_flex_mono
| a_suffix_binding__flex_mono_def : forall A,
    a_suffix_binding (abind_flex_mono_def A).

Inductive a_suffix : aenv -> Prop :=
| a_suffix__nil : a_suffix nil
| a_suffix__cons : forall a b Ξ,
    a_suffix Ξ ->
    a_suffix_binding b ->
    a_suffix ((a ~ b) ++ Ξ).

(** Context well-formedness [Θ ⊢ ctx] (paper app:decl-in-algo-context). *)
Inductive a_wf_aenv : aenv -> Prop :=
| a_wf_aenv__nil : a_wf_aenv nil
| a_wf_aenv__cons : forall a b Θ,
    a_wf_aenv Θ ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ b) ++ Θ).

(* Well-scopedness placeholders: the restart tracks local closure only; the
   context-sensitive strengthening (flex vars bound in [Θ], defs in scope)
   is introduced with the wf metatheory when the paper's proofs need it. *)
Inductive a_wf_ptyp : aenv -> ptyp -> Prop :=
| a_wf_ptyp__decl : forall Θ A,
    lc_ptyp A ->
    a_wf_ptyp Θ A.

Inductive a_wf_pskl : aenv -> pskl -> Prop :=
| a_wf_pskl__decl : forall Θ P,
    lc_pskl P ->
    a_wf_pskl Θ P.

(* ===================================================================== *)
(*  Mode/input-skeleton compatibility  skmod[TY] / skmod[SK]              *)
(*  (algorithmic.tex:239-244, 442-444)                                    *)
(* ===================================================================== *)

Inductive a_ty_mode_compat : mode -> pskl -> Prop :=
| a_ty_mode_compat__ti :                                  (* skmod[TY] □ TI *)
    a_ty_mode_compat mode_ti pskl_hole
| a_ty_mode_compat__tc : forall A,                        (* skmod[TY] A TC *)
    (* the TC input is a TYPE [A], embedded into [pskl] *)
    a_ty_mode_compat mode_tc (ptyp_to_pskl A)
| a_ty_mode_compat__fn : forall M P Q,                    (* skmod[TY] (P→Q) (FN M) *)
    a_ty_mode_compat M Q ->
    a_ty_mode_compat (mode_fn M) (pskl_arrow P Q).

Inductive a_sk_mode_compat : mode -> pskl -> Prop :=
| a_sk_mode_compat__ti :                                  (* skmod[SK] □ TI *)
    a_sk_mode_compat mode_ti pskl_hole
| a_sk_mode_compat__tc :                                  (* skmod[SK] □ TC *)
    a_sk_mode_compat mode_tc pskl_hole
| a_sk_mode_compat__fn : forall M P Q,                    (* skmod[SK] (P→Q) (FN M) *)
    a_sk_mode_compat M Q ->
    a_sk_mode_compat (mode_fn M) (pskl_arrow P Q).

(** Sorts  N ::= TY | SK  (subtyping annotation). *)
Inductive a_sub_mode : Set :=
| a_sub_mode_ty : a_sub_mode
| a_sub_mode_sk : a_sub_mode.

(* [a_flex Θ P]: [P] is a (bound) flexible variable [α̂].  [a_non_flex Θ P]
   (paper [nonflex{P}]): [P] is locally closed and NOT a flexible variable. *)
Inductive a_flex : aenv -> pskl -> Prop :=
| a_flex__var : forall Θ α,
    binds α abind_flex_mono Θ ->
    a_flex Θ (pskl_var_f α)
| a_flex__var_def : forall Θ α τ,
    binds α (abind_flex_mono_def τ) Θ ->
    a_flex Θ (pskl_var_f α).

Definition a_non_flex (Θ : aenv) (P : pskl) : Prop :=
  lc_pskl P /\ ~ a_flex Θ P.

(* ===================================================================== *)
(*  guessMono  (full-algo-spec.tex:479-491)                               *)
(*  [guessMono P = (Ξ; A)]: fill each ghost with a fresh flexible          *)
(*  variable, drop universal ghosts.  [guess[SK] P = (·; P)] is [a_guess]. *)
(*  NB: freshness of the generated [Ξ] is not carried by the relation;     *)
(*  proofs needing it add an explicit freshness premise (paper: "fresh").  *)
(* ===================================================================== *)

Inductive a_guess_mono : aenv -> pskl -> aenv -> ptyp -> Prop :=
| a_guess_mono__hole : forall Θ α,                            (* □ ↦ fresh α̂ *)
    a_guess_mono Θ pskl_hole ((α ~ abind_flex_mono) ++ nil) (ptyp_var_f α)
| a_guess_mono__tophole : forall Θ P Ξ A,                     (* ⫯.P ↦ guess P *)
    a_guess_mono Θ P Ξ A ->
    a_guess_mono Θ (pskl_tophole P) Ξ A
| a_guess_mono__var : forall Θ α,                             (* α / α̂ ↦ (·; α) *)
    a_guess_mono Θ (pskl_var_f α) nil (ptyp_var_f α)
| a_guess_mono__unit : forall Θ,
    a_guess_mono Θ pskl_unit nil ptyp_unit
| a_guess_mono__arrow : forall Θ P Q Ξ1 Ξ2 A B,
    a_guess_mono Θ P Ξ1 A ->
    a_guess_mono Θ Q Ξ2 B ->
    a_guess_mono Θ (pskl_arrow P Q) (Ξ1 ++ Ξ2) (ptyp_arrow A B)
| a_guess_mono__forall : forall L Θ P Ξ A,
    (forall α, α `notin` L ->
       a_guess_mono Θ (open_pskl_wrt_pskl P (pskl_var_f α)) Ξ
         (open_ptyp_wrt_ptyp A (ptyp_var_f α))) ->
    a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all A).

(** [guess[N]{Q} = (Ξ'; Q')] (full-algo-spec.tex:1000): [guess[SK]] is the
    identity; [guess[TY]] is [guessMono] read back into [pskl]. *)
Inductive a_guess : a_sub_mode -> pskl -> aenv -> pskl -> Prop :=
| a_guess__sk : forall Q,
    a_guess a_sub_mode_sk Q nil Q
| a_guess__ty : forall Q Ξ A,
    a_guess_mono nil Q Ξ A ->
    a_guess a_sub_mode_ty Q Ξ (ptyp_to_pskl A).

(* ===================================================================== *)
(*  Constraint collection (paper fig:poly-info-extraction)                *)
(*  C ::= · | sub_M(P) | eq(P), C                                         *)
(*  NO refresh: the finalized paper's LS-Var / LE-Var emit the constraint  *)
(*  directly ("WT: I don't need refresh").                                 *)
(* ===================================================================== *)

Inductive a_cstr : Set :=
| a_cstr_sub : mode -> pskl -> a_cstr
| a_cstr_eq : pskl -> a_cstr.
Definition a_cstrs : Set := list a_cstr.

Reserved Notation "P ≼[ α , m ] P' ⤳ Ξ ⨾ C"
  (at level 75, α at level 0, m at level 0, P' at level 74, Ξ at level 0,
   C at level 74, no associativity).
Reserved Notation "P ∼[ α ] P' ⤳ Ξ ⨾ C"
  (at level 75, α at level 0, P' at level 74, Ξ at level 0, C at level 74,
   no associativity).

Inductive a_looksub : atom -> mode -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_looksub__var : forall α m P,                 (* LS-Var *)
    (pskl_var_f α) ≼[ α , m ] P ⤳ nil ⨾ (a_cstr_sub m P :: nil)
| a_looksub__absent : forall α m P P',           (* LS-Absent *)
    α `notin` ftvar_in_pskl P ->
    P ≼[ α , m ] P' ⤳ nil ⨾ nil
| a_looksub__vacuous : forall α m P,             (* LS-Vacuous: RHS is □ *)
    P ≼[ α , m ] pskl_hole ⤳ nil ⨾ nil
| a_looksub__check : forall α A B Ξ C,           (* LS-Check *)
    A <> pskl_var_f α ->
    guarded_pskl A ->
    guarded_pskl B ->
    A ∼[ α ] B ⤳ Ξ ⨾ C ->
    A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C
| a_looksub__forall_r : forall L α A B Ξ C,      (* LS-ForallR *)
    (forall β, β `notin` L ->
       A ≼[ α , mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C) ->
    A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C
| a_looksub__arrow : forall α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,   (* LS-Arrow *)
    P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 ->
    P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 ->
    (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ] (pskl_arrow P1' P2')
        ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2)
| a_looksub__forall_l : forall L α m P P' Ξ C,   (* LS-ForallL *)
    (forall β, β `notin` L ->
       (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ α , m ] P' ⤳ Ξ ⨾ C) ->
    (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C
| a_looksub__univ_ghost_l : forall α m P P' Ξ C, (* LS-UnivGhostL *)
    P ≼[ α , m ] P' ⤳ Ξ ⨾ C ->
    (pskl_tophole P) ≼[ α , m ] P' ⤳ Ξ ⨾ C

with a_lookeq : atom -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_lookeq__var : forall α P,                    (* LE-Var *)
    (pskl_var_f α) ∼[ α ] P ⤳ nil ⨾ (a_cstr_eq P :: nil)
| a_lookeq__absent : forall α P P',              (* LE-Absent *)
    α `notin` ftvar_in_pskl P ->
    P ∼[ α ] P' ⤳ nil ⨾ nil
| a_lookeq__vacuous : forall α P,                (* LE-Vacuous: RHS is □ *)
    P ∼[ α ] pskl_hole ⤳ nil ⨾ nil
| a_lookeq__flex_r : forall α P β γ,             (* LE-FlexR (β̂ a flex var) *)
    P <> pskl_var_f α ->
    α `in` ftvar_in_pskl P ->
    P ∼[ α ] (pskl_var_f β) ⤳ ((γ ~ abind_flex_mono) ++ nil)
        ⨾ (a_cstr_eq (pskl_var_f γ) :: nil)
| a_lookeq__arrow : forall α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,      (* LE-Arrow *)
    P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 ->
    P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 ->
    (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2') ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2)
| a_lookeq__forall_inh : forall L α P P' Ξ C,    (* LE-ForallInh *)
    (forall β, β `notin` L ->
       (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
         (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C) ->
    (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C
| a_lookeq__forall_syn : forall L α P P' Ξ C,    (* LE-ForallSyn *)
    (forall β, β `notin` L ->
       (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C) ->
    (pskl_all_syn P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost : forall α P P' Ξ C,      (* LE-UnivGhost *)
    P ∼[ α ] P' ⤳ Ξ ⨾ C ->
    (pskl_tophole P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost1 : forall L α P P' Ξ C,   (* LE-UnivGhost1 *)
    (forall β, β `notin` L ->
       (pskl_tophole P) ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C) ->
    (pskl_tophole P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost2 : forall α P P' Ξ C,     (* LE-UnivGhost2 *)
    guarded_pskl P' ->
    P ∼[ α ] P' ⤳ Ξ ⨾ C ->
    (pskl_tophole P) ∼[ α ] P' ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost_r : forall α P P' Ξ C,    (* LE-UnivGhostR *)
    P <> pskl_var_f α ->
    guarded_pskl P ->
    P ∼[ α ] P' ⤳ Ξ ⨾ C ->
    P ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C
where "P ≼[ α , m ] P' ⤳ Ξ ⨾ C" := (a_looksub α m P P' Ξ C) : type_scope
  and "P ∼[ α ] P' ⤳ Ξ ⨾ C" := (a_lookeq α P P' Ξ C) : type_scope.

(* ===================================================================== *)
(*  Constraint solving (paper fig:constraint-solving)                     *)
(*  [Θ] threads only what the flex rules need ([binds α̂] checks); the      *)
(*  paper's judgments are context-free because [α̂] is syntactically        *)
(*  distinct there.                                                       *)
(* ===================================================================== *)

Reserved Notation "Θ ⊢ₛ P ≼[ m ] Q ⤳ P'"
  (at level 75, P at level 74, m at level 0, Q at level 74, P' at level 74,
   no associativity).
Reserved Notation "Θ ⊢ₑ P ∼ Q ⤳ P'"
  (at level 75, P at level 74, Q at level 74, P' at level 74, no associativity).

Inductive a_solve_sub : aenv -> mode -> pskl -> pskl -> pskl -> Prop :=
| a_solve_sub__var : forall Θ m X Q,             (* SS-Var + SS-Flex *)
    Θ ⊢ₛ (pskl_var_f X) ≼[ m ] Q ⤳ (pskl_var_f X)
| a_solve_sub__forall_l : forall L Θ m P Q P',   (* SS-ForallL *)
    (forall β, β `notin` L ->
       Θ ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ m ] Q
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q ⤳ (pskl_all_syn P')
| a_solve_sub__univ_ghost_l : forall Θ m P Q P', (* SS-UnivGhostL *)
    Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
    Θ ⊢ₛ (pskl_tophole P) ≼[ m ] Q ⤳ (pskl_tophole P')
| a_solve_sub__vacuous : forall Θ m P,           (* SS-Vacuous: RHS is □ *)
    Θ ⊢ₛ P ≼[ m ] pskl_hole ⤳ P
| a_solve_sub__check : forall Θ P Q P',          (* SS-Check *)
    guarded_pskl P ->
    guarded_pskl Q ->
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₛ P ≼[ mode_tc ] Q ⤳ P'
| a_solve_sub__forall_r : forall L Θ A B P',     (* SS-ForallR *)
    (forall β, β `notin` L ->
       Θ ⊢ₛ A ≼[ mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ P') ->
    Θ ⊢ₛ A ≼[ mode_tc ] (pskl_all_syn B) ⤳ P'
| a_solve_sub__arrow : forall Θ m P1 P2 Q1 Q2 P1' P2',       (* SS-Arrow *)
    Θ ⊢ₑ P1 ∼ Q1 ⤳ P1' ->
    Θ ⊢ₛ P2 ≼[ m ] Q2 ⤳ P2' ->
    Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
         ⤳ (pskl_arrow P1' P2')
| a_solve_sub__ghost_l_fn : forall Θ m Q1 Q2 P1' P2',        (* SS-GhostLF *)
    Θ ⊢ₑ pskl_hole ∼ Q1 ⤳ P1' ->
    Θ ⊢ₛ pskl_hole ≼[ m ] Q2 ⤳ P2' ->
    Θ ⊢ₛ pskl_hole ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
         ⤳ (pskl_tophole (pskl_arrow P1' P2'))
| a_solve_sub__ghost_l : forall Θ B,             (* SS-GhostL *)
    guarded_pskl B ->
    Θ ⊢ₛ pskl_hole ≼[ mode_tc ] B ⤳ (pskl_tophole B)

with a_solve_eq : aenv -> pskl -> pskl -> pskl -> Prop :=
| a_solve_eq__unit : forall Θ,                   (* SE-Unit *)
    Θ ⊢ₑ pskl_unit ∼ pskl_unit ⤳ pskl_unit
| a_solve_eq__var : forall Θ X Q,                (* SE-Var + SE-FlexL *)
    Θ ⊢ₑ (pskl_var_f X) ∼ Q ⤳ (pskl_var_f X)
| a_solve_eq__flex_r : forall Θ α P,             (* SE-FlexR *)
    binds α abind_flex_mono Θ ->
    a_non_flex Θ P ->
    Θ ⊢ₑ P ∼ (pskl_var_f α) ⤳ (pskl_var_f α)
| a_solve_eq__hole_l : forall Θ Q,               (* SE-GhostL *)
    Θ ⊢ₑ pskl_hole ∼ Q ⤳ Q
| a_solve_eq__hole_r : forall Θ P,               (* SE-VacuousR *)
    Θ ⊢ₑ P ∼ pskl_hole ⤳ P
| a_solve_eq__arrow : forall Θ P1 P2 Q1 Q2 P1' P2',          (* SE-Arrow *)
    Θ ⊢ₑ P1 ∼ Q1 ⤳ P1' ->
    Θ ⊢ₑ P2 ∼ Q2 ⤳ P2' ->
    Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2) ⤳ (pskl_arrow P1' P2')
| a_solve_eq__forall : forall L Θ P Q P',        (* SE-Forall *)
    (forall β, β `notin` L ->
       Θ ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
            ∼ (open_pskl_wrt_pskl Q (pskl_var_f β))
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q) ⤳ (pskl_all_syn P')
| a_solve_eq__tophole_both : forall Θ P Q P',    (* SE-UnivGhost *)
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₑ (pskl_tophole P) ∼ (pskl_tophole Q) ⤳ (pskl_tophole P')
| a_solve_eq__tophole_l_all : forall L Θ P Q P', (* SE-GhostForall *)
    (forall β, β `notin` L ->
       Θ ⊢ₑ (pskl_tophole P) ∼ (open_pskl_wrt_pskl Q (pskl_var_f β))
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₑ (pskl_tophole P) ∼ (pskl_all_syn Q) ⤳ (pskl_all_syn P')
| a_solve_eq__tophole_l_guarded : forall Θ P Q P',           (* SE-GhostGuarded *)
    guarded_pskl Q ->
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₑ (pskl_tophole P) ∼ Q ⤳ P'
| a_solve_eq__all_l_tophole : forall L Θ P Q P', (* SE-ForallGhost *)
    (forall β, β `notin` L ->
       Θ ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼ (pskl_tophole Q)
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_tophole Q) ⤳ (pskl_all_syn P')
| a_solve_eq__tophole_r_guarded : forall Θ P Q P',           (* SE-GuardedGhost *)
    guarded_pskl P ->
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₑ P ∼ (pskl_tophole Q) ⤳ P'
where "Θ ⊢ₛ P ≼[ m ] Q ⤳ P'" := (a_solve_sub Θ m P Q P') : type_scope
  and "Θ ⊢ₑ P ∼ Q ⤳ P'" := (a_solve_eq Θ P Q P') : type_scope.

Reserved Notation "Θ ⊩ C ⨾ P ⤳ Q"
  (at level 75, C at level 74, P at level 74, Q at level 74, no associativity).
(* Constraint-list solving  [solve C P Q] (fig:constraint-solving, top box). *)
Inductive a_solve_cstr : aenv -> a_cstrs -> pskl -> pskl -> Prop :=
| a_solve_cstr__empty : forall Θ P,
    Θ ⊩ nil ⨾ P ⤳ P
| a_solve_cstr__sub : forall Θ m Q P P',
    Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
    Θ ⊩ (a_cstr_sub m Q :: nil) ⨾ P ⤳ P'
| a_solve_cstr__eq : forall Θ Q C P P' P'',
    Θ ⊢ₑ P ∼ Q ⤳ P'' ->
    Θ ⊩ C ⨾ P'' ⤳ P' ->
    Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ P'
where "Θ ⊩ C ⨾ P ⤳ Q" := (a_solve_cstr Θ C P Q) : type_scope.

Reserved Notation "P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q"
  (at level 75, NM at level 0, α at level 0, m at level 0, P' at level 74,
   Ξ at level 0, Q at level 74, no associativity).
(* The look judgment [look[N][M]{α}{P}{P'}{Q}[Ξ]] (fig:poly-info-extraction,
   top box): collect constraints, solve them against the empty input [□],
   then apply [guess[N]]. *)
Inductive a_extract : a_sub_mode -> atom -> mode -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_extract__solve : forall NM α m P P' Ξ Ξ' C Q Q',
    P ≼[ α , m ] P' ⤳ Ξ ⨾ C ->
    Ξ ⊩ C ⨾ pskl_hole ⤳ Q ->
    a_guess NM Q Ξ' Q' ->
    P ⊳[ NM , α , m ] P' ⤳ (Ξ ++ Ξ') ↪ Q'
where "P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q" := (a_extract NM α m P P' Ξ Q) : type_scope.

(* ===================================================================== *)
(*  Flexible-variable machinery (fig:alg-consistency, lower boxes).       *)
(*  [a_unify Θ0 α̂ β̂ Θ1] = [Θ0 ⊲ α̂ ≈ β̂ ⊣ Θ1];                              *)
(*  [a_assign Θ0 Ξ α̂ P Θ1] = [Θ0 | Ξ ⊲ α̂ := P ⊣ Θ1].                      *)
(*  Rules recurse on the list HEAD (the paper's rightmost entry).          *)
(* ===================================================================== *)

Inductive a_unify : aenv -> ptyp -> ptyp -> aenv -> Prop :=
| a_unify__flex_id : forall Θ0 α,                          (* Flex-Flex-Id *)
    binds α abind_flex_mono Θ0 ->
    a_unify Θ0 (ptyp_var_f α) (ptyp_var_f α) Θ0
| a_unify__flex_l : forall Θ0 α β,                         (* Flex-Flex-L *)
    α <> β ->
    a_unify ((α ~ abind_flex_mono) ++ Θ0) (ptyp_var_f α) (ptyp_var_f β)
      ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0)
| a_unify__flex_r : forall Θ0 α β,                         (* Flex-Flex-R *)
    α <> β ->
    a_unify ((β ~ abind_flex_mono) ++ Θ0) (ptyp_var_f α) (ptyp_var_f β)
      ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0)
| a_unify__flex_assign : forall Θ0 Θ1 γ τ A B,             (* Flex-Flex-Assign *)
    a_unify Θ0 (subst_ptyp_in_ptyp τ γ A) (subst_ptyp_in_ptyp τ γ B) Θ1 ->
    a_unify ((γ ~ abind_flex_mono_def τ) ++ Θ0) A B
      ((γ ~ abind_flex_mono_def τ) ++ Θ1)
| a_unify__flex_skip : forall Θ0 Θ1 γ A B,                 (* Flex-Flex-Skip *)
    γ `notin` (ftvar_in_ptyp A `union` ftvar_in_ptyp B) ->
    a_unify Θ0 A B Θ1 ->
    a_unify ((γ ~ abind_flex_mono) ++ Θ0) A B ((γ ~ abind_flex_mono) ++ Θ1)
| a_unify__skip_other : forall Θ0 Θ1 c b A B,              (* Flex-Flex-Skip' *)
    (b = abind_tvar \/
     (exists Q, b = abind_var_typ Q) \/
     (exists Q, b = abind_var_skl Q)) ->
    a_unify Θ0 A B Θ1 ->
    a_unify ((c ~ b) ++ Θ0) A B ((c ~ b) ++ Θ1).

(* [a_assign].  NB: the paper's [Assign-Assign] premise is written
   [unify(α̂[τ/β̂])(P[τ/β̂])] over [Θ0,Ξ], but [P] is a general skeleton (only
   monotype-ified in [Assign-SolveM] via [guessMono]), so monotype-level
   [unify] does not apply; we read it as CONTINUING the assignment on
   [P[τ/β̂]] with the [Θ0 | Ξ] split ([α̂ ≠ β̂] makes [α̂[τ/β̂] = α̂]). *)
Inductive a_assign : aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_assign__univ_ghost_id : forall Θ0 α,                  (* Assign-UnivGhost-Id *)
    a_assign ((α ~ abind_flex_mono) ++ Θ0) nil α
      (pskl_tophole (pskl_var_f α)) ((α ~ abind_flex_mono) ++ Θ0)
| a_assign__solve_m : forall Θ0 Ξ α P βs τ,               (* Assign-SolveM *)
    α `notin` ftvar_in_pskl P ->
    a_guess_mono Θ0 P βs τ ->
    a_assign ((α ~ abind_flex_mono) ++ Θ0) Ξ α P
      ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0)
| a_assign__assign : forall Θ0 Θ1 Ξ α β τ P,              (* Assign-Assign *)
    a_assign Θ0 Ξ α (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) Θ1 ->
    a_assign ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α P
      ((β ~ abind_flex_mono_def τ) ++ Θ1)
| a_assign__depend : forall Θ0 Θ1 Ξ α β P,                (* Assign-Depend *)
    α <> β ->
    β `in` ftvar_in_pskl P ->
    a_assign Θ0 ((β ~ abind_flex_mono) ++ Ξ) α P Θ1 ->
    a_assign ((β ~ abind_flex_mono) ++ Θ0) Ξ α P Θ1
| a_assign__skip : forall Θ0 Θ1 Ξ α β P,                  (* Assign-Skip *)
    α <> β ->
    β `notin` ftvar_in_pskl P ->
    a_assign Θ0 Ξ α P Θ1 ->
    a_assign ((β ~ abind_flex_mono) ++ Θ0) Ξ α P ((β ~ abind_flex_mono) ++ Θ1)
| a_assign__skip_rigid : forall Θ0 Θ1 Ξ α β P,            (* Assign-SkipRigid *)
    β `notin` ftvar_in_pskl P ->
    a_assign Θ0 Ξ α P Θ1 ->
    a_assign ((β ~ abind_tvar) ++ Θ0) Ξ α P ((β ~ abind_tvar) ++ Θ1)
| a_assign__skip_tm_var : forall Θ0 Θ1 Ξ α x Q P,         (* Assign-SkipTmVar *)
    a_assign Θ0 Ξ α P Θ1 ->
    a_assign ((x ~ abind_var_typ Q) ++ Θ0) Ξ α P ((x ~ abind_var_typ Q) ++ Θ1)
| a_assign__skip_tm_skl : forall Θ0 Θ1 Ξ α x Q P,         (* Assign-SkipTmVar (skl) *)
    a_assign Θ0 Ξ α P Θ1 ->
    a_assign ((x ~ abind_var_skl Q) ++ Θ0) Ξ α P ((x ~ abind_var_skl Q) ++ Θ1).

(* ===================================================================== *)
(*  Algorithmic consistency  [Θ0 ⊢[Δ1|Δ2][P0] P ~ Q ⊣ Θ1]                 *)
(*  (fig:alg-consistency).  The finalized paper carries TWO auxiliary      *)
(*  bound-variable sets: Δ1 tracks binders from the input [P0], Δ2 from    *)
(*  [P]; Ghost/GhostR restrict the output fill against them so [Q] is a    *)
(*  valid refinement of both inputs.                                       *)
(* ===================================================================== *)
Inductive a_consis : atoms -> atoms -> aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_consis__ghost : forall Δ1 Δ2 Θ0 P0,                       (* Ghost *)
    AtomSetImpl.inter Δ2 (ftvar_in_pskl P0) [=] empty ->
    a_consis Δ1 Δ2 Θ0 P0 pskl_hole P0 Θ0
| a_consis__unit : forall Δ1 Δ2 Θ0,                           (* Unit *)
    a_consis Δ1 Δ2 Θ0 pskl_unit pskl_unit pskl_unit Θ0
| a_consis__rigid : forall Δ1 Δ2 Θ0 α,                        (* Rigid *)
    binds α abind_tvar Θ0 ->
    a_consis Δ1 Δ2 Θ0 (pskl_var_f α) (pskl_var_f α) (pskl_var_f α) Θ0
| a_consis__arrow : forall Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2, (* Arrow *)
    a_consis Δ1 Δ2 Θ0 P0a P1 Q1 Θ1 ->
    a_consis Δ1 Δ2 Θ1 P0b P2 Q2 Θ2 ->
    a_consis Δ1 Δ2 Θ0 (pskl_arrow P0a P0b) (pskl_arrow P1 P2) (pskl_arrow Q1 Q2) Θ2
| a_consis__forall_inh : forall L Δ1 Δ2 Θ0 Θ1 P0 P Q,         (* ForallInh: α to BOTH *)
    (forall α, α `notin` L ->
       a_consis (add α Δ1) (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
         (open_pskl_wrt_pskl P0 (pskl_var_f α))
         (open_pskl_wrt_pskl P (pskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consis Δ1 Δ2 Θ0 (pskl_all_syn P0) (pskl_all_syn P) (pskl_all_syn Q) Θ1
| a_consis__forall_syn : forall L Δ1 Δ2 Θ0 Θ1 P0 P Q,         (* ForallSyn: α to Δ2 *)
    (forall α, α `notin` L ->
       a_consis Δ1 (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
         (pskl_tophole P0)
         (open_pskl_wrt_pskl P (pskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consis Δ1 Δ2 Θ0 (pskl_tophole P0) (pskl_all_syn P) (pskl_all_syn Q) Θ1
| a_consis__univ_ghost : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,           (* UnivGhost *)
    a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
    a_consis Δ1 Δ2 Θ0 (pskl_tophole P0) (pskl_tophole P) (pskl_tophole Q) Θ1
| a_consis__univ_ghost1 : forall L Δ1 Δ2 Θ0 Θ1 P0 P Q,        (* UnivGhost1: α to Δ1 *)
    (forall α, α `notin` L ->
       a_consis (add α Δ1) Δ2 ((α ~ abind_tvar) ++ Θ0)
         (open_pskl_wrt_pskl P0 (pskl_var_f α))
         (pskl_tophole P)
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consis Δ1 Δ2 Θ0 (pskl_all_syn P0) (pskl_tophole P) (pskl_all_syn Q) Θ1
| a_consis__univ_ghost2 : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,          (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
    a_consis Δ1 Δ2 Θ0 P0 (pskl_tophole P) Q Θ1
| a_consis__flex : forall Δ1 Δ2 Θ0 Θ1 α β,                    (* Flex *)
    a_unify Θ0 (ptyp_var_f α) (ptyp_var_f β) Θ1 ->
    a_consis Δ1 Δ2 Θ0 (pskl_var_f β) (pskl_var_f α) (pskl_var_f α) Θ1
| a_consis__flex_l : forall Δ1 Δ2 Θ0 Θ1 α P0,                 (* FlexL *)
    a_non_flex Θ0 P0 ->
    a_assign Θ0 nil α P0 Θ1 ->
    a_consis Δ1 Δ2 Θ0 P0 (pskl_var_f α) (pskl_var_f α) Θ1
| a_consis__flex_r : forall Δ1 Δ2 Θ0 Θ1 α P,                  (* FlexR *)
    a_non_flex Θ0 P ->
    a_assign Θ0 nil α P Θ1 ->
    a_consis Δ1 Δ2 Θ0 (pskl_var_f α) P (pskl_var_f α) Θ1
| a_consis__ghost_r : forall Δ1 Δ2 Θ0 P,                      (* GhostR *)
    AtomSetImpl.inter Δ1 (ftvar_in_pskl P) [=] empty ->
    a_consis Δ1 Δ2 Θ0 pskl_hole P P Θ0
| a_consis__univ_ghost_r : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,         (* UnivGhostR *)
    guarded_pskl P ->
    a_non_flex Θ0 P ->
    a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
    a_consis Δ1 Δ2 Θ0 (pskl_tophole P0) P Q Θ1.

(* Both-Δ-empty form (the paper "omit[s] them when both are empty"). *)
Notation "Θ ⊢ₐ[ P0 ] P '~ᴬ' Q ⊣ Θ'" := (a_consis empty empty Θ P0 P Q Θ').

(* [aconsis{Θ0}{P}{P0}{Θ1}]: output-suppressed abbreviation (paper). *)
Definition a_consis_chk (Θ0 : aenv) (P P0 : pskl) (Θ1 : aenv) : Prop :=
  exists Q, Θ0 ⊢ₐ[ P0 ] P ~ᴬ Q ⊣ Θ1.

(* ===================================================================== *)
(*  Algorithmic subtyping  [Θ0 ⊢[N][M][P0] P ⊑ Q ⊣ Θ1]                    *)
(*  (fig:alg-subtyping) MUTUAL with the flexible-variable auxiliary        *)
(*  judgment (second box), here [a_sub_flex]: [FlexMono] hands a bare      *)
(*  flex LHS [α̂] to it; its [Flex-Solve] re-enters [a_sub].                *)
(* ===================================================================== *)
Inductive a_sub : a_sub_mode -> mode -> pskl -> aenv -> pskl -> pskl -> aenv -> Prop :=
| a_sub__infer : forall NM P Θ0,                              (* Infer *)
    a_sub NM mode_ti pskl_hole Θ0 P P Θ0
| a_sub__check : forall Θ0 Θ1 A B,                            (* Check *)
    guarded_pskl A -> guarded_pskl B ->
    a_consis_chk Θ0 A B Θ1 ->
    a_sub a_sub_mode_ty mode_tc B Θ0 A B Θ1
| a_sub__forall_r : forall L Θ0 Θ1 Ξ A B,                     (* ForallR *)
    a_suffix Ξ ->
    (forall α, α `notin` L ->
       a_sub a_sub_mode_ty mode_tc (open_pskl_wrt_pskl B (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ0) A (open_pskl_wrt_pskl B (pskl_var_f α))
         (Ξ ++ (α ~ abind_tvar) ++ Θ1)) ->
    a_sub a_sub_mode_ty mode_tc (pskl_all_syn B) Θ0 A (pskl_all_syn B) Θ1
| a_sub__univ_ghost_r : forall Θ0 P,                          (* UnivGhostR *)
    guarded_pskl P ->
    a_sub a_sub_mode_sk mode_tc pskl_hole Θ0 P (pskl_tophole P) Θ0
| a_sub__flex_mono : forall NM M P0 Θ0 Θ1 α A,                (* FlexMono *)
    a_sub_flex NM M P0 Θ0 nil α A Θ1 ->
    a_sub NM (mode_fn M) P0 Θ0 (pskl_var_f α) A Θ1
| a_sub__arrow : forall NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,    (* Arrow *)
    Θ0 ⊢ₐ[ P0a ] P1 ~ᴬ Q1 ⊣ Θ1 ->
    a_sub NM M P0b Θ1 P2 Q2 Θ2 ->
    a_sub NM (mode_fn M) (pskl_arrow P0a P0b) Θ0 (pskl_arrow P1 P2)
      (pskl_arrow Q1 Q2) Θ2
| a_sub__forall_l : forall L NM M P0 Θ0 Θ1 P Q Ξ P1,          (* ForallL *)
    M <> mode_ti ->
    (guarded_pskl P0 \/ P0 = pskl_hole) ->
    (forall α, α `notin` L ->
       a_extract NM α M (open_pskl_wrt_pskl P (pskl_var_f α)) P0 Ξ P1) ->
    a_wf_pskl (Ξ ++ Θ0) P1 ->
    a_sub NM M P0 (Ξ ++ Θ0) (open_pskl_wrt_pskl P P1) Q Θ1 ->
    a_sub NM M P0 Θ0 (pskl_all_syn P) Q Θ1
| a_sub__ghost : forall M Θ0 P0,                              (* Ghost *)
    a_sub a_sub_mode_sk M P0 Θ0 pskl_hole P0 Θ0
| a_sub__univ_ghost_l : forall M Θ0 Θ1 P0 P Q,                (* UnivGhostL *)
    M <> mode_ti ->
    a_sub a_sub_mode_sk M P0 Θ0 P Q Θ1 ->
    a_sub a_sub_mode_sk M P0 Θ0 (pskl_tophole P) Q Θ1

(* Flexible-variable subtyping [Θ | Ξ ⊢[N][FN M][P0] α̂ ⊑ Q ⊣ Θ'] (paper
   fig:alg-subtyping, second box).  [Flex-Assign] is read as the auxiliary
   judgment's continuation keeping the [Θ0 | Ξ] split ([α̂ ≠ β̂] makes
   [α̂[τ/β̂] = α̂]); merging [Θ0,Ξ] and re-entering [a_sub] would re-fire
   [FlexMono] and discard [Ξ]. *)
with a_sub_flex : a_sub_mode -> mode -> pskl -> aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_sub_flex__solve : forall NM M P0 Θ0 Θ1 Ξ α0 α β A,        (* Flex-Solve *)
    a_sub NM (mode_fn M) P0
      (Ξ ++ (α0 ~ abind_flex_mono_def (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
          ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
      (pskl_arrow (pskl_var_f α) (pskl_var_f β)) A Θ1 ->
    a_sub_flex NM M P0 ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 A Θ1
| a_sub_flex__assign : forall NM M P0 Θ0 Θ1 Ξ α β τ A,        (* Flex-Assign *)
    a_sub_flex NM M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) Θ0 Ξ α A Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α A
      ((β ~ abind_flex_mono_def τ) ++ Θ1)
| a_sub_flex__depend : forall NM M P0 Θ0 Θ1 Ξ α β A,          (* Flex-Depend *)
    α <> β ->
    β `in` ftvar_in_pskl P0 ->
    a_sub_flex NM M P0 Θ0 ((β ~ abind_flex_mono) ++ Ξ) α A Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α A Θ1
| a_sub_flex__skip : forall NM M P0 Θ0 Θ1 Ξ α β A,            (* Flex-Skip *)
    α <> β ->
    β `notin` ftvar_in_pskl P0 ->
    a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α A
      ((β ~ abind_flex_mono) ++ Θ1)
| a_sub_flex__skip_rigid : forall NM M P0 Θ0 Θ1 Ξ α β A,      (* Flex-SkipRigid *)
    β `notin` ftvar_in_pskl P0 ->
    a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α A ((β ~ abind_tvar) ++ Θ1).

(* Skeleton splitting  [Θ0 ⊲ split P0 = P→Q ⊣ Θ1] (fig:alg-type-inference). *)
Inductive a_split : aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_split__arrow : forall Θ0 P Q,
    a_split Θ0 (pskl_arrow P Q) P Q Θ0
| a_split__hole : forall Θ0,
    a_split Θ0 pskl_hole pskl_hole pskl_hole Θ0
| a_split__flex : forall Θ0 Θ1 α β γ,                   (* split[α̂] = β̂→γ̂ *)
    a_unify ((γ ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
      (ptyp_var_f α) (ptyp_arrow (ptyp_var_f β) (ptyp_var_f γ)) Θ1 ->
    a_split Θ0 (pskl_var_f α) (pskl_var_f β) (pskl_var_f γ) Θ1
where "Θ ⊢ₐ[ N | m | P0 ] P ⊑ᴬ Q ⊣ Θ'" := (a_sub N m P0 Θ P Q Θ').

(* ===================================================================== *)
(*  Algorithmic skeleton inference  [Θ ⊢[M][P0] M ⇨ P ⊣ Θ']               *)
(*  (fig:alg-skeleton-inference)                                          *)
(* ===================================================================== *)
Inductive a_pat : mode -> aenv -> pskl -> exp -> pskl -> aenv -> Prop :=
| a_pat__unit : forall m Θ0 Θ1 P0 P,                        (* AP-Unit *)
    Θ0 ⊢ₐ[ a_sub_mode_sk | m | P0 ] pskl_unit ⊑ᴬ P ⊣ Θ1 ->
    Θ0 ⊢ₐ[ m ; P0 ] exp_unit ⇨ P ⊣ Θ1
| a_pat__var : forall m Θ0 Θ1 P0 x A Q,         (* AP-Var (type-bound x) *)
    binds x (abind_var_typ A) Θ0 ->
    Θ0 ⊢ₐ[ a_sub_mode_sk | m | P0 ] (ptyp_to_pskl A) ⊑ᴬ Q ⊣ Θ1 ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_var_f x) ⇨ Q ⊣ Θ1
| a_pat__var_skl : forall m Θ0 Θ1 P0 x P Q,     (* AP-Var (skeleton-bound x) *)
    binds x (abind_var_skl P) Θ0 ->
    Θ0 ⊢ₐ[ a_sub_mode_sk | m | P0 ] P ⊑ᴬ Q ⊣ Θ1 ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_var_f x) ⇨ Q ⊣ Θ1
| a_pat__anno : forall m Θ0 Θ1 P0 e A Q,                    (* AP-Anno *)
    Θ0 ⊢ₐ[ a_sub_mode_sk | m | P0 ] (ptyp_to_pskl A) ⊑ᴬ Q ⊣ Θ1 ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_anno e A) ⇨ Q ⊣ Θ1
| a_pat__freeze : forall Θ0 e Q Θ1,                         (* AP-Freeze *)
    Θ0 ⊢ₐ[ mode_ti ; pskl_hole ] e ⇨ Q ⊣ Θ1 ->
    Θ0 ⊢ₐ[ mode_tc ; pskl_hole ] (exp_freeze e) ⇨ Q ⊣ Θ1
| a_pat__abs : forall L m Θ0 Θ1 Θ2 P0 P Q0 e Q Ξ,           (* AP-Abs *)
    m <> mode_tc ->
    a_split Θ0 P0 P Q0 Θ1 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_skl P) ++ Θ1) ⊢ₐ[ (decr_mode m) ; Q0 ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q ⊣ (Ξ ++ (x ~ abind_var_skl P) ++ Θ2)) ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_abs e) ⇨ (pskl_arrow P Q) ⊣ (Ξ ++ Θ2)
| a_pat__abs_anno : forall L m Θ0 Θ1 Θ2 Θ3 P0 P Q0 A e Q Ξ,  (* AP-AbsAnno *)
    m <> mode_tc ->
    a_split Θ0 P0 P Q0 Θ1 ->
    a_consis_chk Θ1 (ptyp_to_pskl A) P Θ2 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_typ A) ++ Θ2) ⊢ₐ[ (decr_mode m) ; Q0 ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3)) ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_abs_anno A e) ⇨ (pskl_arrow (ptyp_to_pskl A) Q) ⊣ (Ξ ++ Θ3)
| a_pat__abs_check : forall L Θ0 Θ1 e Q Ξ,                  (* AP-AbsCheck *)
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_skl pskl_hole) ++ Θ0) ⊢ₐ[ mode_tc ; pskl_hole ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q ⊣ (Ξ ++ (x ~ abind_var_skl pskl_hole) ++ Θ1)) ->
    Θ0 ⊢ₐ[ mode_tc ; pskl_hole ] (exp_abs e)
      ⇨ (pskl_tophole (pskl_arrow pskl_hole Q)) ⊣ (Ξ ++ Θ1)
| a_pat__abs_anno_check : forall L Θ0 Θ1 A e Q Ξ,           (* AP-AbsAnnoCheck *)
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_typ A) ++ Θ0) ⊢ₐ[ mode_tc ; pskl_hole ]
         (open_exp_wrt_exp e (exp_var_f x)) ⇨ Q ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ1)) ->
    Θ0 ⊢ₐ[ mode_tc ; pskl_hole ] (exp_abs_anno A e)
      ⇨ (pskl_tophole (pskl_arrow (ptyp_to_pskl A) Q)) ⊣ (Ξ ++ Θ1)
| a_pat__app : forall m Θ0 Θ1 Θ2 P0 Q0 P Q e1 e2,           (* AP-App *)
    Θ0 ⊢ₐ[ mode_tc ; pskl_hole ] e2 ⇨ P0 ⊣ Θ1 ->
    Θ1 ⊢ₐ[ (mode_fn m) ; (pskl_arrow P0 Q0) ] e1 ⇨ (pskl_arrow P Q) ⊣ Θ2 ->
    Θ0 ⊢ₐ[ m ; Q0 ] (exp_app e1 e2) ⇨ Q ⊣ Θ2
where "Θ ⊢ₐ[ m ; P0 ] e ⇨ Q ⊣ Θ'" := (a_pat m Θ P0 e Q Θ').

(* ===================================================================== *)
(*  Algorithmic type inference  [Θ ⊢[M][P] M ⦂ A ⊣ Θ']                    *)
(*  (fig:alg-type-inference)                                              *)
(* ===================================================================== *)
Inductive a_typing : mode -> aenv -> pskl -> exp -> ptyp -> aenv -> Prop :=
| a_typing__unit : forall m Θ0 P0 A Θ1,                     (* AT-Unit *)
    Θ0 ⊢ₐ[ a_sub_mode_ty | m | P0 ] pskl_unit ⊑ᴬ (ptyp_to_pskl A) ⊣ Θ1 ->
    Θ0 ⊢ₐ[ m ; P0 ] exp_unit ⦂ A ⊣ Θ1
| a_typing__var : forall m Θ0 P0 x A B Θ1,                  (* AT-Var *)
    binds x (abind_var_typ A) Θ0 ->
    Θ0 ⊢ₐ[ a_sub_mode_ty | m | P0 ] (ptyp_to_pskl A) ⊑ᴬ (ptyp_to_pskl B) ⊣ Θ1 ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_var_f x) ⦂ B ⊣ Θ1
| a_typing__anno : forall m Θ0 P0 e A B Θ1 Θ2,              (* AT-Anno *)
    Θ0 ⊢ₐ[ mode_tc ; (ptyp_to_pskl A) ] e ⦂ A ⊣ Θ1 ->
    Θ1 ⊢ₐ[ a_sub_mode_ty | m | P0 ] (ptyp_to_pskl A) ⊑ᴬ (ptyp_to_pskl B) ⊣ Θ2 ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_anno e A) ⦂ B ⊣ Θ2
| a_typing__freeze : forall Θ0 e A B Θ1 Θ2,                 (* AT-Freeze *)
    (* the TC input skeleton IS the checked type [A]; the inferred [B] is
       UNIFIED with it (consistency), no subtyping *)
    Θ0 ⊢ₐ[ mode_ti ; pskl_hole ] e ⦂ B ⊣ Θ1 ->
    a_consis_chk Θ1 (ptyp_to_pskl B) (ptyp_to_pskl A) Θ2 ->
    Θ0 ⊢ₐ[ mode_tc ; (ptyp_to_pskl A) ] (exp_freeze e) ⦂ A ⊣ Θ2
| a_typing__abs : forall L m Θ0 Θ1 Θ2 P0 P Q αs A e B Ξ,    (* AT-Abs *)
    m <> mode_tc ->
    a_split Θ0 P0 P Q Θ1 ->
    a_guess_mono Θ1 P αs A ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_typ A) ++ αs ++ Θ1) ⊢ₐ[ (decr_mode m) ; Q ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_abs e) ⦂ (ptyp_arrow A B) ⊣ (Ξ ++ Θ2)
| a_typing__abs_anno : forall L m Θ0 Θ1 Θ2 Θ3 P0 P Q A e B Ξ,   (* AT-AbsAnno *)
    m <> mode_tc ->
    a_split Θ0 P0 P Q Θ1 ->
    a_consis_chk Θ1 (ptyp_to_pskl A) P Θ2 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_typ A) ++ Θ2) ⊢ₐ[ (decr_mode m) ; Q ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3)) ->
    Θ0 ⊢ₐ[ m ; P0 ] (exp_abs_anno A e) ⦂ (ptyp_arrow A B) ⊣ (Ξ ++ Θ3)
(* AT-AbsCheck / AT-AbsAnnoCheck (input [∀ᾱ.A₀]): the ᾱ-prefix is folded one
   [∀] at a time — [_step] peels one rigid quantifier from the input type and
   the result, [_base] splits the (non-∀) input type into [A→B] and checks
   the body.  Mirrors [d_sd_typing__abs_check_step]/[_base]. *)
| a_typing__abs_check_step : forall L Θ0 Θ1 A0 e A Ξ,
    a_suffix Ξ ->
    (forall X, X `notin` L ->
       ((X ~ abind_tvar) ++ Θ0)
         ⊢ₐ[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ]
         (exp_abs e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f X))
         ⊣ (Ξ ++ (X ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ₐ[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ] (exp_abs e) ⦂ (ptyp_all A) ⊣ Θ1
| a_typing__abs_check_base : forall L Θ0 Θ1 Θ2 A0 A B e Ξ,
    a_split Θ0 (ptyp_to_pskl A0) (ptyp_to_pskl A) (ptyp_to_pskl B) Θ1 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_typ A) ++ Θ1) ⊢ₐ[ mode_tc ; (ptyp_to_pskl B) ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    Θ0 ⊢ₐ[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs e) ⦂ (ptyp_arrow A B) ⊣ Θ2
| a_typing__abs_anno_check_step : forall L Θ0 Θ1 A0 Aan e A Ξ,
    a_suffix Ξ ->
    (forall X, X `notin` L ->
       ((X ~ abind_tvar) ++ Θ0)
         ⊢ₐ[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ]
         (exp_abs_anno Aan e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f X))
         ⊣ (Ξ ++ (X ~ abind_tvar) ++ Θ1)) ->
    Θ0 ⊢ₐ[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ] (exp_abs_anno Aan e) ⦂ (ptyp_all A) ⊣ Θ1
| a_typing__abs_anno_check_base : forall L Θ0 Θ1 Θ2 Θ3 A0 A' A B e Ξ,
    a_split Θ0 (ptyp_to_pskl A0) (ptyp_to_pskl A') (ptyp_to_pskl B) Θ1 ->
    a_consis_chk Θ1 (ptyp_to_pskl A') (ptyp_to_pskl A) Θ2 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       ((x ~ abind_var_typ A) ++ Θ2) ⊢ₐ[ mode_tc ; (ptyp_to_pskl B) ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3)) ->
    Θ0 ⊢ₐ[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs_anno A e) ⦂ (ptyp_arrow A B) ⊣ Θ3
| a_typing__app : forall m Θ0 Θ1 Θ2 Θ3 P Q A A' B e1 e2,    (* AT-App *)
    Θ0 ⊢ₐ[ mode_tc ; pskl_hole ] e2 ⇨ P ⊣ Θ1 ->
    Θ1 ⊢ₐ[ (mode_fn m) ; (pskl_arrow P Q) ] e1 ⦂ (ptyp_arrow A B) ⊣ Θ2 ->
    Θ2 ⊢ₐ[ mode_tc ; (ptyp_to_pskl A) ] e2 ⦂ A' ⊣ Θ3 ->
    Θ0 ⊢ₐ[ m ; Q ] (exp_app e1 e2) ⦂ B ⊣ Θ3
where "Θ ⊢ₐ[ m ; P0 ] e ⦂ B ⊣ Θ'" := (a_typing m Θ P0 e B Θ').
