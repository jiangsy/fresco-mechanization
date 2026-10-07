(** Fresco algorithmic-system definitions — RESTARTED against the finalized
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

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope fresco_a_scope.

Reserved Notation "{{ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}a"
  (at level 0, Δ1 at level 0, Δ2 at level 0, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  Δ1  |  Δ2  |  P0  ]  P  ∼  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊲ A ≈ᵘ B ⊣ Θ' }}a"
  (at level 0, A at level 74, B at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊲  A  ≈ᵘ  B  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}a"
  (at level 0, Ξ at level 0, α at level 74, P at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊲[  Ξ  ]  α  ≔  P  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}a"
  (at level 0, P0 at level 74, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊲  P0  ▹  P  ⇢  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊢[ N | m | P0 ] P ⩽ Q ⊣ Θ' }}a"
  (at level 0, N at level 0, m at level 0, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  N  |  m  |  P0  ]  P  ⩽  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}a"
  (at level 0, m at level 0, P0 at level 0, e at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢ˢ[  m  ;  P0  ]  e  ⦂  Q  ⊣  Θ'  '}}a'").
Reserved Notation "{{ Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ' }}a"
  (at level 0, m at level 0, P0 at level 0, e at level 74, B at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  m  ;  P0  ]  e  ⦂  B  ⊣  Θ'  '}}a'").

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

(** The skeleton a TERM-variable entry carries, if it is one — the [abind]
    mirror of [dbind_to_pskl] (coercions.v).  Skeleton inference reads a
    variable's skeleton through this, so both binding forms of the paper's
    single [x : P] entry are accepted: a stored skeleton verbatim, a stored
    type via its painting.  Type-level entries ([abind_tvar] and the two
    flexible forms) are not term variables and yield [None]. *)
Definition abind_to_pskl (b : abind) : option pskl :=
  match b with
  | abind_var_skl P => Some P
  | abind_var_typ A => Some (ptyp_to_pskl A)
  | abind_tvar => None
  | abind_flex_mono => None
  | abind_flex_mono_def _ => None
  end.

(* ===================================================================== *)
(*  Free variables of, and RENAMING through, an algorithmic context.      *)
(*                                                                        *)
(*  Freshness-campaign infrastructure (DESIGN.md §4.3): exists-fresh       *)
(*  rules state their side conditions against what the context MENTIONS   *)
(*  (domain + payload free variables), and renaming lemmas must move a    *)
(*  name through the CONTEXT and the GENERATED block too, not just the    *)
(*  skeletons.  NB a key-only rename would be WRONG — three of the five   *)
(*  bindings carry a payload that can mention the renamed variable        *)
(*  ([α̂ ≔ τ], [x : A], [x : P]).                                          *)
(* ===================================================================== *)

Definition ftvar_in_abind (bd : abind) : atoms :=
  match bd with
  | abind_tvar            => empty
  | abind_var_typ A       => ftvar_in_ptyp A
  | abind_var_skl P       => ftvar_in_pskl P
  | abind_flex_mono       => empty
  | abind_flex_mono_def A => ftvar_in_ptyp A
  end.

(** Every atom a context mentions: its domain PLUS the free variables of
    every payload (a flexible definition [α̂ ≔ τ] may mention a rigid). *)
Fixpoint ftvar_in_aenv (Θ : aenv) : atoms :=
  match Θ with
  | nil           => empty
  | (x, bd) :: Θ' => add x (ftvar_in_abind bd `union` ftvar_in_aenv Θ')
  end.


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

(* [Θ ⊢ ctx] is defined below, after the wf judgments its entries need. *)

(** A type-variable occurrence in [Θ]: rigid, or a flexible declaration /
    definition (an occurrence of a defined [α̂] is still a variable; its
    definition is retrieved by lookup rules where needed). *)
Definition a_binds_tvar (α : atom) (Θ : aenv) : Prop :=
  binds α abind_tvar Θ \/
  binds α abind_flex_mono Θ \/
  (exists τ, binds α (abind_flex_mono_def τ) Θ).

(* Well-scopedness of types / skeletons under [Θ].  This is what the paper's
   implicit "all inputs are well-formed" and the explicit [Θ0,Ξ ⊢ P1] premise
   of ForallL mean; crucially, [a_inc]'s flex rule checks the solving monotype
   here, which is what forces identity information-increases to KEEP flexible
   variables in the target (stability of variable lookups depends on it). *)
(* ⚙ COFINITE, DELIBERATELY — and so are [a_scope_pskl] and [a_wf_pskl] below,
   against the exists-fresh discipline every OPERATIONAL judgment in this file
   follows.  Well-formedness is not a run: nothing here opens a binder at a
   name it chose, so there is no witness to name, and the cofinite form gives
   the strong elimination the whole tree leans on.  Do not "fix" these three to
   match their file-mates.  (The one genuine violation is [a_pat]'s four binder
   rows at the bottom of this file — see docs/REPORT-remech-cleanup-audit.md
   §3.) *)
Inductive a_wf_ptyp : aenv -> ptyp -> Prop :=
| a_wf_ptyp__unit : forall Θ,
    a_wf_ptyp Θ ptyp_unit
| a_wf_ptyp__var : forall Θ α,
    a_binds_tvar α Θ ->
    a_wf_ptyp Θ (ptyp_var_f α)
| a_wf_ptyp__arrow : forall Θ A1 A2,
    a_wf_ptyp Θ A1 ->
    a_wf_ptyp Θ A2 ->
    a_wf_ptyp Θ (ptyp_arrow A1 A2)
| a_wf_ptyp__all : forall L Θ A,
    (forall α, α `notin` L ->
       a_wf_ptyp ((α ~ abind_tvar) ++ Θ) (open_ptyp_wrt_ptyp A (ptyp_var_f α))) ->
    a_wf_ptyp Θ (ptyp_all A).

Inductive a_scope_pskl : aenv -> pskl -> Prop :=
| a_scope_pskl__unit : forall Θ,
    a_scope_pskl Θ pskl_unit
| a_scope_pskl__var : forall Θ α,
    a_binds_tvar α Θ ->
    a_scope_pskl Θ (pskl_var_f α)
| a_scope_pskl__arrow : forall Θ P1 P2,
    a_scope_pskl Θ P1 ->
    a_scope_pskl Θ P2 ->
    a_scope_pskl Θ (pskl_arrow P1 P2)
| a_scope_pskl__all : forall L Θ P,
    (forall α, α `notin` L ->
       a_scope_pskl ((α ~ abind_tvar) ++ Θ) (open_pskl_wrt_pskl P (pskl_var_f α))) ->
    a_scope_pskl Θ (pskl_all_syn P)
| a_scope_pskl__hole : forall Θ,
    a_scope_pskl Θ pskl_hole
| a_scope_pskl__tophole : forall Θ P,
    a_scope_pskl Θ P ->
    a_scope_pskl Θ (pskl_tophole P).

Reserved Notation "{{ Θ ⨟ Δ ⊢ₚₛ P }}a"
  (at level 0, Δ at level 74, P at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ₚₛ  P  '}}a'").

(* ===================================================================== *)
(*  Skeleton well-formedness over Θ  (decl [{{ Γ ⨟ Δ ⊢ₚₛ P }}d])         *)
(* ===================================================================== *)

Inductive a_wf_pskl : aenv -> atoms -> pskl -> Prop :=
| a_wf_pskl__unit : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ₚₛ pskl_unit }}a
| a_wf_pskl__var : forall Θ Δ α,
    α `in` Δ \/ a_binds_tvar α Θ ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_var_f α) }}a
| a_wf_pskl__arrow : forall Θ Δ P1 P2,
    {{ Θ ⨟ Δ ⊢ₚₛ P1 }}a ->
    {{ Θ ⨟ Δ ⊢ₚₛ P2 }}a ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_arrow P1 P2) }}a
| a_wf_pskl__all : forall L Θ Δ P,
    (forall α, α `notin` L ->
       {{ Θ ⨟ (add α Δ) ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f α)) }}a) ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a
| a_wf_pskl__hole : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ₚₛ pskl_hole }}a
| a_wf_pskl__tophole : forall Θ Δ P,
    guarded_pskl P ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    {{ Θ ⨟ Δ ⊢ₚₛ (pskl_tophole P) }}a
where "{{ Θ ⨟ Δ ⊢ₚₛ P }}a" := (a_wf_pskl Θ Δ P) : fresco_a_scope.

Reserved Notation "{{ ⊢ Θ }}a"
  (at level 0, format "'{{'  ⊢  Θ  '}}a'").

(** Context well-formedness [Θ ⊢ ctx] (full-algo-spec.tex:224): each
    definition's body is a well-formed monotype in its tail, each term
    variable's skeleton is well-formed in its tail; atom freshness is the
    paper's ambient Barendregt convention, made explicit. *)
Inductive a_wf_aenv : aenv -> Prop :=
| a_wf_aenv__nil :
    {{ ⊢ nil }}a
| a_wf_aenv__flex : forall α Θ,
    α `notin` dom Θ ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((α ~ abind_flex_mono) ++ Θ) }}a
| a_wf_aenv__flex_def : forall α τ Θ,
    α `notin` dom Θ ->
    a_wf_ptyp Θ τ ->
    mono_ptyp τ ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((α ~ abind_flex_mono_def τ) ++ Θ) }}a
| a_wf_aenv__var : forall x P Θ,
    x `notin` dom Θ ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((x ~ abind_var_skl P) ++ Θ) }}a
| a_wf_aenv__var_typ : forall x A Θ,
    x `notin` dom Θ ->
    a_wf_ptyp Θ A ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a
| a_wf_aenv__tvar : forall α Θ,
    α `notin` dom Θ ->
    {{ ⊢ Θ }}a ->
    {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a
where "{{ ⊢ Θ }}a" := (a_wf_aenv Θ) : fresco_a_scope.

(* ===================================================================== *)
(*  Mode/input-skeleton compatibility  skmod[TY] / skmod[SK]              *)
(*  (algorithmic.tex:239-244, 442-444)                                    *)
(* ===================================================================== *)

(** ⚠️ These are the algorithmic counterparts of [mod_comp_ty] / [mod_comp_sk]
    (fresco/def_shapes.v) — same concept, but the words are in the opposite order
    AND so are the arguments (this pair is mode-first, that one subject-first).
    See the ⛔ note at [mod_comp_ty] before trying to unify them. *)
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


(* [α̂ ∈ Θ] as a flexible variable — the paper's hatted metavariable
   convention, made explicit where a rule's variable must be hatted. *)
Definition a_flex_tvar (Θ : aenv) (α : atom) : Prop :=
  binds α abind_flex_mono Θ \/
  (exists τ, binds α (abind_flex_mono_def τ) Θ).

(** ⭐ THE FlexR-PRIORITY GUARD (2026-08-18).  [flex_r_off Θ P'] says the
    collection's LE-FlexR row does NOT apply at counterpart [P'].

    The paper's row concludes at a HATTED counterpart —
    [lookeq{α}{P}{β̂}{≐ γ̂}[γ̂]], full-algo-spec.tex:1110-1116 — and the
    reference implementation renders that as the match arm [| _, MFlex beta],
    type.ml:561, where [MFlex] is a constructor DISTINCT from [TVar]
    (lib/type.ml:23).  So the row fires at a FLEXIBLE counterpart and at
    nothing else, and [LE-UnivGhost2] (:618) is reached only after that test
    has failed.

    ⚠️ NOT admissible, like the ForallR-priority guard and unlike the
    absence-first one: [guarded_pskl] includes VARIABLES, so without it the
    two rows both fire at a ⫯ subject against a flexible and their answers
    differ in KIND — FlexR invents a flexible and spends supply, UnivGhost2
    strips and collects whatever the premise collected.  Machine-checked at
    the collection (cex/probe_bcore_ug2_flexr.v) and, one level up, at
    [e_extract] (cex/probe_extract_flexr_ug2_drift.v).  docs/PAPER-GAPS.md. *)

Definition flex_r_off (Θ : aenv) (P' : pskl) : Prop :=
  forall β, P' = pskl_var_f β -> ~ a_flex_tvar Θ β.

(** The two ways a site discharges it. *)

Lemma flex_r_off_nonvar : forall Θ P',           (* not a variable at all *)
  (forall β, P' <> pskl_var_f β) -> flex_r_off Θ P'.
Proof. intros Θ P' H β Heq; exfalso; exact (H β Heq). Qed.

Lemma flex_r_off_rigid : forall Θ β,             (* a RIGID variable *)
  ~ a_flex_tvar Θ β -> flex_r_off Θ (pskl_var_f β).
Proof. intros Θ β H β0 Heq; injection Heq as ->; exact H. Qed.

(* ===================================================================== *)
(*  guess^TY  (full-algo-spec.tex:479-491; the LaTeX source writes the     *)
(*  \guessMono macro, which renders as guess^TY — macro.tex:1505)          *)
(*  [guess^TY(P) = (Ξ; A)]: fill each ghost with a fresh flexible          *)
(*  variable, drop universal ghosts.  [guess[SK] P = (·; P)] is [a_guess]. *)
(*  NB: freshness of the generated [Ξ] is not carried by the relation;     *)
(*  proofs needing it add an explicit freshness premise (paper: "fresh").  *)
(* ===================================================================== *)

Inductive a_guess_mono : aenv -> pskl -> aenv -> ptyp -> Prop :=
| a_guess_mono__hole : forall Θ α,                            (* □ ↦ fresh α̂ *)
    (* the invented flexible avoids everything the ambient context MENTIONS
       (domain + payload ftv) — INPUT-only, and the mech's rendering of the
       implementation's global counter ([incr counter; Bindlib.new_var],
       type.ml:92-95).  Together with the ∀ rule's witness entering the
       context, "generated names avoid enclosing witnesses" becomes a
       DERIVABLE property ([a_guess_mono_generated_fresh], algo/prop_basic.v)
       instead of a hypothesis renaming lemmas cannot even state. *)
    α `notin` ftvar_in_aenv Θ ->
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
(* EXISTS-FRESH, INPUT-only side condition, explicit CLOSE (DESIGN.md
   §4.3).  The condition names only the INPUTS [Θ] and [P] — a rule chooses
   its binder, so it cannot avoid outputs that do not exist yet — and the
   result is re-bound by an explicit [close_ptyp_wrt_ptyp], mirroring the
   implementation's [bind_var v] after the recursive call (type.ml:88-91);
   the [ptyp_all] wrapper keeps index 0 bound, so the output stays lc.

   THE WITNESS ENTERS THE AVOID-INPUT: under the ∀ the bound variable is a
   rigid in scope, so the premise runs at [(β~tvar) ++ Θ].  This is what
   the hole rule's freshness bites on — every name generated below a
   binder avoids the binder — and it makes the junk-free discipline
   DERIVABLE ([a_guess_mono_generated_fresh]) instead of assumed; the
   renaming/opening kit is UNPROVABLE without it (a hole below a ∀ could
   otherwise generate the witness itself, and the ∀-opening bridge
   [a_guess_mono_open_at] is false on such derivations).  The paper's
   guess is context-free; [Θ] here is the relational rendering of the
   implementation's global fresh counter.  Consumer-visible cost:
   context-GENERIC guess claims ([forall Θg, a_guess_mono Θg …]) are
   retired — witness lemmas quantify the context together with an
   avoid-set bound ([forall Θg, ftvar_in_aenv Θg [<=] L -> …]). *)
| a_guess_mono__forall : forall Θ P Ξ A β,
    (* [ftvar_in_aenv], not [dom]: a payload ([α̂ ≔ τ]) may mention the
       witness, and it must not.  INPUT-only. *)
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P ->
    a_guess_mono ((β ~ abind_tvar) ++ Θ)
      (open_pskl_wrt_pskl P (pskl_var_f β)) Ξ A ->
    a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all (close_ptyp_wrt_ptyp β A)).

(** [guess^N(Q) = (Ξ'; Q')] (full-algo-spec.tex:1000): [guess^SK] is the
    identity; [guess^TY] is [a_guess_mono] read back into [pskl].
    The avoid-input [Θ] is threaded on (cluster 1 gave [a_guess_mono] one;
    running the inner guess at [nil] left that discipline INERT here, so the
    generated block avoided nothing). *)
Inductive a_guess : aenv -> a_sub_mode -> pskl -> aenv -> pskl -> Prop :=
| a_guess__sk : forall Θ Q,
    a_guess Θ a_sub_mode_sk Q nil Q
| a_guess__ty : forall Θ Q Ξ A,
    a_guess_mono Θ Q Ξ A ->
    a_guess Θ a_sub_mode_ty Q Ξ (ptyp_to_pskl A).

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

(** The free variables of a constraint list.  ⭐ It lives HERE, above the
    rules, because two of them now READ it: the collection's arrow rows
    carry the CROSS-HALF freshness guard (see [a_lookeq__arrow]).  Until
    2026-08-19 there were two identical copies of this function, one in
    algo/sub/prop_looksub.v ([ftvar_in_cstrs]) and one in
    ext_algo/def_look.v ([ftvar_in_a_cstrs], whose header said to move it
    here as soon as a [fresco/algo] consumer appeared).  It has appeared. *)
Definition ftvar_in_a_cstr (c : a_cstr) : atoms :=
  match c with
  | a_cstr_sub _ P => ftvar_in_pskl P
  | a_cstr_eq P    => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_a_cstrs (C : a_cstrs) : atoms :=
  match C with
  | nil      => empty
  | c :: C'  => ftvar_in_a_cstr c `union` ftvar_in_a_cstrs C'
  end.

Lemma ftvar_in_a_cstrs_app : forall C1 C2,
  ftvar_in_a_cstrs (C1 ++ C2)
  [=] ftvar_in_a_cstrs C1 `union` ftvar_in_a_cstrs C2.
Proof.
  induction C1 as [ | c C1' IH ]; intros; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Reserved Notation "{{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a"
  (at level 0, P at level 74, α at level 0, m at level 0, P' at level 74, Ξ at level 74, C at level 74,
   format "'{{'  Θ  ⊢  P  ≼[  α  ,  m  ]  P'  ⤳  Ξ  ⨾  C  '}}a'").
Reserved Notation "{{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a"
  (at level 0, P at level 74, α at level 0, P' at level 74, Ξ at level 74, C at level 74,
   format "'{{'  Θ  ⊢  P  ∼[  α  ]  P'  ⤳  Ξ  ⨾  C  '}}a'").

(* EXISTS-FRESH with an AVOID-INPUT context (DESIGN.md §4.3, cluster 3 of
   the freshness campaign).

   [Θ] is an INPUT the paper's context-free look judgments do not carry: it
   is the relational rendering of the implementation's global fresh counter
   ([incr counter; Bindlib.new_var], type.ml:563-565), exactly as for
   [a_guess_mono] and the solve judgments.  Without it LE-FlexR's paper-side
   side condition "fresh γ̂" (algorithmic.tex:1204) has NO rendering at all,
   and — decisively — [a_looksub_lookeq_ftv] cannot even be STATED once the
   ∀ rules leak: its repaired disjunct is "or the variable is one the run
   generated", i.e. "∉ ftvar_in_aenv Θ" (cf. [a_solve_cstr_ftv]).

   ALL FIVE ∀ rules LEAK their binder — the reference implementation
   unbinds and DISCARDS the name in every one of them
   ([constr_collect_eq]: LE-ForallInh type.ml:579-583, LE-ForallSyn :595-598,
   LE-UnivGhost1 :610-613; [constr_collect_sub]: LS-ForallR :668-672,
   LS-ForallL :685-688), and neither function ever calls [bind_var].  So the
   outputs [Ξ] and [𝒞] may mention the binder, which is precisely what the
   old cofinite rendering forbade: sharing one 𝒞 across the whole family
   silently restricted the rules to vacuous binders.

   The witness ENTERS the premise's context, so names generated below a
   binder avoid it (junk-freeness DERIVED, as in cluster 1); the side
   conditions name INPUTS only — [Θ], the looked-for variable [α], and the
   rule's input skeletons. *)
Inductive a_looksub : aenv -> atom -> mode -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_looksub__var : forall Θ α m P,               (* LS-Var *)
    {{ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P ⤳ nil ⨾ (a_cstr_sub m P :: nil) }}a
| a_looksub__absent : forall Θ α m P P',         (* LS-Absent *)
    α `notin` ftvar_in_pskl P ->
    {{ Θ ⊢ P ≼[ α , m ] P' ⤳ nil ⨾ nil }}a
| a_looksub__vacuous : forall Θ α m P,           (* LS-Vacuous: RHS is □ *)
    (* [paper-gap] ◇-DISPATCH GUARD — the runner answers a ghost
       counterpart immediately (LS/LE-Vacuous), and dispatches on the
       SUBJECT before any counterpart test, so LS-Var wins at [α]. *)
    P <> pskl_var_f α ->
    {{ Θ ⊢ P ≼[ α , m ] pskl_hole ⤳ nil ⨾ nil }}a
| a_looksub__check : forall Θ α A B Ξ C,         (* LS-Check *)
    (* SORT: [A] and [B] are TYPES in the paper (full-algo-spec.tex:1042-1049),
       matching the [a_sub__check] row this collection rule covers.  ⚠️ Only
       the TARGET is mechanized — see the SORT note on [a_looksub__forall_r]
       for why the subject is not. *)
    pskl_ghost_free B ->
    A <> pskl_var_f α ->
    guarded_pskl A ->
    guarded_pskl B ->
    {{ Θ ⊢ A ∼[ α ] B ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C }}a
| a_looksub__forall_r : forall Θ α A B Ξ C β,    (* LS-ForallR — LEAKS *)
    (* SORT — TARGET ONLY, here and at [a_looksub__check].  The paper sorts
       the collection's SUBJECT as a type too ([A], full-algo-spec.tex:1042-1056),
       and it is TRUE — but only because these two rows are reachable at the TY
       sort ALONE: they need a guarded target, and [skmod{SK}] pins the
       collection's target to [◇] at every mode.  Mechanizing it would
       therefore mean threading [skmod] through the collection's STRUCTURAL
       lemmas, which are mode-agnostic by design.  Two of them show why the
       premise is not free: [a_looksub_lookeq_subst_stable] and
       [a_looksub_lookeq_subst_gen_size] (prop_looksub.v §4, prop_decorate_sub.v
       §8) substitute an ARBITRARY skeleton into the subject, and the latter's
       consumer — [a_subtag_decoration]'s ForallL row — feeds it the node's
       guess [P1], which at the SK sort IS the raw solve output and carries
       ghosts.  The TARGET premise below has no such cost: it is read straight
       off [skmod{TY}], which every consumer already carries.
       docs/PAPER-GAPS.md. *)
    pskl_ghost_free (pskl_all_syn B) ->
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl A
                       `union` ftvar_in_pskl B) ->
    (* [paper-gap] ABSENCE-FIRST GUARD — see [a_looksub__forall_r]. *)
    α `in` ftvar_in_pskl A ->
    A <> pskl_var_f α ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
      (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}a
| a_looksub__arrow : forall Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2, (* LS-Arrow *)
    (* ⭐⭐ [paper-gap] THE CROSS-HALF FRESHNESS GUARD (2026-08-19).  Both
       premises run at the SAME [Θ] and the collection has NO SUPPLY, so an
       atom one half LEAKS as a ∀ opener and the other half INVENTS as a
       flexible may be THE SAME ATOM: [LE-ForallInh]'s side condition reads
       [β ∉ add α (ftvar Θ ∪ ftvar P ∪ ftvar P')] and [LE-FlexR]'s reads
       [γ̂ ∉ add α (add β̂ (ftvar Θ ∪ ftvar P))], and neither excludes the
       other.  Machine-checked, together with the fact that the collision is
       LOAD-BEARING — the solver reads the leaked opener as HATTED, because
       the sibling put it in [Ξ], and fires [SolE-FlexR] on it where a run
       with a fresh-name counter is stuck:
       [cex/probe_extract_conflated_opener.v].

       ⭐ IT COSTS COMPLETENESS NOTHING.  It is a THEOREM of the
       supply-threaded encoding ([e_looksub_lookeq_cstr_ftvar] bounds
       [ftvar 𝒞₁] by the intermediate supply, which the right half's block
       is drawn outside of, and symmetrically), so the reference
       implementation — one global counter, never reused — cannot violate
       it; [e_looksub_sound] discharges both conjuncts.  It is the fourth
       freshness prose-completion this encoding needs, after [AT-Abs]'s
       [uniq (αs ++ Θ1)], [a_sub__forall_l]'s [uniq (Ξ ++ Θ0)] and
       [a_guess_mono]'s.  docs/PAPER-GAPS.md.

       ⚠️ THREADING THE CONTEXT IS NOT ENOUGH, which is why this is a
       premise and not a shape change: running the second half at
       [Ξ1 ++ Θ] (what [SolS-Arrow] does) kills only the MIRROR direction —
       a LEFT-half opener is invisible to the right half whatever the
       context carries. *)
    ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty ->
    ftvar_in_a_cstrs C2 ∩ dom Ξ1 [=] empty ->
    {{ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}a ->
    {{ Θ ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}a ->
    {{ Θ ⊢ (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ] (pskl_arrow P1' P2')
        ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}a
| a_looksub__forall_l : forall Θ α m P P' Ξ C β, (* LS-ForallL — LEAKS *)
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->
    (* [paper-gap] ABSENCE-FIRST GUARD — see [a_looksub__forall_r]. *)
    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    P' <> pskl_hole ->
    (* [paper-gap] ForallR-PRIORITY GUARD — the runner tries LS-ForallR
       first at a ∀ counterpart in check mode ([forall_r_off],
       fresco/def_shapes.v).  ⚠️ NOT admissible: the two rows disagree. *)
    forall_r_off m P' ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β))
      ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a
| a_looksub__univ_ghost_l : forall Θ α m P P' Ξ C, (* LS-UnivGhostL *)
    P' <> pskl_hole ->
    (* [paper-gap] ForallR-PRIORITY GUARD — see [a_looksub__forall_l]. *)
    forall_r_off m P' ->
    {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_tophole P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a

with a_lookeq : aenv -> atom -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_lookeq__var : forall Θ α P,                  (* LE-Var *)
    {{ Θ ⊢ (pskl_var_f α) ∼[ α ] P ⤳ nil ⨾ (a_cstr_eq P :: nil) }}a
| a_lookeq__absent : forall Θ α P P',            (* LE-Absent *)
    α `notin` ftvar_in_pskl P ->
    {{ Θ ⊢ P ∼[ α ] P' ⤳ nil ⨾ nil }}a
| a_lookeq__vacuous : forall Θ α P,              (* LE-Vacuous: RHS is □ *)
    (* [paper-gap] ◇-DISPATCH GUARD — the runner answers a ghost
       counterpart immediately (LS/LE-Vacuous), and dispatches on the
       SUBJECT before any counterpart test, so LS-Var wins at [α]. *)
    P <> pskl_var_f α ->
    {{ Θ ⊢ P ∼[ α ] pskl_hole ⤳ nil ⨾ nil }}a
| a_lookeq__flex_r : forall Θ α P β α1,          (* LE-FlexR (β̂ a flex var) *)
    (* the paper's [fresh γ̂] (algorithmic.tex:1204).  [ftvar_in_aenv], not
       [dom]: a payload ([α̂ ≔ τ]) may mention the name, and it must not. *)
    α1 `notin` add α (add β (ftvar_in_aenv Θ `union` ftvar_in_pskl P)) ->
    (* [paper-gap] THE HAT.  The paper's row concludes at [β̂]; one atom class
       means the mech must SAY so, exactly as its SOLVE-layer mirror
       [a_solve_eq__flex_r] already does.  Without it the row fires at a RIGID
       variable too, where the implementation takes LE-UnivGhost2 — and there
       the two answers DISAGREE ([flex_r_off], above). *)
    a_flex_tvar Θ β ->
    P <> pskl_var_f α ->
    α `in` ftvar_in_pskl P ->
    {{ Θ ⊢ P ∼[ α ] (pskl_var_f β) ⤳ ((α1 ~ abind_flex_mono) ++ nil)
        ⨾ (a_cstr_eq (pskl_var_f α1) :: nil) }}a
| a_lookeq__arrow : forall Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,    (* LE-Arrow *)
    (* [paper-gap] CROSS-HALF FRESHNESS GUARD — see [a_looksub__arrow]. *)
    ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty ->
    ftvar_in_a_cstrs C2 ∩ dom Ξ1 [=] empty ->
    {{ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}a ->
    {{ Θ ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}a ->
    {{ Θ ⊢ (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2')
        ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}a
| a_lookeq__forall_inh : forall Θ α P P' Ξ C β,  (* LE-ForallInh — LEAKS *)
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->
    (* [paper-gap] ABSENCE-FIRST GUARD — see [a_looksub__forall_r]. *)
    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
      (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a
| a_lookeq__forall_syn : forall Θ α P P' Ξ C β,  (* LE-ForallSyn — LEAKS *)
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->
    (* [paper-gap] ABSENCE-FIRST GUARD — see [a_looksub__forall_r]. *)
    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
      (pskl_tophole P') ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost : forall Θ α P P' Ξ C,    (* LE-UnivGhost *)
    {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_tophole P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost1 : forall Θ α P P' Ξ C β, (* LE-UnivGhost1 — LEAKS *)
    β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl P
                       `union` ftvar_in_pskl P') ->
    (* [paper-gap] ABSENCE-FIRST GUARD — see [a_looksub__forall_r]. *)
    α `in` ftvar_in_pskl (pskl_tophole P) ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (pskl_tophole P) ∼[ α ]
      (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_tophole P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost2 : forall Θ α P P' Ξ C,   (* LE-UnivGhost2 *)
    guarded_pskl P' ->
    (* [paper-gap] FlexR-PRIORITY GUARD — [guarded_pskl] includes VARIABLES,
       and the runner reaches this row only after the flexible-counterpart
       test has failed ([flex_r_off], above). *)
    flex_r_off Θ P' ->
    {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ (pskl_tophole P) ∼[ α ] P' ⤳ Ξ ⨾ C }}a
| a_lookeq__univ_ghost_r : forall Θ α P P' Ξ C,  (* LE-UnivGhostR *)
    P <> pskl_var_f α ->
    guarded_pskl P ->
    {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
    {{ Θ ⊢ P ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C }}a
where "{{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a" := (a_looksub Θ α m P P' Ξ C) : fresco_a_scope
  and "{{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a" := (a_lookeq Θ α P P' Ξ C) : fresco_a_scope.

(* ===================================================================== *)
(*  Constraint solving (paper fig:constraint-solving)                     *)
(*  [Θ] threads only what the flex rules need ([binds α̂] checks); the      *)
(*  paper's judgments are context-free because [α̂] is syntactically        *)
(*  distinct there.                                                       *)
(*                                                                        *)
(*  ⭐ THE SOLVE NOW EMITS A FRESH FLEXIBLE BLOCK [Ξ] (2026-08-04).        *)
(*  SE-FlexR used to DISCARD the accumulated pattern ([P ∼ α̂ ⤳ α̂]), which *)
(*  is the whole defect behind the two machine-checked refutations         *)
(*  (docs/refutations.tex: Lemma E.17 look-completeness and Theorem 4.6).  *)
(*  The repair the authors adopted keeps the pattern, NORMALIZED by        *)
(*  [guess^TY]: a flexible position can only ever receive a ghost-free     *)
(*  skeleton, so each ghost of the pattern becomes a FRESH flexible —      *)
(*  exactly what the collection's own LE-FlexR already does.  Those fresh  *)
(*  names have to reach the caller, so [Ξ] is threaded through ALL THREE   *)
(*  solve judgments and lands in [a_extract]'s output suffix.              *)
(*                                                                        *)
(*  ⚠️ CONSEQUENCE FOR THE ∀-OPENING ROWS.  The solve used to generate no  *)
(*  names at all, so its five binder rules could run their premise at [Θ]  *)
(*  with the witness merely avoided.  Now a guess can fire BELOW such a    *)
(*  binder, and (four of the five rows CLOSE over the witness) a generated *)
(*  name equal to the witness would be captured.  The witness therefore    *)
(*  ENTERS THE PREMISE'S CONTEXT — the same avoid-input discipline         *)
(*  [a_guess_mono] and the look judgments already use (DESIGN.md §4.3):    *)
(*  [ftvar_in_aenv ((β ~ tvar) ++ Θ)] contains β, so `generated names      *)
(*  avoid enclosing witnesses' stays DERIVABLE rather than assumed.        *)
(*                                                                        *)
(*  ⭐ AND THE WITNESS AVOIDS [ftvar_in_aenv Θ], NOT MERELY [dom Θ]        *)
(*  (2026-08-04).  All five binder rows were strengthened together, for    *)
(*  the reason [a_guess_mono__forall] and every [a_looksub]/[a_lookeq]     *)
(*  binder row already carry the same set: a flexible's PAYLOAD            *)
(*  ([α̂ ≔ τ]) may mention an atom that is not in [dom Θ], so [dom] is the  *)
(*  wrong avoid-set for anything that touches the guess — and SE-FlexR     *)
(*  now does.  Concretely it is what makes the WITNESS-MOVE work: the      *)
(*  swap [swap_aenv b δ Θ] collapses to [Θ] exactly when both atoms dodge  *)
(*  [ftvar_in_aenv Θ] ([a_solve_eq_weaken_tvar], sub/look/prop_rsubst.v),    *)
(*  and the same set is what [a_solve_sub_eq_ctx_change] transports.       *)
(*  The change only SHRINKS the judgment, so every consumer (soundness,    *)
(*  decoration) is unaffected; the completeness proofs CONSTRUCT these     *)
(*  derivations and simply pick their witness from the larger avoid-set.   *)
(* ===================================================================== *)

Reserved Notation "{{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a"
  (at level 0, P at level 74, m at level 0, Q at level 74, Ξ at level 74, P' at level 74,
   format "'{{'  Θ  ⊢ₛ  P  ≼[  m  ]  Q  ⤳  Ξ  ⨾  P'  '}}a'").
Reserved Notation "{{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a"
  (at level 0, P at level 74, Q at level 74, Ξ at level 74, P' at level 74,
   format "'{{'  Θ  ⊢ₑ  P  ∼  Q  ⤳  Ξ  ⨾  P'  '}}a'").

Inductive a_solve_sub : aenv -> mode -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_solve_sub__var : forall Θ m α Q,             (* SS-Var + SS-Flex *)
    {{ Θ ⊢ₛ (pskl_var_f α) ≼[ m ] Q ⤳ nil ⨾ (pskl_var_f α) }}a
| a_solve_sub__forall_l : forall Θ m P Q Ξ P' β,   (* SS-ForallL *)
    (* exists-fresh, INPUT-only freshness + explicit CLOSE (DESIGN.md §4.3):
       the side condition names only the inputs; the result is re-bound by
       [close_pskl_wrt_pskl], mirroring the implementation's [bind_var]
       after the recursive call (type.ml:499-505).  The [pskl_all_syn]
       wrapper keeps the closed body's index 0 bound, so the output is lc.
       ⭐ THE WITNESS ENTERS THE CONTEXT (2026-08-04): the premise may now
       GENERATE names (SE-FlexR's guess), and this row CLOSES over β, so a
       generated β would be captured.  [ftvar_in_aenv] of the extended
       context contains β, which is precisely what [a_guess_mono]'s hole
       row avoids — so "the block is apart from β" is DERIVABLE.
       ⭐ [ftvar_in_aenv], NOT [dom] (2026-08-04, and see the box above the
       judgment): a flexible's PAYLOAD may mention the witness. *)
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β))
      ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_sub__univ_ghost_l : forall Θ m P Q Ξ P', (* SS-UnivGhostL *)
    {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ (pskl_tophole P) ≼[ m ] Q ⤳ Ξ ⨾ (pskl_tophole P') }}a
| a_solve_sub__vacuous : forall Θ m P,           (* SS-Vacuous: RHS is □ *)
    (* [paper-gap] SOLVE-DISPATCH GUARD — see [peel_l_off], def_shapes.v.
       [SolS-ForallL] and [SolS-UnivGhostL] are matched BEFORE this row
       (type.ml:494), and at a ∀ subject the ForallL route draws an opener
       this one does not — same answer, one more atom spent. *)
    peel_l_off P ->
    {{ Θ ⊢ₛ P ≼[ m ] pskl_hole ⤳ nil ⨾ P }}a
| a_solve_sub__check : forall Θ P Q Ξ P',        (* SS-Check *)
    (* SORT: the paper writes [solvesub{P}{TC}{B}{P'}] — the LHS is the
       accumulated PATTERN (a skeleton) but the RHS is a TYPE
       (full-algo-spec.tex:1262-1267).  The asymmetry is real: the pattern
       starts at [◇] and is a skeleton throughout, while the target is a
       mode-spine position of [P0], hence [⌈A⌉] at the TY sort. *)
    pskl_ghost_free Q ->
    guarded_pskl P ->
    guarded_pskl Q ->
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ P ≼[ mode_tc ] Q ⤳ Ξ ⨾ P' }}a
| a_solve_sub__forall_r : forall Θ P B Ξ P' β,   (* SS-ForallR *)
    (* SORT — TARGET ONLY.  The paper writes [solvesub{A}{TC}{\forall\beta.B}]
       (full-algo-spec.tex:1269-1273), i.e. it sorts BOTH sides as types; the
       LHS reading is a metavariable slip and is NOT mechanized, because this
       rule's own premise is discharged by SolS-GhostL, whose LHS is the ghost
       [◇] (:1283-1294).  Sorting the LHS would leave [◇ ≼TC ∀β.B] with no
       rule at all, and that configuration is reachable (subject [∀α.α]
       against a ∀-target: LS-Var emits [sub_TC(∀β.B)] and the pattern is
       still [◇]).  docs/PAPER-GAPS.md.  The binder is therefore named [P],
       not [A], per the mech's own convention. *)
    pskl_ghost_free (pskl_all_syn B) ->
    (* [paper-gap] SOLVE-DISPATCH GUARD — see [solve_l_off], def_shapes.v.
       [SolS-Var], [SolS-ForallL] and [SolS-UnivGhostL] are all matched
       BEFORE this row (type.ml:494); at a VARIABLE subject in particular
       the implementation answers with the variable and never peels, where
       this row would peel and spend an opener. *)
    solve_l_off P ->
    (* exists-fresh, INPUT-only freshness, NO close: the result passes
       through unchanged, so β may legitimately ESCAPE into [P'] — the
       implementation opens the RHS and DISCARDS the binder name
       ([let _, b = Bindlib.unbind b in end_rule (solve_sub (Check b) a)],
       type.ml:517-520), and the paper's rule (full-algo-spec.tex:1271)
       runs its premise at [B] with β still free.  The leak is BY DESIGN;
       ill-scoped results are filtered downstream by wf side conditions
       ([a_sub__forall_l]'s [{{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a]), not by narrowing
       this rule.  A cofinite rendering would demand ONE β-free [P'] for
       the whole family, degenerating the rule to "fires only when the
       binder is vacuous".  Consequence: [a_solve_sub_ftv] is DISJUNCTIVE
       (an output variable is an input variable or avoids [dom Θ]). *)
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl B ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
      (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a
(* ⚠️ THE SIBLING PREMISE THREADS, [Ξ2 ++ Ξ1].  Both halves may now GENERATE
   names, and a guess avoids only what its own context mentions — run both at
   [Θ] and the two blocks can pick THE SAME atom, making [Ξ1 ++ Ξ2] non-[uniq]
   and silently conflating two independently-invented flexibles in
   [P1' → P2'].  Running the second half at [Ξ1 ++ Θ] makes disjointness
   DERIVABLE from [a_guess_mono]'s avoid-input instead of an obligation the
   caller must re-arrange, and it is what the reference implementation does
   anyway (one global counter, never reused).  Same shape as
   [a_solve_cstr__eq], where the threading is forced by the pattern fold. *)
| a_solve_sub__arrow : forall Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2',  (* SS-Arrow *)
    {{ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
    {{ (Ξ1 ++ Θ) ⊢ₛ P2 ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}a ->
    {{ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
         ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}a
| a_solve_sub__ghost_l_fn : forall Θ m Q1 Q2 Ξ1 Ξ2 P1' P2',   (* SS-GhostLF *)
    {{ Θ ⊢ₑ pskl_hole ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
    {{ (Ξ1 ++ Θ) ⊢ₛ pskl_hole ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}a ->
    {{ Θ ⊢ₛ pskl_hole ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
         ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_tophole (pskl_arrow P1' P2')) }}a
| a_solve_sub__ghost_l : forall Θ B,             (* SS-GhostL *)
    (* SORT: [guarded{B}] with [B] a TYPE (full-algo-spec.tex:1283-1288). *)
    pskl_ghost_free B ->
    guarded_pskl B ->
    {{ Θ ⊢ₛ pskl_hole ≼[ mode_tc ] B ⤳ nil ⨾ (pskl_tophole B) }}a

with a_solve_eq : aenv -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_solve_eq__unit : forall Θ,                   (* SE-Unit *)
    {{ Θ ⊢ₑ pskl_unit ∼ pskl_unit ⤳ nil ⨾ pskl_unit }}a
| a_solve_eq__var : forall Θ α Q,                (* SE-Var + SE-FlexL *)
    {{ Θ ⊢ₑ (pskl_var_f α) ∼ Q ⤳ nil ⨾ (pskl_var_f α) }}a
| a_solve_eq__flex_r : forall Θ α P Ξ A,         (* SE-FlexR *)
    (* the paper's FlexR (full-algo-spec.tex:1374) is context-free and fires
       on ANY hatted variable — defined or not; [α̂ ∈ Θ] here is only the
       mech's rendering of hattedness.  The earlier [binds α abind_flex_mono]
       (undefined-only) encoding was UNFAITHFULLY narrow: a defined flexible
       nested in a structural counterpart makes the solve stuck here but not
       on paper, falsifying the completeness statements independently of the
       flexible-counterpart cex (cex_p6_flex_counterpart.v).  Widened
       2026-07-24.

       ⭐ THE OUTPUT IS THE ACCUMULATED PATTERN, NOT THE FLEXIBLE
       (2026-08-04 — the authors' repair of the row this mechanization
       refuted; docs/refutations.tex §"Suggested repair").  The old reading
       [P ∼ α̂ ⤳ α̂] DISCARDS everything the collection has already computed
       about this position: at the double-occurrence configuration it
       overwrites the eq-constraint's yield [∀γ.γ→γ] with the flexible, the
       enclosing SS-ForallL then re-binds a VACUOUS binder [∀_.β̂], and the
       continuation is scope-stuck — which is exactly why NO [a_sub] run
       existed there (cex/probe_double_occ_run.v) even though the run with
       the right instantiation does (cex/probe_solve_flexr.v).  A raw
       flexible and a ghost are the SAME epistemic situation, and the ghost
       twins SE-VacuousR / SS-Vacuous both KEEP the pattern.

       The pattern is handed through [guess^TY] rather than verbatim: what
       lands here will be ASSIGNED to [α̂], and a flexible can only receive a
       ghost-free skeleton, so each ghost becomes a FRESH flexible — the same
       move the collection's own LE-FlexR makes.  [Ξ] is that fresh block,
       and it is why all three solve judgments now carry an output suffix.
       (The [P = ◇] case — where returning [α̂] let the guess SHARE the
       flexible — is already covered by SE-GhostL, [◇ ∼ Q ⤳ Q].)

       ⚠️ AND THAT IS WHY THE SUBJECT MUST BE NONGHOST (2026-08-04; a
       FINDING on the authors' proposed rule — docs/PAPER-GAPS.md).  Under
       the OLD row the ghost-subject overlap was harmless: [◇ ∼ α̂] gave [α̂]
       by SE-GhostL and [α̂] by SE-FlexR, the SAME answer.  Under the repair
       they DISAGREE — [guess^TY(◇)] invents a FRESH [α̂1], so FlexR returns
       [α̂1] where GhostL returns the target [α̂], and the sharing that makes
       the marker's solution land on [α̂] is lost.  The reference
       implementation never takes that branch (its match puts SolE-GhostL
       and SolE-GhostGuarded strictly before SolE-FlexR — see
       [nonghost_pskl], fresco/def_shapes.v), and the paper's own
       [nonflex{P}] side condition is prose that says nothing about ghosts
       because on paper the two rows agreed.  Restoring the exclusion costs
       completeness NOTHING: at [◇] SE-GhostL is strictly more informative,
       and at [∀◇P0] SE-GhostGuarded peels to the same place.  It also keeps
       [a_solve_eq_hole_subject_inv] (sub/look/prop_rsubst.v) — "solving with
       the ghost subject returns the target verbatim", which the paper uses
       silently in every [P_i = □] subcase — TRUE. *)
    a_flex_tvar Θ α ->
    a_non_flex Θ P ->
    nonghost_pskl P ->
    a_guess_mono Θ P Ξ A ->
    {{ Θ ⊢ₑ P ∼ (pskl_var_f α) ⤳ Ξ ⨾ (ptyp_to_pskl A) }}a
| a_solve_eq__hole_l : forall Θ Q,               (* SE-GhostL *)
    {{ Θ ⊢ₑ pskl_hole ∼ Q ⤳ nil ⨾ Q }}a
| a_solve_eq__hole_r : forall Θ P,               (* SE-VacuousR *)
    {{ Θ ⊢ₑ P ∼ pskl_hole ⤳ nil ⨾ P }}a
| a_solve_eq__arrow : forall Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2',    (* SE-Arrow *)
    (* threads — see [a_solve_sub__arrow] *)
    {{ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
    {{ (Ξ1 ++ Θ) ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ P2' }}a ->
    {{ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2)
         ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}a
| a_solve_eq__forall : forall Θ P Q Ξ P' β,      (* SE-Forall *)
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
         ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q)
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_eq__tophole_both : forall Θ P Q Ξ P',  (* SE-UnivGhost *)
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_tophole P) ∼ (pskl_tophole Q) ⤳ Ξ ⨾ (pskl_tophole P') }}a
| a_solve_eq__tophole_l_all : forall Θ P Q Ξ P' β, (* SE-GhostForall *)
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_tophole P)
      ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_tophole P) ∼ (pskl_all_syn Q)
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_eq__tophole_l_guarded : forall Θ P Q Ξ P',         (* SE-GhostGuarded *)
    guarded_pskl Q ->
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_tophole P) ∼ Q ⤳ Ξ ⨾ P' }}a
| a_solve_eq__all_l_tophole : forall Θ P Q Ξ P' β, (* SE-ForallGhost *)
    β `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
      ∼ (pskl_tophole Q) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_tophole Q)
         ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
| a_solve_eq__tophole_r_guarded : forall Θ P Q Ξ P',         (* SE-GuardedGhost *)
    guarded_pskl P ->
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₑ P ∼ (pskl_tophole Q) ⤳ Ξ ⨾ P' }}a
where "{{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a" := (a_solve_sub Θ m P Q Ξ P') : fresco_a_scope
  and "{{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a" := (a_solve_eq Θ P Q Ξ P') : fresco_a_scope.

Reserved Notation "{{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}a"
  (at level 0, C at level 74, P at level 74, Ξ at level 74, Q at level 74,
   format "'{{'  Θ  ⊩  C  ⨾  P  ⤳  Ξ  ⨾  Q  '}}a'").
(* Constraint-list solving  [solve C P Q] (fig:constraint-solving, top box). *)
(* ⚠️ THE TAIL RUNS AT [Ξ1 ++ Θ].  The eq-row's fresh block is in scope for
   every later constraint — its yield [P''] is THE PATTERN the tail solves
   on, and that pattern now mentions the flexibles SE-FlexR invented.  A
   later row asking "is this variable hatted?" ([a_solve_eq__flex_r]'s
   [a_flex_tvar]) must be able to see them, which is the same fidelity
   argument [a_extract] already makes for running the solve at [Ξ ++ Θ0]. *)
Inductive a_solve_cstr : aenv -> a_cstrs -> pskl -> aenv -> pskl -> Prop :=
| a_solve_cstr__empty : forall Θ P,
    {{ Θ ⊩ nil ⨾ P ⤳ nil ⨾ P }}a
| a_solve_cstr__sub : forall Θ m Q P Ξ P',
    {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊩ (a_cstr_sub m Q :: nil) ⨾ P ⤳ Ξ ⨾ P' }}a
| a_solve_cstr__eq : forall Θ Q C P Ξ1 Ξ2 P' P'',
    {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}a ->
    {{ (Ξ1 ++ Θ) ⊩ C ⨾ P'' ⤳ Ξ2 ⨾ P' }}a ->
    {{ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ (Ξ2 ++ Ξ1) ⨾ P' }}a
where "{{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}a" := (a_solve_cstr Θ C P Ξ Q) : fresco_a_scope.

Reserved Notation "{{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}a"
  (at level 0, P at level 74, NM at level 0, α at level 0, m at level 0, P' at level 74, Ξ at level 74, Q at level 74,
   format "'{{'  Θ0  ⊢  P  ⊳[  NM  ,  α  ,  m  ]  P'  ⤳  Ξ  ↪  Q  '}}a'").
(* The look judgment [look[N][M]{α}{P}{P'}{Q}[Ξ]] (fig:poly-info-extraction,
   top box): collect constraints, solve them against the empty input [□],
   then apply [guess[N]]. *)
(* ⚠️ THE SOLVE RUNS AT [Ξ ++ Θ0], NOT AT [Ξ] ALONE.  The paper's constraint
   solving is CONTEXT-FREE — [solve C P Q], [solveeq P Q P'] and
   [guess^N(Q)] carry no context at all (full-algo-spec.tex:1216-1375) —
   because there [α̂] is a syntactically distinct metavariable class.  The
   mech has ONE atom class, so [a_solve_eq__flex_r] must consult a context to
   decide HATTEDNESS; that is the only context-sensitive rule in the whole
   solve cluster.  Handing it [Ξ] alone therefore hides Θ0's flexibles and
   makes the rule UNFAITHFULLY NARROW — the very error already corrected once
   at [a_solve_eq__flex_r] itself (see its comment: the undefined-only
   [binds α abind_flex_mono] reading, widened 2026-07-24).  It is not
   harmless: a Θ0-flexible target is reachable ([skmod{TY}] at TC makes P0 a
   TYPE, and a type may BE a flexible of Θ0), and then a non-first
   [eq α̂] constraint needs SE-FlexR, which [Ξ] cannot supply — so P6-L
   ([a_extract_complete_gen]) is not provable against the narrow reading.
   docs/DESIGN-completeness-subtyping.md §7.4.
   Soundness is unaffected: its only consumers are [a_extract_decls] (which
   reads Ξ, not the solve) and [a_extract_decorate], whose solve lemmas
   [solve_cstr_top_guarded_tg] / [solve_cstr_decorate] quantify Θ universally
   and never mention it in their conclusions. *)
(* ⭐ THE OUTPUT SUFFIX HAS THREE BLOCKS (2026-08-04).  The solve now emits
   its own fresh flexibles [Ξs] (SE-FlexR's [guess^TY] of the accumulated
   pattern), so the look's suffix is [Ξ ++ Ξs ++ Ξ'] — collection, solving,
   final guess — and each stage's avoid-input is everything generated before
   it.  All three are blocks of UNDEFINED flexibles, so their relative order
   is semantically immaterial (the homogeneous-flex reorder kit of
   sub/look/prop_eq_cstr.v moves between them); it is fixed here only
   because [app] is not commutative on the nose. *)
Inductive a_extract : aenv -> a_sub_mode -> atom -> mode -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_extract__solve : forall Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q',
    {{ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
    {{ (Ξ ++ Θ0) ⊩ C ⨾ pskl_hole ⤳ Ξs ⨾ Q }}a ->
    (* the guess runs AFTER the collection AND the solving, so its
       avoid-input is the whole [Ξs ++ Ξ ++ Θ0] — this is what makes the
       three halves of the output block [Ξ ++ Ξs ++ Ξ'] disjoint *)
    a_guess (Ξs ++ Ξ ++ Θ0) NM Q Ξ' Q' ->
    (* ⭐⭐ [paper-gap] THE CROSS-LAYER FRESHNESS GUARD (2026-08-20): the
       FOLD's generated flexibles are fresh for the CONSTRAINTS it is
       solving.  docs/PAPER-GAPS.md.

       ⛔ WHY IT IS OWED, and it is the same species as [a_looksub__arrow]'s
       CROSS-HALF guard one layer down.  The collection LEAKS openers into
       [C] — all five of its ∀ rows do — and a leaked opener is bound
       NOWHERE: not in [Θ0], not in [Ξ].  The fold then runs at [Ξ ++ Θ0]
       and [SE-FlexR]'s guess draws its flexibles fresh for
       [ftvar_in_aenv (Ξ ++ Θ0)] ONLY, so it MAY DRAW ONE.  The two roles
       then collapse onto one atom: a later [eq γ] constraint reads γ as
       FLEXIBLE (it is in [Ξs]) where the reference implementation — which
       never reuses a name — reads a rigid free atom and takes a different
       rule.  ⇒ the run is not the implementation's.

       ✅ IT COSTS THE THREADED ENCODING NOTHING, and that is a THEOREM
       ([e_extract_solve_guard], ext_algo/prop_lift.v): [e_looksub]'s
       constraints live in the supply it has already SPENT and
       [e_solve_cstr]'s block is drawn STRICTLY ABOVE it, so
       [e_extract_sound] discharges the guard from facts its proof already
       computes.  Same shape as [e_looksub_lookeq_cstr_old] for the
       cross-half guard.

       ⚙ LAST, not after the solve premise, so every consumer's positional
       tactic list grows at its END. *)
    ftvar_in_a_cstrs C ∩ dom Ξs [=] empty ->
    (* ⭐⭐ [paper-gap] THE GUESS'S HALF OF THE SAME GUARD (2026-08-21).
       docs/PAPER-GAPS.md.

       ⛔ WHY IT IS OWED, and it is the SAME SPECIES as the premise above.
       The collection leaks openers into [C] and the FOLD leaks its own into
       [Q]; a leaked opener is bound NOWHERE — not in [Θ0], not in [Ξ], not
       in [Ξs] — and [a_guess_mono]'s hole row draws its flexible fresh for
       [ftvar_in_aenv] of its CONTEXT only ([a_guess_mono_generated_fresh]
       is context-only, NOT subject-aware).  ⇒ THE FINAL GUESS MAY DRAW A
       LEAKED OPENER, and the two roles then collapse onto one atom exactly
       as they could at the fold before its own guard: one name is at once a
       rigid ∀-witness and a generated flexible, and the reference
       implementation — one global counter, never reused — makes no such run.

       ✅ IT COSTS THE THREADED ENCODING NOTHING, and that is a THEOREM
       ([e_extract_sound], ext_algo/prop_extract.v): [e_guess]'s block is
       drawn STRICTLY ABOVE the supply that already holds both [C]'s and
       [Q]'s atoms ([e_guess_block_fresh]), so soundness discharges it from
       facts its proof already computes.

       ⚙ LAST, so every consumer's positional tactic list grows at its END. *)
    (ftvar_in_a_cstrs C ∪ ftvar_in_pskl Q) ∩ dom Ξ' [=] empty ->
    {{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ (Ξ ++ Ξs ++ Ξ') ↪ Q' }}a
where "{{ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}a" := (a_extract Θ0 NM α m P P' Ξ Q) : fresco_a_scope.

(* ===================================================================== *)
(*  Algorithmic consistency  [Θ0 ⊢[Δ1|Δ2][P0] P ~ Q ⊣ Θ1]                 *)
(*  (fig:alg-consistency).  The finalized paper carries TWO auxiliary      *)
(*  bound-variable sets: Δ1 tracks binders from the input [P0], Δ2 from    *)
(*  [P]; Ghost/GhostR restrict the output fill against them so [Q] is a    *)
(*  valid refinement of both inputs.                                       *)
(* ===================================================================== *)
(* ===================================================================== *)
(*  Flexible-variable machinery (fig:alg-consistency, lower boxes).       *)
(*  [a_assign Θ0 Ξ α̂ P Θ1] = [Θ0 | Ξ ⊲ α̂ := P ⊣ Θ1];                      *)
(*  [a_unify Θ0 α̂ β̂ Θ1]    = [Θ0 ⊲ α̂ ∼ β̂ ⊣ Θ1];                          *)
(*  [a_consis ...]          = algorithmic consistency (above).            *)
(*  Rules recurse on the list HEAD (the paper's rightmost entry).          *)
(* ===================================================================== *)

(* All THREE judgments are MUTUALLY inductive — the recursion cycle is

     consis --Flex-------------> unify
     consis --FlexL / FlexR----> assign
     unify  --Flex-Flex-Assign-> consis     (premise is the two-slot [∼])
     assign --Assign-Assign----> consis     (premise is the two-slot [∼])

   Both back-edges are the paper's OUTPUT-SUPPRESSED consistency abbreviation
   (full-algo-spec.tex:1440-1442: "we write [Θ₀ ⊢ P ∼ P₀ ⊣ Θ₁] for
   [Θ₀ ⊢[P₀] P ∼ Q ⊣ Θ₁] when the output [Q] is not used"), i.e. the LEFT slot
   is the SUBJECT and the RIGHT slot is the INPUT [P₀].  The paper's own proofs
   expand them exactly so and appeal to "the IH of consistency"
   (consistency-proofs.tex:1636-1643 for Flex-Flex-Assign, :1720-1724 for
   Assign-Assign), which is why its soundness proof is a 3-WAY mutual induction
   "on the algorithmic consistency derivation together with the two auxiliary
   judgements of variable unification and assignment" (:1562).  The reference
   implementation agrees: both [U-Flex-Flex-Assign] and [U-Assign-Assign] call
   [join_sk] — the consistency/join function — not [join_var] / [assign]
   (paper/artifact/implementation/lib/type.ml:316-321, :358-363).

   Prose-completion (Barendregt): the paper's "fresh β̄" in Assign-SolveM is
   GLOBALLY fresh, but a solve node only sees its local tail; with the mutual
   cycle it can fire deep inside a consistency premise, BELOW entries the skip
   rules have walked past, so a guessed name could collide with a walked head
   and re-attaching it would break context well-formedness.  Each of the eight
   RE-ATTACHING rules therefore states, of the entry it puts back, that the
   premise did not reinvent it: [β ∉ dom Θ1].  This is the same discipline
   [a_sub_flex] carries, and it LOSES NOTHING — prop_swap.v §13b proves the
   rule fires whenever a premise-free version would, the run's generated names
   merely transposed (a derivation is finitely supported, so a fresh γ always
   exists and equivariance moves the run to it while fixing every input).

   ⚠️ Do NOT reintroduce a used-name set [F] as a fourth index: it is a
   mech-only device the paper does not have, and it cannot coexist with the
   §13b argument, which needs [β ∉ F] — false at a premise running at
   [add β F].  DESIGN.md §4.3. *)
Inductive a_assign : aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_assign__univ_ghost_id : forall Θ0 α,                (* Assign-UnivGhost-Id *)
    {{ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ nil ] α ≔ (pskl_tophole (pskl_var_f α))
      ⊣ ((α ~ abind_flex_mono) ++ Θ0) }}a
| a_assign__solve_m : forall Θ0 Ξ α P βs τ,             (* Assign-SolveM *)
    α `notin` ftvar_in_pskl P ->
    a_guess_mono Θ0 P βs τ ->
    (* the paper binds the result to the SORTED metavariable τ: the rule
       applies only when guess^TY returns a monotype (hence Solve-M);
       otherwise assignvar fails — a monomorphic α̂ has no polytype solution.
       Mirrors the implementation's [if not (is_mono tau) then raise]. *)
    mono_ptyp τ ->
    (* the paper's "fresh β̄" (prose-completion, cf. PAPER-GAPS) *)
    uniq βs ->
    (forall α1, α1 `in` dom βs ->
       α1 `notin` add α (dom (Ξ ++ Θ0))) ->
    {{ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0) }}a
| a_assign__assign : forall Θ0 Θ1 Ξ α β τ P Q,          (* Assign-Assign *)
    (* The premise is CONSISTENCY over the MERGED context [Θ₀,Ξ = Ξ ++ Θ0],
       with subject [α̂[τ/β̂]] and input [P[τ/β̂]], output dropped.  [Δ₁∣Δ₂] are
       omitted in the paper, which per full-algo-spec.tex:1472-1473 means BOTH
       EMPTY.

       The premise ABSORBS [Ξ] into the context and resets the pending suffix:
       consistency has no [Ξ] slot, and its FlexL rule restarts the assignment
       with [| ·].  The implementation does exactly this —
       [join_sk (subst p) (subst α̂) (xi @ theta)], type.ml:358-363.

       BOTH SIDES ARE SUBSTITUTED, and [α̂ = β̂] is REACHABLE — do NOT add an
       [α̂ ≠ β̂] premise and do NOT simplify the subject to [pskl_var_f α].
       Nothing requires an assignment's subject to be an UNDEFINED flex var:
       neither [a_consis__flex_l] nor the implementation's [U-FlexL]
       ([| p0, MFlex alpha -> assign alpha p0 [] theta], type.ml:182-185) guards
       on it.  So a DEFINED [α̂] can be the subject, the walk then reaches [α̂]'s
       OWN definition, and this rule must fire with [β̂ = α̂] — whereupon the
       subject [α̂[τ/α̂]] is [τ], not a variable.  (Witness: [Θ = α̂ ≔ unit→unit],
       subject [α̂], input [unit→unit]: FlexL, then the walk hits the head
       [α̂ ≔ τ].  With [α̂ ≠ β̂] premised, NO rule fires and assignvar is stuck.)
       The implementation computes exactly this — [subst_var (MFlex alpha) tau
       beta] with [beta = alpha] reduces to [tau].  For [α̂ ≠ β̂] the subject
       reduces back to [pskl_var_f α] by one [eq_var] split. *)
    (* HATTED SUBJECT (paper metavariable convention, cf. PAPER-GAPS — the same
       prose-completion [a_unify__flex_assign] already carries, for the same
       reason).  Every OTHER [a_assign] rule derives "α̂ is flexible" from its own
       shape (Assign-UnivGhost-Id / Assign-SolveM match on [α ~ abind_flex_mono])
       or from its [a_assign] IH; this one cannot, since its premise is a
       CONSISTENCY derivation.  Without it the rule is WRONG, not merely weak:
       consistency's [Rigid] rule accepts a var subject for a RIGID [α], so the
       assignment would be allowed to target a rigid type variable.  Stated on
       the CONCLUSION's context, which is what covers the [β̂ = α̂] case (there
       [α̂] IS the head binding, so it is not in [Θ0] at all). *)
    a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α ->
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    {{ (Ξ ++ Θ0) ⊢[ empty | empty
         | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
      (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q ⊣ Θ1 }}a ->
    {{ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono_def τ) ++ Θ1) }}a
| a_assign__depend : forall Θ0 Θ1 Ξ α β P,              (* Assign-Depend *)
    (* [Ξ] grows at its TAIL (the paper's [Θ₀ | β̂,Ξ]; the implementation's
       [assign alpha p (xi @ [hd]) theta]).  Consing at the head instead would
       REVERSE the dependency block relative to [Θ₀,Ξ,β̄,α̂≔τ] in Assign-SolveM
       — inert on its own (every [Ξ] entry is an undefined flex var, so their
       relative order carries no information) but wrong for Assign-Assign,
       whose premise context is literally [Ξ ++ Θ0]. *)
    α <> β ->
    β `in` ftvar_in_pskl P ->
    {{ Θ0 ⊲[ Ξ ++ (β ~ abind_flex_mono) ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a
| a_assign__skip : forall Θ0 Θ1 Ξ α β P,                (* Assign-Skip *)
    α <> β ->
    β `notin` ftvar_in_pskl P ->
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((β ~ abind_flex_mono) ++ Θ1) }}a
| a_assign__skip_rigid : forall Θ0 Θ1 Ξ α β P,          (* Assign-SkipRigid *)
    β `notin` ftvar_in_pskl P ->
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ ((β ~ abind_tvar) ++ Θ1) }}a
| a_assign__skip_tm_var : forall Θ0 Θ1 Ξ α x A P,       (* Assign-SkipTmVar *)
    (* NAMING: the entry's payload is a [ptyp], so [A]. *)
    x `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((x ~ abind_var_typ A) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_typ A) ++ Θ1) }}a
| a_assign__skip_tm_skl : forall Θ0 Θ1 Ξ α x Q P,       (* Assign-SkipTmVar (skl) *)
    x `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
    {{ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
      ⊣ ((x ~ abind_var_skl Q) ++ Θ1) }}a

with a_unify : aenv -> atom -> atom -> aenv -> Prop :=
(* NB the SUBJECTS are atoms.  The paper's [unifyvar{α̂}{β̂}] has HATTED
   metavariables, i.e. its subjects are always flexible VARIABLES; taking
   general monotypes here was what forced the (now deleted) [a_unify_var_inv].
   The substitution in Flex-Flex-Assign can of course turn a subject into an
   arbitrary monotype — and that is exactly why its premise drops into
   CONSISTENCY, which takes skeletons. *)
| a_unify__flex_id : forall Θ0 α,                        (* Flex-Flex-Id *)
    (* The paper's premise is [α̂ ∈ dom(Θ₀)] — the hatted metavariable means
       "a flexible variable", DEFINED or NOT (the implementation's guard is
       [is_in_dom_ alpha theta], type.ml:302).  Demanding [abind_flex_mono]
       here would be gratuitously strict: a DEFINED [α̂] would have to route
       through Flex-Flex-Assign instead (whose premise degenerates to the
       consistency [τ ∼ τ]), so no derivation is lost either way — but the
       rule would not be the paper's. *)
    a_flex_tvar Θ0 α ->
    {{ Θ0 ⊲ α ≈ᵘ α ⊣ Θ0 }}a
| a_unify__flex_l : forall Θ0 α β,                       (* Flex-Flex-L *)
    α <> β ->
    (* hatted payload (paper metavariable convention, cf. PAPER-GAPS) *)
    a_flex_tvar Θ0 β ->
    {{ ((α ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0) }}a
| a_unify__flex_r : forall Θ0 α β,                       (* Flex-Flex-R *)
    α <> β ->
    a_flex_tvar Θ0 α ->
    {{ ((β ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0) }}a
| a_unify__flex_assign : forall Θ0 Θ1 α1 τ α β Q,         (* Flex-Flex-Assign *)
    (* [paper-gap] The premise's [∼] is CONSISTENCY, not [unifyvar].  The paper
       (full-algo-spec.tex:1440-1442) writes "we write Θ₀ ⊢ P ∼ P₀ ⊣ Θ₁ for
       Θ₀ ⊢[P₀] P ∼ Q ⊣ Θ₁ WHEN THE OUTPUT Q IS NOT USED" — so the two-slot form
       is consistency with SUBJECT [α̂[τ/α1̂]], INPUT [β̂[τ/α1̂]] and the output
       dropped.  [Δ₁∣Δ₂] are omitted there, which per :1472-1473 means BOTH
       EMPTY.  The rule drops out of [unifyvar] precisely because substituting
       the definition can turn a variable subject into an arbitrary MONOTYPE,
       which only consistency can handle (via FlexL / FlexR / the structural
       rules).

       Recursing into [a_unify] here — as this rule previously did — left the
       algorithm STUCK on any non-variable definition (machine-checked at the
       time; now a SUCCESS regression test, algo/test_unify_regression.v).
       Hence [a_unify] and [a_consis] are MUTUAL, which
       is also how the paper's own soundness proof is organised
       (consistency-proofs.tex:1562: "by mutual induction on the algorithmic
       consistency derivation together with the two auxiliary judgements of
       variable unification and assignment"). *)
    (* hatted subjects (paper metavariable convention, cf. PAPER-GAPS — the same
       prose-completion already applied to Flex-Flex-L/R's payload).  The other
       rules derive this from their own shape or their IH; this one cannot, since
       its premise is a CONSISTENCY derivation. *)
    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α ->
    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β ->
    α1 `notin` dom Θ1 ->                    (* prose-completion (Barendregt) *)
    {{ Θ0 ⊢[ empty | empty
         | (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))) ]
      (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))) ∼ Q ⊣ Θ1 }}a ->
    {{ ((α1 ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β
      ⊣ ((α1 ~ abind_flex_mono_def τ) ++ Θ1) }}a
| a_unify__flex_skip : forall Θ0 Θ1 α1 α β,               (* Flex-Flex-Skip *)
    α1 <> α ->
    α1 <> β ->
    α1 `notin` dom Θ1 ->                    (* prose-completion (Barendregt) *)
    {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
    {{ ((α1 ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((α1 ~ abind_flex_mono) ++ Θ1) }}a
| a_unify__skip_other : forall Θ0 Θ1 c b α β,            (* Flex-Flex-Skip' *)
    (b = abind_tvar \/
     (exists A, b = abind_var_typ A) \/
     (exists Q, b = abind_var_skl Q)) ->
    c `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
    {{ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((c ~ b) ++ Θ1) }}a

with a_consis : atoms -> atoms -> aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_consis__ghost : forall Δ1 Δ2 Θ0 P0,                     (* Ghost *)
    Δ2 ∩ ftvar_in_pskl P0 [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_hole ∼ P0 ⊣ Θ0 }}a
| a_consis__unit : forall Δ1 Δ2 Θ0,                         (* Unit *)
    {{ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] pskl_unit ∼ pskl_unit ⊣ Θ0 }}a
| a_consis__rigid : forall Δ1 Δ2 Θ0 α,                      (* Rigid *)
    binds α abind_tvar Θ0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ0 }}a
| a_consis__arrow : forall Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2, (* Arrow *)
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}a ->
    {{ Θ1 ⊢[ Δ1 | Δ2 | P0b ] P2 ∼ Q2 ⊣ Θ2 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
      (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2) ⊣ Θ2 }}a
(* EXISTS-FRESH, INPUT-only side condition, explicit CLOSE (DESIGN.md §4.3,
   the freshness campaign's cluster 4).  ⚠️ NOT a repair: unlike the look /
   solve / guess clusters, these three rows CLOSE — the skeleton output is
   re-bound and the context output strips the binder — so the cofinite
   rendering was NOT degenerate.  Its equivalence with this one is
   MACHINE-CHECKED, in both directions, by the [_cofinite] admissibility
   lemmas ([a_consis_forall_inh_cofinite] et al, prop_consis_rename.v §9),
   which is also what consumers wanting a family should apply.  The
   conversion is for ONE freshness discipline per layer.

   The avoid-input is [ftvar_in_aenv] (domain PLUS payloads — an [α̂ ≔ τ]
   may mention the witness), the inputs' [ftvar_in_pskl], and the two
   bound-variable sets; the OUTPUTS [Q] and [Θ1] are not named, and must
   not be (the algorithm has not computed them when it picks α).
   Soundness' invariant conjunct, the one place that looked like it
   needed [α ∉ Δ], is discharged instead from [α ∉ dom Θ1], which the
   premise's own output well-formedness supplies.  [Θ1] needs
   no condition — an output payload can never mention the binder, because
   the walk crosses it only through [Assign-SkipRigid], whose own side
   condition demands [α ∉ ftv] of the assigned skeleton
   ([a_assign_unify_consis_tvar_prefix], L8). *)
| a_consis__forall_inh : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,       (* ForallInh: α to BOTH *)
    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
      `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ (add α Δ1) | (add α Δ2)
        | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
      (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
      ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
      (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}a
| a_consis__forall_syn : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,       (* ForallSyn: α to Δ2 *)
    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
      `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ Δ1 | (add α Δ2) | (pskl_tophole P0) ]
      (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
      ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
      (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}a
| a_consis__univ_ghost : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,         (* UnivGhost *)
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
      (pskl_tophole P) ∼ (pskl_tophole Q) ⊣ Θ1 }}a
| a_consis__univ_ghost1 : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,      (* UnivGhost1: α to Δ1 *)
    (* exists-fresh + close, as ForallInh/ForallSyn above *)
    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
      `union` ftvar_in_pskl P `union` Δ1 `union` Δ2 ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ (add α Δ1) | Δ2
        | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
      (pskl_tophole P) ∼ Q
      ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
      (pskl_tophole P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}a
| a_consis__univ_ghost2 : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,        (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_tophole P) ∼ Q ⊣ Θ1 }}a
| a_consis__flex : forall Δ1 Δ2 Θ0 Θ1 α β,                  (* Flex *)
    {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}a
(* ⭐ [P0 <> ◇] / [P <> ◇] on the two FlexL/FlexR rows render the reference
   implementation's DISPATCH ORDER, exactly as [nonghost_pskl] does for
   [SE-FlexR] above (:721, and see its header).  [a_consis]'s consistency
   clause in [type.ml] matches the PATTERN first and its hole arm is
   unconditional in the subject, so the implementation NEVER reaches FlexL
   at a [◇] pattern; the mirror arm bars FlexR at a [◇] subject.  A
   relational encoding has no match order, so each exclusion must be a
   premise — and [a_non_flex] does NOT supply it ("nonflex{P0} rules out a
   flexible VARIABLE, not a hole", cex/probe_consis_ghost_flex.v).

   The guards select the ghost-first output.  At a [◇] pattern,
   [C-GhostR] leaves the flexible unsolved, whereas FlexL introduces a
   fresh unconstrained alias; the mirror holds with [C-Ghost].  These
   concrete answers are EQUIGENERAL: cex/probe_inc_more_general.v checks
   information increases in both directions.  Their different contexts
   do not demonstrate a loss of optimality.  Completeness with the guards
   is proved separately by [a_consis_complete].  Without the guards the
   rules admit BOTH outputs, which is the divergence
   docs/HANDOFF-close-consis-unrestricted.md was written about: five
   candidate relations between those two outputs are machine-checked
   refuted (cex/probe_consis_ghost_flex.v, probe_isub_too_strong.v,
   probe_inc_head_blind.v, probe_assign_migrates.v,
   probe_collapse_orientation.v).  [paper-gap] filed in docs/PAPER-GAPS.md
   beside SE-FlexR's. *)
| a_consis__flex_l : forall Δ1 Δ2 Θ0 Θ1 α P0,               (* FlexL *)
    a_non_flex Θ0 P0 ->
    P0 <> pskl_hole ->
    {{ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}a
| a_consis__flex_r : forall Δ1 Δ2 Θ0 Θ1 α P,                (* FlexR *)
    a_non_flex Θ0 P ->
    P <> pskl_hole ->
    {{ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] P ∼ (pskl_var_f α) ⊣ Θ1 }}a
| a_consis__ghost_r : forall Δ1 Δ2 Θ0 P,                    (* GhostR *)
    Δ1 ∩ ftvar_in_pskl P [=] empty ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | pskl_hole ] P ∼ P ⊣ Θ0 }}a
| a_consis__univ_ghost_r : forall Δ1 Δ2 Θ0 Θ1 P0 P Q,       (* UnivGhostR *)
    guarded_pskl P ->
    a_non_flex Θ0 P ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ] P ∼ Q ⊣ Θ1 }}a
where "{{ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}a" := (a_assign Θ Ξ α P Θ') : fresco_a_scope
and "{{ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}a" := (a_unify Θ α β Θ') : fresco_a_scope
and "{{ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}a" :=
  (a_consis Δ1 Δ2 Θ P0 P Q Θ') : fresco_a_scope.

(* Mutual induction scheme for the algorithmic judgments.  Kept next to the
   inductives (it needs only them) so the metasubst-layer flex-preservation
   bundle in prop_inc_strengthen can use it WITHOUT importing prop_consis_sound
   (which would create a prop_inc_strengthen -> prop_consis_sound cycle). *)
Scheme a_assign_mind := Induction for a_assign Sort Prop
  with a_unify_mind  := Induction for a_unify  Sort Prop
  with a_consis_mind := Induction for a_consis Sort Prop.
Combined Scheme a_assign_unify_consis_mutind
  from a_assign_mind, a_unify_mind, a_consis_mind.

(* Both-Δ-empty form (the paper "omit[s] them when both are empty"). *)
Notation "{{ Θ ⊢[ P0 ] P ∼ Q ⊣ Θ' }}a" := (a_consis empty empty Θ P0 P Q Θ')
  (at level 0, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  Θ  ⊢[  P0  ]  P  ∼  Q  ⊣  Θ'  '}}a'") : fresco_a_scope.

(* [aconsis{Θ0}{P}{P0}{Θ1}]: output-suppressed abbreviation (paper). *)
Definition a_consis_chk (Θ0 : aenv) (P P0 : pskl) (Θ1 : aenv) : Prop :=
  exists Q, {{ Θ0 ⊢[ P0 ] P ∼ Q ⊣ Θ1 }}a.

(* ===================================================================== *)
(*  Algorithmic subtyping  [{{ Θ0 ⊢[ N | M | P0 ] P ⩽ Q ⊣ Θ1 }}a]         *)
(*  (fig:alg-subtyping) MUTUAL with the flexible-variable auxiliary        *)
(*  judgment (second box), here [a_sub_flex]: [FlexMono] hands a bare      *)
(*  flex LHS [α̂] to it; its [Flex-Solve] re-enters [a_sub].                *)
(* ===================================================================== *)
Inductive a_sub : a_sub_mode -> mode -> pskl -> aenv -> pskl -> pskl -> aenv -> Prop :=
| a_sub__infer : forall NM P Θ0,                              (* Infer *)
    a_sub NM mode_ti pskl_hole Θ0 P P Θ0
| a_sub__check : forall Θ0 Θ1 A B,                            (* Check *)
    (* SORT (2026-08-06).  The paper writes this rule with the metavariables
       [A] and [B] — TYPES, not skeletons (full-algo-spec.tex:799-804, and
       [guarded{T,B}] in the decorated mirror, decorated-algosub.tex:57).  The
       mech keeps ONE [pskl] carrier for both sorts, so the restriction is a
       premise: ghost-freeness IS "being a painted [ptyp]"
       ([pskl_ghost_free_to_ptyp]).  On the target it is not even new
       information — [skmod{TY}{B}{TC}] already forces [B = ⌈A0⌉]
       ([a_ty_mode_compat_tc_ghost_free]) — but [skmod] is the paper's
       IMPLICIT side condition on the judgment, which a Coq [Inductive] has
       no way to carry, so the rules that need it state it.

       The SUBJECT's sort is stated too: both figures agree on it here (plain
       [A], decorated [T]), unlike at ForallR.  It is not free — nothing in
       [a_sub] forces it — but it IS invariant: at the TY sort the subject
       comes from typing, which only ever hands [a_sub] a [ptyp] painting. *)
    pskl_ghost_free A -> pskl_ghost_free B ->
    guarded_pskl A -> guarded_pskl B ->
    a_consis_chk Θ0 A B Θ1 ->
    a_sub a_sub_mode_ty mode_tc B Θ0 A B Θ1
| a_sub__forall_r : forall α Θ0 Θ1 Ξ A B,                     (* ForallR *)
    (* SORT: the paper's target here is [∀α.B] with [B] a TYPE
       (full-algo-spec.tex:806-811) — see [a_sub__check].  Only the TARGET is
       constrained: the paper's two figures DISAGREE on the subject (the plain
       rule writes [A], the decorated one writes the skeleton [S],
       decorated-algosub.tex:64), and the subject's sort is pinned by the
       Check leaf this rule eventually reaches anyway. *)
    pskl_ghost_free (pskl_all_syn B) ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->                                          (* Barendregt: the run's new names avoid the input (prose-completion) *)
    (* ⚠️ EXISTS-FRESH, deliberately (encoding fix 2026-07-31).  The paper's
       rule (full-algo-spec.tex:806) runs ONE fresh α and discards the junk
       suffix Ξ ("anything in Ξ is not mentioned in the result") — and that
       junk may legitimately MENTION α (an extraction guess eq-constrained
       against the binder can be solved above it), so a COFINITE premise
       sharing Ξ across the whole family is unsatisfiable in reachable
       configurations and breaks completeness.  The freshness side condition
       is the paper's Barendregt convention, prose-completed — the same
       style as [a_sub_flex__solve]'s deposited names.  Consumers that need
       the binder away from ambient data re-freshen via renaming lemmas
       (cf. prop_soundness_sub's [a_subtag_decoration] ForallR case). *)
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_pskl A `union` ftvar_in_pskl B ->
    a_sub a_sub_mode_ty mode_tc (open_pskl_wrt_pskl B (pskl_var_f α))
      ((α ~ abind_tvar) ++ Θ0) A (open_pskl_wrt_pskl B (pskl_var_f α))
      (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
    a_sub a_sub_mode_ty mode_tc (pskl_all_syn B) Θ0 A (pskl_all_syn B) Θ1
| a_sub__univ_ghost_r : forall Θ0 P,                          (* UnivGhostR *)
    guarded_pskl P ->
    a_sub a_sub_mode_sk mode_tc pskl_hole Θ0 P (pskl_tophole P) Θ0
| a_sub__flex_mono : forall NM M P0 Θ0 Θ1 α Q,                (* FlexMono *)
    (* NAMING: the OUTPUT is the paper's [Q] — a skeleton, not a type
       (full-algo-spec.tex:820-824), so [Q] and not [A] here and in the
       whole [a_sub_flex] family below (A/B/C = ptyp/btyp/utyp,
       P/Q/R = pskl/bskl/uskl). *)
    a_sub_flex NM M P0 Θ0 nil α Q Θ1 ->
    a_sub NM (mode_fn M) P0 Θ0 (pskl_var_f α) Q Θ1
| a_sub__arrow : forall NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,    (* Arrow *)
    {{ Θ0 ⊢[ P0a ] P1 ∼ Q1 ⊣ Θ1 }}a ->
    a_sub NM M P0b Θ1 P2 Q2 Θ2 ->
    a_sub NM (mode_fn M) (pskl_arrow P0a P0b) Θ0 (pskl_arrow P1 P2)
      (pskl_arrow Q1 Q2) Θ2
| a_sub__forall_l : forall α NM M P0 Θ0 Θ1 P Q Ξ P1,          (* ForallL *)
    M <> mode_ti ->
    (guarded_pskl P0 \/ P0 = pskl_hole) ->
    (* EXISTS-FRESH (campaign cluster 5, 2026-08-02), with the canon's
       input-only side condition.  Unlike [a_sub__forall_r]'s 2026-07-31 fix
       this is a UNIFORMITY conversion, not a repair: the cofinite rendering
       was FAITHFUL here even though the shared outputs [Ξ]/[P1] are produced
       under the binder and not re-bound, because the look cluster's generated
       names already avoid the looked-for variable, so ONE instance generates
       the whole family with the SAME [Ξ ↪ P1]
       ([a_extract_family_of_instance], sub/look/prop_extract.v).
       Consumers that want a family apply that lemma. *)
    α `notin` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P
      `union` ftvar_in_pskl P0 ->
    {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}a ->
    (* prose-completion (PAPER-GAPS): the paper's "fresh" Ξ — [a_lookeq]'s
       LE-FlexR and [a_guess_mono]'s hole rule pick arbitrary names, so
       re-attaching Ξ needs the freshness stated. *)
    uniq (Ξ ++ Θ0) ->
    (* the paper's [Θ₀,Ξ ⊢ P₁] is its DISCIPLINED skeleton wf (there is no
       weak judgment in the paper; [a_scope_pskl]'s scoping-only reading is the
       mech/impl liberalism, WF-SIDE-CONDITIONS.md) — the instantiation must
       not smuggle a binder into a ∀◇-body (∀α.∀◇.(α→α) is wf nowhere). *)
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
    a_sub NM M P0 (Ξ ++ Θ0) (open_pskl_wrt_pskl P P1) Q Θ1 ->
    a_sub NM M P0 Θ0 (pskl_all_syn P) Q Θ1
(* ⭐ [M <> mode_ti] is the guard SI-Ghost's IMMEDIATE NEIGHBOUR
   [SI-UnivGhostL] spells out below ("should not inst when TI",
   full-algo-spec.tex:855) and that SI-Ghost itself omits (:849).  The
   RUNNER dispatches on the mode first and its [mode_ti] arm is SI-Infer's
   alone — it tests the counterpart for [◇] and rejects otherwise
   (ext_algo/def_sub_impl.v:509-515) — so without the guard the relation
   derives, at [(SK, TI, P0 ≠ ◇, subject ◇)], a judgement the runner
   rejects: cex/probe_sub_ghost_ti.v, machine-checked.

   ⚙ WHY ON THE RULE rather than as a premise on level 6's motive: the
   configuration is REACHED HEREDITARILY.  [SI-Arrow] concludes at [FN M]
   and runs its second premise at [M] against the counterpart's CODOMAIN,
   so a root-level premise ["M = TI -> P0 = ◇"] is vacuous at the
   conclusion and says nothing one arrow down (§3 of that probe).  On the
   rule it holds at every node, which is what the authors' own
   implementation gets by construction: [type.ml]'s [mode] FUSES the mode
   with its counterpart, and [sk_of_mode] sends [Infer] to [Ghost], so
   [TI] pairs with [◇] and cannot do otherwise.  With the guard, SI-Infer
   is the ONLY rule at [TI] (every other row fixes the mode to [TC] or
   [FN _], and [SI-ForallL] / [SI-UnivGhostL] already carry this very
   premise).  [paper-gap] filed in docs/PAPER-GAPS.md. *)
| a_sub__ghost : forall M Θ0 P0,                              (* Ghost *)
    M <> mode_ti ->
    a_sub a_sub_mode_sk M P0 Θ0 pskl_hole P0 Θ0
| a_sub__univ_ghost_l : forall M Θ0 Θ1 P0 P Q,                (* UnivGhostL *)
    M <> mode_ti ->
    a_sub a_sub_mode_sk M P0 Θ0 P Q Θ1 ->
    a_sub a_sub_mode_sk M P0 Θ0 (pskl_tophole P) Q Θ1

(* Flexible-variable subtyping [Θ | Ξ ⊢[N][FN M][P0] α̂ ⩽ Q ⊣ Θ'] (paper
   fig:alg-subtyping, second box).  [Flex-Assign] merges [Θ0,Ξ] and
   re-enters the MAIN judgment with the substituted subject [α̂[τ/β̂]],
   exactly as the paper and the reference implementation do (audit F1):
   for β̂ = α̂ the subject becomes the monotype τ; for β̂ ≠ α̂ the re-entry
   re-fires [FlexMono] over the merged context, which terminates because
   the consumed definition is gone. *)
with a_sub_flex : a_sub_mode -> mode -> pskl -> aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_sub_flex__solve : forall NM M P0 Θ0 Θ1 Ξ α0 α β Q,        (* Flex-Solve *)
    (* prose-completion: the deposited α̂,β̂ are fresh (Barendregt) *)
    α <> β ->
    α `notin` add α0 (dom (Ξ ++ Θ0)) ->
    β `notin` add α0 (dom (Ξ ++ Θ0)) ->
    a_sub NM (mode_fn M) P0
      (Ξ ++ (α0 ~ abind_flex_mono_def (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
          ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
      (pskl_arrow (pskl_var_f α) (pskl_var_f β)) Q Θ1 ->
    a_sub_flex NM M P0 ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 Q Θ1
| a_sub_flex__assign : forall NM M P0 Θ0 Θ1 Ξ α β τ Q,        (* Flex-Assign *)
    (* Paper (full-algo-spec.tex:888-894): MERGE [Θ0,Ξ] and re-enter the
       MAIN judgment with the substituted subject [α̂[τ/β̂]] — for β̂ = α̂ the
       subject becomes the monotype τ (the audit's F1: the subject may BE
       defined, exactly as in the fixed a_assign β̂=α̂ case; the impl does
       this verbatim, type.ml:1021-1027).  Prose-completion: the walked
       definition re-attaches above the output (Barendregt). *)
    β `notin` dom Θ1 ->
    a_sub NM (mode_fn M) (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
      (Ξ ++ Θ0)
      (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α Q
      ((β ~ abind_flex_mono_def τ) ++ Θ1)
| a_sub_flex__depend : forall NM M P0 Θ0 Θ1 Ξ α β Q,          (* Flex-Depend *)
    α <> β ->
    β `in` ftvar_in_pskl P0 ->
    (* β̂ joins the suffix at the Θ0-adjacent END (paper [β̂,Ξ],
       full-algo-spec.tex:896-902; audit F4 — mirror a_assign__depend). *)
    a_sub_flex NM M P0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q Θ1
| a_sub_flex__skip : forall NM M P0 Θ0 Θ1 Ξ α β Q,            (* Flex-Skip *)
    α <> β ->
    β `notin` ftvar_in_pskl P0 ->
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q
      ((β ~ abind_flex_mono) ++ Θ1)
| a_sub_flex__skip_rigid : forall NM M P0 Θ0 Θ1 Ξ α β Q,      (* Flex-SkipRigid *)
    α <> β ->                               (* prose-completion (Barendregt) *)
    β `notin` ftvar_in_pskl P0 ->
    β `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α Q ((β ~ abind_tvar) ++ Θ1)
(* ⛔ [paper-gap] Flex-SkipTmVar — MISSING from fig:alg-subtyping's second box
   (full-algo-spec.tex:883-912), which has only the five rules above, ALL of
   them matching a TYPE-variable entry.  The paper's TWIN walk has the rule
   (Assign-SkipTmVar, full-algo-spec.tex:1791; [a_assign__skip_tm_var] /
   [a_assign__skip_tm_skl] just above), and without it the subtyping walk is
   STUCK the moment a term entry sits above the subject — which is where
   `fun x -> x 1` puts it, since [a_typing__abs] pushes the binder ABOVE the
   flexibles [a_guess_mono] just invented and [a_typing__var] then hands that
   flexible to subtyping at an FN mode.  thm:complete-subtyping is FALSE for
   the five-rule set (cex/cex_p7_flex_walk_tm_var.v, which also records that
   the reference implementation CRASHES on that program), so these two rules
   are added in the paper's own idiom, verbatim mirrors of the twin walk's.
   The mech splits the paper's single [x : P] entry into a type binding and a
   skeleton binding, hence two rules for the paper's one.  docs/PAPER-GAPS.md *)
| a_sub_flex__skip_tm_var : forall NM M P0 Θ0 Θ1 Ξ α x Apay Q, (* Flex-SkipTmVar *)
    x `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((x ~ abind_var_typ Apay) ++ Θ0) Ξ α Q
      ((x ~ abind_var_typ Apay) ++ Θ1)
| a_sub_flex__skip_tm_skl : forall NM M P0 Θ0 Θ1 Ξ α x Qpay Q, (* Flex-SkipTmVar (skl) *)
    x `notin` dom Θ1 ->                     (* prose-completion (Barendregt) *)
    a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
    a_sub_flex NM M P0 ((x ~ abind_var_skl Qpay) ++ Θ0) Ξ α Q
      ((x ~ abind_var_skl Qpay) ++ Θ1).

(* Skeleton splitting  [Θ0 ⊲ split P0 = P→Q ⊣ Θ1] (fig:alg-type-inference). *)
Inductive a_split : aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_split__arrow : forall Θ0 P Q,
    {{ Θ0 ⊲ (pskl_arrow P Q) ▹ P ⇢ Q ⊣ Θ0 }}a
| a_split__hole : forall Θ0,
    {{ Θ0 ⊲ pskl_hole ▹ pskl_hole ⇢ pskl_hole ⊣ Θ0 }}a
| a_split__flex : forall Θ0 Θ1 α β α1 Q,                 (* split[α̂] = β̂→α1̂ *)
    (* The two invented flexibles are FRESH.  The paper says so in prose
       ("fresh"); the mech makes it a rule premise, INPUT-only and against
       [ftvar_in_aenv] rather than [dom], exactly as [a_guess_mono__hole]
       does — a payload [α̂ ≔ τ] may mention them, and it must not.  Without
       this, [a_split_refines_gen] (typing/prop_soundness_typing.v) cannot reach
       [a_assign_sound], whose own premise is that the extended context is
       well-formed.  WF-SIDE-CONDITIONS.md pattern. *)
    β `notin` ftvar_in_aenv Θ0 ->
    α1 `notin` add β (ftvar_in_aenv Θ0) ->
    (* [paper-gap] The paper writes this premise as [unify{α̂}{β̂ → α1̂}]
       (full-algo-spec.tex:393 / algorithmic.tex:330), and that [∼] is
       CONSISTENCY — subject [α̂], input [β̂ → α1̂], output dropped.  It CANNOT be
       [unifyvar], whose subjects are hatted variables: the input here is an
       ARROW.  (Encoding it as [a_unify] is what forced [a_unify] to take
       general monotypes rather than the paper's hatted variables.)
       Consistency's FlexL then assigns [α̂ ≔ β̂ → α1̂]. *)
    {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
      ⊢[ empty | empty | (pskl_arrow (pskl_var_f β) (pskl_var_f α1)) ]
        (pskl_var_f α) ∼ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊲ (pskl_var_f α) ▹ (pskl_var_f β) ⇢ (pskl_var_f α1) ⊣ Θ1 }}a
where "{{ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}a" := (a_split Θ P0 P Q Θ') : fresco_a_scope
  and "{{ Θ ⊢[ N | m | P0 ] P ⩽ Q ⊣ Θ' }}a" := (a_sub N m P0 Θ P Q Θ') : fresco_a_scope.

(* ===================================================================== *)
(*  Algorithmic skeleton inference  [{{ Θ ⊢ˢ[ M ; P0 ] e ⦂ Q ⊣ Θ' }}a]     *)
(*  (fig:alg-skeleton-inference)                                          *)
(* ===================================================================== *)
(* ⭐ THE FOUR BINDER ROWS BELOW ARE EXISTS-FRESH (converted 2026-08-13), so the
   tree's LAST departure from the exists-fresh discipline for algorithmic rules
   is gone (docs/REPORT-remech-cleanup-audit.md §3 recommended exactly this;
   [a_typing]'s six counterparts were converted 2026-08-08, `7061d31`).

   The side condition is verbatim [a_typing__abs]'s: the run names the binder it
   opens at and keeps it away from the input, from the discarded suffix, and
   from the term.  ⚙ [dom Θ2] is an OUTPUT constraint, the Barendregt
   prose-completion the six [a_typing] rows already carry.

   ⚙ WHAT THE CONVERSION COST, measured rather than estimated.  It re-opened
   [a_pat_sound] (theorem 1) and [a_pat_complete] (theorem 3), and the two
   moved in OPPOSITE directions, which is the whole trade:

   - COMPLETENESS got shorter.  It no longer has to regenerate a cofinite
     family from the IH's one instance, so the four [a_pat_rename_tm] calls
     went away — and with them the lemma itself (prop_swap.v §6), whose only
     consumers they were.  ⚙ It could not have been kept: stated over
     exists-fresh rows it would have to rename the rule's OWN binder, which is
     the thing it was being used to do.
   - SOUNDNESS got slightly longer.  It receives ONE binder name instead of
     choosing its own, so the cofinite [a_wf_exp] families must be opened at
     exactly that name — which is what [a_wf_exp_abs_pick] /
     [a_wf_exp_abs_anno_pick] (prop_soundness_pat.v §3) already existed for,
     built for [a_typing]'s 2026-08-08 conversion. *)
Inductive a_pat : mode -> aenv -> pskl -> exp -> pskl -> aenv -> Prop :=
| a_pat__unit : forall m Θ0 Θ1 P0 P,                        (* AP-Unit *)
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] pskl_unit ⩽ P ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] exp_unit ⦂ P ⊣ Θ1 }}a
| a_pat__var : forall m Θ0 Θ1 P0 x A Q,         (* AP-Var (type-bound x) *)
    binds x (abind_var_typ A) Θ0 ->
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}a
| a_pat__var_skl : forall m Θ0 Θ1 P0 x P Q,     (* AP-Var (skeleton-bound x) *)
    binds x (abind_var_skl P) Θ0 ->
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] P ⩽ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}a
| a_pat__anno : forall m Θ0 Θ1 P0 e A Q,                    (* AP-Anno *)
    {{ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_anno e A) ⦂ Q ⊣ Θ1 }}a
| a_pat__freeze : forall Θ0 e Q Θ1,                         (* AP-Freeze *)
    {{ Θ0 ⊢ˢ[ mode_ti ; pskl_hole ] e ⦂ Q ⊣ Θ1 }}a ->
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] (exp_freeze e) ⦂ Q ⊣ Θ1 }}a
| a_pat__abs : forall x m Θ0 Θ1 Θ2 P0 P Q0 e Q Ξ,           (* AP-Abs *)
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ1) `union` dom Θ2 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_skl P) ++ Θ1) ⊢ˢ[ (decr_mode m) ; Q0 ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_skl P) ++ Θ2) }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs e) ⦂ (pskl_arrow P Q) ⊣ (Ξ ++ Θ2) }}a
| a_pat__abs_anno : forall x m Θ0 Θ1 Θ2 Θ3 P0 P Q0 A e Q Ξ,  (* AP-AbsAnno *)
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl A) P Θ2 ->
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ2) `union` dom Θ3 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ2) ⊢ˢ[ (decr_mode m) ; Q0 ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}a ->
    {{ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs_anno A e) ⦂ (pskl_arrow (ptyp_to_pskl A) Q) ⊣ (Ξ ++ Θ3) }}a
| a_pat__abs_check : forall x Θ0 Θ1 e Q Ξ,                  (* AP-AbsCheck *)
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_skl pskl_hole) ++ Θ0) ⊢ˢ[ mode_tc ; pskl_hole ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_skl pskl_hole) ++ Θ1) }}a ->
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] (exp_abs e)
      ⦂ (pskl_tophole (pskl_arrow pskl_hole Q)) ⊣ (Ξ ++ Θ1) }}a
| a_pat__abs_anno_check : forall x Θ0 Θ1 A e Q Ξ,           (* AP-AbsAnnoCheck *)
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ0) ⊢ˢ[ mode_tc ; pskl_hole ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) }}a ->
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] (exp_abs_anno A e)
      ⦂ (pskl_tophole (pskl_arrow (ptyp_to_pskl A) Q)) ⊣ (Ξ ++ Θ1) }}a
| a_pat__app : forall m Θ0 Θ1 Θ2 P0 Q0 P Q e1 e2,           (* AP-App *)
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] e2 ⦂ P0 ⊣ Θ1 }}a ->
    {{ Θ1 ⊢ˢ[ (mode_fn m) ; (pskl_arrow P0 Q0) ] e1 ⦂ (pskl_arrow P Q) ⊣ Θ2 }}a ->
    {{ Θ0 ⊢ˢ[ m ; Q0 ] (exp_app e1 e2) ⦂ Q ⊣ Θ2 }}a
where "{{ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}a" := (a_pat m Θ P0 e Q Θ') : fresco_a_scope.

(* ===================================================================== *)
(*  Algorithmic type inference  [{{ Θ ⊢[ M ; P0 ] e ⦂ A ⊣ Θ' }}a]         *)
(*  (fig:alg-type-inference)                                              *)
(* ===================================================================== *)
Inductive a_typing : mode -> aenv -> pskl -> exp -> ptyp -> aenv -> Prop :=
| a_typing__unit : forall m Θ0 P0 A Θ1,                     (* AT-Unit *)
    {{ Θ0 ⊢[ a_sub_mode_ty | m | P0 ] pskl_unit ⩽ (ptyp_to_pskl A) ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ m ; P0 ] exp_unit ⦂ A ⊣ Θ1 }}a
| a_typing__var : forall m Θ0 P0 x A B Θ1,                  (* AT-Var *)
    binds x (abind_var_typ A) Θ0 ->
    {{ Θ0 ⊢[ a_sub_mode_ty | m | P0 ] (ptyp_to_pskl A) ⩽ (ptyp_to_pskl B) ⊣ Θ1 }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_var_f x) ⦂ B ⊣ Θ1 }}a
| a_typing__anno : forall m Θ0 P0 e A B Θ1 Θ2,              (* AT-Anno *)
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e ⦂ A ⊣ Θ1 }}a ->
    {{ Θ1 ⊢[ a_sub_mode_ty | m | P0 ] (ptyp_to_pskl A) ⩽ (ptyp_to_pskl B) ⊣ Θ2 }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_anno e A) ⦂ B ⊣ Θ2 }}a
| a_typing__freeze : forall Θ0 e A B Θ1 Θ2,                 (* AT-Freeze *)
    (* the TC input skeleton IS the checked type [A]; the inferred [B] is
       UNIFIED with it (consistency), no subtyping *)
    {{ Θ0 ⊢[ mode_ti ; pskl_hole ] e ⦂ B ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl B) (ptyp_to_pskl A) Θ2 ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ] (exp_freeze e) ⦂ A ⊣ Θ2 }}a
| a_typing__abs : forall x m Θ0 Θ1 Θ2 P0 P Q αs A e B Ξ,    (* AT-Abs *)
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a ->
    a_guess_mono Θ1 P αs A ->
    (* [paper-gap] The consumer-side filter for [guess^TY]'s block, verbatim
       the premise [a_sub__forall_l] already carries for the same reason:
       [a_guess_mono]'s ARROW row runs both halves at the same [Θ], so two
       independently-invented blocks can pick the same atom and [uniq αs] is
       NOT derivable OF THIS [a_guess_mono] ("two independent generators",
       docs/PAPER-GAPS.md).  The implementation's global counter is what rules
       it out; a relational rule has to filter it downstream, at the rule that
       puts the block in the context.  Without it the body's run has no
       well-formed input context.
       ⚙ A THREADED [a_guess_mono__arrow] (second half at [Ξ1 ++ Θ], result
       [Ξ2 ++ Ξ1] — the shape every other generating judgement here already
       uses) would make [uniq] derivable and drop this premise.  It is not a
       gap in the paper, it is a choice in the encoding: 316 occurrences across
       19 files, against one premise line.  docs/REPORT-postclosure-audit.md
       §1.3. *)
    uniq (αs ++ Θ1) ->
    a_suffix Ξ ->
    (* EXISTS-FRESH binder, uniformly with the check rows below. *)
    x `notin` dom (Ξ ++ αs ++ Θ1) `union` dom Θ2 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ αs ++ Θ1) ⊢[ (decr_mode m) ; Q ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_abs e) ⦂ (ptyp_arrow A B) ⊣ (Ξ ++ Θ2) }}a
| a_typing__abs_anno : forall x m Θ0 Θ1 Θ2 Θ3 P0 P Q A e B Ξ,   (* AT-AbsAnno *)
    m <> mode_tc ->
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl A) P Θ2 ->
    a_suffix Ξ ->
    x `notin` dom (Ξ ++ Θ2) `union` dom Θ3 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ2) ⊢[ (decr_mode m) ; Q ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}a ->
    {{ Θ0 ⊢[ m ; P0 ] (exp_abs_anno A e) ⦂ (ptyp_arrow A B) ⊣ (Ξ ++ Θ3) }}a
(* AT-AbsCheck / AT-AbsAnnoCheck (input [∀ᾱ.A₀]): the ᾱ-prefix is folded one
   [∀] at a time — [_step] peels one rigid quantifier from the input type and
   the result, [_base] splits the (non-∀) input type into [A→B] and checks
   the body.  Mirrors [d_sd_typing__abs_check_step]/[_base]. *)
(* ⭐ [paper-gap] THE PENDING SUFFIX IS DISCARDED HERE, and the discard forced
   THREE repairs against fig:alg-type-inference (docs/PAPER-GAPS.md,
   WF-SIDE-CONDITIONS.md).  These four rows — and only these four — return an
   output context that DROPS the suffix [Ξ] the body's run deposited;
   [a_pat]'s check rows keep theirs, which is why thm:sound-skeleton-inference
   never met any of this.

   (1) [uniq (Ξ ++ Θ)] — the run's new names avoid the input context.  This
       is verbatim the premise [a_sub__forall_r] already carries for its own
       discarded suffix ("Barendregt: the run's new names avoid the input").
       The paper's soundness proof assumes it when invoking
       lemma:suffix-erasure ("since all variables in Ξ do not appear in
       inh{B}", proofs.tex AbsCheck case).
   (2) [Ξ] does not occur in the RESULT type — the other fact that same
       proof step assumes.  It is a real invariant of the algorithm
       (thm:complete-type-inference discharges it when BUILDING these rows),
       but no scoping theorem local to the rule supplies it, so it stays a
       premise.
   (3) THE [_base] BODY PREMISE'S RESULT IS A FREE [B1], NOT pinned to the
       split codomain [B], and the conclusion's codomain is that [B1].  The
       figure's pinned premise [Θ1,ᾱ,x:A ⊢[TC;B] M ⦂ B] is UNSATISFIABLE
       whenever the split codomain [B] is a flexible and the body is itself
       a lambda (the inner run concludes the INNER split's arrow, never the
       flexible itself) or an application (the function run returns the
       solved codomain) — so terms the implementation accepts, e.g.
       λy.λz.e checked against a flexible, would have NO derivation and
       completeness fails.  The reference implementation never looks at the
       body's returned type (type.ml I-AbsCheck: [end_rule (t, ...)] after
       [let* _, m = finfer (Check b) m e]), and the paper's own completeness
       proof concludes with the body's [B_1], not the split's [B]
       (proofs.tex AbsCheck case, [∀ᾱ.A'→B_1]) — the rule follows the proof.
   (4) ALL FOUR rows quantify their binder EXISTS-FRESH, not cofinitely —
       verbatim [a_sub__forall_r]'s 2026-07-31 repair.  For the [_step]
       rows it is forced: the discarded junk [Ξ] may legitimately MENTION
       the peeled [α] (an AbsAnnoCheck body's consistency stage can solve a
       deposited flexible against it), and the [_base] rows' [Ξ] and result
       [B1] may likewise mention data the run invented for that one binder,
       so a COFINITE premise sharing [Ξ]/[B1] (resp. [Ξ]/[A]) across the
       whole family is unsatisfiable in reachable configurations and breaks
       completeness.  Consumers that need the binder away from ambient data
       re-freshen via the decl-side renaming lemmas. *)
| a_typing__abs_check_step : forall α Θ0 Θ1 A0 e A Ξ,
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->                                   (* Barendregt (1) *)
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->  (* (2) *)
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_ptyp A0 `union` ftvar_in_ptyp A `union`
      ftvar_in_exp (exp_abs e) ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
      (exp_abs e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
      ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ] (exp_abs e) ⦂ (ptyp_all A) ⊣ Θ1 }}a
| a_typing__abs_check_base : forall x Θ0 Θ1 Θ2 A0 A B B1 e Ξ,
    {{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A) ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}a ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ1) ->                                   (* Barendregt (1) *)
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->  (* (2) *)
    x `notin` dom (Ξ ++ Θ1) `union` dom Θ2 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ1) ⊢[ mode_tc ; (ptyp_to_pskl B) ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B1 ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}a ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs e) ⦂ (ptyp_arrow A B1) ⊣ Θ2 }}a
| a_typing__abs_anno_check_step : forall α Θ0 Θ1 A0 Aan e A Ξ,
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->                                   (* Barendregt (1) *)
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->  (* (2) *)
    α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
      ftvar_in_ptyp A0 `union` ftvar_in_ptyp A `union`
      ftvar_in_exp (exp_abs_anno Aan e) ->
    {{ ((α ~ abind_tvar) ++ Θ0)
      ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
      (exp_abs_anno Aan e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
      ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}a ->
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ] (exp_abs_anno Aan e)
      ⦂ (ptyp_all A) ⊣ Θ1 }}a
| a_typing__abs_anno_check_base : forall x Θ0 Θ1 Θ2 Θ3 A0 A' A B B1 e Ξ,
    {{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A') ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}a ->
    a_consis_chk Θ1 (ptyp_to_pskl A') (ptyp_to_pskl A) Θ2 ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ2) ->                                   (* Barendregt (1) *)
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->  (* (2) *)
    x `notin` dom (Ξ ++ Θ2) `union` dom Θ3 `union` fvar_in_exp e ->
    {{ ((x ~ abind_var_typ A) ++ Θ2) ⊢[ mode_tc ; (ptyp_to_pskl B) ]
      (open_exp_wrt_exp e (exp_var_f x)) ⦂ B1 ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}a ->
    (* ⭐ [paper-gap] THE RESULT'S DOMAIN IS THE SPLIT'S [A'], NOT THE WRITTEN
       ANNOTATION [A].  The paper's (commented-out) AT-AbsAnnoCheck writes
       [A → B] (algorithmic.tex:296-303) while orienting its consistency
       [A' ∼ A] — subject the split's domain, input the annotation — the
       reverse of AT-AbsAnno's [A ∼ P].  The two cannot both hold: with
       [A → B] the soundness proof owes [inh⌈A'⌉ ⊳ ⌈A⌉], and the consistency
       run transports the OTHER way ([inh⌈A⌉ ⊳ colouring of A']), which would
       need refinement symmetry.  [A' → B] is also what the un-annotated
       AT-AbsCheck already returns (its domain is the split's), and it is
       exactly what the appendix's [≡ᵗ] premise on sd-AbsAnnoCheck is FOR:
       "the conclusion's domain is any Θ-equivalent A'".  docs/PAPER-GAPS.md *)
    {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs_anno A e)
      ⦂ (ptyp_arrow A' B1) ⊣ Θ3 }}a
| a_typing__app : forall m Θ0 Θ1 Θ2 Θ3 P Q A A' B e1 e2,    (* AT-App *)
    {{ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] e2 ⦂ P ⊣ Θ1 }}a ->
    {{ Θ1 ⊢[ (mode_fn m) ; (pskl_arrow P Q) ] e1 ⦂ (ptyp_arrow A B) ⊣ Θ2 }}a ->
    {{ Θ2 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e2 ⦂ A' ⊣ Θ3 }}a ->
    {{ Θ0 ⊢[ m ; Q ] (exp_app e1 e2) ⦂ B ⊣ Θ3 }}a
where "{{ Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ' }}a" := (a_typing m Θ P0 e B Θ') : fresco_a_scope.
