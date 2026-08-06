# HANDOFF — section D (`proofs.tex`): soundness and completeness of skeleton and type inference

**Status 2026-08-06 (third pass).** The definitional layer is DONE (`dd1f176`),
suffix MOVING is closed (`prop_ctx_mono.v`), and **thm:sound-skeleton-inference
itself is now assembled**: `a_pat_sound` (`algo/prop_soundness_pat.v` §5) is
Qed over all ten `a_pat` rows, with `Print Assumptions` showing exactly ONE
axiom — the isolated `a_consis_chk_annot_refine`, which is AbsAnno at the
ARROW split shape.  §7 has the proved statement, the kit, and the now-concrete
route for that one lemma.  Headlines discovered while building it:

- ⭐ **Theorem 1 needs NEITHER lemma:split-refine NOR refinement
  transitivity** (`a_split_sk_shape`, prop_soundness_pat.v §3b): under the
  judgement's own `skmod{SK}` side condition the split can only be the ARROW
  or HOLE row — `a_sk_mode_compat` has no rule for a flexible input, so the
  flex row (§2's hard case) is reachable only from TYPE inference.  At the
  arrow shape the composed refinement is one `__arrow` of a reflexivity and
  the IH; at the hole shape one `__hole` over the IH's syn-painting inversion
  (`ad_refine_syn_syn_l` at `P := pskl_hole` + `ad_refine_syn_hole_l_target_wf`).
- ⭐ **The paper's "stability" is not free, and the repair is the
  TM-VERBATIM invariant**: `⊴` preserves a term entry only up to `≡ᵗ`
  (`a_inc__var`), so `ad_pat` does not transport along `⊴` alone.  What the
  paper leaves implicit is that the algorithm NEVER rewrites a term entry;
  both directions are now proved for the whole cluster (forward
  `*_tm_le` in prop_stability.v; reverse `*_tm_ge` in prop_soundness_pat.v),
  and `ad_pat_isub_tm` = stability under `⊴` + tm-verbatim.
- ⚠️ **`a_wf_aenv` under-approximates the paper's `Θ ⊢ ctx` at skeleton
  term entries** (`a_wf_aenv__var` stores only `a_scope_pskl`, the paper's
  figure requires `Θ ⊢ P`).  The `AP-Var(skl)` case must feed the entry to
  `a_sub_sound_thm`, which demands the DISCIPLINED `⊢ₚₛᵃ` — so the theorem
  carries the paper's implicit condition as a hypothesis
  (`forall x P, binds x (abind_var_skl P) Θ0 -> Θ0 ⨟ ∅ ⊢ₚₛᵃ P`), sustained
  through the induction by tm_le/tm_ge + `a_wf_pskl_isub`.
  WF-SIDE-CONDITIONS.md pattern; do NOT change the `a_wf_aenv` rule
  mid-campaign.

⚠️ **The paper marks three of these lemmas "straightforward induction".  In the
mechanization they are not**, for reasons recorded per-lemma below.  Read those
before estimating.

---

## 0. What the layer gives you

| Coq | notation | paper |
|---|---|---|
| `ad_pat M Θ e Q` | `Θ ⊢ᵃ[ M ] e ⇨ Q` | `\patp[\M]{\Theta}{M}{\bid{Q}}` |
| `ad_sd_typing M Θ e B` | `Θ ⊢ˢᵃ[ M ] e ⦂ B` | `\typp[\M]{\Theta}{M}{\bid{A}}` |
| `a_pat m Θ0 P0 e P Θ1` | `Θ ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ'` | fig:alg-skeleton-inference |
| `a_typing m Θ0 P0 e A Θ1` | `Θ ⊢ₐ[ m ; P0 ] e ⦂ B ⊣ Θ'` | fig:alg-type-inference |
| `a_split Θ P0 P Q Θ'` | `Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ'` | `\split` |
| `ad_precise Θ Δ P Q` | `Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ Q` | `\precise{P}{Q}` — **LEFT is the more precise one** (checked against `ad_precise_preserves_refine`) |

The appendix's own reason for adding no new rule to either judgement: new rules
are needed only where a FLEXIBLE variable can appear, and neither judgement
looks a type variable up directly — every type-level lookup happens inside the
embedded subtyping / consistency / refinement premises, which already carry
their flexible rows.  What IS carried are the appendix's three explicit
`Θ ⊢ _ ≡ᵗ _` premises on `sd-Freeze`, `sd-AbsAnnoCheck`, `sd-AbsAnno`.

---

## 1. `lemma:suffix-moving` + `lemma:suffix-erasure` — the big one, do it FIRST

    (* moving:  Θ1,Θ2,Ξ  ⟹  Θ1,Ξ,Θ2   — mech lists grow at the FRONT,
       so the paper's [Θ1,Θ2,Ξ] is [Ξ ++ Θ2 ++ Θ1] in Coq *)
    Lemma ad_sd_typing_suffix_moving : forall M Θ1 Θ2 Ξ e B,
      (Ξ ++ Θ2 ++ Θ1) ⊢ˢᵃ[ M ] e ⦂ B ->
      <Ξ does not depend on Θ2> ->
      (Θ2 ++ Ξ ++ Θ1) ⊢ˢᵃ[ M ] e ⦂ B.

    Lemma ad_sd_typing_suffix_erasure : forall M Θ Ξ e B,
      (Ξ ++ Θ) ⊢ˢᵃ[ M ] e ⦂ B ->
      <Ξ fresh for B> ->
      Θ ⊢ˢᵃ[ M ] e ⦂ B.

⛔ **Two things the paper's "straightforward induction on the typing
derivation" hides.**

1. **The dependency relation does not exist yet.**  Closest existing pieces:
   `a_suffix` (algo/def_extra.v — a block of flexible-only entries),
   `no_flex_dep Δ Θ` and `flex_above_free Δ Θ`
   (prop_soundness_consis.v:1452/1457).  Neither is the paper's "Ξ does not
   depend on entries in Θ₂".  Decide its shape ONCE — every later lemma quotes
   it.  Suggested: `forall β τ, binds β (abind_flex_mono_def τ) Ξ ->
   ftvar_in_ptyp τ ∩ dom Θ2 [=] empty`, plus `dom Ξ ∩ dom Θ2 [=] empty`.
2. **The induction is not over one judgement.**  `ad_sd_typing` embeds SIX
   different premise forms — `ad_pat_sub` at `a_sub_mode_ty`, `ad_pat`,
   `ad_refine_syn`, `a_wf_ptyp`, `a_tyequiv`, `mod_comp_ty` — and each needs
   its OWN moving/erasure lemma before the typing induction can close a single
   base rule.  That per-judgement kit is the bulk of the work; the typing
   induction on top of it really is routine.  `mod_comp_ty` is context-free, so
   five kits, not six.

Do these first: everything downstream in section D quotes them, and the kit is
reusable for the two soundness theorems.

---

## 2. `lemma:split-refine` — NOT a straightforward induction (⚠ now TYPE-inference-only: theorem 1 does not use it, see §7)

    Lemma a_split_refines : forall Θ0 P0 P Q Θ1,
      Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 ->
      Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->          (* EXTERNAL wf, see below *)
      Θ1 ⨟ empty ⊢ᵣₚᵃ P0 ⊳ (pskl_arrow P Q).

Two of the three rows are easy; the third is a genuine proof.

- `a_split__arrow` (`P0 = P → Q`, `Θ1 = Θ0`) — `ad_refine_pskl_refl`
  (prop_refine.v:177), whose premise `Θ ⨟ Δ ⊢ₚₛᵃ P` is why the statement needs
  the EXTERNAL wf side condition above.  That is the documented pattern, see
  `docs/WF-SIDE-CONDITIONS.md`; the paper supplies it in prose.
- `a_split__hole` (`□ ▹ □ ⇢ □`) — `ad_refine_pskl__hole` + `a_wf_pskl__arrow`
  of two `a_wf_pskl__hole`s.
- ⛔ `a_split__flex` — the row's premise is a **full `a_consis` run**, not a
  syntactic step.  (The paper writes it `unify{α̂}{β̂ → α1̂}`, but that `∼` is
  CONSISTENCY, not `unifyvar`: `unifyvar`'s subjects are hatted variables and
  the input here is an ARROW — see the `[paper-gap]` note on the rule in
  `algo/def_extra.v`.)  To reach `Θ1 ⨟ ∅ ⊢ᵣₚᵃ α̂ ⊳ (β̂ → α1̂)` you must

  1. invert that run.  Only `a_consis__flex_l` can fire (subject `α̂` flexible,
     `P0 = β̂ → α1̂` non-flex), which hands back
     `((α1~flex) ++ (β~flex) ++ Θ0) ⊲[nil] α ≔ (β̂ → α1̂) ⊣ Θ1`;
  2. read α's DEFINITION out of that assignment — `ad_refine_pskl__flex_l`
     needs exactly `binds α (abind_flex_mono_def τ) Θ1` together with
     `Θ1 ⨟ ∅ ⊢ᵣₚᵃ (ptyp_to_pskl τ) ⊳ (β̂ → α1̂)`.  ⚠️ τ is NOT syntactically
     `β̂ → α1̂`: the assign walk's skip rows may have moved/refreshed entries,
     and β̂ / α1̂ may themselves have been defined along the way.

  ⭐ **THE ROUTE FOR STEP 2, scouted 2026-08-06** — do not go via
  `a_consis_sound`'s refinement conjunct, which is useless here: at
  `a_consis__flex_l` the run's OUTPUT is the subject itself (`Q = α̂`), so that
  conjunct degenerates to `α̂ ⊳ α̂`.  Go through the ASSIGNMENT instead.

  `a_assign_sound` (prop_soundness_consis.v:4495) turns the row's
  `Θ0' ⊲[nil] α ≔ (β̂ → α1̂) ⊣ Θ1` into

      ad_pat_consis ∅ Θ1 (pskl_to_uskl (β̂ → α1̂)) (bskl_var_f α)

  and that consistency can only have come from `ad_pat_consis__flex_r`: the
  LHS is an ARROW so `__arrow` needs an arrow on the right, and `__var`
  demands `a_binds_tvar α Θ1`, i.e. a RIGID α, which it is not.  So inversion
  hands you exactly

      binds α (abind_flex_mono_def τ) Θ1                (* = premise 1 of
                                                           ad_refine_pskl__flex_l *)
      ∅ ⨟ Θ1 ⊢ₛᵃ (pskl_to_uskl (β̂ → α1̂)) ∼ (ptyp_to_bskl_syn τ)

  leaving one obligation: `Θ1 ⨟ ∅ ⊢ᵣₚᵃ (ptyp_to_pskl τ) ⊳ (β̂ → α1̂)`.  Both
  sides there are MONOTYPE-level (τ is a monotype by construction; `β̂ → α1̂` is
  an arrow of flexibles, hence ghost-free), so this is the mono bridge's
  territory — `consis_refine_mono_tyequiv` / `tyequiv_mono_consis` /
  `consis_mono_trans` (prop_mono_bridge.v) plus a
  `≡ˢ ⟹ ⊳` step.  That last step is the one genuinely new fact; check whether
  `a_pskl_tyequiv` already has a refinement corollary before proving it.

  Other handles if the above stalls: `a_assign_unify_subject_flex`
  (prop_consis_rename.v §4), `a_assign_subject_flex_local` (prop_metasubst.v).

---

## 3. `lemma:precision-sub` — check the Ghost row before believing the statement

    Lemma ad_precise_extends_pat_sub : forall Θ Δ P' P Ψ M Q,
      Θ ⨟ Δ ⊢ₚᵣᵃ P' ⊑ P ->
      Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_sk | M ] (pskl_to_uskl P) ⩽ Q ->
      Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_sk | M ] (pskl_to_uskl P') ⩽ Q.

⚠️ **Scout this one before committing to the statement.**  `P' ⊑ P` permits
`P' = □` (`ad_refine_pskl__hole`, which only needs `Q` well-formed) and
`P' = ⫯P''` (`__tophole_remove`) and `P' = α̂` (`__flex_l`).  At `P' = □` the
only applicable subtyping row is `ad_pat_sub__ghost`, whose target must be an
INHERITED PAINTING `pskl_to_bskl_inh P` and which carries `mod_comp_sk` — so
for an arbitrary `Q` produced by the `P` derivation the conclusion is not
immediate.  Either the paper's `precise` is implicitly restricted here, or the
statement needs a side condition.  Settle that with a small probe first (a
`cex/` file if it turns out false — the tree's standing rule).

---

## 4. `lemma:precision-preserves-refinement` — ✅ ALREADY DONE

`ad_precise_preserves_refine` (prop_precise.v:585), Qed and audited in
`README.v`.  It carries three external wf side conditions beyond the paper
(`a_wf_aenv Θ`, Δ-disjointness from `dom Θ`, wf of the target) — the
WF-SIDE-CONDITIONS pattern again.  Nothing to do.

---

## 5. Context precision — a new definition plus one lemma

The paper's `⪯ctx` (proofs.tex, "Definition (Context precision)"), three rules:
empty; a non-term-variable entry copied verbatim; a term-variable entry made
more precise.  In mech terms the third is
`Θ' ⨟ ∅ ⊢ₚᵣᵃ P' ⊑ P` over the two `abind` term forms (`abind_var_skl` directly,
`abind_var_typ` through `ptyp_to_pskl` — cf. the new `abind_to_pskl`).

    Inductive ad_ctx_precise : aenv -> aenv -> Prop := (* Θ' ⪯ctx Θ *) ...

    Lemma ad_ctx_precise_pat : forall Θ' Θ M e Q,
      ad_ctx_precise Θ' Θ ->
      Θ ⊢ᵃ[ M ] e ⇨ Q ->
      Θ' ⊢ᵃ[ M ] e ⇨ Q.

The paper's proof sketch names the load-bearing step: "refinement and subtyping
judgements that do not involve a term-variable lookup are preserved because the
contexts have the same non-variable entries".  That is a **context-change
lemma for `ad_pat_sub` and `ad_refine_syn`** which does not exist yet — the
closest existing shapes are `a_looksub_lookeq_ctx_ftv_mono` (prop_looksub.v)
and `a_solve_sub_eq_ctx_change`.  Prove it over "same non-variable entries"
(same `abind_tvar` / `abind_flex_mono` / `abind_flex_mono_def` entries at the
same positions) and the rest follows.

`ad_pat__var` is the only interesting row: it reads the bound skeleton through
`abind_to_pskl`, then runs `ad_pat_sub` on its painting — so it needs §3's
`lemma:precision-sub` to push the entry's precision through.  **§3 gates §5.**

---

## 6. The four theorems

Order them soundness-first; the two soundness theorems are independent of the
`ad_pat_sub_gv` question, the two completeness ones are not.

1. **Soundness of skeleton inference** — `a_pat` ⟹ information increase +
   `ad_pat` at the output context.  Consumes `a_sub_sound_thm`
   (prop_decorate_key.v; since `9189ba8` it concludes the PLAIN
   `Θ1 ⨟ ∅ ⊢ᵣᵃ … ⊳ …`) and §1's suffix kit.
2. **Soundness of type inference** — `a_typing` ⟹ increase + `ad_sd_typing`.
   Same shape; additionally needs `a_tyequiv` to discharge the appendix's three
   equivalence premises, which is where the algorithm's flexibles show up.
3. **Completeness + optimality of skeleton inference**
4. **Completeness + optimality of type inference**

⚠️ **3 and 4 will hit the `ad_pat_sub_gv` composition gap** (PROGRESS.md §4b):
they consume `a_sub_complete_thm`, which ASSUMES `ad_pat_sub_gv`, while
`a_sub_sound_thm` only CONCLUDES the plain `ad_pat_sub`.  The fix identified
there is to strengthen `a_subtag_sound_bundle` to conclude `_gv` — the content
is already proved (it is the last conjunct of `a_consis_sound` and
`a_consistag_sound_aux`), the only real cost being that `_gv` is fuel-indexed
so soundness must produce an `exists n` (`ad_pat_sub_to_n` is the precedent).
Do that between 2 and 3.

---

## 7. thm:sound-skeleton-inference — ✅ ASSEMBLED (2026-08-06, third pass); ONE open lemma left

`a_pat_sound` (`frost/algo/prop_soundness_pat.v` §5) is **Qed**, `make coq`
clean.  `Print Assumptions a_pat_sound` lists exactly one axiom, §7.3's
`a_consis_chk_annot_refine`; every support lemma is *Closed under the global
context*.

### 7.1 The statement as proved

    Theorem a_pat_sound : forall m Θ0 P0 e P Θ1,
      Θ0 ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ1 ->
      a_wf_aenv Θ0 ->
      (forall x Ps, binds x (abind_var_skl Ps) Θ0 ->
         Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->                  (* the paper's Θ ⊢ ctx *)
      Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
      a_sk_mode_compat m P0 ->
      a_wf_exp Θ0 e ->                            (* "M is wf in Θ0" *)
      Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
      exists Qt, bskl_to_pskl Qt = P /\
        (Θ1 ⊢ᵃ[ m ] e ⇨ Qt) /\
        (Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ Qt).

⚠️ The two hypotheses beyond the paper's list are the WF-SIDE-CONDITIONS
pattern: `a_wf_aenv__var` stores only `a_scope_pskl` where the paper's
`Θ ⊢ ctx` figure requires `Θ ⊢ P`, and `AP-Var(skl)` feeds that entry to
`a_sub_sound_thm`, which demands the DISCIPLINED `⊢ₚₛᵃ`.  Do NOT change the
`a_wf_aenv` rule to fix this — it would ripple through the whole tree.

### 7.2 What was added to close it (all in `prop_soundness_pat.v` unless noted)

| lemma | role |
|---|---|
| `a_pat_tm_ge` (+ `aenv_tm_le_via_binder_ge`) | reverse tm-verbatim for `a_pat`; with `a_pat_tm_le` it says a run's term entries are unchanged, which sustains the skl-entry-wf hypothesis through App/AbsAnno |
| `a_wf_aenv_strip_tm_mid`, `a_scope_pskl_mono` (prop_ctx_mono.v) | drop the walked term entry from the middle of a wf context; payloads are term-blind |
| `uniq_mid_eq`, `a_inc_weaken_suffix_target`, `a_isub_peel_var_skl_mid`, `a_isub_peel_var_typ_mid` | the ⊴-peel at the four binder rows |
| `a_wf_aenv_binds_var_typ_wf` | the `a_wf_aenv_binds_def_wf` mirror, for `AP-Var(typ)` |
| `ad_pat_mod_comp_sk` | ⭐ provable STANDALONE — the theorem does NOT need a strengthened conclusion |
| `mod_comp_sk_{ti,tc,fn}_inv`, `bskl_to_pskl_arrow_inv`, `ad_refine_syn_arrow_inv`, `btyp_to_bskl_ptyp_to_btyp_syn`, `bskl_to_pskl_btyp_to_bskl`, `a_wf_pskl_scope`, `a_wf_{pskl,ptyp,exp}_weaken_cons`, `a_wf_exp_*_inv` | small inversions/coercions the rows quote |
| `a_consis_chk_sound` | `a_consis_sound_aux` in the output-suppressed form, keeping `a_wf_aenv Θ1` |

⭐ **The ⊴-peel must conclude at `Ξ ++ Θ2`, not at `Θ2`.** The
definition-preservation component of `⊴` maps into the WHOLE target, so a
definition of the source could a priori be matched inside the pending suffix;
at `Ξ,Θ2` the peeled entry drops by payload shape (a definition is never a
term entry) and no freshness is needed, whereas at `Θ2` it would need a
freshness fact the statement does not carry.

### 7.3 ⛔ THE ONE OPEN LEMMA — and its now-concrete route

    Lemma a_consis_chk_annot_refine : forall Θ0 A P Θ1,
      a_consis_chk Θ0 (ptyp_to_pskl A) P Θ1 ->
      a_wf_aenv Θ0 -> a_wf_ptyp Θ0 A -> Θ0 ⨟ empty ⊢ₚₛᵃ P ->
      exists B, btyp_to_ptyp B = A /\
        Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B).

It is needed by `AP-AbsAnno` at the **ARROW** split shape only; at the HOLE
shape the row answers with the all-synthesised painting `ptyp_to_btyp_syn A`
through `ad_refine_syn__hole`, and that is proved.  The paper asserts the
lemma inline ("by preservation of refinement under type equivalence") and
never states it.

**Do NOT prove it by induction on `a_consis`.**  Consistency's ∀ rows bind the
fresh α in **Θ**, refinement's bind it in **Δ**; reconciling that is precisely
what `ad_refine_syn_f`'s hygiene set exists for, so that route re-does
consistency soundness.

**Prove it as a TARGET TRANSPORT on the declarative layer.**
`a_consis_chk_sound` already hands back, at the SAME context,

    empty ⨟ Θ1 ⊢ₛᵃ (pskl_to_uskl (ptyp_to_pskl A)) ∼ Qt
    Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ Qt

so what is missing is

    forall Θ Δ Qb Qt A,
      a_wf_aenv Θ -> a_wf_ptyp Θ A ->
      empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl (ptyp_to_pskl A)) ∼ Qt ->
      Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ Qt ->
      exists B, btyp_to_ptyp B = A /\ Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ (btyp_to_bskl B)

by a **nested** induction — outer on the consistency, inner on the refinement
in the rows whose target does not pin the refinement's last rule.  Every row
has an answer (the full per-row map is the §4 header comment in
`prop_soundness_pat.v`); the headlines:

- the subject is a `ptyp` painting, so it is never `uskl_hole` / `uskl_topholeg`
  / `uskl_all_etag` — **eight** consistency rows are dead on arrival;
- ⭐ `Qb = bskl_hole` is ALWAYS answerable by `B := ptyp_to_btyp_syn A`; that
  is what the `a_wf_ptyp Θ A` hypothesis buys, and it is the same move the
  AbsAnno HOLE shape already makes;
- ⭐ the `flex_l` / `flex_r` rows rebuild because **a definition is a
  monotype**, so its colouring is unique — the missing one-liner is
  `mono_ptyp (btyp_to_ptyp B) -> btyp_to_bskl B = ptyp_to_bskl_syn (btyp_to_ptyp B)`
  (the `ptyp_to_bskl_inh_syn_eq` pattern, prop_mono_bridge.v);
- ⛔ the two live ∀ rows need a new `ad_refine_syn_delta_to_ctx`
  (`Θ ⨟ add α Δ ⊢ᵣᵃ … -> (α~tvar),Θ ⨟ Δ ⊢ᵣᵃ …`).  That direction is a
  WEAKENING and holds — `__var` already accepts either side, `__hole`'s
  `Θ ⨟ ∅ ⊢ₚₛᵃ P` only grows, `__tophole_fill` needs one exchange via
  `ad_refine_syn_mono`.  The REVERSE direction is false and is not needed.
  `__tophole_fill` additionally closes an α-dependent witness,
  `B := btyp_all_syn (close_btyp_wrt_btyp α B0)`.

⚙ **Build it once for both theorems.**  Read as consis-to-`≡ᵗ` this is exactly
what thm:sound-type-inference's `Freeze` case needs (the paper's "which further
gives `Θ2 ⊢ B ≡ A`").  Prove whichever form is more convenient and derive the
other; do not build both.

### 7.4 Traps this pass cost time to

- A bare `subst` consumes the erasure equation `bskl_to_pskl Qt = Q` — the RHS
  is a bare variable, so `subst` orients it and CLEARS the hypothesis.  Use
  `subst m` / `subst P0 P Q0` in the split-shape case splits.
- `eapply a_wf_aenv_strip_tm_mid` leaves the peeled binding an evar, so
  `intros []` on `~ abind_is_ty ?b` fails ("Not an inductive product").  Put
  the `a_wf_aenv` goal first: `eapply …; [ | exact H ]; intros []`.
- `simpl_env in H |- *` is a syntax error; write the two calls.
- `simpl in Heq` unfolds metalib's `one`, which then breaks any `match goal`
  pattern written with `~`.  Prove the shape facts with
  `inversion Heq; subst; first [ reflexivity | assumption ]` instead.
- Lemmas whose variables occur only under a function application (e.g.
  `bskl_to_pskl Q = …`, `Ξ1 ++ (x ~ b1) ++ Θ1 = …`) are NOT strict-implicit
  under `Set Implicit Arguments`; give them an `Arguments … : ` line rather
  than counting underscores at each call site.

### 7.5 What is next

1. Close §7.3 (it unblocks nothing else in theorem 1, but theorem 2 needs the
   same content).
2. thm:sound-type-inference — same shape, plus `a_tyequiv` for the appendix's
   three equivalence premises.  §1's suffix ERASURE is still open and is
   TYPE-inference-only, as is §2's `lemma:split-refine`.
3. Then the `ad_pat_sub_gv` composition gap (§6) before the two completeness
   theorems.
