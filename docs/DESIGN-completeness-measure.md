# Design — the induction measure for `thm:complete-consistency`

Status: **analysis only, no `.v` touched.**  Target theorem: *Completeness and
optimality of consistency*, `paper/sections/appendices/full-algo-spec.tex:1541-1559`.
Paper proof: `paper/sections/appendices/consistency-proofs.tex:2225-3167`
("Completeness of Consistency"), read in full, all three parts, every case.

Judgments: `mechanization/frost/algo/def_extra.v:514-806` — one mutual block,
`a_assign` (8 rules), `a_unify` (6), `a_consis` (14).

---

## 0. Verdict, up front

**Both of the tensions in the brief are REAL.  Confirmed against the rules, with
concrete witnesses.  A third one, worse than either, is confirmed as well.**

* **(a) is confirmed, and is worse than "unbounded":** at `Assign-Assign` the
  declarative derivation handed to the consistency IH can be *strictly larger*
  than the one the assignment node started with.  It is not merely "not bounded
  by the context measure" — it is not bounded by the *declarative* measure
  either.  Witness in §3.2.
* **(b) is confirmed:** `ForallInh` / `ForallSyn` / `UnivGhost1` each add a rigid
  `α` to the premise's `Θ₀`, and `Arrow`'s second premise runs at `Θ₁`, which
  `Assign-SolveM` can have extended with fresh `β̄` *and* with definitions.  The
  brief's candidate weight (`|Θ₀|` **including** the sizes of its definitions
  `τ`) therefore *increases* there — a one-flex-var `Θ₀` of weight 1 becomes a
  `Θ₁` of weight 5.  Witness in §3.1.

So **the brief's candidate measure fails**, and so does every measure whose
outermost component is *either* the context *or* the declarative derivation.
The paper's three stated induction subjects (`§1` declarative derivation, `§2`
context `Θ₀`, `§3` context pair `Θ₀ ∣ Ξ`) genuinely do **not** combine into one
well-founded order.  On top of that, the paper's `§1` induction is not
well-founded even *on its own*: the `UnivGhostR` step
(`consistency-proofs.tex:2570-2572`) recurses with the **same** declarative
derivation.

**But a measure does survive.**  It is neither of the two the paper suggests:

> **V — the size of the *solved* skeletons**, i.e. the skeletons pushed through
> the solution's metasubstitution `θ` and then through the target context `Θ`'s
> own definitions.

`V` strictly decreases on **all 11** consistency-internal edges and is **exactly
constant** on **all 4** cross-edges (`consis↔unify`, `consis↔assign`).  That
constancy is what lets the context length serve as the second component, where
it *does* strictly decrease on every walk step and every back-edge.  Full
per-edge proof in §5.

This is a **GAP (repaired)**, not a FALSE statement.  §9 lists the four things
the paper's proof omits that the mechanization must supply.

---

## 1. The three judgments, as mechanized

Recall the list convention: **the head is the most recent binding**; every rule
recurses on the head; a definition `γ̂ ≔ τ` has `τ` well-formed in the *tail*.

| judgment | mech | paper |
|---|---|---|
| assignment | `a_assign F Θ₀ Ξ α P Θ₁` = `Θ₀ ⊲[F][Ξ] α ≔ P ⊣ Θ₁` | `Θ₀ ∣ Ξ ⊲ α̂ ≔ P ⊣ Θ₁` |
| unification | `a_unify F Θ₀ α β Θ₁` = `Θ₀ ⊲[F] α ≈ᵘ β ⊣ Θ₁` | `Θ₀ ⊲ α̂ ≈ β̂ ⊣ Θ₁` |
| consistency | `a_consis F Δ₁ Δ₂ Θ₀ P₀ P Q Θ₁` = `Θ₀ ⊢ₐ[F][Δ₁∣Δ₂∣P₀] P ≈ Q ⊣ Θ₁` | `Θ₀ ⊢[Δ₁∣Δ₂][P₀] P ≈ Q ⊣ Θ₁` |

`F` (the used-name set) is a prose-completion and is **measure-irrelevant**: the
completeness statement quantifies over `F` universally in the conclusion
(we *construct* the derivation, and `Assign-SolveM`'s guessed `β̄` can always
avoid any finite `F`).  It is carried but never measured.

Throughout, for a node I write the **pair of skeletons** it is about:

* consistency node → `(P, P₀)`  (subject, input)
* unification node → `(α̂, β̂)`
* assignment node → `(P, α̂)`   (assigned skeleton, subject variable)

This pairing is not decoration; it is exactly what makes `V` constant on the
cross-edges (§5.3).

---

## 2. COMPLETE EDGE LIST

`Θ` is the target of the *given* solution and is **fixed for the whole tree**
(the only thing that ever happens to it is a rigid extension `Θ,α` in
`ForallInh`/`ForallSyn`/`UnivGhost1` — see §4.3, it does not matter).
`θ`, `θ₁`, `θ₂` are the metasubstitutions into `Θ`, related by `a_inc_equiv`.

### 2.1 `a_unify` (6 rules) — `def_extra.v:602-670`, paper `:2260-2401`

| # | rule | edge | context | decl. derivation handed to the callee |
|---|---|---|---|---|
| U1 | `Flex-Flex-Id` | — (axiom) | — | — |
| U2 | `Flex-Flex-L` | — (axiom) | `Θ₀ = Θ₀',α̂` | — |
| U3 | `Flex-Flex-R` | — (axiom) | `Θ₀ = Θ₀',β̂` | — |
| U4 | `Flex-Flex-Assign` | **unify(Θ₀',γ̂≔τ; α̂; β̂) → consis(Θ₀'; P₀ = β̂[τ/γ̂]; P = α̂[τ/γ̂])** | head `γ̂≔τ` dropped, `−1` | `⟨e⟩ Θ ⊢ θ(α̂[τ/γ̂]) ≈ θ(β̂[τ/γ̂])` — this is the node's *own* `⟨b⟩ Θ ⊢ θα̂ ≈ θβ̂` **transported along `≡ᵗ`** (`θγ̂ ≡ᵗ θτ`).  **Not a subderivation. Not smaller.** |
| U5 | `Flex-Flex-Skip` | unify → unify | `−1` | unchanged |
| U6 | `Flex-Flex-Skip'` | unify → unify | `−1` | unchanged |

Note `a_unify__flex_assign` has **no** `γ ≠ α`/`γ ≠ β` premise, so `γ̂` may *be*
`α̂` or `β̂`; then the spawned consistency subject is the monotype `τ`, not a
variable.  (That is exactly why the rule drops into `a_consis`, not `a_unify` —
`def_extra.v:625-651`.)

### 2.2 `a_assign` (8 rules) — `def_extra.v:514-600`, paper `:2403-2559`

| # | rule | edge | context | decl. derivation handed to the callee |
|---|---|---|---|---|
| A1 | `Assign-UnivGhost-Id` | — (axiom) | — | — |
| A2 | `Assign-SolveM` | — (axiom) | `Θ₀ = Θ₀',α̂`; **output grows by `|β̄|`** | — |
| A3 | `Assign-Assign` | **assign(Θ₀',β̂≔τ; Ξ; α̂; P) → consis(Ξ++Θ₀'; P₀ = P[τ/β̂]; P = α̂[τ/β̂])** | `|Ξ|+|Θ₀|` drops by 1 (head `β̂≔τ` dropped, `Ξ` absorbed) | `⟨g⟩ Θ ⊢ syn θ(α̂[τ/β̂]) ≈ bid θ(α̂[τ/β̂])` — **REFLEXIVITY on the monotype `θα̂`** (paper `:2510-2515`).  **Not a subderivation; can be strictly LARGER than the node's own `⟨b⟩ Θ ⊢ θP ≈ θα̂`** (§3.2). |
| A4 | `Assign-Depend` | assign → assign | `|Ξ|+|Θ₀|` **unchanged** (head moves `Θ₀ → Ξ`); `|Θ₀|` drops by 1 | unchanged |
| A5 | `Assign-Skip` | assign → assign | `−1` | unchanged |
| A6 | `Assign-SkipRigid` | assign → assign | `−1` | unchanged |
| A7 | `Assign-SkipTmVar` | assign → assign | `−1` | unchanged |
| A8 | `Assign-SkipTmSkl` | assign → assign | `−1` | unchanged |

`Assign-Assign` is the *only* rule whose head is a **defined** flex var, and
there is **no** skip rule for a defined flex var — so it always fires there.

### 2.3 `a_consis` (14 rules) — `def_extra.v:672-806`, paper `:2561-3167`

The paper's `§1` dispatches in three layers (`:2566-2574`): first on `P₀`'s
shape (the `GhostR` / `UnivGhostR` "special cases"), then on `P`/`P₀` being
flexible (dispatch to `§2`/`§3`), then on the last rule of the **declarative**
derivation.  Below, `S` is the decorated skeleton, `P = ⌊S⌋ˢ`.

| # | algo rule fired | decl. rule / trigger | edge | decl. derivation | skeletons |
|---|---|---|---|---|---|
| C1 | `GhostR` | `P₀ = ◇` (`:2570`) | — (axiom) | — | — |
| C2 | `UnivGhostR` | `P₀ = ⊤◇.P₀'`, `P` guarded (`:2571-2572`) | consis → consis `(Θ₀; P₀'; P)` | **SAME derivation** ⚠ | `|P₀|` `−1` |
| C3 | `Ghost` | `≡Ghost` (`S=◇`) | — (axiom) | — | — |
| C4 | `Ghost` | `≡GhostG` (`S=◇_g`, inversion gives `P₀=◇`) | — (axiom) | — | — |
| C5 | `Unit` | `≡Unit` | — (axiom) | — | — |
| C6 | `Rigid` | `≡Var` | — (axiom) | — | — |
| C7a | `Arrow` (1st) | `≡Arrow` (`:2693`) | consis → consis `(Θ₀; P₀a; P₁)` | subderivation `⟨a⟩` | both `<` |
| C7b | `Arrow` (2nd) | `≡Arrow` | consis → consis `(Θ₁; P₀b; P₂)` at `θ₁` | subderivation `⟨b⟩`, rewritten by `θ ≡ θ₁` | both `<` |
| C8 | `ForallInh` | `≡ForallInh` (`:2779`) | consis → consis `(α,Θ₀; P₀'^α; P'^α)` | subderivation | both `−1` |
| C9 | `ForallSyn` | `≡ForallSyn` | consis → consis `(α,Θ₀; ⊤◇.P₀'` **unchanged**`; P'^α)` | subderivation | `|P|` `−1` |
| C10 | `UnivGhost` | `≡UnivGhost` / `≡UnivGhostG` | consis → consis `(Θ₀; P₀'; P')` | subderivation | both `−1` |
| C11 | `UnivGhost1` | `≡UnivGhost1` | consis → consis `(α,Θ₀; P₀'^α; ⊤◇.P'` **unchanged**`)` | subderivation | `|P₀|` `−1` |
| C12 | `UnivGhost` | `≡UnivGhost2` (`:3074`), sub-case `P₀=⊤◇.P₀'` | consis → consis `(Θ₀; P₀'; P')` | subderivation | both `−1` |
| C13 | `UnivGhost2` | `≡UnivGhost2`, sub-case `P₀` guarded | consis → consis `(Θ₀; P₀` **unchanged**`; P')` | subderivation | `|P|` `−1` |
| C14 | `Flex` | `P = α̂`, `P₀ = β̂` (both flexible) | **consis → unify(Θ₀; α̂; β̂)** | *must be constructed* ⚠ (§9.1) | — |
| C15 | `FlexL` | `P = α̂`, `P₀` non-flex | **consis → assign(Θ₀; ·; α̂; P₀)** | *must be constructed* ⚠ | — |
| C16 | `FlexR` | `P₀ = α̂`, `P` non-flex | **consis → assign(Θ₀; ·; α̂; P)** | *must be constructed* ⚠ | — |

C14–C16 are the paper's entire treatment of the flexible cases: the single
sentence *"The cases where `P` or `P₀` is a flexible variable are handled by the
other two parts of the lemma"* (`:2568-2569`).  See §9.1 — that sentence hides
real work.

**Context behaviour of the consistency rules** (this is (b)):

* C7b runs at `Θ₁` = the *output* of the first premise ⊇ `Θ₀`;
* C8/C9/C11 run at `(α ~ abind_tvar) ++ Θ₀`, i.e. `|Θ₀| + 1`.

**Total: 21 recursive edges** (4 `unify`, 6 `assign`, 11 `consis`) + 10 axioms.

---

## 3. Why the brief's candidate measure fails — witnesses

Candidate: lexicographic on `( W(Θ₀) , part-tag , |declarative derivation| )`
where `W` is the total syntactic size of `Θ₀` **including** the sizes of the
definitions `τ`.

### 3.1 `Arrow`'s second premise breaks `W` (this is (b), confirmed)

    Θ₀ = (α̂ : flex_mono)                       W(Θ₀) = 1
    consistency problem:  input  P₀ = (◇ → unit) → unit
                          subject P  = α̂ → unit

`Arrow` (C7a) on the left component: `Θ₀ ⊢[◇→unit] α̂ ≈ ? ⊣ Θ₁`.  The subject is
a flexible variable and the input is not, so `FlexL` fires → `assign(Θ₀; ·; α̂;
◇→unit)`.  The head *is* `α̂`, so `Assign-SolveM` fires with
`guess^TY(◇→unit) = (β̂ ; β̂→unit)` (`a_guess_mono__hole`, `def_extra.v:223`), and

    Θ₁ = (α̂ ≔ β̂ → unit) , (β̂ : flex_mono)      W(Θ₁) = (1 + 3) + 1 = 5

Then `Arrow`'s **second** premise (C7b) runs at `Θ₁`.  `W` went `1 → 5`.  Both
effects fire: a **fresh flexible variable** was added (`|β̄| = 1`) *and* a
**definition** was made (`α̂` gained a `τ` of size 3).  Even counting only
entries (`|Θ₀|`, ignoring definitions) it goes `1 → 2`.  Even counting only
*flexible* entries it goes `1 → 2`.

`ForallInh`/`ForallSyn`/`UnivGhost1` break `|Θ₀|` more cheaply: `+1` rigid.
(That one *can* be dodged by weighting rigid entries `0` — but 3.1 cannot.)

> **No context-based measure can be the outermost component.**

### 3.2 `Assign-Assign` breaks `|declarative derivation|` (this is (a), confirmed — and worse)

    Θ₀ = (β̂ ≔ unit) , (α̂ : flex_mono)
    assignment problem: (Θ₀ ; Ξ = · ; α̂ ; P = ◇ → unit)
    solution:  θ = { β̂ ↦ unit , α̂ ↦ (unit → unit) → unit }   into Θ = ·

The node's own declarative derivation `⟨b⟩ Θ ⊢ θP ≈ θα̂` is

    Arrow( Ghost(◇ ≈ inh(unit→unit)) , Unit )              — 3 nodes

The head of `Θ₀` is a **defined** flex var, so `Assign-Assign` **must** fire
(there is no skip rule for a defined flex head).  The paper's `:2510-2515`
supplies the consistency IH with `⟨g⟩` = **reflexivity** on
`θ(α̂[unit/β̂]) = (unit→unit)→unit`:

    Arrow( Arrow(Unit,Unit) , Unit )                        — 5 nodes

`5 > 3`.  The declarative derivation handed to the callee is **strictly larger**
than the caller's.  The `Ghost` rule is the mechanism: it absorbs an arbitrarily
large `Q` in **one** node, so the assignment node's derivation is bounded by the
*ghost-ridden* `P`, while the spawned consistency node's derivation is bounded
by the *fully-solved* `θα̂`.

`Flex-Flex-Assign` (U4) is milder — the derivation is only `≡ᵗ`-transported, not
grown — but `≡ᵗ` is **not size-preserving** either (see §4.1), so it is not
"unchanged" as a natural number.

And `UnivGhostR` (C2) recurses with the **literally identical** derivation.

> **No declarative-derivation-based measure can be the outermost component
> either.**  In particular the paper's `§1` "induction on the declarative
> consistency derivation" is not a well-founded induction as written.

### 3.3 What this means

The two candidate outer components fail on *disjoint* edge sets, so no
lexicographic combination of them in either order works.  A different quantity
is needed.

---

## 4. THE MEASURE THAT SURVIVES

### 4.1 The obstacle to fix first: `≡ᵗ` is not size-preserving

`a_tyequiv` (`algo/def_meta.v:105-133`) is refl/sym/trans/congruence **plus**

```coq
| a_tyequiv__flex_def : forall Θ α τ,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⊢ (ptyp_var_f α) ≡ᵗ τ
```

So `α ≡ᵗ τ` for *any* `τ` — sizes differ arbitrarily.  And `≡ᵗ` is exactly what
`a_inc__flex_def` (`def_meta.v:148-155`) and `a_inc_equiv__flex/_def`
(`def_meta.v:191-201`) use.  So `size(msubst_pskl θ P)` is **not** stable under
the two moves the proof constantly makes:

* **(M1)** `θ ≡ θ₁` on `Θ₀` (`a_inc_equiv`) — used at `Arrow`'s second premise;
* **(M2)** `θγ̂ ≡ᵗ θτ` — used at both back-edges to rewrite `X[τ/γ̂]` into `X`.

**Fix — the `⇓` normal form.**  A well-formed `Θ` is ordered and acyclic
(definitions are well-formed in the tail), so it induces a *total unfolding*
substitution, definable as a plain structural `Fixpoint`:

```coq
Fixpoint aenv_msubst (Θ : aenv) : metasubst :=
  match Θ with
  | nil => nil
  | (α, abind_flex_mono_def τ) :: Θ' =>
      let θ' := aenv_msubst Θ' in (α, msubst_ptyp θ' τ) :: θ'
  | (α, abind_flex_mono) :: Θ'     => (α, ptyp_var_f α) :: aenv_msubst Θ'
  | _ :: Θ'                        => aenv_msubst Θ'
  end.

Notation "⇓[ Θ ] A" := (msubst_ptyp (aenv_msubst Θ) A).   (* and msubst_pskl *)
```

Two properties carry the whole measure (§8, L1–L3):

* **`⇓` is `≡ᵗ`-sound:** `a_wf_aenv Θ → Θ ⊢ A ≡ᵗ B → ⇓[Θ]A = ⇓[Θ]B`.
* **`⇓` ignores rigid and term-var entries:** `aenv_msubst ((α~tvar)::Θ) = aenv_msubst Θ`.

### 4.2 Definition of the measure

Fix the root solution's target `Θ`.  For a node with pair `(X, Y)` (§1) and
metasubstitution `θ` into `Θ`:

```
    V  =  size (⇓[Θ] (θ X))  +  size (⇓[Θ] (θ Y))          -- SOLVED skeleton size
    n  =  length Θ₀                    (consis, unify)
          length Ξ + length Θ₀         (assign)
    t  =  1 (consis) | 0 (unify) | 0 (assign)
    k  =  length Θ₀ (assign) | 0 (consis, unify)

    μ  =  (V, n, t, k)      lexicographic on ℕ⁴  —  well-founded.
```

`V` is a natural number, and by §4.1 it is invariant under (M1) and (M2), which
is the whole point.

### 4.3 Why `V` is the right quantity, in one line

`V` is the size of the skeletons **as the solution sees them**.  The back-edges
`X ↦ X[τ/γ̂]` merely *unfold a definition the solution had already unfolded*,
so `V` cannot notice them; and the consistency rules *decompose* the skeletons,
so `V` cannot fail to notice those.  It is precisely orthogonal to both failure
modes of §3.  (The rigid extension `Θ → Θ,α` in C8/C9/C11 is invisible to `⇓`
by the second bullet of §4.1, and opening with a free variable preserves
`size_pskl` — LNgen's `size_pskl_open_pskl_wrt_pskl_var`.)

---

## 5. PER-EDGE VERIFICATION — every one of the 21 edges

`⟦X⟧ := size (⇓[Θ] (θ X))`.  `⟦·⟧` is a homomorphism for `arrow`, `all_syn`,
`tophole`, `hole` (it is a substitution followed by a substitution), and
`⟦P^α⟧ = ⟦P⟧` for a rigid `α` (opening preserves size).

### 5.1 Consistency-internal edges — `V` strictly decreases (`n`, `t`, `k` irrelevant)

| edge | `V` before | `V` after | Δ |
|---|---|---|---|
| C2 `UnivGhostR` | `⟦P⟧ + ⟦⊤◇.P₀'⟧` | `⟦P⟧ + ⟦P₀'⟧` | **−1** |
| C7a `Arrow` 1st | `⟦P₁→P₂⟧ + ⟦P₀a→P₀b⟧` | `⟦P₁⟧ + ⟦P₀a⟧` | **≤ −2** |
| C7b `Arrow` 2nd | ditto (at `θ`) | `⟦P₂⟧ + ⟦P₀b⟧` (at `θ₁`) | **≤ −2** — *and this is exactly where (M1) is needed: `θ ≡ θ₁` on `Θ₀`, `P₂`/`P₀b` wf in `Θ₀`, so `⇓[Θ](θ₁P₂) = ⇓[Θ](θP₂)`.  The context growth of §3.1 is simply not measured.* |
| C8 `ForallInh` | `⟦∀α.P⟧ + ⟦∀α.P₀⟧` | `⟦P^α⟧ + ⟦P₀^α⟧` | **−2** |
| C9 `ForallSyn` | `⟦∀α.P⟧ + ⟦⊤◇.P₀⟧` | `⟦P^α⟧ + ⟦⊤◇.P₀⟧` | **−1** |
| C10 `UnivGhost` | `⟦⊤◇.P⟧ + ⟦⊤◇.P₀⟧` | `⟦P⟧ + ⟦P₀⟧` | **−2** |
| C11 `UnivGhost1` | `⟦⊤◇.P⟧ + ⟦∀α.P₀⟧` | `⟦⊤◇.P⟧ + ⟦P₀^α⟧` | **−1** |
| C12 `≡UnivGhost2`, `P₀=⊤◇.P₀'` | `⟦⊤◇.P⟧ + ⟦⊤◇.P₀'⟧` | `⟦P⟧ + ⟦P₀'⟧` | **−2** |
| C13 `≡UnivGhost2`, `P₀` guarded | `⟦⊤◇.P⟧ + ⟦P₀⟧` | `⟦P⟧ + ⟦P₀⟧` | **−1** |

Note C2/C9/C11/C13 are exactly the four edges where *one* skeleton stands still —
they are why `V` must sum **both** skeletons, and why the paper's
"declarative derivation" alone (which stands still at C2) cannot work.

### 5.2 Walk edges — `V` constant, `n` (or `k`) strictly decreases

| edge | `V` | `n` | `t` | `k` |
|---|---|---|---|---|
| U5 `Flex-Flex-Skip` | `=` (`γ ≠ α,β`; `θ` merely restricted) | **−1** | | |
| U6 `Flex-Flex-Skip'` | `=` | **−1** | | |
| A5 `Assign-Skip` | `=` (`β ∉ ftv P`, `β ≠ α`) | **−1** | | |
| A6 `Assign-SkipRigid` | `=` (`β ∉ ftv P`) | **−1** | | |
| A7/A8 `Assign-SkipTmVar/Skl` | `=` | **−1** | | |
| A4 `Assign-Depend` | `=` (`P`, `α̂` unchanged; `θ` unchanged — `β̂` only *moves* `Θ₀ → Ξ`) | `=` | `=` | **−1** |

`A4` is the only edge that needs `k`.  `n = |Ξ| + |Θ₀|` is deliberately the
*merged* length precisely so that A4 keeps it flat and A3 drops it.

### 5.3 Cross edges — `V` exactly constant

| edge | `V` before | `V` after | why |
|---|---|---|---|
| C14 `Flex` | `⟦α̂⟧ + ⟦β̂⟧` | `⟦α̂⟧ + ⟦β̂⟧` | pairing (§1) |
| C15 `FlexL` | `⟦α̂⟧ + ⟦P₀⟧` | `⟦P₀⟧ + ⟦α̂⟧` | pairing |
| C16 `FlexR` | `⟦P⟧ + ⟦α̂⟧` | `⟦P⟧ + ⟦α̂⟧` | pairing |

All three keep `n` (`|Θ₀| + |·| = |Θ₀|`) — **`t` breaks the tie: `1 → 0`.**

### 5.4 Back-edges — `V` exactly constant, `n` strictly decreases

**U4 `Flex-Flex-Assign`.**  Node: `unify(Θ₀',γ̂≔τ; α̂; β̂)`, `V = ⟦α̂⟧ + ⟦β̂⟧`,
`n = 1 + |Θ₀'|`.  Callee: `consis(Θ₀'; β̂[τ/γ̂]; α̂[τ/γ̂])` at `θ' = θ↾Θ₀'`,
`n' = |Θ₀'|` — **`n` drops by 1** ✓.  And

  `⇓[Θ](θ'(α̂[τ/γ̂])) = ⇓[Θ](θα̂)` — by (M2): if `γ̂ ≠ α̂` this is *syntactic*
  identity; if `γ̂ = α̂` it is `⇓[Θ](θ'τ) = ⇓[Θ](θα̂)`, which is exactly
  `a_inc__flex_def`'s `Θ ⊢ θγ̂ ≡ᵗ msubst θ' τ` pushed through the `≡ᵗ`-soundness
  of `⇓`.  Same for `β̂`.  So **`V' = V`** ✓.  (`t` rises `0 → 1`, harmless: `n`
  already dropped.)

**A3 `Assign-Assign`.**  Node: `assign(Θ₀',β̂≔τ; Ξ; α̂; P)`, `V = ⟦P⟧ + ⟦α̂⟧`,
`n = |Ξ| + 1 + |Θ₀'|`.  Callee: `consis(Ξ++Θ₀'; P[τ/β̂]; α̂[τ/β̂])`,
`n' = |Ξ| + |Θ₀'|` — **`n` drops by exactly 1** ✓.  And
`⇓[Θ](θ'(P[τ/β̂])) = ⇓[Θ](θP)`, `⇓[Θ](θ'(α̂[τ/β̂])) = ⇓[Θ](θα̂)` by (M2) again
(including the `β̂ = α̂` case, where the subject becomes the monotype `τ`).  So
**`V' = V`** ✓.

> **This is the payoff.**  The declarative derivation blew up here (§3.2) and the
> context blew up at C7b (§3.1).  `V` does neither: it is stationary on exactly
> the edges where `n` moves, and moves on exactly the edges where `n` is
> unreliable.

### 5.5 Axioms (no edge)

`Flex-Flex-Id`, `Flex-Flex-L`, `Flex-Flex-R`, `Assign-UnivGhost-Id`,
`Assign-SolveM`, `Ghost`, `GhostR`, `Unit`, `Rigid` — and the declarative
`≡Ghost` / `≡GhostG` / `≡Unit` / `≡Var` cases they answer.

**All 21 edges verified.  The measure holds.**

---

## 6. A BETTER DECOMPOSITION — confine the measure to the easy half

The measure is only needed for **existence**.  **Optimality** — the hard,
content-heavy half — can induct on the **algorithmic derivation**, which by then
exists, and so reuses the *existing* `Combined Scheme`.

* **(OPT)** `a_assign_unify_consis_optimal` — by mutual induction on the
  algorithmic derivation (`a_assign_unify_consis_mutind`, `prop_consis_sound.v:2486`).
  *Given* `Θ₀ ⊢ₐ[…] P ≈ Q₁ ⊣ Θ₁` and *any* solution `(θ, Θ, Q)`, produce
  `ζ : Θ₁ ≤[ζ] Θ`, `a_inc_equiv Θ₀ θ ζ Θ`, and `Θ ⨟ Δ₁∪Δ₂ ⊢ₚᵣᵃ ζ Q₁ ⊑ Q`.
  Every back-edge premise (`Flex-Flex-Assign`, `Assign-Assign`) *is* an
  algorithmic consistency derivation, so the IH is right there.  **No measure.**
* **(EX)** `a_assign_unify_consis_complete` — by well-founded induction on `μ`.
  *Given* a solution, produce the algorithmic derivation.  Its `Arrow` case needs
  a solution at `Θ₁` for the second premise; it gets `ζ₁` by **calling (OPT)** on
  the derivation the first IH just produced.

Dependency is one-way: **(EX) uses (OPT); (OPT) does not use (EX).**  This is
strictly better than the paper's single fused statement:

* it puts *all* the `⇓`/`≡ᵗ`/size scaffolding in (EX), where the goal is a bare
  `exists`, so nothing about precision or composition has to survive the
  well-founded recursion;
* (OPT) is shaped exactly like the already-green soundness bundle.

Recommended unless (EX) turns out to need a precision fact from its own IH — I
checked all 21 edges and it does not: every (EX) IH consumer needs only
`∃ Θ₁ Q₁, derivation`, plus a solution at the *shifted* context, which (OPT)
manufactures.  **Fall back to the paper's fused statement (§7.2) if that turns
out to be wrong.**

---

## 7. MECHANIZATION PLAN

### 7.1 Induction principle

* **(OPT):** `apply (a_assign_unify_consis_mutind …)` — reuse verbatim, three
  motives, 28 cases, exactly the `prop_consis_sound.v:2562-2577` shape.
* **(EX):** `well_founded_induction` on `μ`.  Concretely: define
  `Definition mu : nat * nat * nat * nat := …` and use `Wf_nat.lt_wf` lifted
  through a `lex4` order, or (simpler and what I'd do) **flatten to one `nat`
  by a strong-induction wrapper**: prove
  `forall N, forall node, mu_rank node < N -> Goal node` by `induction N`, with
  `mu_rank` any injective-enough monotone encoding — but `V` and `n` are
  unbounded, so a genuine lex order is cleaner.  Suggested:
  `Require Import Coq.Wellfounded.Lexicographic_Product` or hand-roll
  `Definition lt4 := ...` + `Lemma lt4_wf`.  The three motives are then *three
  separate `Prop`s* dispatched by the `t` tag, so the recursion is a single
  `Fix` over one predicate `EXgoal : node -> Prop` with a sum type of the three
  node shapes.  (Alternatively: three mutually-defined lemmas each taking a
  `fuel : nat` bound on `μ` and passing `fuel - 1` — ugly but trivially accepted
  by Coq and avoids the sum type.  Given this codebase's style I'd take the
  fuel/strong-induction-on-`V` route and nest an inner induction on `n`.)

**Recommended concrete shape:** outer `induction` on `V` (strong, `lt_wf_ind`),
inner `induction` on `n` (strong), then the `t`/`k` tie-breaks are handled by
ordering the three lemmas within one `Section` and inlining `Assign-Depend`'s
sub-recursion as a third `induction` on `|Θ₀|`.  That is three nested strong
inductions and no `Program Fixpoint`.

### 7.2 The three motives (mirroring `*_sound_post`)

```coq
(* the paper's AUGMENTED consistency solution, :2230-2242 *)
Definition consis_complete_post
    (F Δ1 Δ2 Ψ : atoms) (Θ0 : aenv) (P0 : pskl) (S : uskl)
    (θ : metasubst) (Θ : aenv) (Q : bskl) : Prop :=
  (* hypotheses: (θ;Θ;Q) is a solution to (Δ1;Δ2;Ψ;Θ0;P0;⌊S⌋ˢ) *)
  Θ0 ≤[ θ ] Θ ->
  Ψ ⨟ Θ ⊨ₛᵃ (msubst_uskl θ S) ≈ Q ->                       (* decl consistency *)
  Θ ⨟ Δ1 ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ Q ->  (* Δ1 refinement   *)
  Θ ⨟ Δ2 ⊢ᵣᵃ ... (msubst_pskl θ ⌊S⌋ˢ) ⊳ Q ->               (* Δ2 refinement   *)
  no_flex_dep (Δ1 ∪ Δ2) Θ -> flex_above_free (Δ1 ∪ Δ2) Θ ->
  (* conclusion, :2246-2255 *)
  exists Θ1 P1 θ1,
    Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] ⌊S⌋ˢ ≈ P1 ⊣ Θ1 /\
    Θ1 ≤[ θ1 ] Θ /\
    a_inc_equiv Θ0 θ θ1 Θ /\
    Θ ⨟ (Δ1 ∪ Δ2) ⊢ₚᵣᵃ (msubst_pskl θ1 P1) ⊑ (bskl_to_pskl Q).

Definition unify_complete_post (F : atoms) (Θ0 : aenv) (α β : atom)
    (θ : metasubst) (Θ : aenv) : Prop :=
  Θ0 ≤[ θ ] Θ ->
  empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl (msubst_lookup θ α))
             ≈ (ptyp_to_bskl_syn (msubst_lookup θ β)) ->
  exists Θ1 θ1, Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1
             /\ Θ1 ≤[ θ1 ] Θ /\ a_inc_equiv Θ0 θ θ1 Θ.

Definition assign_complete_post (F : atoms) (Θ0 Ξ : aenv) (α : atom) (P : pskl)
    (θ : metasubst) (Θ : aenv) : Prop :=
  (Ξ ++ Θ0) ≤[ θ ] Θ ->
  empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ P))
             ≈ (ptyp_to_bskl_syn (msubst_lookup θ α)) ->
  exists Θ1 θ1, Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1
             /\ Θ1 ≤[ θ1 ] Θ /\ a_inc_equiv (Ξ ++ Θ0) θ θ1 Θ.
```

`Ψ` and the *decorated* `S : uskl` (with `P = ⌊S⌋ˢ`, `algo/def_decorated.v:44`)
are **mandatory** — the paper's augmented solution `:2235-2242` is stated on the
decorated skeleton with a tag context, and the `ForallInh` case's declarative
premise consumes a `δ` from `Ψ`.  The existing soundness motive
(`consis_sound_post`, `prop_consis_sound.v:2501`) instantiates `Ψ := empty` and
`S := pskl_to_uskl P` because *it* gets to choose the decoration; completeness is
*given* one and cannot.

Split per §6: `unify/assign_complete_post` are the **(EX)** halves;
the `Θ1 ≤[θ1] Θ ∧ a_inc_equiv ∧ ⊑` conjuncts move into **(OPT)**, which is stated
over an *already-given* derivation.

### 7.3 Supporting lemmas that DO NOT EXIST YET

**(L-measure) — new file `algo/prop_measure.v`.**  None of this exists; grep
found no context-unfolding substitution anywhere.

| # | statement | notes |
|---|---|---|
| L1 | `aenv_msubst : aenv -> metasubst` (§4.1) | plain `Fixpoint`; needs `a_wf_aenv`'s "definitions are wf in the tail" only for the *proofs*, not the definition |
| L2 | `aenv_msubst_agree_tail : uniq Θ -> Θ = Θp ++ Θs -> forall X ∈ dom Θs, msubst_lookup (aenv_msubst Θ) X = msubst_lookup (aenv_msubst Θs) X` | the workhorse; uses `msubst_ptyp_agree` (`prop_compose.v:445`) |
| L3 | **`a_tyequiv_downarrow : a_wf_aenv Θ -> Θ ⊢ A ≡ᵗ B -> ⇓[Θ]A = ⇓[Θ]B`** | the crux.  Induction on `a_tyequiv`; `flex_def` case = L2; `all` case needs `msubst_ptyp_open` (`prop_compose.v:307`) |
| L4 | `aenv_msubst_tvar : aenv_msubst ((α~abind_tvar) :: Θ) = aenv_msubst Θ` (and `var_typ`/`var_skl`) | one line; makes `Θ → Θ,α` invisible |
| L5 | `downarrow_msubst_subst : ⇓[Θ](msubst θ' (P[τ/γ̂])) = ⇓[Θ](msubst θ P)` given `((γ̂≔τ)::Θ₀') ≤[θ] Θ` and `θ' = tail θ` | (M2); L3 + a subst-commutation |
| L6 | `a_inc_equiv_downarrow : a_inc_equiv Θ₀ θ θ₁ Θ -> a_wf_pskl Θ₀ P -> ⇓[Θ](msubst θ P) = ⇓[Θ](msubst θ₁ P)` | (M1) |
| L7 | `size_pskl` invariance under opening with a free var | LNgen already generates `size_pskl_open_pskl_wrt_pskl_var` (`prop_ln.v:227` neighbourhood) — **check it is there, else generate** |

**(L-structure) — needed by (EX) to *build* the rules.**

| # | statement | why |
|---|---|---|
| L8 | **head-preservation:** `a_consis` from `(α~abind_tvar) ++ Θ₀` outputs `(α~abind_tvar) ++ Θ₁` | C8/C9/C11 must re-attach the rigid head to match `a_consis__forall_inh`'s shape.  `Assign-SolveM` inserts `β̄` *below* `α̂`, which is below the walked prefix, so this is true — but it needs proving |
| L9 | cofinite renaming for the constructed derivation (`a_consis_rename_tvar`) | C8/C9/C11 need the derivation for *all* `α ∉ L` |
| L10 | `msubst_compose ζ ι ≡ ζ` | to land `a_consis_optimal`'s `θ ≡ ζ ∘ θ₁` from the paper's `θ ≡ θ₁` (the algorithm's `θ₁` is the identity `ι`, `a_isub`) |

**(L-bridge) — the missing content of C14/C15/C16.**  See §9.1.

**Already green and reusable:** `a_inc_compose` (`prop_compose.v:695`),
`msubst_pskl_compose` (`:594`), `a_tyequiv_msubst` (`:547`),
`a_inc_peel_suffix` (`:629`), `ad_precise` + `ad_precise_preserves_refine`
(`prop_precise.v:47, 585`), `ad_refine_syn_trans` (`prop_precise.v:423`).

---

## 8. CORRECTIONS NEEDED TO `algo/prop_consis_complete.v`

The file is definitions only (108 lines).  Three of them are **wrong or
incomplete after the refactor**:

1. **`a_assign_problem` (line ~96) — `a_wf_pskl Θ0 P` is too strong.**
   `Assign-Depend` *moves* flexible variables out of `Θ0` into `Ξ` while `P`
   keeps mentioning them (its premise is literally `β̂ ∈ ftv(P)`).  So at a
   recursive assignment node `P` is well-formed in **`Ξ ++ Θ0`**, not in `Θ0`.
   The soundness side already has this right: `assign_sound_concl`
   (`prop_consis_sound.v:2554`) requires `(Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P`.
   Same for `a_non_flex Θ0 P → a_non_flex (Ξ ++ Θ0) P`.
   *(The two coincide only at the top-level call, where `Ξ = nil`.)*

2. **`a_assign_problem` — missing the paper's `Ξ` invariant.**  `full-algo-spec.tex:1508-1509`
   requires "`Ξ` only contains declarations of flexible variables **appearing in
   `P`**".  `a_decls Ξ` gives only "all entries are undefined flexible".  Add
   `dom Ξ [<=] ftvar_in_pskl P`.  `Assign-Depend` maintains it (`β ∈ ftv P`).

3. **`a_unify_problem` — `α ∈ dom Θ0` should be `a_flex_tvar Θ0 α`.**  The paper's
   `α̂`/`β̂` are hatted (flexible), and the mechanized rules
   (`a_unify__flex_id`/`_l`/`_r`/`_assign`) all carry `a_flex_tvar` explicitly
   (the prose-completion recorded in `PAPER-GAPS.md:428`).  `α ∈ dom Θ0` also
   admits rigid and term variables.

4. **`a_consis_solution` / `a_consis_optimal` are the *unaugmented* forms.**  They
   are correct as the *statement* of the theorem, but the **induction** must run on
   the augmented problem `(Δ₁; Δ₂; Ψ; Θ₀; P₀; S)` of `:2230-2242` — decorated `S`,
   tag context `Ψ`, and the second refinement `Δ₂ ⊢ θ⌊S⌋ ⊳ Q`, plus the
   `no_flex_dep` / `flex_above_free` side conditions that `consis_sound_post`
   already carries.  Keep the current definitions as the top-level corollaries and
   add augmented `*_post` motives next to them.

`a_assign_solution` and `a_unify_solution` themselves are **fine**: `Assign-Assign`
absorbing `Ξ` into its premise's *context* is a property of the rule, and the
solution definition already quantifies over `(Ξ ++ Θ0) ≤[θ1] Θ1`, which is what
the paper says (`:1510-1512`).  The brief's worry there is unfounded.

---

## 9. PAPER GAPS FOUND (for `docs/PAPER-GAPS.md`)

### 9.1 GAP — `§1`'s flexible cases are one sentence, and they hide two obligations

`consistency-proofs.tex:2568-2569`: *"The cases where `P` or `P₀` is a flexible
variable are handled by the other two parts of the lemma."*  That is the entire
treatment of `Flex`, `FlexL`, `FlexR` (C14–C16).  Two things are missing:

* **Constructing the callee's solution.**  A consistency solution gives
  `Θ ⊢ syn θS ≈ bid Q` **and** `Δ₁ ⊢ inh θP₀ ⊳ Q`.  The unification/assignment
  problem needs `Θ ⊢ θα̂ ≈ θβ̂` / `Θ ⊢ θP₀ ≈ θα̂` — a *different* judgment
  between the *two inputs*, with `Q` eliminated.  Getting it requires the
  **bridge** (consistency-into-`Q` + refinement-of-`Q` ⟹ relation between the
  two inputs) — the same bridge already built for the soundness converse
  (`prop_consis_sound.v`, "consistency's join + refinement ⟹ type equivalence").
  The paper never invokes it here.
* **Recovering the consistency conclusion's PRECISION.**  `§1`'s conclusion
  demands `Δ₁,Δ₂ ⊢ θ₁P₁ ⊑ Q`, and for `Flex`/`FlexL`/`FlexR` the algorithmic
  output is `P₁ = α̂`.  The `§2`/`§3` IHs produce **no precision statement at
  all** (`:2266-2270`, `:2412-2416`).  So `Θ ⊢ θ₁α̂ ⊑ Q` has to be proved
  separately — it is *not* "handled by the other two parts".

### 9.2 GAP — `§3` never proves the algorithm is not STUCK

`§3`'s skip cases are dismissed with *"Our goal follows from IH and context
weakening"* (`:2557-2558`), but `Assign-Skip`/`Assign-SkipRigid` carry the side
condition `β̂ ∉ ftv(P)` and there is **no rule at all** for a **rigid** head
`β ∈ ftv(P)`.  Completeness must therefore *prove the walk never reaches such a
head* — the escape/scope check.  It is true (and provable): `a_inc`
(`def_meta.v:143-171`) peels the rigid `β` via `a_inc__tvar` **before** it reaches
`α̂`, so `θα̂` is well-formed in a target *below* `β`; whereas `β ∈ ftv(P)` forces
`β ∈ ftv(θP)` (`β` is rigid, `θ` cannot erase it) and consistency against the
**monotype** `θα̂` forces `β ∈ ftv(θα̂)` — contradiction.  But the paper does not
do it, and it is the classic hard step in DK-style completeness.

Similarly `Assign-SolveM` (`:2430-2461`) silently assumes both of its premises:
* the **occurs check** `α̂ ∉ ftv(P)` — never established;
* that `guess^TY(P)` **succeeds and returns a monotype** (`a_guess_mono` has no
  `all` case, `def_extra.v:222-236`; `a_assign__solve_m` additionally premises
  `mono_ptyp τ`).  The paper gestures at this ("By definition of `guess^TY`, ⟨c⟩,
  and ⟨b⟩") but does not prove it.  Both follow from the solution, but both are
  real obligations.

### 9.3 GAP — the three induction subjects do not combine (the subject of this doc)

`:2257` ("mutual induction for the three parts"), `:2277` ("induction on the
context `Θ₀`"), `:2420` ("induction on the pair of contexts `Θ₀ ∣ Ξ`"), `:2565`
("induction on the declarative consistency derivation").  §3 shows no
lexicographic combination of *those three* is well-founded, and that `:2565` is
not well-founded on its own (`UnivGhostR`, `:2570-2572`, recurses with the same
derivation).  **Repaired** by §4's `V`, which is a quantity the paper never
names.  Worth reporting: the proof is *correct*, its stated induction is not.

---

## 10. Summary of the plan

1. `algo/prop_measure.v` — `aenv_msubst`, `⇓`, L1–L7.  Self-contained, no
   dependence on the consistency judgments.  **Do this first; it is the crux and
   the only genuinely new idea.**
2. `algo/prop_consis_complete.v` — fix the four definition issues in §8, add the
   augmented `*_post` motives.
3. **(OPT)** `a_assign_unify_consis_optimal` by
   `a_assign_unify_consis_mutind` — 28 cases, same shape as the green soundness
   bundle.  Needs L10, the bridge, `prop_compose` + `prop_precise` (both green).
4. **(EX)** `a_assign_unify_consis_complete` by nested strong induction on
   `(V, n, t, k)`, calling (OPT) at `Arrow`.  Needs L8, L9, and §9.2's three
   not-stuck lemmas.
5. Top-level corollaries: the theorem exactly as
   `full-algo-spec.tex:1541-1559`, against the *unaugmented* definitions already
   in `prop_consis_complete.v`.

The one place I am **not certain**: §6's claim that (EX) never needs a precision
fact from *its own* IH.  I checked all 21 edges and none does — every (EX) IH
consumer needs only `∃ Θ₁ Q₁, derivation` plus a solution at the shifted context,
which (OPT) supplies.  But this is the kind of thing that only survives contact
with Coq.  If it breaks, fuse (OPT) and (EX) into the paper's single statement
(`:2246-2255`) and run the *whole* thing on `μ` — the measure verification in §5
is unaffected either way, since it never mentions the conclusion.
