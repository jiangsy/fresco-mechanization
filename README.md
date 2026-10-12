# Fresco — Rocq mechanization

This is the mechanization part of the artifact for the POPL27 paper #1060:

"Bidirectional Typing with Freezing, Skeletons, and Ghosts", by Wenhao
Tang, Shengyi Jiang, Aghilas Y. Boussaa, Sam
Lindley, and Bruno C. d. S. Oliveira

The implementation part of the artifact is available at
[fresco-implementation](https://github.com/4y8/freso-implementation).

Everything is proved: there are no admitted lemmas and no axioms.  The entry
point is [`README.v`](README.v), which `Check`s every headline result at its
paper-level statement and runs `Print Assumptions` on it; every report reads
"Closed under the global context".

## Scope

Section 5 of the paper describes the mechanization as a faithful encoding of
the declarative type system.  It serves as a formal reference for the paper's
definitions, including the colours, modes, skeletons and ghosts.  It also
checks declarative properties, such as the equivalence of the syntax-directed
and declarative typing rules (Lemmas B.1 and B.2).

Beyond that, the mechanization covers:

- **The full algorithmic system** of Section 4 and Appendix C: constraint
  collection and solving, consistency, subtyping, skeleton splitting, skeleton
  inference and type inference.  Each judgement has soundness and completeness
  (with optimality), proved against the declarative system: Theorems 4.2,
  4.3, 4.5, 4.6, C.2 and C.3, and the supporting lemmas of Appendices D–F.
- **An extractable algorithm.**  `fresco/ext_algo/` re-encodes the algorithm
  with a threaded fresh-name supply.  It proves the algorithm terminates and is
  equivalent to the relational algorithm in `fresco/algo/`, so the theorems
  above carry over to it.  It also gives a certified decision procedure for
  type inference (`fresco_infer`), which extracts to OCaml.
- **A frontend.**  `frontend/` is a small parser and command-line driver
  around the extracted OCaml.  `examples/` contains the paper's comparison
  examples (Appendix A), and the regression tests check that each is accepted
  or rejected as the paper reports.

## Getting started

### Dependencies

| Dependency | Version tested | Needed for |
|---|---|---|
| [Rocq / Coq](https://rocq-prover.org) | 8.20.0 (OCaml 4.14.2) | everything |
| [Metalib](https://github.com/plclub/metalib) | `master` (opam `coq-metalib.dev`) | locally nameless infrastructure |
| [Equations](https://github.com/mattam82/Coq-Equations) | 1.3.1+8.20 | `fresco/ext_algo/` (well-founded recursion) |
| OCaml | ≥ 4.14 (`ocamlc` on `PATH`) | the frontend only |
| Python | 3 | the frontend's regression tests only |
| [Ott](https://github.com/ott-lang/ott) *(optional)* | 0.34 | regenerating `fresco/def_ott.v` |
| [LNgen](https://github.com/plclub/lngen) *(optional)* | 0.3.2 (`master`, tested at `c034c8d`) | regenerating `fresco/prop_ln.v` |

One way to install everything with [opam](https://opam.ocaml.org):

```sh
opam switch create fresco ocaml-base-compiler.4.14.2
eval $(opam env --switch=fresco)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.20.0
opam install coq-equations.1.3.1+8.20
opam pin add coq-metalib https://github.com/plclub/metalib.git
```

#### Optional: Ott and LNgen

The Ott and LNgen outputs (`fresco/def_ott.v`, `fresco/prop_ln.v`) are
committed, so `make coq` does not need either tool.  They are only needed to
regenerate those two files from `fresco/language.ott`.

```sh
opam install ott.0.34

# LNgen is built from source with Haskell Stack (https://haskellstack.org).
git clone https://github.com/plclub/lngen.git
cd lngen && stack install           # installs `lngen` into ~/.local/bin
```

Then regenerate both files:

```sh
make -B ott lngen                   # -B: the committed files look up to date
make -B LNGEN=<path-to-lngen> ott lngen   # if lngen is not on PATH
```

The regenerated files are token-identical to the committed ones, apart from
comments, which the committed copies omit.  Build LNgen from `master`: an
older LNgen 0.3.2 build produces a different `prop_ln.v`.

### Building and checking the proofs

```sh
make coq            # full kernel check; parallel, NJOBS=4 by default
make NJOBS=8 coq    # more parallel jobs
```

`make coq` builds the proofs, including `README.v`, which prints one `Check`
and one assumption report per headline result when compiled.  An up-to-date
build does not print these reports again.  To check them repeatably, run the
following from the repository root to build the dependencies and explicitly
recompile `README.v`:

```sh
make coq &&
coqc -R . src README.v > assumptions.log 2>&1 &&
test "$(grep -c '^Closed under the global context$' assumptions.log)" -eq 34
```

The command must succeed, confirming exactly 34 closed assumption reports.
Then inspect the log for axioms or admissions:

```sh
grep -nE 'Axioms:|admit' assumptions.log
```

This final command should produce no output.  `grep` returns status 1 when
it finds no matches; that is the expected result here.  If you replace the
log redirection with a `tee` pipeline, first enable `set -o pipefail` in Bash
or Zsh so that compiler failures remain visible in the pipeline's exit status.

A full build took about **9 minutes** with `NJOBS=8` on an Apple M2 Max
(12 cores, 64 GB).  The build is limited by one long chain of dependent
files, so more than about 8 jobs saves little time.  `make quick`
type-checks statements only (`.vos` mode); use it only for a fast sanity
check, because it does not replay the proofs.

`make coq` also extracts the type inference procedure to
`fresco/ext_algo/extraction/extracted/fresco_guess.ml`.

### Frontend and paper examples

```sh
make frontend                       # extract, then compile with ocamlc
make examples                       # run the accepted examples
make test-frontend                  # also check the expected rejections
_build/frontend/fresco examples/E3b.fresco
printf 'fun x -> x\n' | _build/frontend/fresco -
```

The frontend uses only the OCaml standard library. Its executable and compiler
products live in `_build/frontend/`; `make clean-frontend` removes them.
The handwritten lexer, parser, context setup, and printer are not verified.
Type inference uses the extracted, verified `fresco_infer` / `e_typing_run`.

#### Input syntax and output

Each file contains optional context declarations followed by one expression.
For example, [`examples/A2.fresco`](examples/A2.fresco) contains:

```text
val choose : forall a. a -> a -> a;
val id : forall a. a -> a;

choose id
```

`val` declares a term assumption and `type` declares a rigid type variable.
These describe the initial context, not executable bindings; they cannot
refer to later declarations. Names must be unique within each declaration
namespace. Local binders may shadow earlier names.

```text
program     ::= declaration* expression EOF
declaration ::= "type" name ";" | "val" name ":" type ";"
expression  ::= "fun" parameter+ "->" expression
              | application [":" type]
application ::= atom atom*
atom        ::= name | "(" ")" | "(" expression ")"
              | "{|" expression "|}"
parameter   ::= name | "_" | "(" name ":" type ")"
type        ::= "forall" name+ "." type
              | type-atom ["->" type]
type-atom   ::= "unit" | name | "(" type ")"
```

Application associates left; type arrows associate right. Annotation has lower
precedence than application; parenthesize a lambda to annotate the entire lambda.
`{| ... |}` is freeze. Identifiers start with an ASCII letter or underscore,
followed by letters, digits, underscores, or apostrophes. `_` is a lambda
parameter that cannot be referenced. `--` starts a line comment.

`forall` binds variables only within its type, not in a
lambda body. Unbound names are rejected before inference. The syntax is
implemented in [`frontend/parser.ml`](frontend/parser.ml).

Output is `filename: inferred-type`. Unsolved monotype variables print as
`?m0`, `?m1`, etc.; these are inference metavariables, not implicit `forall`
binders or accepted input syntax. Explicit universal binders print as
`forall a0. ...`; the frontend performs no extra generalization.

Exit status is 0 for success, 1 for algorithmic rejection, and 2 for lexical,
syntax, scope, file, or command-line errors. Syntax/scope errors include the
filename, line, and column. Multiple files are all processed, returning the
largest exit status. `-` reads standard input; `--help` prints usage.

#### Paper examples and regression checks

Each [`examples/*.fresco`](examples/) file is named after its row in the
comparison tables of Appendix A (Figures 8 and 9) and includes its required
library assumptions. The examples cover a subset of the tables. `Int` and
`Bool` are distinct rigid type variables; `Int × Bool` is encoded as
`forall c. (Int -> Bool -> c) -> c`.

`make examples` runs the 12 accepted examples. [`examples/rejected/`](examples/rejected/)
holds the rejected rows A8 and E2a, and E3b without its freeze.
`make test-frontend` runs [`frontend/test_frontend.py`](frontend/test_frontend.py),
checking all 15 examples, exact inferred outputs, shadowing, binding indices,
precedence, freshness across context declarations, diagnostics, and CLI behavior.

## Layout

| Directory | Contents |
|---|---|
| `fresco/language.ott` | the grammar (types, skeletons, terms, contexts) |
| `fresco/` | generated syntax (`def_ott.v`) and locally nameless lemmas (`prop_ln.v`); shape predicates (`def_shapes.v`); colour coercions (`coercions.v`); notations (`notations.v`) |
| `fresco/decl/` | the declarative system of Section 3 and Appendix B, and its metatheory |
| `fresco/algo_decl/` | the declarative judgements over algorithmic contexts (Appendix C.2), precision, and the conservativity bridge back to `decl/` |
| `fresco/algo/` | the algorithm of Section 4 and Appendix C, in four groups (`basic/`, `consistency/`, `subtyping/`, `typing/`), each with soundness and completeness |
| `fresco/deco_algo/` | the decorated (ε-tag-carrying) algorithm of Appendices E.1 and F, used for the soundness proofs |
| `fresco/ext_algo/` | the supply-threaded, executable algorithm: termination, equivalence with `algo/`, decidability, extraction driver |
| `frontend/`, `examples/` | OCaml frontend for the extracted algorithm; the paper's comparison examples |
| `README.v` | the index of headline results |

`README.v` is the only Coq file with comments.

## Paper → Rocq: definitions

Figure numbers refer to the full version of the paper, with appendices.  All
files are under `fresco/`.

| Paper | Rocq | File |
|---|---|---|
| Types `A`, bidirectional types, unresolved types, terms, contexts (§3.1, §3.4) | `ptyp`, `btyp`, `utyp`, `exp`, `denv` | `def_ott.v` (from `language.ott`) |
| Synthesised / inherited / decorated types, values | `is_styp`, `is_ityp`, `is_dtyp`, `is_value` | `def_shapes.v` |
| Skeletons; bidirectional / unresolved skeletons (§3.5) | `pskl`, `bskl`, `uskl` | `def_ott.v` |
| Synthesised / inherited / decorated skeletons | `is_sskl`, `is_iskl`, `is_dskl` | `def_shapes.v` |
| Painting with colours, `syn{A}` / `inh{A}`, type ↦ skeleton | `ptyp_to_btyp_syn`, `ptyp_to_btyp_inh`, `ptyp_to_pskl`, … | `coercions.v` |
| Well-formedness of types and skeletons (§3.5) | `d_wf_ptyp`, `d_wf_btyp`, `d_wf_utyp`, `d_wf_pskl`, `d_wf_uskl` | `decl/def_rules.v` |
| Refinement `Γ ⨟ Δ ⊢ P ⊳ Q` (§3.5) | `d_refine_syn`, `d_refine_pskl` | `decl/def_rules.v` |
| Declarative typing (Fig. 1) | `d_typing` | `decl/def_rules.v` |
| Syntax-directed typing (§3.3, App. B.2) | `d_sd_typing` | `decl/def_rules.v` |
| Subtyping and consistency (Fig. 2; all-in-one, Fig. 11) | `d_sub`, `d_consis` | `decl/def_rules.v` |
| Tag judgement `Γ ⊢ Ψ ▹ ψ` (Fig. 11) | `d_tags`, `d_tags_skl` | `decl/def_rules.v` |
| Skeleton inference (Fig. 3) | `d_pat` | `decl/def_rules.v` |
| Skeleton subtyping and consistency (Fig. 4) | `d_pat_sub`, `d_pat_consis` | `decl/def_rules.v` |
| Algorithmic contexts and their well-formedness (§4.1, App. C.2) | `abind`, `aenv`, `a_wf_aenv`, `a_wf_ptyp`, `a_wf_pskl` | `algo/def_rules.v` |
| Metasubstitutions, information increase, equivalence (§4.1, Fig. 12) | `metasubst`, `msubst_*`, `a_inc`, `a_inc_equiv` | `algo/basic/def_meta.v` |
| Declarative judgements in algorithmic contexts (Fig. 13) | `ad_sd_typing`, `ad_pat`, `ad_pat_sub`, `ad_pat_consis`, `ad_refine_syn`, `ad_refine_pskl` | `algo_decl/def_*.v` |
| Partial precision (App. E.3) | `ad_partial_precise` | `algo_decl/def_subtyping.v` |
| Guessing input skeletons (§4.2) | `a_guess`, `a_guess_mono` | `algo/def_rules.v` |
| Algorithmic type inference and skeleton splitting (Fig. 14) | `a_typing`, `a_split` | `algo/def_rules.v` |
| Algorithmic skeleton inference (Fig. 15) | `a_pat` | `algo/def_rules.v` |
| Algorithmic subtyping (Fig. 16) | `a_sub`, `a_sub_flex` | `algo/def_rules.v` |
| Look and constraint collection (Fig. 17) | `a_extract`, `a_looksub`, `a_lookeq` | `algo/def_rules.v` |
| Constraint solving (Fig. 18) | `a_solve_cstr`, `a_solve_sub`, `a_solve_eq` | `algo/def_rules.v` |
| Algorithmic consistency, unification, assignment (Fig. 19) | `a_consis`, `a_unify`, `a_assign` | `algo/def_rules.v` |
| Decorated subtyping, consistency, tag solving (Figs. 20–22) | `a_subtag`, `a_subtag_flex`, `a_consistag`, `a_solvetag`, `a_solvetag_sub`, `a_solvetag_eq` | `deco_algo/def_decorated.v` |

Judgements are written in notations close to the paper's, e.g.
`{{ Γ ⊢[ m ] e ⦂ B }}d`.  The brace pair names the system: `d` declarative,
`ad` declarative over algorithmic contexts, `a` algorithmic, `da` decorated.
The full legend is at the top of [`README.v`](README.v) and in
`fresco/notations.v`.

## Paper → Rocq: results

Every entry is `Check`ed in `README.v` with `Print Assumptions`.

| Paper | Rocq | File |
|---|---|---|
| Lemma B.1 (Soundness of syntax-directed rules) | `d_sd_typing_sound` | `decl/prop_syntax_directed.v` |
| Lemma B.2 (Completeness of syntax-directed rules) | `d_sd_typing_complete` | `decl/prop_syntax_directed.v` |
| General subsumption (syntax-directed; declarative corollary) | `d_sd_typing_general_subsumption`, `d_typing_general_subsumption` | `decl/prop_general_subsumption.v`, `decl/prop_syntax_directed.v` |
| Theorem 4.2 (Soundness of type inference) | `a_typing_sound`; closed programs: `a_typing_sound_infer`, `a_typing_sound_check` | `algo/typing/prop_soundness_typing.v`, `algo/typing/prop_typing_closed.v` |
| Theorem 4.3 (Completeness and optimality of type inference) | `a_typing_complete`; closed programs: `a_typing_complete_{infer,check}`, over syntax-directed typing `a_typing_complete_sd_{infer,check}`, over declarative typing `a_typing_complete_decl_{infer,check}` | `algo/typing/prop_completeness_typing.v`, `algo/typing/prop_typing_closed.v` |
| Theorem 4.5 (Soundness of subtyping) | `a_sub_sound` | `deco_algo/prop_soundness_sub.v` |
| Theorem 4.6 (Completeness and optimality of subtyping) | `a_sub_complete` | `algo/subtyping/prop_completeness_sub.v` |
| Theorem C.2 (Soundness of skeleton inference) | `a_pat_sound` | `algo/typing/prop_soundness_pat.v` |
| Theorem C.3 (Completeness and optimality of skeleton inference) | `a_pat_complete` | `algo/typing/prop_completeness_pat.v` |
| Lemma C.6 (Soundness of consistency) | `a_consis_sound` | `algo/consistency/prop_soundness_consis.v` |
| Lemma C.7 (Completeness and optimality of consistency) | `a_consis_complete` | `algo/consistency/prop_completeness_consis.v` |
| Lemma D.4 (Precision extends skeleton subtyping) | `ad_precise_extends_pat_sub` | `algo/subtyping/prop_completeness_sub_precise.v` |
| Lemma D.7 (Context precision preserves skeleton inference) | `ad_ctx_precise_pat` | `algo_decl/prop_ctx_precision.v` |
| Lemma E.14 (Stability of subtyping under more precise substitution) | `ad_pat_sub_precise_upre_fuel` | `algo/subtyping/prop_completeness_sub_precise.v` |
| Lemma E.15 (Completeness of constraint collection and solving for variables) | `a_solve_sub_complete_var` | `algo/subtyping/prop_completeness_solve_sub_var.v` |
| Lemma E.16 (Completeness of constraint collection and solving) | `a_looksub_solve_complete` | `algo/subtyping/prop_completeness_looksub_solve.v` |
| Lemma E.17 (Look completeness) | `a_extract_complete` | `algo/subtyping/prop_completeness_extract.v` |
| Lemma F.5 (Completeness of consistency constraint collection and solving) | `a_lookeq_solve_complete` | `algo/subtyping/prop_completeness_lookeq_solve.v` |
| Lemma F.6 (… for variables) | `a_solve_eq_complete_var` | `algo/subtyping/prop_completeness_solve_eq_var.v` |
| Consistency–subtyping transitivity | `d_consis_sub_trans` | `decl/prop_general_subsumption.v` |
| Order irrelevance of arguments (§2.8) | `d_typing_order_irrel` | `decl/prop_stability.v` |
| Checking-mode subtyping subsumes shallow monotype subtyping (§2.8) | `d_shallow_sub_complete` | `decl/prop_shallow.v` |
| Only polytypes need annotation | `mono_lambda_anno_redundant` | `decl/prop_shallow.v` |
| Decidability of type inference | `e_typing_dec_init`, and the certified function `fresco_infer` | `ext_algo/prop_run_corollaries.v` |

The last five rows are not numbered results in the paper.  The first four
are properties the paper uses or discusses informally, and the last one is
the decidability result for the extracted algorithm.

## How the encoding differs from the paper

These are the differences a reader comparing statements will notice.  None
changes what a theorem means.

- **Locally nameless binders.**  Generated by Ott and LNgen.  Declarative
  rules quantify cofinitely over fresh names; algorithmic rules pick one
  fresh name, as a run does.
- **One syntax per sort, colours as predicates.**  Where the paper writes
  `syn{A}` and `inh{A}` over one metavariable, the Rocq statement quantifies
  over one colourless base and applies the coercions `ptyp_to_btyp_syn` /
  `ptyp_to_btyp_inh`.  "Synthesised type" and similar are predicates on the
  one syntax (`is_styp`, …), not separate datatypes.
- **Tag contexts and `Δ` are finite atom sets**, compared up to set equality
  (`[=]`).
- **Prose side conditions become explicit hypotheses.**  The paper states some
  requirements in prose, for example "all inputs are well-formed".  The Rocq
  statements carry these as hypotheses, or as premises on the rules where the
  paper's metavariable implies them.  An example of the second is that a
  position written `A` holds a type, not a skeleton.

## License

MIT, see [LICENSE](LICENSE).
