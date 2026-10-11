# Frontend for the extracted Fresco algorithm

From the repository root:

```sh
make frontend
make examples
make test-frontend
_build/frontend/fresco examples/A2.fresco
_build/frontend/fresco examples/E3b.fresco
printf 'fun x -> x\n' | _build/frontend/fresco -
```

The existing Coq dependencies (including Metalib and Equations) and OCaml
4.14 or later must be on `PATH`. Tests additionally require Python 3. The
frontend uses only the OCaml standard library; it needs neither Menhir nor
Dune. `make frontend` builds the extraction's Coq dependencies and compiles
`fresco_guess.ml` with the handwritten frontend. The executable and OCaml
compiler products live in `_build/frontend/`; `make clean-frontend` removes
them. Extraction output remains generated and ignored by Git.

Each file contains optional context declarations followed by one expression.
For example, paper row A2 is:

```text
val choose : forall a. a -> a -> a;
val id : forall a. a -> a;

choose id
```

`val` declares a term assumption and `type` declares a rigid type variable;
these headers describe the initial algorithmic context, not executable
bindings. They cannot define functions, recurse, or refer to later declarations.
Names must be unique within each declaration namespace. Local binders may
shadow declarations or earlier binders.

## Syntax

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
precedence than application. Parenthesize a lambda when annotating the entire
lambda. Identifiers begin with an ASCII letter or underscore and continue with
letters, digits, underscores, or apostrophes. `_` is a non-referenceable lambda
parameter. `--` comments continue through the end of the line or file.

The expression forms correspond directly to `exp` in `fresco/def_ott.v`:
unit, variables, annotated/unannotated lambdas, application, annotation, and
freeze. There is no `let`, type application, recursion, integer literal, native
pair, or native list syntax. `forall` binds type variables only within its type;
it does not introduce type variables into a lambda body. Unbound names are
rejected before the runner is called.

## Runner and output

The parser resolves local variables to de Bruijn indices and declared names to
fresh extracted atoms. Contexts are built newest-first, with every annotation
well scoped in the preceding context. The initial freshness supply contains all
context atoms as well as the expression's free atoms.

Files without declarations call the extracted `fresco_infer`. Files with an
initial context call `e_typing_run supply Mode_ti context Pskl_ghost expression`,
matching the judgments used by `test/test_examples.v`. No typing algorithm is
reimplemented in the frontend. The handwritten lexer, parser, context setup,
and printer are not themselves verified in Coq.

Output is `filename: inferred-type`. The printer follows solved monotype
bindings in the returned context. Unsolved monotype variables are displayed
as `?m0`, `?m1`, etc.; these are inference metavariables, not implicit `forall`
binders or accepted input syntax. Explicit universal binders print as
`forall a0. ...`. Output describes the runner's result, not a claim of principal
typing or extra generalization.

Exit status is 0 for success, 1 for algorithmic rejection, and 2 for lexical,
syntax, scope, file, or command-line errors. Syntax/scope errors report the
filename, line, and column. Multiple files are all processed; the largest exit
status is returned. `-` reads standard input, and `--help` prints usage.

## Paper examples

The files in `../examples/` transcribe rows from Fresco's comparison tables
(`impredicative/paper/sections/comparison-table.tex`, labels
`fig:comparison-table-QL` and `fig:function-signatures`). Each file contains
its own required library assumptions, so no sibling checkout is needed to run
it. The eight rows already proved in this repository's
[`test/test_examples.v`](../test/test_examples.v) are included, along with
additional instantiation and freeze cases.

| Files | Paper expression | Expected |
| --- | --- | --- |
| A1 | `fun x y -> y` | accept |
| A2 | `choose id` | accept |
| A4 | `fun (x : forall a. a -> a) -> x x` | accept |
| A5, A6 | `id auto`, `id auto'` | accept |
| A7 | `choose id auto` | accept |
| A10a, A10b, A10c | `poly id`, `poly (fun x -> x)`, `id poly (fun x -> x)` | accept |
| C2 | `r (fun x y -> y)` | accept |
| E2b | annotated `fun x -> poly x` | accept |
| E3b | `app (fun x -> poly x) {\| id \|}` | accept with freeze |
| rejected/A8 | `choose id auto'` | reject |
| rejected/E2a | `fun x -> poly x` | reject |
| rejected/E3b-unfrozen | `app (fun x -> poly x) id` | reject without freeze |

Following the existing Coq examples, `Int` and `Bool` are distinct rigid type
variables, and `Int × Bool` is encoded as
`forall c. (Int -> Bool -> c) -> c`. No native data types have been added to the
mechanization. The examples cover a subset of the paper, not its entire table.

`make examples` runs the 12 accepted examples. `make test-frontend` additionally
checks the three rejected examples, exact inferred outputs, shadowing, binding
indices, precedence, freshness across context declarations, diagnostics, and
CLI behavior.

The separation between a handwritten frontend and an extracted runner follows
the organization of [McTT](https://github.com/Beluga-lang/McTT); the concrete
`fun`, `forall`, and `{| ... |}` syntax follows the existing implementation in
`impredicative/paper/artifact/implementation/lib/parser.mly`.
