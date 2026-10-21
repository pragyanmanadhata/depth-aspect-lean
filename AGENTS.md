# AGENTS.md — shared rules for this formalization

Short, binding, and the same for every agent and human contributor.

## Mathematical rules

1. **No gaps.** A result is *completed* only if it compiles with the pinned
   toolchain and contains no `sorry`, `admit`, project-declared `axiom`,
   `native_decide`, `decide!`, `unsafe`, `implemented_by`/`extern` tricks, or any
   other kernel bypass. Partial work may exist on a branch but is never listed as
   completed in `STATUS.md`.
2. **Audit axioms.** Every completed theorem gets a `#guard_msgs in #print axioms`
   entry in `DepthAspect/Audit.lean`. Only `propext`, `Classical.choice`,
   `Quot.sound` are allowed. Also audit the *explicit* hypotheses: each must be a
   background input or a conjectural hypothesis listed in `DEPENDENCIES.md`.
3. **Inputs are hypotheses, never axioms.** Background facts from the literature
   and conjectures (GRH for Dirichlet `L`-functions) enter as explicit
   hypotheses of the theorems that use them. Conjectural hypotheses are never
   discharged; non-conjectural inputs may be discharged later (stronger endpoint).
4. **Statements are frozen once agreed.** The Lean statement of a paper item
   recorded as *agreed* in `STATUS.md` is not changed silently. A change needs a
   PR whose description says what changed in the statement and why, and the
   `STATUS.md` row is updated in the same PR.
5. **Casts and conventions are explicit.** Say in the docstring where an `ℕ`/`ℤ`
   subtraction or a cast happens and why it is harmless; prove a sanity lemma
   when it is cheap (see `oldformTotal_eq_sub_cast`).
6. **Paper correspondence in docstrings.** Each definition/theorem names the
   paper item it realizes (e.g. "eq. (11)", "Lemma 2.3") and what is *not* part
   of it.
7. **Search before building.** Before writing substantial infrastructure, search
   Mathlib (and the research libraries listed in `DEPENDENCIES.md`) and record
   the result there, even when the result is "not present".

## Collaboration rules

8. **Branches.** `main` holds the scaffold and reviewed, merged results. Each
   component is developed on its own feature branch and merged through a PR.
   Do not commit directly to `main` after the initial scaffold.
9. **Do not touch another agent's active branch.** In particular, Astra's
   specification branch is read-only for everyone else; propose changes via
   comments or a separate PR. Never rewrite history (rebase/force-push/amend) on
   a branch you did not create.
10. **Pins.** Lean, Mathlib and the manifest are pinned. Bumping them is a
    dedicated PR with a green build and nothing else in it.
11. **Reviews.** A proof PR stays open for independent review; the author does
    not merge their own proof PR. Review checks: statement matches `STATUS.md`,
    axioms audit, hypotheses audit, build green, docs updated.
12. **What goes in the repository.** Only project materials: Lean sources,
    docs, CI, manifests. Never credentials, correspondence, chat logs,
    dependency checkouts (`.lake/`), or build outputs. The repository stays
    private unless the owner explicitly asks for publication.
13. **Docs move with the code.** A PR that proves or restates something updates
    `STATUS.md` and, if inputs change, `DEPENDENCIES.md`.
