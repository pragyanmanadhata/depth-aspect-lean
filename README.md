# depth-aspect-lean

Lean 4 / Mathlib formalization of the **new arguments** in

> *Low-lying zeros of newforms in the depth aspect at the prime 2, split by root number.*

The family is the set of holomorphic newforms of weight `k` and level `2^n`
("depth" `n → ∞`), and the paper studies the one-level density of their
low-lying zeros, both for the whole family and after splitting by root number.

This repository is **private** and is a collaboration between the paper's
author, the agent that prepares the mathematical specification (Astra), and
the agents that formalize individual components. The shared rules are in
[`AGENTS.md`](AGENTS.md).

## What "complete" means here

**Milestone 1 (current).** Verify the paper's *new* arguments relative to a
list of *precisely stated background inputs*. Every background input is an
explicit hypothesis of the Lean theorem that uses it (a structure field or a
named `(h : …)` argument), never an `axiom`. A paper statement counts as
*verified relative to its inputs* when

1. its Lean statement has been agreed in [`STATUS.md`](STATUS.md),
2. the proof compiles with the pinned toolchain,
3. `#print axioms` (checked by `DepthAspect/Audit.lean`) lists only
   `propext`, `Classical.choice`, `Quot.sound`, and
4. every hypothesis of the theorem is one of the background inputs or
   conjectural hypotheses recorded in [`DEPENDENCIES.md`](DEPENDENCIES.md).

**Stronger endpoint.** Discharge the additional (non-conjectural) inputs, i.e.
prove them in Lean/Mathlib, so that the theorems depend on nothing beyond
Mathlib and the intended conjectural hypotheses.

**Conjectural hypotheses are never discharged.** The Generalized Riemann
Hypothesis for Dirichlet `L`-functions is an *intended* hypothesis of the
signed (root-number-split) theorem and stays an explicit hypothesis in its
Lean statement. The unsplit theorem is intended to be unconditional.

**Out of scope** (unless the specification says otherwise): numerical
experiments in the paper, remarks, and any results merely quoted from the
literature without new proof.

### Current state

| Component | Where | State |
|---|---|---|
| Project scaffold (toolchain, Mathlib pin, CI, docs) | `main` | done |
| Finite-sum identity behind Lemma 2.3 / eq. (11) (oldform second difference) | `DepthAspect/OldformSecondDifference.lean` | proved (PR #1), under review |
| Oldform decomposition for level `2^n` (input B1) | — | separate prerequisite, not started |
| Everything else in the paper | — | awaiting specification |

See [`STATUS.md`](STATUS.md) for the statement-by-statement map.

## Building

Pinned versions (do not bump outside a dedicated PR):

| Tool | Version |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` (see `lean-toolchain`) |
| Mathlib | tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (see `lakefile.toml` and `lake-manifest.json`) |

```sh
# 1. Install elan (Lean version manager) once: https://github.com/leanprover/elan
# 2. Clone, then from the repository root:
lake exe cache get      # download prebuilt Mathlib (fast; needs network access to the Mathlib cache)
lake build              # builds the `DepthAspect` library, including the axiom audit
```

If the Mathlib cache is unreachable, `lake build` compiles the needed part of
Mathlib from source; this works but takes much longer.

Continuous integration (`.github/workflows/build.yml`) runs the same build on
every push to `main` and every pull request, using the Mathlib cache, and then
greps the project sources for `sorry`, `admit`, `axiom` and kernel bypasses.

## Repository layout

```
lean-toolchain                 pinned Lean version
lakefile.toml                  package config; pins Mathlib to a tag
lake-manifest.json             pinned transitive dependency revisions (tracked)
DepthAspect.lean               library root; imports every project module
DepthAspect/Basic.lean         shared notation and conventions
DepthAspect/Audit.lean         `#print axioms` guard for every completed result
DepthAspect/*.lean             one file per paper component
README.md  DEPENDENCIES.md  STATUS.md  AGENTS.md
.github/workflows/build.yml    CI build check
```

## Source of truth for statements

The paper's statements are recorded in `STATUS.md` from the project
specification. The paper file itself was not available in the session that
created this scaffold; the entries marked *provisional* there were written from
the task description and the standard shape of such results and must be
checked against the paper by Astra before being treated as agreed.
