# tabular-types

This repository contains the Lean 4 proofs for $\lambda^\Rightarrow_\rho$ at the top-level of the `TabularTypes` directory, and $\mathrm{F}^{\otimes\oplus}_\omega$ within the `TabularTypes/F⊗⊕ω` subdirectory. For each language, components are mainly organized into `Syntax`, `Semantics`, `Lemmas`, and `Theorems` directories.

## Usage

The proofs can be checked by [installing Lean 4](https://lean-lang.org/install/), fetching from the mathlib cache with `lake exe cache get`, then running `lake build` from the commandline. They can also be explored interactively within VS Code, or within another editor with Lean support.

## `sorry`s

There are currently three places that require additional work:

1. We haven't yet proven normalization for the small step rules for the target types (`TabularTypes.«F⊗⊕ω».MultiSmallStep.normalization`), as this is difficult to mechanize, but we believe it should hold since the type level language is not particularly complex.
2. One substitution lemma (`TabularTypes.«F⊗⊕ω».SmallStep.TypeVar_subst_in`) needed to prove that the small step equivalence closure property is implied by stratified type equivalence is defined with a mutual recursion block which we have not yet been able to show is decreasing in Lean. Instead, we provide a pen-and-paper proof in the appendix of the paper.
3. Finally and most trivially, we need to refactor target kinding to make it deterministic (like source kinding). The only case which breaks this currently is empty type lists, which can be given any inner kind. This is necessary to show that type equivalence and small step type reduction preserve kinding in both directions (`TabularTypes.«F⊗⊕ω».TypeEquivalenceS.preservation` and `TabularTypes.«F⊗⊕ω».SmallStep.preservation`/`preservation_rev`). This change is conceptually easy if we require kind annotations on empty type lists (like we do for empty rows in the source), but it requires lots of manual refactoring.
