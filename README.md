# tabular-types

This repository contains the Lean 4 proofs for $\lambda^\Rightarrow_\rho$ at the top-level of the `TabularTypes` directory, and $\mathrm{F}^{\otimes\oplus}_\omega$ within the `TabularTypes/F⊗⊕ω` subdirectory. For each language, components are mainly organized into `Syntax`, `Semantics`, `Lemmas`, and `Theorems` directories.

## Usage

The proofs can be checked by [installing Lean 4](https://lean-lang.org/install/), fetching from the mathlib cache with `lake exe cache get`, then running `lake build` from the commandline. They can also be explored interactively within VS Code, or within another editor with Lean support.
