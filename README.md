# tabular-types

This repository contains the proofs for _Extensible Data Types with Ad-Hoc Polymorphism_.

## List of Claims

The numbered theorems from the paper correspond to the following Lean theorems:

- Theorem 4.1: [`TabularTypes.«F⊗⊕ω».progress`](TabularTypes/F⊗⊕ω/Theorems.lean)
- Theorem 4.2: [`TabularTypes.«F⊗⊕ω».preservation`](TabularTypes/F⊗⊕ω/Theorems.lean)
- Theorem 5.1:
  - Kinding: [`TabularTypes.TypeScheme.KindingAndElaboration.soundness`](TabularTypes/Theorems/Type/KindingAndElaboration.lean)
  - Row Equivalence: [`TabularTypes.Monotype.RowEquivalenceAndElaboration.soundness`](TabularTypes/Theorems/Type/Basic.lean)
  - Subtyping: [`TabularTypes.TypeScheme.SubtypingAndElaboration.soundness`](TabularTypes/Theorems/Type/Basic.lean)
  - Constraint Solving: [`TabularTypes.Monotype.ConstraintSolvingAndElaboration.soundness`](TabularTypes/Theorems/Type/ConstraintSolvingAndElaboration.lean)
- Theorem 5.2: [`TabularTypes.Term.TypingAndElaboration.soundness`](TabularTypes/Theorems/Term.lean)

## Download, Installation, and Sanity-Testing Instructions

The proofs only require an installation of the Lean theorem prover. Local installation is recommended since Lean should be straightforward to install on most systems, but a virtual machine is also available.

### Local

First, install Lean 4 by following [the instructions on the Lean website](https://lean-lang.org/install/). This can be done through VSCode (which is recommended if you want to explore the proofs interactively), or through a terminal with the [manual installation](https://lean-lang.org/install/manual/) steps. While these proofs specifically require Lean v4.17.0, those installation instructions will download a version manager which automatically selects the correct version based on the [`lean-toolchain`](lean-toolchain) file, so no special action is required to ensure the correct version is used.

Once Lean is installed, run the following commands from the root of the project. The first downloads cached [mathlib](https://github.com/leanprover-community/mathlib4) artifacts, and may take some time depending on the speed of your internet connection. The second will build the proofs, and will also take a while (around 15 minutes on a i5-7600K with 16GB of RAM).

```sh
lake exe cache get
lake build
```

(If you encounter an error about `lake` not being found, and you installed Lean through VSCode, you may also need to modify the environment to include `$HOME/.elan/bin` in your `$PATH` first.)

### Virtual Machine

The virtual machine image, which is based on Ubuntu 24.04, can be downloaded from [Zenodo](https://zenodo.org/records/17298034). The OVA can be loaded into VirtualBox by using the "Import Appliance" option from the "File" menu and booted without any additional configuration. The username is `tabular-types`, and the password is also `tabular-types`. You should automatically be logged in, though you may have to provide the password to unlock a keychain used by VSCode. You may want to pull the latest version of the repository, in case any changes have been made since the virtual machine was created. VSCode should automatically open a workspace with the proofs on login. While the proofs have been prebuilt, you can rebuild everything to check them again by running `lake clean`, then following the build instructions under the previous heading.

## Evaluation Instructions

Lean prints warnings if any of the code that was built depends on [`sorry`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#sorry), which leverages a special axiom to close the goal without an actual proof being provided. Our proofs are complete, so the build steps above should've completed without any warnings.

To ensure that the mechanized proofs properly support the theorems from the paper, artifact reviewers should examine the statements of the key theorems listed in the first section of this README to ensure the Lean types match the theorems described in the paper. (As mentioned in section 5.5, the prose versions of the theorems do not explicitly include the class and instance environment well-formedness conditions, though these are assumed.) Reviewers can also examine the definitions of the syntax and semantics to ensure they match those given in the paper. These can be found in [`TabularTypes/Syntax`](TabularTypes/Syntax) and [`TabularTypes/Semantics`](TabularTypes/Semantics) for the source, and [`TabularTypes/F⊗⊕ω/Syntax`](TabularTypes/F⊗⊕ω/Syntax) and [`TabularTypes/F⊗⊕ω/Semantics`](TabularTypes/F⊗⊕ω/Semantics) for the target. Note that the presentation in the paper intentionally omits some details, such as the use of locally nameless representation, or annotations which ensure target type lists and source rows have deterministic kinds.

## Additional Description

Within the `TabularTypes` directory, the main subdirectories are:

- `Syntax`: The grammar of the source language.
- `Semantics`: The judgements about the source language.
- `Lemmas`: Proofs about minor properties of the source.
- `Theorems`: Proofs about major properties of the source.
- `F⊗⊕ω`: Contains further subdirectories of the same names as those listed above, but for the target language instead of the source.

In addition to the theorems listed in the first section of this README, the following theorems may also be interesting:

- [`TabularTypes.Program.TypingAndElaboration.soundness`](TabularTypes/Theorems/Program.lean)
- [`TabularTypes.TypeEnvironment.WellFormednessAndElaboration.soundness`](TabularTypes/Theorems/Type/KindingAndElaboration.lean)
- [`TabularTypes.TypeScheme.KindingAndElaboration.Monotype_open_preservation`](TabularTypes/Lemmas/Type/MonotypeOpenPreservation.lean)
- [`TabularTypes.«F⊗⊕ω».SmallStep.local_confluence`](TabularTypes/F⊗⊕ω/Lemmas/Type/SmallStep.lean)
- [`TabularTypes.«F⊗⊕ω».IndexedStronglyNormalizing.of_Kinding`](TabularTypes/F⊗⊕ω/Lemmas/Type/SmallStep.lean)
- [`TabularTypes.«F⊗⊕ω».MultiSmallStep.confluence`](TabularTypes/F⊗⊕ω/Lemmas/Type/SmallStep.lean)
