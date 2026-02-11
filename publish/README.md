# Formal Verification: The Golden-Ratio Polyhedral Journey

[![Lean Build](../../actions/workflows/lean.yml/badge.svg)](../../actions/workflows/lean.yml)

This repository contains a machine-checked proof, written in the [Lean 4](https://lean-lang.org/) theorem prover with the [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) mathematics library, verifying the central claims of:

> **"The Golden-Ratio Polyhedral Journey: A Complete Forward Loop from Tetrahedron to Maximum Complexity and Return"**
> by Shiva Meucci (January 2026)

## What does "machine-checked" mean?

Unlike a traditional mathematical proof that relies on human reviewers to catch errors, this proof has been verified line-by-line by a computer. The Lean theorem prover is a program that accepts a mathematical statement only if every logical step is justified — no hand-waving, no gaps, no implicit assumptions.

**If the build badge above is green, the proof is valid.** You don't need to install anything or understand Lean to trust this — the verification runs automatically via GitHub's CI system every time the code is updated.

## What exactly is proved?

The main theorem (`the_golden_ratio_polyhedral_journey` in [Synthesis.lean](LeanProofing/Synthesis.lean)) formally verifies:

1. **Closed loop**: The journey starts at the tetrahedron and returns to the tetrahedron
2. **All forward**: Every step uses one of five permitted geometric operations (rectification, dualization, stellation, continuous deformation, subset extraction) — none is reversed
3. **60-face saturation**: The rhombic hexecontahedron achieves exactly 60 faces, saturating the icosahedral symmetry bound
4. **Belt identity**: The exact algebraic identity φ⁸ + φ⁻⁸ = 47, where φ is the golden ratio
5. **Coset structure**: The icosahedral group contains exactly 5 copies of the tetrahedral group (|I|/|T| = 60/12 = 5)
6. **Pentagonal incompatibility**: Five-fold symmetry is absent from the tetrahedral group, making exact orientational return impossible

### Axiom transparency

Lean reports exactly which foundational axioms any theorem depends on. The main theorem uses only Lean's three standard axioms:

```
'the_golden_ratio_polyhedral_journey' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the minimal logical foundations shared by essentially all of modern mathematics. Notably absent: `sorryAx` (which would indicate an unproven gap). **There are no gaps in this proof.**

## Verify it yourself

### Option 1: GitHub Codespaces (no installation required)

1. Click the green **Code** button above, then **Codespaces** → **Create codespace on main**
2. In the terminal, run:
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
source ~/.elan/env
lake exe cache get
lake build 2>&1 | tee build.log
```
3. Wait for the build to complete (the `lake exe cache get` step downloads precompiled dependencies to save time)
4. Look for `Build completed successfully` and the axiom verification line

### Option 2: Local installation

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager):

```bash
git clone https://github.com/SteamPunkPhysics/Polyhedral-Loop-Lean.git
cd Polyhedral-Loop-Lean
lake exe cache get
lake build
```

## Project structure

| File | Paper Section | What it proves |
|------|--------------|----------------|
| [GoldenRatio.lean](LeanProofing/GoldenRatio.lean) | §3 | φ² = φ + 1, Fibonacci-structured powers, **belt identity φ⁸ + φ⁻⁸ = 47** |
| [FiniteGroups.lean](LeanProofing/FiniteGroups.lean) | §4 | Klein's classification, **icosahedral group is maximal (order 60)** |
| [Polyhedra.lean](LeanProofing/Polyhedra.lean) | — | Definitions of all 12 polyhedra, Euler formula verification |
| [PlatonicSpine.lean](LeanProofing/PlatonicSpine.lean) | §5 | **Phase I**: Tetrahedron → Octahedron → Cube → Cuboctahedron → Rhombic Dodecahedron |
| [IcosahedralTransition.lean](LeanProofing/IcosahedralTransition.lean) | §6 | **Phase II**: Coset completion (5 tetrahedra → dodecahedron), rectification to RT |
| [Stellation.lean](LeanProofing/Stellation.lean) | §7 | **Phase III**: Four stellations RT → RHC, scaling by φ⁸ |
| [ForwardReturn.lean](LeanProofing/ForwardReturn.lean) | §11 | **Phase IV**: RHC → DH → Icosidodecahedron → Tetrahedron |
| [Incommensurability.lean](LeanProofing/Incommensurability.lean) | §12 | **5 ∉ T**: pentagonal symmetry incompatible with tetrahedral group |
| [Synthesis.lean](LeanProofing/Synthesis.lean) | §13 | **Main theorem**: complete forward loop with all properties |

## Paper

Shiva Meucci, "The Golden-Ratio Polyhedral Journey: A Complete Forward Loop from Tetrahedron to Maximum Complexity and Return" (January 2026).

## Technical details

- **Lean version**: 4.28.0-rc1 (pinned in `lean-toolchain`)
- **Mathlib commit**: pinned in `lake-manifest.json` for exact reproducibility
- **Lines of proof**: ~1,600 across 9 modules
- **Build system**: Lake (Lean's build tool)
