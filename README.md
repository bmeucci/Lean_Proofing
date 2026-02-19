# Every Prime is a Forbidden Harmonic: Lean 4 Formalization

Formal verification in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4) of the paper

> **"Every Prime is a Forbidden Harmonic"**
> by Shiva Meucci (2026)

## Main Result

The central theorem, verified without `sorry` or custom axioms:

**Forb(I) &cap; {primes} = SSP &cap; [2, 29]**

The prime forbidden harmonic degrees of the icosahedral rotation group
are exactly the dense supersingular primes:

{2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

This identity connects the representation theory of finite rotation
groups to the arithmetic geometry of supersingular elliptic curves,
mediated by the Klein j-function.

## What Is Proven

The formalization verifies the complete logical chain of the paper.
Every theorem statement below has a machine-checked proof in Lean 4.

### Definitions and Foundational Results

| Result | Lean theorem | File |
|--------|-------------|------|
| Numerical semigroup membership (decidable) | `decidableInSemigroup` | `NumericalSemigroup.lean` |
| Forbidden degree predicate | `IsForbiddenDegree` | `MolienSeries.lean` |
| Polyhedral harmonic data (T, O, I) | `tetrahedralData`, `octahedralData`, `icosahedralData` | `Basic.lean` |
| Chevalley degree assignments | `tetrahedral_is_A3`, `octahedral_is_B3`, `icosahedral_is_H3` | `ChevalleyDegrees.lean` |

### Explicit Forbidden Sets

| Result | Lean theorem | File |
|--------|-------------|------|
| Forb(T) = {1, 2, 5} | `forbT`, `forbT_card` | `ForbiddenSets.lean` |
| Forb(O) = {1, 2, 3, 5, 7, 11} | `forbO`, `forbO_card` | `ForbiddenSets.lean` |
| Forb(I) = {1,2,3,4,5,7,8,9,11,13,14,17,19,23,29} | `forbI`, `forbI_card` | `ForbiddenSets.lean` |
| Each element verified forbidden via Molien predicate | `forbI_1_forbidden` ... `forbI_29_forbidden` | `ForbiddenSets.lean` |

### Theorems and Propositions (matching paper numbering)

| Paper Reference | Statement | Lean theorem | File |
|----------------|-----------|-------------|------|
| **Theorem 3** | \|Forb(G)\| = \|G\|/4 for G &isin; {T, O, I} | `g4_formula_T`, `g4_formula_O`, `g4_formula_I` | `CountingTheorem.lean` |
| **Theorem 3** (general) | (a-1)(b-1) + (a+b-1) = ab | `gcd2_counting_identity` | `CountingTheorem.lean` |
| **Theorem 4** | I is the unique group with sat(G) = 1 | `icosahedral_unique_saturation` | `Uniqueness.lean` |
| **Theorem 4** (equation) | (d&#8321;-4)(d&#8322;-4) = 12 has unique solution (6,10) | `uniqueness_exhaustion` | `Uniqueness.lean` |
| **Proposition 2** | 7+4+4 decomposition of Forb(I) | `decomp_union_eq_forbI` | `Decomposition.lean` |
| **Proposition 3** | A&#8325; simplicity forces obstruction concentration | `simplicity_saturation_coincidence` | `Simplicity.lean` |
| **Proposition 5** | Degree-6 critical point orbits: 12+20+30 = 62 | `degree6_orbit_sizes` | `KleinBridge.lean` |
| **Proposition 7** | Forbidden ceiling = 29 = \|I\|/2 - 1 | `forbI_max`, `ceiling_half_order` | `Decomposition.lean` |
| **Proposition 8** | Klein bridge: &Delta;(2,3,5) &rarr; &Delta;(2,3,&infin;) | `klein_from_icosahedral`, `icosahedral_equation_balance` | `KleinBridge.lean` |
| **Proposition 9** | dim M_{p-1} &le; 3 for p &le; 29 | `dim_at_5` ... `dim_at_29` | `ModularForms.lean` |
| **Proposition 10** | Constraint-saturation splitting for p &le; 29 | `trivial_split_small_primes`, `qr_7_mod_29` | `Splitting.lean` |
| **Proposition 11** | Discriminant transition at p = 37 | `dim_escape_37`, `p37_not_ssp` | `Splitting.lean` |

### Corollaries

| Paper Reference | Statement | Lean theorem | File |
|----------------|-----------|-------------|------|
| **Corollary 1** | Every prime is forbidden for some rotation group | `universal_prime_coverage` | `ForbiddenSets.lean` |
| **Corollary 2** | Forb(T) &sub; Forb(O) &sub; Forb(I) | `forbT_ssubset_forbO`, `forbO_ssubset_forbI` | `ForbiddenSets.lean` |
| **Corollary 3** | I-unique primes = {13, 17, 19, 23, 29} | `iUniquePrimes`, `iUnique_sdiff` | `Decomposition.lean` |
| **Corollary 4** | Overdetermined uniqueness of I | `overdetermined_uniqueness` | `Simplicity.lean` |

### Capstone

| Result | Lean theorem | File |
|--------|-------------|------|
| **Main Theorem**: Forb(I) &cap; Primes = SSP &cap; [2,29] | `main_theorem` | `Synthesis.lean` |
| Dense SSP = prime forbidden degrees | `denseSSP_eq_forbI_primes` | `Splitting.lean` |
| Complete verification chain (10 links) | `chain_molien` ... `chain_coincidence` | `Synthesis.lean` |

## Axiom Audit

The formalization relies only on the standard Lean 4 / Mathlib axioms:

- `propext` (propositional extensionality)
- `Classical.choice` (classical logic)
- `Quot.sound` (quotient soundness)

**No `sorry`, `sorryAx`, `native_decide`, or custom axioms appear anywhere
in the codebase.** The `#print axioms` commands in `Synthesis.lean` verify
this for all key theorems at compile time.

## File Structure

```
ForbiddenHarmonics/
  Basic.lean              -- Rotation group data structures, harmonic parameters
  NumericalSemigroup.lean -- Decidable semigroup membership, Frobenius numbers, gaps
  MolienSeries.lean       -- Forbidden degree predicate from Molien series
  ChevalleyDegrees.lean   -- Coxeter types A₃, B₃, H₃ and their degree data
  ForbiddenSets.lean      -- Explicit Forb(T), Forb(O), Forb(I) with element-wise proofs
  CountingTheorem.lean    -- |Forb(G)| = |G|/4 (Theorem 3)
  Decomposition.lean      -- 7+4+4 structure, I-unique primes, forbidden ceiling
  Uniqueness.lean         -- Saturation, (d₁-4)(d₂-4) = 12, icosahedral uniqueness
  Simplicity.lean         -- A₅ simplicity, overdetermined uniqueness
  KleinBridge.lean        -- Binary icosahedral group 2I, Klein invariants, j-function
  ModularForms.lean       -- dim M_k(SL₂(Z)), supersingular primes, Hasse invariant
  Splitting.lean          -- QR checks, constraint-saturation, discriminant transition
  Synthesis.lean          -- Main theorem, complete chain, axiom audit
ForbiddenHarmonics.lean   -- Root import file
```

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
# Clone the repository
git clone <repo-url>
cd <repo-name>

# Fetch Mathlib cache (saves hours of compilation)
lake exe cache get

# Build the formalization
lake build ForbiddenHarmonics
```

**Lean version:** 4.28.0-rc1 (see `lean-toolchain`)
**Mathlib:** latest master at time of verification

Build time is approximately 15-20 minutes on first run
(after fetching the Mathlib cache).

## Proof Architecture

The formalization uses three main proof strategies:

1. **Decision procedures** (`decide`): For concrete finite computations
   over explicit `Finset` values -- membership, subset, cardinality,
   disjointness, and primality checks.

2. **Arithmetic tactics** (`omega`, `norm_num`, `nlinarith`): For linear
   and nonlinear numeric facts. `omega` handles linear ℕ/ℤ arithmetic,
   `nlinarith` handles quadratic bounds, and `norm_num` evaluates
   concrete numeric expressions.

3. **Algebraic tactics** (`zify`, `ring`): For polynomial identities
   over ℕ, lifted to ℤ where subtraction is well-behaved.

## License

See LICENSE file for terms.

## Citation

If you use this formalization in your work, please cite:

```bibtex
@article{meucci2026forbidden,
  title   = {Every Prime is a Forbidden Harmonic},
  author  = {Meucci, Shiva},
  year    = {2026}
}
```
