# Handoff Document: Lean 4 Formalization of "Every Prime is a Forbidden Harmonic"

## For the Fresh Claude Instance Starting the Formalization

---

## 1. Context

This is the second Lean 4 formalization project for Shiva Meucci's mathematical papers. The first project — formalizing "The Golden-Ratio Polyhedral Journey" — is complete, published at `SteamPunkPhysics/Polyhedral-Loop-Lean`, and provides reusable infrastructure.

### Key documents to read first:
1. **`LEAN_LESSONS_LEARNED.md`** — Every compilation pitfall from the first project, organized by category. Read this BEFORE writing any Lean code.
2. **`PAPER_ANALYSIS.md`** — Complete analysis of the paper, Mathlib coverage, module structure, and risk assessment.
3. **`paper/every_prime_forbidden_harmonic.tex`** — The full LaTeX source of the paper being formalized.
4. **`LeanProofing/`** — The working first-project source files with reusable components.

---

## 2. Environment Setup

### Step 1: Verify Lean toolchain
```bash
source ~/.elan/env  # Add to .bashrc immediately!
cat lean-toolchain  # Must match Mathlib's lean-toolchain exactly
```

### Step 2: Create the new project
Either create a new Lake project or add modules to the existing one. Recommendation: **create a new package** `ForbiddenHarmonics` within the same workspace, or a separate repo.

If starting fresh:
```bash
lake init ForbiddenHarmonics math
```
Then fix `lakefile.toml` to use direct git URL for Mathlib (not Reservoir):
```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "master"
```

### Step 3: Cache and build
```bash
lake update
lake exe cache get     # ALWAYS do this first
lake build 2>&1 | tee build.log
```

---

## 3. Critical Lessons from First Project (Summary)

These are the bugs that consumed the most time. **Read `LEAN_LESSONS_LEARNED.md` for full details.**

1. **`theorem` vs `def`**: `theorem` is ONLY for `Prop`. Structures, data, functions → `def`.
2. **NEVER universally quantify over structs with defaults**: `theorem foo (x : MyStruct) : x.field = ...` ALWAYS fails. Use concrete values.
3. **`sorry` contaminates everything**: Any transitive dependency on `sorry` adds `sorryAx`. Use `#print axioms` to verify clean.
4. **Named lemmas break between Mathlib versions**: Prefer `field_simp`, `nlinarith`, `ring`, `norm_num`, `omega`, `decide` over named rewrite lemmas.
5. **`rfl` only works for definitional equality**: Use `simp [defs]` for anything involving nested definitions.
6. **`ring` can't use hypotheses**: Use `linarith`/`nlinarith` when hypotheses are needed.
7. **`simp` may close the goal**: Don't add tactics after `simp` without checking first.
8. **Always capture build output**: `lake build 2>&1 | tee build.log`
9. **Fix ALL errors in one pass**: Builds take 10-20 minutes per file. Don't fix one error and rebuild.

---

## 4. Recommended Proof Tactics by Goal Type

| Goal Type | Tactic |
|-----------|--------|
| Arithmetic on naturals | `norm_num` or `omega` |
| Polynomial identity (no hypotheses) | `ring` |
| Identity with square roots | `field_simp; nlinarith [sqrt_sq_lemma]` |
| Linear consequence of hypotheses | `linarith` or `nlinarith` |
| Structure field equality | `simp [def1, def2]` |
| Finset membership | `simp [finsetName]` or `decide` |
| Fin cases exhaustion | `fin_cases i <;> simp_all [def]` |
| Concrete decidable computation | `decide` or `native_decide` |
| List/set containment | `simp [listDef]` then `omega` if needed |
| Power/exponent comparison | `exact pow_lt_pow_right₀ h_gt_one (by omega)` |

---

## 5. Proposed Module Architecture

### 5.1 Module dependency graph
```
Basic.lean
  ├── ChevalleyDegrees.lean
  ├── NumericalSemigroup.lean
  │     └── ForbiddenSets.lean
  │           ├── CountingTheorem.lean
  │           │     └── Uniqueness.lean
  │           └── Decomposition.lean
  ├── MolienSeries.lean
  │     └── ForbiddenSets.lean (also depends on this)
  ├── Simplicity.lean
  ├── KleinBridge.lean
  │     └── ModularForms.lean
  │           └── Splitting.lean
  └── Synthesis.lean (imports everything)
```

### 5.2 Module descriptions

#### `Basic.lean`
- Import Mathlib
- Reuse/import `FiniteRotationGroup3D` from first project (or redefine)
- Reuse golden ratio definitions if needed (φ, belt identity for §12)
- Define `ForbiddenDegree` predicate

#### `ChevalleyDegrees.lean`
- Define Coxeter types as inductive: A_n, B_n, D_n, E_6, E_7, E_8, F_4, H_3, H_4, I_2(m)
- For each: Chevalley degrees, group order, dimension
- Harmonic generators (Chevalley degrees minus d₁=2)
- Define the Molien exponent N = Σ(d_i - 1)

#### `NumericalSemigroup.lean`
- Define numerical semigroup ⟨a,b⟩ for coprime a, b
- Define representability: `n ∈ ⟨a,b⟩ ↔ ∃ x y : ℕ, n = a*x + b*y`
- Frobenius number: `F(a,b) = a*b - a - b`
- Gap count: `(a-1)(b-1)/2` (Sylvester's formula)
- Concrete computation for ⟨3,4⟩, ⟨3,5⟩, ⟨2,3⟩
- Gaps of ⟨3,5⟩ = {1, 2, 4, 7} — verify by `decide` or explicit enumeration

#### `MolienSeries.lean`
- Define harmonic Molien series as rational function: `(1 + t^N) / ∏(1 - t^{d_i})`
- For 3D case: `H_G(t) = (1 + t^(d₁+d₂-1)) / ((1-t^d₁)(1-t^d₂))`
- Define Molien coefficient extraction (coefficient of t^ℓ)
- Define forbidden degree: Molien coefficient = 0

#### `ForbiddenSets.lean`
- Compute Forb(T) = {1, 2, 5} from Molien series
- Compute Forb(O) = {1, 2, 3, 5, 7, 11}
- Compute Forb(I) = {1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 14, 17, 19, 23, 29}
- Verify |Forb(T)| = 3, |Forb(O)| = 6, |Forb(I)| = 15
- B_n forbidden sets for specific odd n (n=3,5,7,...)
- Universal prime coverage: every prime is in some Forb(B_n)

#### `CountingTheorem.lean`
- |G|/4 theorem: Forb count = |G|/4 for T, O, I
- Case 1 (gcd=1, tetrahedral): Sylvester gap count
- Case 2 (gcd=2, octahedral/icosahedral): parity decomposition
- Full algebraic proof with Sylvester formula

#### `Uniqueness.lean`
- Define Molien saturation: sat(G) = #Forb(G) / N
- Compute saturation for T (0.5), O (0.667), I (1.0)
- The algebraic equation: sat=1 requires (d₁-4)(d₂-4) = 12
- Only (6,10) satisfies this among polyhedral degree pairs
- Higher-dimensional saturation computations (B_n, A_n, D_n, E_n)
- Global uniqueness: I is the unique saturation-1 group

#### `Decomposition.lean`
- 7+4+4 decomposition of Forb(I)
- Parity wall: 7 odd degrees < 15
- Even gaps: 2 × gaps(⟨3,5⟩) = {2, 4, 8, 14}
- Post-threshold: 15 + 2 × gaps(⟨3,5⟩) = {17, 19, 23, 29}
- Forbidden ceiling: 29 = |I|/2 - 1
- I-unique primes: Forb(I) \ Forb(O) = {13, 17, 19, 23, 29}

#### `Simplicity.lean`
- A₅ is simple (use Mathlib's `alternatingGroup.isSimpleGroup_five`)
- A₄ has normal subgroup V₄
- S₄ has normal subgroups A₄ and V₄
- Only the simple group achieves saturation 1
- Overdetermined uniqueness corollary

#### `KleinBridge.lean`
- Define binary icosahedral group 2I (order 120)
- State: 2I ≅ SL(2, F₅)
- Klein invariant degrees: (12, 20, 30) = 2 × (6, 10, 15)
- Icosahedral equation: f⁵ + T² + cH³ = 0 (as axiom/definition)
- j-function as rational function of Klein invariants (stated)
- The Klein bridge: Δ(2,3,5) → Δ(2,3,∞), sending 5 → ∞ (stated)

#### `ModularForms.lean`
- Dimension formula for M_k(SL₂(ℤ))
- Compute dim M_{p-1} for p = 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
- Hasse invariant statement: S_p(j) = E_{p-1} mod p (axiomatized)
- Supersingular prime definition and list

#### `Splitting.lean`
- For p ≤ 23: dim M_{p-1} ≤ 2, so ≤ 1 generic root → trivially splits
- For p = 29: dim M_{28} = 3, discriminant Δ = -80 ≡ 7 (mod 29)
- 7 is QR mod 29 (6² = 36 ≡ 7) → quadratic splits
- For p = 37: dim M_{36} = 4, first failure
- SSP list = {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71}
- Dense SSP (≤ 29) = prime forbidden degrees of I

#### `Synthesis.lean`
- Import all modules
- Main theorem: the complete chain
- Forb(I) ∩ {primes} = SSP ∩ [2,29]
- #print axioms for the main theorem

---

## 6. Concrete Starting Code Skeleton

### `Basic.lean` (start here)
```lean
/-
  ForbiddenHarmonics/Basic.lean

  Foundational definitions for the formalization of
  "Every Prime is a Forbidden Harmonic" by Shiva Meucci.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

/-! ## Finite Rotation Groups in 3D (Klein's Classification) -/

/-- Klein's classification of finite rotation groups in SO(3). -/
inductive FiniteRotationGroup3D where
  | cyclic (n : ℕ) (hn : n ≥ 1) : FiniteRotationGroup3D
  | dihedral (n : ℕ) (hn : n ≥ 2) : FiniteRotationGroup3D
  | tetrahedral : FiniteRotationGroup3D
  | octahedral : FiniteRotationGroup3D
  | icosahedral : FiniteRotationGroup3D
  deriving DecidableEq

namespace FiniteRotationGroup3D

def order : FiniteRotationGroup3D → ℕ
  | cyclic n _ => n
  | dihedral n _ => 2 * n
  | tetrahedral => 12
  | octahedral => 24
  | icosahedral => 60

def isPolyhedral : FiniteRotationGroup3D → Prop
  | tetrahedral => True
  | octahedral => True
  | icosahedral => True
  | _ => False

end FiniteRotationGroup3D

/-! ## Polyhedral Harmonic Data -/

/-- The harmonic Chevalley degrees for 3D polyhedral groups.
    These are (d₁, d₂) where d₁·d₂ = |G| and the parent
    reflection group has degrees (2, d₁, d₂). -/
structure PolyhedralHarmonicData where
  d₁ : ℕ  -- first harmonic generator
  d₂ : ℕ  -- second harmonic generator
  N : ℕ   -- Molien exponent = d₁ + d₂ - 1
  hN : N = d₁ + d₂ - 1
  hOrder : d₁ * d₂ = order  -- |G| = d₁ · d₂
  order : ℕ

/-- Tetrahedral harmonic data: (3, 4), N = 6 -/
def tetrahedralData : PolyhedralHarmonicData where
  d₁ := 3; d₂ := 4; N := 6; order := 12
  hN := by norm_num
  hOrder := by norm_num

/-- Octahedral harmonic data: (4, 6), N = 9 -/
def octahedralData : PolyhedralHarmonicData where
  d₁ := 4; d₂ := 6; N := 9; order := 24
  hN := by norm_num
  hOrder := by norm_num

/-- Icosahedral harmonic data: (6, 10), N = 15 -/
def icosahedralData : PolyhedralHarmonicData where
  d₁ := 6; d₂ := 10; N := 15; order := 60
  hN := by norm_num
  hOrder := by norm_num
```

### Key design decisions:
1. **Forbidden sets as `Finset ℕ`** — concrete, decidable, can use `decide`
2. **Numerical semigroup membership as decidable predicate** — enables `decide`/`native_decide`
3. **Saturation as `ℚ` ratio** — exact computation, no floating point
4. **Modular form dimensions as concrete `ℕ` values** — tabulated, verified by `norm_num`
5. **Klein bridge as stated axiom** — honest about what's classical input vs. new proof

---

## 7. Build Order and Testing Strategy

### Phase 1: Foundation (expect 1 build cycle)
1. Write `Basic.lean`, `ChevalleyDegrees.lean`, `NumericalSemigroup.lean`
2. Build and fix
3. These have no deep Mathlib dependencies

### Phase 2: Core Forbidden Set Theory (expect 2-3 build cycles)
4. Write `MolienSeries.lean`, `ForbiddenSets.lean`
5. Write `CountingTheorem.lean`, `Decomposition.lean`
6. Build and fix

### Phase 3: Uniqueness and Simplicity (expect 1-2 build cycles)
7. Write `Uniqueness.lean`, `Simplicity.lean`
8. Build and fix

### Phase 4: Klein Bridge and Modular Forms (expect 2-3 build cycles)
9. Write `KleinBridge.lean`, `ModularForms.lean`, `Splitting.lean`
10. These are the hardest — expect iteration

### Phase 5: Synthesis (expect 1 build cycle)
11. Write `Synthesis.lean`
12. Verify with `#print axioms`
13. Clean up warnings

### Total estimate: 6-10 build cycles, similar to first project

---

## 8. What "Formally Verified" Means for This Paper

### The honest scope statement:

The formalization will verify that:
1. **All arithmetic identities** follow from the definitions (|G|/4, forbidden ceiling, set counts, nesting)
2. **The combinatorial structure** (7+4+4 decomposition, Sylvester gap counts) is correct
3. **Icosahedral uniqueness** follows algebraically from (d₁-4)(d₂-4)=12
4. **A₅ simplicity** is a Mathlib theorem, not an axiom
5. **The dimension counts** dim M_{p-1} are correct for all relevant primes
6. **The quadratic residue checks** (splitting at p=29, failure at p=37) are verified computationally
7. **The complete chain** connects correctly: each result's conclusion is the next result's hypothesis

### Classical inputs treated as definitions (not axioms with `sorry`):
- Chevalley degrees of each Coxeter type
- Group orders |T|=12, |O|=24, |I|=60
- Klein's result: j-function from 2I invariants
- Deligne/Kaneko-Zagier: supersingular polynomial from Hasse invariant
- Ogg's characterization: SSP = genus-0 primes
- Borcherds: SSP = prime divisors of |M|

This is the same approach as the first project: encode classical, uncontroversial mathematical facts as definitions, then verify that all claimed *consequences* follow rigorously.

---

## 9. Files in This Repository

```
Lean_Proofing/
├── HANDOFF.md                          ← THIS FILE (you are here)
├── PAPER_ANALYSIS.md                   ← Detailed paper analysis and Mathlib coverage
├── LEAN_LESSONS_LEARNED.md             ← All compilation pitfalls from first project
├── paper/
│   ├── every_prime_forbidden_harmonic.tex  ← Full LaTeX source
│   └── Polyhedral_Loop_v10.pdf            ← First paper PDF
├── LeanProofing/                       ← First project source (reusable components)
│   ├── GoldenRatio.lean                ← φ, ψ, belt identity
│   ├── FiniteGroups.lean               ← Klein classification, group orders
│   ├── Polyhedra.lean                  ← Polyhedra definitions
│   ├── PlatonicSpine.lean              ← Phase I chain
│   ├── IcosahedralTransition.lean      ← Phase II
│   ├── Stellation.lean                 ← Phase III
│   ├── ForwardReturn.lean              ← Phase IV
│   ├── Incommensurability.lean         ← 5 ∉ T
│   └── Synthesis.lean                  ← Main theorem
├── lakefile.toml                       ← Build config (Mathlib via git URL)
├── lean-toolchain                      ← Lean version pin
└── lake-manifest.json                  ← Dependency lock
```

---

## 10. Quick Reference: The 15 Forbidden Icosahedral Degrees

```
Forb(I) = {1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 14, 17, 19, 23, 29}

Parity wall (odd < 15):     {1, 3, 5, 7, 9, 11, 13}        — 7 degrees
Even gaps (2×gaps(⟨3,5⟩)):  {2, 4, 8, 14}                   — 4 degrees
Post-threshold (15+above):   {17, 19, 23, 29}                — 4 degrees
                                                        Total: 15 = |I|/4

Prime forbidden degrees:     {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} = first 10 SSP
Non-prime forbidden degrees: {1, 4, 8, 9, 14}

Forb(T) = {1, 2, 5}                  ⊂ Forb(O) ⊂ Forb(I)
Forb(O) = {1, 2, 3, 5, 7, 11}       ⊂ Forb(I)

SSP = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}
```

---

## 11. Golden Ratio Connection (Link to First Project)

The paper references the belt identity φ⁸ + φ⁻⁸ = 47 in §12 (The Golden Thread):
- L₈ = 47 is the 13th supersingular prime
- ∑SSP₁..₁₃ = 248 = dim(E₈)
- 47 + 1 = 48 = |2O| (binary octahedral)
- The index 8 = rank(E₈) = dim(O) (octonions)

The golden ratio module from the first project (`GoldenRatio.lean`) already proves:
- φ² = φ + 1
- φ⁸ = 21φ + 13
- φ⁸ + φ⁻⁸ = 47

These can be imported directly or the file can be copied into the new project.
