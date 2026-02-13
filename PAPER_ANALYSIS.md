# Paper Analysis: "Every Prime is a Forbidden Harmonic"

## Formalization Planning for Lean 4 + Mathlib

---

## 1. Paper Structure Overview

The paper has two parts:

- **Part I (Sections 2–8):** 20 proved results — the algebraic chain from Chevalley degrees through Molien series, Klein invariants, and the triangle group bridge to forced supersingularity for primes ≤ 29.
- **Part II (Sections 9–14):** Structural consequences — observations, conjectures, and arithmetic evidence connecting forbidden harmonics to division algebras, the Monster, etc. **Not claimed as proved theorems.**

### Formalization scope: Part I is the target. Part II is observational/conjectural.

---

## 2. The 20 Proved Results (Part I)

### Tier 1: Purely computational / combinatorial (straightforward in Lean)

| # | Result | Paper Ref | Core Content | Lean Difficulty |
|---|--------|-----------|-------------|-----------------|
| 1 | Rotation-subgroup decomposition | Lemma 2.1 | $H^G(t) = (1+t^N)/\prod(1-t^{d_i})$ | Medium — define as formula, verify for 3D cases |
| 3 | Explicit Forb(B_n) | Thm 3.1 | Forbidden set = {odd < n²} ∪ {2, n²+2}, count (n²+3)/2 | Medium — verify for specific n values |
| 4 | Every prime is forbidden | Cor 3.2 | Constructive: choose odd n > √p | Easy — just instantiate |
| 5 | Parity-wall prime capture | Thm 3.3 | All primes < N forbidden for parity-walled groups | Easy |
| 6 | |G|/4 counting theorem | Thm 4.1 | #Forb(G) = |G|/4 for T, O, I | Medium — three cases, Sylvester formula |
| 7 | Forbidden set nesting | Cor 4.2 | Forb(T) ⊂ Forb(O) ⊂ Forb(I) | Easy — concrete list check |
| 9 | 7+4+4 decomposition | Prop 5.1 | Forb(I) = parity wall + even gaps + post-threshold | Easy — concrete verification |
| 10 | I-unique primes | Cor 5.2 | {17,19,23,29} = N + 2×gaps(⟨3,5⟩) | Easy — concrete arithmetic |
| 16 | Forbidden ceiling | Prop 7.1 | 29 = |I|/2 − 1 = N + 2F(3,5) | Easy — norm_num |

### Tier 2: Group-theoretic / structural (moderate difficulty)

| # | Result | Paper Ref | Core Content | Lean Difficulty |
|---|--------|-----------|-------------|-----------------|
| 2 | Finiteness of Forb | Prop 2.1 | Finite iff gcd=1 or (gcd=2, N odd) | Medium — case analysis |
| 8 | Icosahedral uniqueness | Thm 5.1 | I is unique saturation-1 group across all dims | Medium-Hard — must exhaust Coxeter classification |
| 11 | Simplicity forces concentration | Prop 6.1 | A₅ is simple; T, O are not | Medium — Mathlib has A₅ simplicity |
| 12 | Overdetermined uniqueness | Cor 6.2 | I is simultaneously simple, maximal, terminal, has 5-fold | Medium — properties already in first project |
| 13 | Coprimality = incommensurability | Prop 6.3 | (3,5) are axis orders; gcd(3,5)=1 | Easy-Medium |
| 14 | Degree-6 critical point structure | Prop 7.2 | First I-invariant at degree 6; critical points on polyhedra | Medium — topological argument |

### Tier 3: Deep algebraic / number-theoretic (hard, requires significant infrastructure)

| # | Result | Paper Ref | Core Content | Lean Difficulty |
|---|--------|-----------|-------------|-----------------|
| 15 | Klein invariant bridge | Prop 8.1 | 2I invariants at degrees 2×(6,10,15) generate j | Very Hard — requires binary icosahedral group theory |
| 17 | Klein/triangle group bridge | Prop 8.2 | j bridges Δ(2,3,5) → Δ(2,3,∞), sending 5→∞ | Very Hard — deep classical result |
| 18 | Hasse invariant / Deligne | Prop 8.3 | S_p(j) = E_{p-1} mod p | Very Hard — modular forms over finite fields |
| 19 | Constraint-saturation splitting | Prop 8.4 | Icosahedral structure forces SSP splitting for p ≤ 29 | Very Hard — combines all previous + modular form dimension count |
| 20 | Discriminant transition at p=37 | Prop 8.5 | dim M_{36} = 4, splitting fails | Hard — explicit computation |

---

## 3. Mathlib Coverage Assessment

### Available in Mathlib (can be used directly)

| Concept | Mathlib Import | Notes |
|---------|---------------|-------|
| Power series | `Mathlib.RingTheory.PowerSeries.Basic` | For Molien series as formal object |
| Representation theory | `Mathlib.RepresentationTheory.*` | Characters, invariants, Maschke |
| A₅ simplicity | `Mathlib.GroupTheory.SpecificGroups.Alternating` | `alternatingGroup.isSimpleGroup_five` |
| Coxeter groups | `Mathlib.GroupTheory.Coxeter.*` | Basic theory, matrices, length |
| Modular forms | `Mathlib.NumberTheory.ModularForms.*` | M_k(SL_2(Z)), level 1, q-expansions |
| Eisenstein series | `Mathlib.NumberTheory.ModularForms.EisensteinSeries.*` | E_k definitions |
| j-invariant | `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` | `WeierstrassCurve.j` |
| Elliptic curves | `Mathlib.AlgebraicGeometry.EllipticCurve.*` | Comprehensive |
| Quadratic residues | `Mathlib.NumberTheory.LegendreSymbol.*` | Legendre symbol, reciprocity |
| Dedekind eta | `Mathlib.NumberTheory.ModularForms.DedekindEta` | η function |

### NOT available in Mathlib (must be built or axiomatized)

| Concept | Severity | Strategy |
|---------|----------|----------|
| Molien series | High | Define as rational generating function; prove properties for specific groups via concrete computation |
| Numerical semigroups | Medium | Define ⟨a,b⟩ and Frobenius number F(a,b) = ab−a−b; prove gap counts via Sylvester's formula |
| Chevalley-Shephard-Todd | Medium | State as definition for specific groups (encode Chevalley degrees as data) |
| Binary icosahedral group 2I | High | Define SL(2, ZMod 5) using Mathlib's SpecialLinearGroup; prove order = 120 |
| Klein invariants (f, H, T) | Very High | State degrees (12,20,30) and relation f⁵+T²+cH³=0 as axioms/definitions |
| Supersingular classification | High | Define via Hasse invariant; verify for small primes computationally |
| Triangle group bridge | Very High | Classical result (Klein 1884); axiomatize the orbifold isomorphism |
| SO(3) classification | Medium | Already built in first project as `FiniteRotationGroup3D` |

---

## 4. Recommended Formalization Strategy

### Approach: Hybrid definitional + computational

Like the first project, encode **classical mathematical inputs as definitions** (group orders, Chevalley degrees, forbidden sets computed from the Molien formula) and then **formally verify the algebraic and logical consequences** (counting theorems, nesting, uniqueness, ceiling formulas).

The deeper results (Klein bridge, constraint-saturation) can be formalized at the **statement level** — state them as theorems with their hypotheses clearly laid out — while the proofs that connect concrete computations (like the quadratic residue check at p=29) can be verified with `decide` or `native_decide`.

### What to encode as definitions (classical inputs):
- Chevalley degrees for each Coxeter type
- Group orders
- Molien series formula (Lemma 2.1)
- Klein invariant degrees (12, 20, 30)
- Modular form dimension formula
- Supersingular prime list

### What Lean should verify:
- All arithmetic identities (|G|/4, ceiling formula, forbidden set counts)
- Forbidden set nesting via concrete enumeration
- Saturation computation for each Coxeter type
- Uniqueness of saturation-1 (algebraic: (d₁−4)(d₂−4)=12)
- A₅ simplicity (from Mathlib)
- Quadratic residue checks for splitting at p ≤ 29
- dim M_{p-1} computation for each prime

---

## 5. Reusable Components from First Project

### Directly reusable:
| Component | File | What it provides |
|-----------|------|-----------------|
| `FiniteRotationGroup3D` inductive type | `FiniteGroups.lean` | Klein's classification, group orders |
| `icosahedral_maximal_polyhedral` | `FiniteGroups.lean` | I is maximal among polyhedral groups |
| `tetrahedral_index_in_icosahedral` | `FiniteGroups.lean` | |I|/|T| = 5 |
| `octahedral_not_divides_icosahedral` | `FiniteGroups.lean` | 24 ∤ 60 |
| `IcosahedralConjugacyData` | `FiniteGroups.lean` | Element counts by type |
| `φ`, `ψ` definitions and properties | `GoldenRatio.lean` | Golden ratio algebra |
| `belt_identity` (φ⁸ + φ⁻⁸ = 47) | `GoldenRatio.lean` | Lucas number L₈ = 47 |
| `φ_sq`, `φ_pow4`, `φ_pow8` | `GoldenRatio.lean` | Power identities |

### Needs adaptation:
| Component | Why | How |
|-----------|-----|-----|
| Group action framework | First project used face actions; new paper needs harmonic actions | Refactor to use Molien coefficient framework |
| Polyhedra definitions | First project defined vertex/edge/face counts; new paper needs Chevalley degrees | Extend or define separately |

### New infrastructure needed:
- Molien series type and coefficient extraction
- Numerical semigroup type with Frobenius number
- Coxeter type classification with Chevalley degrees
- Modular form dimension formula
- Supersingular polynomial machinery

---

## 6. Proposed Module Structure

```
ForbiddenHarmonics/
├── Basic.lean              -- Imports, golden ratio reuse, basic definitions
├── ChevalleyDegrees.lean   -- Coxeter types, Chevalley degrees, group data
├── MolienSeries.lean       -- Harmonic Molien series, forbidden degree definition
├── NumericalSemigroup.lean -- ⟨a,b⟩ semigroup, Frobenius number, gap counting
├── ForbiddenSets.lean      -- Computed forbidden sets for T, O, I, B_n
├── CountingTheorem.lean    -- |G|/4 theorem, nesting, parity wall
├── Uniqueness.lean         -- Saturation definition, (d₁−4)(d₂−4)=12, global uniqueness
├── Decomposition.lean      -- 7+4+4 decomposition, ceiling formula
├── Simplicity.lean         -- A₅ simplicity forces concentration (uses Mathlib)
├── KleinBridge.lean        -- Klein invariants, degrees (12,20,30), j-function connection
├── ModularForms.lean       -- dim M_k formula, constraint counting
├── Splitting.lean          -- Quadratic residue checks, forced splitting for p ≤ 29
├── Synthesis.lean          -- Main theorem: complete chain from Chevalley to SSP
└── ForbiddenHarmonics.lean -- Root import file
```

### Estimated size: ~2,500–3,500 lines across 13 modules

---

## 7. Risk Assessment

### Low Risk (will definitely work):
- All concrete arithmetic (forbidden sets, counting, ceiling formula, nesting)
- Saturation computation for each group
- Uniqueness via (d₁−4)(d₂−4)=12
- A₅ simplicity (Mathlib provides this)
- Lucas numbers, golden ratio properties (reuse from first project)

### Medium Risk (may need creative approaches):
- Numerical semigroup gap counting (define from scratch, prove Sylvester formula)
- B_n forbidden set theorem (needs induction on n)
- Exhausting Coxeter classification for global uniqueness
- dim M_k formula verification

### High Risk (may need axiomatization):
- Klein invariant bridge (deep classical result)
- Triangle group bridge (orbifold theory not in Mathlib)
- Constraint-saturation mechanism (combines everything)
- Supersingular polynomial splitting (needs modular forms over F_p)

### Recommended pragmatic approach:
Formalize Tier 1 and Tier 2 results fully. For Tier 3, state the theorems precisely with all hypotheses, prove the **computational** parts (dimension counts, quadratic residue checks), and axiomatize the **structural** parts (Klein's classical result, the orbifold isomorphism). This is honest: the axiomatized classical results are cited theorems from Klein (1884), Deligne (1975), etc. The paper's own contribution — using those to derive forced splitting — can be verified computationally.
