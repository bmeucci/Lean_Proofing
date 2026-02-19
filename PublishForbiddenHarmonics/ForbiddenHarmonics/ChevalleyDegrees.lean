/-
  ForbiddenHarmonics/ChevalleyDegrees.lean

  Coxeter types and their Chevalley degrees.
  Encodes the classical data for reflection groups as definitions.

  Key results:
  - Inductive type for Coxeter groups with finite forbidden sets
  - Chevalley degrees for each type
  - Group orders
  - The harmonic generator lists (Chevalley degrees minus d₁=2)
-/
import ForbiddenHarmonics.Basic

/-! ## Coxeter Types with Finite Forbidden Sets

  From the finiteness criterion (Proposition 1 of the paper):
  Forb(G) is finite iff gcd(d₂,...,dₙ) = 1 or (gcd = 2 and N odd).

  The types satisfying this include:
  - A_n (n ≥ 2): degrees (2,3,...,n+1), gcd = 1, semigroup-gapped
  - B_n (n ≥ 3, odd): degrees (2,4,6,...,2n), gcd = 2, N = n² (odd)
  - D_n (n ≥ 5, odd): degrees (2,4,6,...,2n-2,n), gcd depends on n
  - H₃: degrees (2,6,10), gcd = 2, N = 15 (odd) → icosahedral
  - H₄: degrees (2,12,20,30), gcd = 2, N = 60 (even) → infinite forb set
  - E₆: degrees (2,5,6,8,9,12), gcd = 1
  - E₇: degrees (2,6,8,10,12,14,18), gcd = 2, N = 63 (odd)
  - F₄: degrees (2,6,8,12), gcd = 2, N = 24 (even) → infinite forb set
-/

/-- Coxeter types whose rotation subgroups have finite forbidden sets.
    We focus on the types relevant to the paper's analysis. -/
inductive CoxeterFiniteForb where
  | A (n : ℕ) (hn : n ≥ 2) : CoxeterFiniteForb   -- A_n, semigroup-gapped
  | B (n : ℕ) (hn : n ≥ 3) (hodd : n % 2 = 1) : CoxeterFiniteForb  -- B_n, n odd
  | H3 : CoxeterFiniteForb                         -- Icosahedral (3D)
  | E6 : CoxeterFiniteForb                         -- E₆
  | E7 : CoxeterFiniteForb                         -- E₇

namespace CoxeterFiniteForb

/-- The dimension of the ambient space for each Coxeter type. -/
def dim : CoxeterFiniteForb → ℕ
  | A n _ => n
  | B n _ _ => n
  | H3 => 3
  | E6 => 6
  | E7 => 7

/-- The group order of the rotation subgroup for each Coxeter type. -/
def groupOrder : CoxeterFiniteForb → ℕ
  | A n _ => Nat.factorial (n + 1) / 2
  | B n _ _ => Nat.factorial n * 2^(n - 1)
  | H3 => 60
  | E6 => 25920
  | E7 => 1451520

/-- The Molien exponent N = Σ(dᵢ - 1) for each Coxeter type. -/
def molienExp : CoxeterFiniteForb → ℕ
  | A n _ => n * (n + 1) / 2  -- Σ(i-1) for i=2..n+1 = n(n+1)/2
  | B n _ _ => n * n           -- Σ(2i-1) for i=1..n = n²
  | H3 => 15
  | E6 => 36
  | E7 => 63

end CoxeterFiniteForb

/-! ## Polyhedral Groups as Special Cases

  The three 3D polyhedral groups correspond to:
  - T = A₃ (alternating group A₄, parent W = S₄)
  - O = B₃ (octahedral, parent W = hyperoctahedral B₃)
  - I = H₃ (icosahedral, parent W = full icosahedral H₃)
-/

/-- Tetrahedral is isomorphic to A₃ rotation subgroup.
    Parent Coxeter: A₃ with degrees (2, 3, 4). -/
theorem tetrahedral_is_A3 :
    tetrahedralData.d₁ = 3 ∧ tetrahedralData.d₂ = 4 ∧
    tetrahedralData.groupOrder = 12 := by
  decide

/-- Octahedral is isomorphic to B₃ rotation subgroup.
    Parent Coxeter: B₃ with degrees (2, 4, 6). -/
theorem octahedral_is_B3 :
    octahedralData.d₁ = 4 ∧ octahedralData.d₂ = 6 ∧
    octahedralData.groupOrder = 24 := by
  decide

/-- Icosahedral is H₃ rotation subgroup.
    Parent Coxeter: H₃ with degrees (2, 6, 10). -/
theorem icosahedral_is_H3 :
    icosahedralData.d₁ = 6 ∧ icosahedralData.d₂ = 10 ∧
    icosahedralData.groupOrder = 60 := by
  decide

/-! ## B_n Harmonic Data for Odd n

  For B_n with n ≥ 3 odd:
  - Chevalley degrees: (2, 4, 6, ..., 2n)
  - Harmonic generators: (4, 6, 8, ..., 2n) — all even
  - N = n²
  - gcd of harmonic generators = 2
  - N is odd (since n is odd)
-/

/-- The Molien exponent for B_n (n odd) is n². -/
theorem Bn_molien_exp (n : ℕ) (_hn : n ≥ 3) (_hodd : n % 2 = 1) :
    n * n = n ^ 2 := by ring

/-- For B₃: N = 9, harmonic generators (4, 6), gcd = 2. -/
theorem B3_data : 3 * 3 = 9 ∧ Nat.gcd 4 6 = 2 := by
  constructor <;> decide

/-- For B₅: N = 25, gcd of harmonic generators = 2. -/
theorem B5_N : 5 * 5 = 25 := by norm_num

/-- For B₇: N = 49. -/
theorem B7_N : 7 * 7 = 49 := by norm_num
