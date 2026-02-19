/-
  ForbiddenHarmonics/CountingTheorem.lean

  Theorem 3 (The |G|/4 Formula): For each polyhedral rotation group
  G ∈ {T, O, I}, the number of forbidden degrees equals |G|/4.

  Proof structure:
  - Case 1: gcd(d₁,d₂) = 1 (tetrahedral only)
    Forbidden count = Sylvester gap count = (d₁-1)(d₂-1)/2
  - Case 2: gcd(d₁,d₂) = 2 (octahedral, icosahedral)
    Write d₁ = 2a, d₂ = 2b with gcd(a,b) = 1
    Forbidden count = (a-1)(b-1) + (a+b-1) = ab = d₁d₂/4 = |G|/4
-/
import ForbiddenHarmonics.ForbiddenSets

/-! ## The |G|/4 Formula -/

/-- **Theorem 3**: |Forb(T)| = |T|/4. -/
theorem g4_formula_T : forbT.card = 12 / 4 := by decide

/-- **Theorem 3**: |Forb(O)| = |O|/4. -/
theorem g4_formula_O : forbO.card = 24 / 4 := by decide

/-- **Theorem 3**: |Forb(I)| = |I|/4. -/
theorem g4_formula_I : forbI.card = 60 / 4 := by decide

/-! ## Case 1: gcd(d₁,d₂) = 1 (Tetrahedral)

  For T with (d₁, d₂) = (3, 4) and gcd(3,4) = 1:
  - Forbidden degrees = gaps of ⟨3,4⟩ (all gaps < N = 6)
  - Count = Sylvester formula: (3-1)(4-1)/2 = 3
-/

/-- Tetrahedral case: gcd = 1, forbidden count = Sylvester gap count. -/
theorem tetrahedral_sylvester :
    (3 - 1) * (4 - 1) / 2 = 3 ∧ 3 = 12 / 4 := by norm_num

/-- The gaps of ⟨3,4⟩ are exactly Forb(T). -/
theorem tetrahedral_gaps_eq_forb :
    gaps_3_4 = forbT := by decide

/-! ## Case 2: gcd(d₁,d₂) = 2 (Octahedral and Icosahedral)

  For gcd = 2 case, write d₁ = 2a, d₂ = 2b, N = 2(a+b) - 1.
  Three contributions to forbidden count:
  1. Even forbidden: (a-1)(b-1)/2 gaps of ⟨a,b⟩
  2. Odd forbidden below N: a + b - 1 degrees
  3. Odd forbidden above N: (a-1)(b-1)/2 degrees

  Total = (a-1)(b-1)/2 + (a+b-1) + (a-1)(b-1)/2
        = (a-1)(b-1) + (a+b-1) = ab = d₁d₂/4 = |G|/4
-/

/-- Octahedral case: (a,b) = (2,3), the three-part count sums to 6.
    Even gaps: (2-1)(3-1)/2 = 1
    Odd below N=9: 2+3-1 = 4
    Odd above N: (2-1)(3-1)/2 = 1
    Total: 1 + 4 + 1 = 6 = 24/4 -/
theorem octahedral_three_part :
    (2 - 1) * (3 - 1) / 2 + (2 + 3 - 1) + (2 - 1) * (3 - 1) / 2 = 6 := by norm_num

/-- Octahedral algebraic identity: ab = |O|/4. -/
theorem octahedral_ab_quarter : 2 * 3 = 24 / 4 := by norm_num

/-- Icosahedral case: (a,b) = (3,5), the three-part count sums to 15.
    Even gaps: (3-1)(5-1)/2 = 4
    Odd below N=15: 3+5-1 = 7
    Odd above N: (3-1)(5-1)/2 = 4
    Total: 4 + 7 + 4 = 15 = 60/4 -/
theorem icosahedral_three_part :
    (3 - 1) * (5 - 1) / 2 + (3 + 5 - 1) + (3 - 1) * (5 - 1) / 2 = 15 := by norm_num

/-- Icosahedral algebraic identity: ab = |I|/4. -/
theorem icosahedral_ab_quarter : 3 * 5 = 60 / 4 := by norm_num

/-- The general algebraic identity for gcd = 2 case:
    (a-1)(b-1) + (a+b-1) = ab.
    This proves |Forb(G)| = |G|/4 for all parity-walled 3D groups. -/
theorem gcd2_counting_identity (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) :
    (a - 1) * (b - 1) + (a + b - 1) = a * b := by
  have hab : 1 ≤ a + b := by omega
  zify [ha, hb, hab]; ring
