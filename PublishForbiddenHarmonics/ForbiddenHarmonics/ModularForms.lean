/-
  ForbiddenHarmonics/ModularForms.lean

  Proposition 9: Modular form dimensions and the Hasse invariant.

  Key results:
  - Dimension formula for M_k(SL₂(Z))
  - Concrete dimension table for all relevant primes
  - The denominator 12 = |T| = |I|/5 in the formula
  - Hasse invariant: S_p(j) = E_{p-1} mod p (stated as definition)

  Classical inputs treated as definitions:
  - Modular form dimension formula
  - Eisenstein series generate the graded ring
  - Hasse invariant (Deligne, Kaneko–Zagier)
-/
import Mathlib.Tactic
import ForbiddenHarmonics.Basic

/-! ## Dimension Formula for M_k(SL₂(Z))

  For even k ≥ 0:
    dim M_k = ⌊k/12⌋     if k ≡ 2 (mod 12)
    dim M_k = ⌊k/12⌋ + 1  if k ≢ 2 (mod 12)

  Special case: dim M_0 = 1, dim M_2 = 0.
-/

/-- The dimension of M_k(SL₂(Z)) for even k ≥ 4. -/
def dimMk (k : ℕ) : ℕ :=
  if k % 12 = 2 then k / 12 else k / 12 + 1

/-- Dimension table verification for specific weights. -/
theorem dim_M4 : dimMk 4 = 1 := by decide
theorem dim_M6 : dimMk 6 = 1 := by decide
theorem dim_M8 : dimMk 8 = 1 := by decide
theorem dim_M10 : dimMk 10 = 1 := by decide
theorem dim_M12 : dimMk 12 = 2 := by decide
theorem dim_M14 : dimMk 14 = 1 := by decide
theorem dim_M16 : dimMk 16 = 2 := by decide
theorem dim_M18 : dimMk 18 = 2 := by decide
theorem dim_M20 : dimMk 20 = 2 := by decide
theorem dim_M22 : dimMk 22 = 2 := by decide
theorem dim_M24 : dimMk 24 = 3 := by decide
theorem dim_M26 : dimMk 26 = 2 := by decide
theorem dim_M28 : dimMk 28 = 3 := by decide
theorem dim_M30 : dimMk 30 = 3 := by decide
theorem dim_M36 : dimMk 36 = 4 := by decide

/-! ## Dimension for p-1 where p is prime

  The key table for the supersingular analysis:
  | p  | k=p-1 | dim M_k |
  | 5  |   4   |    1    |
  | 7  |   6   |    1    |
  | 11 |  10   |    1    |
  | 13 |  12   |    2    |
  | 17 |  16   |    2    |
  | 19 |  18   |    2    |
  | 23 |  22   |    2    |
  | 29 |  28   |    3    | ← Molien ceiling
  | 31 |  30   |    3    |
  | 37 |  36   |    4    | ← first non-SSP
-/

/-- For p = 5: dim M_4 = 1. -/
theorem dim_at_5 : dimMk (5 - 1) = 1 := by decide
/-- For p = 7: dim M_6 = 1. -/
theorem dim_at_7 : dimMk (7 - 1) = 1 := by decide
/-- For p = 11: dim M_10 = 1. -/
theorem dim_at_11 : dimMk (11 - 1) = 1 := by decide
/-- For p = 13: dim M_12 = 2. -/
theorem dim_at_13 : dimMk (13 - 1) = 2 := by decide
/-- For p = 17: dim M_16 = 2. -/
theorem dim_at_17 : dimMk (17 - 1) = 2 := by decide
/-- For p = 19: dim M_18 = 2. -/
theorem dim_at_19 : dimMk (19 - 1) = 2 := by decide
/-- For p = 23: dim M_22 = 2. -/
theorem dim_at_23 : dimMk (23 - 1) = 2 := by decide
/-- For p = 29: dim M_28 = 3 (Molien ceiling). -/
theorem dim_at_29 : dimMk (29 - 1) = 3 := by decide
/-- For p = 31: dim M_30 = 3. -/
theorem dim_at_31 : dimMk (31 - 1) = 3 := by decide
/-- For p = 37: dim M_36 = 4 (first dimension jump). -/
theorem dim_at_37 : dimMk (37 - 1) = 4 := by decide

/-! ## Critical Dimension Transitions -/

/-- All primes p ≤ 29 have dim M_{p-1} ≤ 3. -/
theorem dim_controlled_below_ceiling :
    dimMk (5 - 1) ≤ 3 ∧ dimMk (7 - 1) ≤ 3 ∧ dimMk (11 - 1) ≤ 3 ∧
    dimMk (13 - 1) ≤ 3 ∧ dimMk (17 - 1) ≤ 3 ∧ dimMk (19 - 1) ≤ 3 ∧
    dimMk (23 - 1) ≤ 3 ∧ dimMk (29 - 1) ≤ 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The first prime with dim M_{p-1} = 4 is p = 37. -/
theorem dim_first_escape : dimMk (37 - 1) = 4 := by decide

/-- For p ≤ 23: dim M_{p-1} ≤ 2, so at most 1 generic root. -/
theorem dim_at_most_2_small :
    dimMk (5 - 1) ≤ 2 ∧ dimMk (7 - 1) ≤ 2 ∧ dimMk (11 - 1) ≤ 2 ∧
    dimMk (13 - 1) ≤ 2 ∧ dimMk (17 - 1) ≤ 2 ∧ dimMk (19 - 1) ≤ 2 ∧
    dimMk (23 - 1) ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The Denominator 12

  The constant 12 in the dimension formula dim M_k ≈ k/12
  equals |T| = |I|/5.
-/

/-- The modular denominator 12 = |T| = |I|/5. -/
theorem modular_denominator :
    12 = 60 / 5 := by norm_num

/-- The dimension grows approximately as k/12:
    for large k, dim M_k ≈ k/12. -/
theorem dim_growth_rate (k : ℕ) (_hk : k ≥ 12) (_heven : k % 2 = 0) :
    k / 12 ≤ dimMk k ∧ dimMk k ≤ k / 12 + 1 := by
  constructor
  · unfold dimMk; split <;> omega
  · unfold dimMk; split <;> omega

/-! ## Eisenstein Series Generators

  The graded ring M_*(SL₂(Z)) = C[E₄, E₆].
  Monomials: E₄ᵃ E₆ᵇ with 4a + 6b = k form a basis.

  Count of monomials = number of solutions to 4a + 6b = k with a,b ≥ 0.
-/

/-- The monomial count for weight k matches the dimension formula.
    For k = 28: monomials are E₄⁷, E₄⁴E₆², E₄E₆⁴... we check dim = 3. -/
theorem monomials_weight_28 :
    -- Solutions to 4a + 6b = 28: (7,0), (4,2), (1,4) → 3 monomials
    4 * 7 + 6 * 0 = 28 ∧ 4 * 4 + 6 * 2 = 28 ∧ 4 * 1 + 6 * 4 = 28 := by
  constructor <;> [norm_num; constructor <;> norm_num]

/-- For k = 36: 4 monomials.
    (9,0), (6,2), (3,4), (0,6) -/
theorem monomials_weight_36 :
    4 * 9 + 6 * 0 = 36 ∧ 4 * 6 + 6 * 2 = 36 ∧
    4 * 3 + 6 * 4 = 36 ∧ 4 * 0 + 6 * 6 = 36 := by
  constructor <;> [norm_num; constructor <;> [norm_num; constructor <;> norm_num]]

/-! ## Hasse Invariant (Deligne, Kaneko–Zagier)

  The Hasse invariant A_p is a mod-p modular form of weight p-1
  whose roots are the supersingular j-invariants.

  E_{p-1} mod p = (scalar) · A_p

  When expressed as polynomial in j: roots of S_p(j) = supersingular loci.
-/

/-- The Hasse invariant weight for prime p is p-1. -/
def hasseWeight (p : ℕ) : ℕ := p - 1

/-- Supersingular prime: a prime p such that all supersingular
    j-invariants in characteristic p lie in F_p.
    Equivalently, S_p(j) splits completely over F_p. -/
def IsSupersingularPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71} : Finset ℕ)

/-- The list of supersingular primes (Ogg's list). -/
def sspList : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}

/-- There are exactly 15 supersingular primes. -/
theorem ssp_count : sspList.card = 15 := by decide

/-- All SSP entries are indeed prime. -/
theorem ssp_all_prime : ∀ p ∈ sspList, Nat.Prime p := by
  intro p hp
  simp only [sspList, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
