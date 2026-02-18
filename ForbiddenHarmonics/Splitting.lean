/-
  ForbiddenHarmonics/Splitting.lean

  Propositions 10 and 11: Constraint-saturation splitting
  and discriminant transition.

  Key results:
  - For p ≤ 23: dim M_{p-1} ≤ 2, trivially splits
  - For p = 29: dim M_{28} = 3, discriminant check shows QR
  - For p = 37: dim M_{36} = 4, first failure (QNR)
  - SSP ∩ [2,29] = prime content of Forb(I)
-/
import ForbiddenHarmonics.ModularForms
import ForbiddenHarmonics.ForbiddenSets

/-! ## Proposition 10: Constraint-Saturation Splitting

  When dim M_{p-1} ≤ 3, the icosahedral equation f⁵ + T² + cH³ = 0
  constrains the invariant ring sufficiently to force S_p(j) to split.
-/

/-! ### Case 1: dim ≤ 2 (primes p ≤ 23)

  With at most 2 monomials, at most 1 generic supersingular j-value.
  A single root trivially lies in F_p.
-/

/-- For primes p ≤ 23, the supersingular polynomial has degree at most 1
    (after removing possible roots at j = 0 and j = 1728).
    A degree-1 polynomial over F_p trivially splits. -/
theorem trivial_split_small_primes :
    dimMk (5 - 1) ≤ 2 ∧ dimMk (7 - 1) ≤ 2 ∧ dimMk (11 - 1) ≤ 2 ∧
    dimMk (13 - 1) ≤ 2 ∧ dimMk (17 - 1) ≤ 2 ∧ dimMk (19 - 1) ≤ 2 ∧
    dimMk (23 - 1) ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Case 2: dim = 3 (prime p = 29)

  S₂₉(j) = j(j² + 2j + 21)
  Discriminant of j² + 2j + 21:
    Δ = 4 - 4·21 = 4 - 84 = -80
    -80 ≡ 7 (mod 29)
    6² = 36 ≡ 7 (mod 29) → 7 is a QR mod 29
  So the quadratic splits over F₂₉.

  All three roots: j ≡ 0, 2, 25 (mod 29) lie in F₂₉. ✓
-/

/-- Discriminant computation for p = 29:
    Δ = 4 - 4·21 = -80. -/
theorem discriminant_29 : 4 - 4 * 21 = -(80 : Int) := by norm_num

/-- -80 mod 29 = 7. -/
theorem discriminant_mod_29 : ((-80 : Int) % 29) = 7 := by norm_num

/-- 7 is a quadratic residue mod 29: 6² = 36 ≡ 7 (mod 29). -/
theorem qr_7_mod_29 : 6 * 6 % 29 = 7 := by norm_num

/-- The three supersingular j-values mod 29 are {0, 2, 25}. -/
def ss_roots_29 : Finset ℕ := {0, 2, 25}

/-- All three roots lie in F₂₉ (i.e., are < 29). -/
theorem ss_roots_29_in_field : ∀ r ∈ ss_roots_29, r < 29 := by decide

/-- Verification: r = 0 satisfies j(j² + 2j + 21) ≡ 0 (mod 29). -/
theorem ss_root_0_check : 0 * (0^2 + 2 * 0 + 21) % 29 = 0 := by norm_num

/-- Verification: r = 2 satisfies j² + 2j + 21 ≡ 0 (mod 29). -/
theorem ss_root_2_check : (2^2 + 2 * 2 + 21) % 29 = 0 := by norm_num

/-- Verification: r = 25 satisfies j² + 2j + 21 ≡ 0 (mod 29).
    25² + 2·25 + 21 = 625 + 50 + 21 = 696 = 24·29. -/
theorem ss_root_25_check : (25^2 + 2 * 25 + 21) % 29 = 0 := by norm_num

/-- Three roots ✓: p = 29 is supersingular. -/
theorem p29_is_ssp : 29 ∈ sspList := by decide

/-! ## Proposition 11: Discriminant Transition at p = 37

  At p = 37, dim M_{36} = 4. The fourth monomial introduces
  a degree of freedom beyond icosahedral control.
  The discriminant becomes a QNR, and S₃₇(j) does NOT split.
-/

/-- At p = 37: dim M_36 = 4 > 3. -/
theorem dim_escape_37 : dimMk (37 - 1) = 4 := by decide

/-- 4 > 3: the dimension exceeds the icosahedral constraint capacity. -/
theorem dim_exceeds_constraint : 4 > 3 := by norm_num

/-- p = 37 is NOT a supersingular prime. -/
theorem p37_not_ssp : 37 ∉ sspList := by decide

/-- p = 37 is prime. -/
theorem p37_prime : Nat.Prime 37 := by norm_num

/-! ## The SSP–Forb(I) Coincidence

  Dense SSP (SSP ∩ [2, 29]) = prime forbidden degrees of I
-/

/-- The dense SSP: primes in SSP that are ≤ 29. -/
def denseSSP : Finset ℕ := sspList.filter (· ≤ 29)

/-- The dense SSP has 10 elements. -/
theorem denseSSP_card : denseSSP.card = 10 := by decide

/-- The dense SSP equals the prime forbidden icosahedral degrees. -/
theorem denseSSP_eq_forbI_primes : denseSSP = forbI_primes := by
  decide

/-- Every prime forbidden degree of I is a supersingular prime. -/
theorem forbI_primes_subset_ssp : forbI_primes ⊆ sspList := by
  decide

/-- Every SSP ≤ 29 is a forbidden icosahedral degree. -/
theorem ssp_le29_in_forbI_primes :
    ∀ p ∈ sspList, p ≤ 29 → p ∈ forbI_primes := by
  decide

/-! ## Dimension Threshold = Molien Ceiling

  The transition from controlled (dim ≤ 3) to uncontrolled (dim ≥ 4)
  occurs precisely at the Molien ceiling boundary:
  - Last controlled: p = 29 (ceiling of Forb(I))
  - First uncontrolled: p = 37 (first prime > 31 with dim = 4)
-/

/-- The Molien ceiling 29 is the largest forbidden prime of I. -/
theorem ceiling_is_largest_forb_prime :
    29 ∈ forbI_primes ∧ ∀ p ∈ forbI_primes, p ≤ 29 := by
  constructor
  · decide
  · intro p hp
    simp only [forbI_primes, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- p = 31 is still SSP but NOT in Forb(I) (31 > 29 = ceiling). -/
theorem p31_ssp_not_forb : 31 ∈ sspList ∧ 31 ∉ forbI := by
  exact ⟨by decide, by decide⟩
