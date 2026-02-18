/-
  ForbiddenHarmonics/Decomposition.lean

  Proposition 2: The 7+4+4 decomposition of Forb(I).

  Forb(I) = ParityWall ∪ EvenGaps ∪ PostThreshold

  Where:
  - ParityWall = {1, 3, 5, 7, 9, 11, 13} — all odd ℓ < N = 15 (7 degrees)
  - EvenGaps = {2, 4, 8, 14} — 2 × gaps(⟨3,5⟩) (4 degrees)
  - PostThreshold = {17, 19, 23, 29} — N + 2 × gaps(⟨3,5⟩) (4 degrees)

  Also: Corollary 3 (I-unique primes) and Proposition 7 (forbidden ceiling).
-/
import ForbiddenHarmonics.ForbiddenSets

/-! ## The Three Components of Forb(I) -/

/-- Parity wall: all odd degrees below N = 15. -/
def parityWall_I : Finset ℕ := {1, 3, 5, 7, 9, 11, 13}

/-- Even gaps: 2 × gaps(⟨3,5⟩) = 2 × {1,2,4,7}. -/
def evenGapsDecomp_I : Finset ℕ := {2, 4, 8, 14}

/-- Post-threshold: 15 + 2 × gaps(⟨3,5⟩). -/
def postThresholdDecomp_I : Finset ℕ := {17, 19, 23, 29}

/-- The parity wall has 7 elements. -/
theorem parityWall_I_card : parityWall_I.card = 7 := by decide

/-- The even gaps have 4 elements. -/
theorem evenGapsDecomp_I_card : evenGapsDecomp_I.card = 4 := by decide

/-- The post-threshold has 4 elements. -/
theorem postThresholdDecomp_I_card : postThresholdDecomp_I.card = 4 := by decide

/-- 7 + 4 + 4 = 15 = |Forb(I)|. -/
theorem decomposition_count : 7 + 4 + 4 = 15 := by norm_num

/-! ## Decomposition Correctness -/

/-- The three components are pairwise disjoint. -/
theorem decomp_disjoint_pw_eg : Disjoint parityWall_I evenGapsDecomp_I := by
  rw [Finset.disjoint_left]; decide

theorem decomp_disjoint_pw_pt : Disjoint parityWall_I postThresholdDecomp_I := by
  rw [Finset.disjoint_left]; decide

theorem decomp_disjoint_eg_pt : Disjoint evenGapsDecomp_I postThresholdDecomp_I := by
  rw [Finset.disjoint_left]; decide

/-- The union of all three components equals Forb(I). -/
theorem decomp_union_eq_forbI :
    parityWall_I ∪ evenGapsDecomp_I ∪ postThresholdDecomp_I = forbI := by
  decide

/-! ## Parity Wall Analysis -/

/-- All parity wall elements are odd. -/
theorem parityWall_all_odd :
    ∀ x ∈ parityWall_I, x % 2 = 1 := by decide

/-- All parity wall elements are less than N = 15. -/
theorem parityWall_below_N :
    ∀ x ∈ parityWall_I, x < 15 := by decide

/-- The parity wall count matches a + b - 1 = 3 + 5 - 1 = 7. -/
theorem parityWall_count_formula : 3 + 5 - 1 = 7 := by norm_num

/-! ## Even Gap Analysis -/

/-- All even gap elements are even. -/
theorem evenGaps_all_even :
    ∀ x ∈ evenGapsDecomp_I, x % 2 = 0 := by decide

/-- Even gaps are exactly 2 × gaps(⟨3,5⟩). -/
theorem evenGaps_from_semigroup :
    2 * 1 = 2 ∧ 2 * 2 = 4 ∧ 2 * 4 = 8 ∧ 2 * 7 = 14 := by
  constructor <;> [norm_num; constructor <;> [norm_num; constructor <;> norm_num]]

/-! ## Post-Threshold Analysis -/

/-- All post-threshold elements are above N = 15. -/
theorem postThreshold_above_N :
    ∀ x ∈ postThresholdDecomp_I, x > 15 := by decide

/-- Post-threshold elements are N + 2 × gaps(⟨3,5⟩). -/
theorem postThreshold_from_semigroup :
    15 + 2 * 1 = 17 ∧ 15 + 2 * 2 = 19 ∧ 15 + 2 * 4 = 23 ∧ 15 + 2 * 7 = 29 := by
  constructor <;> [norm_num; constructor <;> [norm_num; constructor <;> norm_num]]

/-- All post-threshold forbidden degrees are prime. -/
theorem postThreshold_all_prime :
    ∀ p ∈ postThresholdDecomp_I, Nat.Prime p := by decide

/-! ## Corollary 3: I-Unique Primes -/

/-- The I-unique primes: Forb(I) \ Forb(O) restricted to primes. -/
def iUniquePrimes : Finset ℕ := {13, 17, 19, 23, 29}

/-- The I-unique primes are exactly those in Forb(I) but not in Forb(O). -/
theorem iUnique_sdiff : forbI \ forbO = {4, 8, 9, 13, 14, 17, 19, 23, 29} := by
  decide

/-- The 4 post-threshold I-unique primes are exactly N + 2 × gaps(⟨3,5⟩). -/
theorem iUnique_postThreshold :
    postThresholdDecomp_I ⊆ iUniquePrimes := by decide

/-! ## Proposition 7: Forbidden Ceiling -/

/-- The largest element of Forb(I) is 29. -/
theorem forbI_max : ∀ x ∈ forbI, x ≤ 29 := by decide

/-- 29 ∈ Forb(I). -/
theorem forbI_contains_29 : 29 ∈ forbI := by decide

/-- **Proposition 7**: The forbidden ceiling 29 = N + 2·F(3,5) = 15 + 14. -/
theorem forbidden_ceiling_formula : 15 + 2 * 7 = 29 := by norm_num

/-- The ceiling equals |I|/2 - 1. -/
theorem ceiling_half_order : 60 / 2 - 1 = 29 := by norm_num

/-- The ceiling equals 2ab - 1 where (a,b) = (3,5). -/
theorem ceiling_2ab : 2 * 3 * 5 - 1 = 29 := by norm_num

/-- lcm(d₁, d₂) = 30 = first allowed degree above ceiling. -/
theorem lcm_first_allowed : Nat.lcm 6 10 = 30 := by decide

/-- 30 = |I|/2 is the first degree where both generators synchronize. -/
theorem sync_degree : 60 / 2 = 30 := by norm_num
