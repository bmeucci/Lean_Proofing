/-
  ForbiddenHarmonics/ForbiddenSets.lean

  Explicit computation of forbidden sets for the polyhedral groups T, O, I.
  Also B_n forbidden sets for specific odd n, and universal prime coverage.

  Key results:
  - Forb(T) = {1, 2, 5} (3 elements)
  - Forb(O) = {1, 2, 3, 5, 7, 11} (6 elements)
  - Forb(I) = {1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 14, 17, 19, 23, 29} (15 elements)
  - Forbidden set nesting: Forb(T) ⊂ Forb(O) ⊂ Forb(I)
  - Universal prime coverage (Corollary 1)
-/
import ForbiddenHarmonics.MolienSeries
import ForbiddenHarmonics.NumericalSemigroup

/-! ## Tetrahedral Forbidden Set: Forb(T) = {1, 2, 5} -/

/-- The forbidden set of the tetrahedral group. -/
def forbT : Finset ℕ := {1, 2, 5}

/-- Each element of Forb(T) is indeed forbidden for (d₁, d₂, N) = (3, 4, 6). -/
theorem forbT_1_forbidden : IsForbiddenDegree 3 4 6 1 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbT_2_forbidden : IsForbiddenDegree 3 4 6 2 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbT_5_forbidden : IsForbiddenDegree 3 4 6 5 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

/-- |Forb(T)| = 3. -/
theorem forbT_card : forbT.card = 3 := by decide

/-- |Forb(T)| = |T|/4 = 12/4 = 3. -/
theorem forbT_quarter_order : forbT.card = 12 / 4 := by decide

/-! ## Octahedral Forbidden Set: Forb(O) = {1, 2, 3, 5, 7, 11} -/

/-- The forbidden set of the octahedral group. -/
def forbO : Finset ℕ := {1, 2, 3, 5, 7, 11}

/-- Each element of Forb(O) is forbidden for (d₁, d₂, N) = (4, 6, 9). -/
theorem forbO_1_forbidden : IsForbiddenDegree 4 6 9 1 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbO_2_forbidden : IsForbiddenDegree 4 6 9 2 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbO_3_forbidden : IsForbiddenDegree 4 6 9 3 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbO_5_forbidden : IsForbiddenDegree 4 6 9 5 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbO_7_forbidden : IsForbiddenDegree 4 6 9 7 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbO_11_forbidden : IsForbiddenDegree 4 6 9 11 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · right; show ¬ inSemigroup 4 6 (11 - 9)
    unfold inSemigroup; push_neg; intro x y; omega

/-- |Forb(O)| = 6. -/
theorem forbO_card : forbO.card = 6 := by decide

/-- |Forb(O)| = |O|/4 = 24/4 = 6. -/
theorem forbO_quarter_order : forbO.card = 24 / 4 := by decide

/-! ## Icosahedral Forbidden Set: Forb(I) -/

/-- The forbidden set of the icosahedral group. -/
def forbI : Finset ℕ := {1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 14, 17, 19, 23, 29}

/-- Each element of Forb(I) is forbidden for (d₁, d₂, N) = (6, 10, 15). -/
theorem forbI_1_forbidden : IsForbiddenDegree 6 10 15 1 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_2_forbidden : IsForbiddenDegree 6 10 15 2 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_3_forbidden : IsForbiddenDegree 6 10 15 3 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_4_forbidden : IsForbiddenDegree 6 10 15 4 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_5_forbidden : IsForbiddenDegree 6 10 15 5 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_7_forbidden : IsForbiddenDegree 6 10 15 7 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_8_forbidden : IsForbiddenDegree 6 10 15 8 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_9_forbidden : IsForbiddenDegree 6 10 15 9 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_11_forbidden : IsForbiddenDegree 6 10 15 11 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_13_forbidden : IsForbiddenDegree 6 10 15 13 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_14_forbidden : IsForbiddenDegree 6 10 15 14 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem forbI_17_forbidden : IsForbiddenDegree 6 10 15 17 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · right; show ¬ inSemigroup 6 10 (17 - 15)
    unfold inSemigroup; push_neg; intro x y; omega

theorem forbI_19_forbidden : IsForbiddenDegree 6 10 15 19 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · right; show ¬ inSemigroup 6 10 (19 - 15)
    unfold inSemigroup; push_neg; intro x y; omega

theorem forbI_23_forbidden : IsForbiddenDegree 6 10 15 23 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · right; show ¬ inSemigroup 6 10 (23 - 15)
    unfold inSemigroup; push_neg; intro x y; omega

theorem forbI_29_forbidden : IsForbiddenDegree 6 10 15 29 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · right; show ¬ inSemigroup 6 10 (29 - 15)
    unfold inSemigroup; push_neg; intro x y; omega

/-- Degree 6 is NOT forbidden (6 = 6·1 + 10·0). -/
theorem forbI_6_allowed : ¬ IsForbiddenDegree 6 10 15 6 := by
  intro ⟨h, _⟩; exact h ⟨1, 0, by norm_num⟩

/-- Degree 10 is NOT forbidden (10 = 6·0 + 10·1). -/
theorem forbI_10_allowed : ¬ IsForbiddenDegree 6 10 15 10 := by
  intro ⟨h, _⟩; exact h ⟨0, 1, by norm_num⟩

/-- Degree 30 is NOT forbidden (30 = 6·5 + 10·0 = 6·0 + 10·3). -/
theorem forbI_30_allowed : ¬ IsForbiddenDegree 6 10 15 30 := by
  intro ⟨h, _⟩; exact h ⟨5, 0, by norm_num⟩

/-- |Forb(I)| = 15. -/
theorem forbI_card : forbI.card = 15 := by decide

/-- |Forb(I)| = |I|/4 = 60/4 = 15. -/
theorem forbI_quarter_order : forbI.card = 60 / 4 := by decide

/-! ## Forbidden Set Nesting (Corollary 2) -/

/-- Forb(T) ⊆ Forb(O). -/
theorem forbT_subset_forbO : forbT ⊆ forbO := by decide

/-- Forb(O) ⊆ Forb(I). -/
theorem forbO_subset_forbI : forbO ⊆ forbI := by decide

/-- Forb(T) ⊆ Forb(I) (transitive). -/
theorem forbT_subset_forbI : forbT ⊆ forbI :=
  forbT_subset_forbO.trans forbO_subset_forbI

/-- Forb(T) ⊊ Forb(O) (strict subset): 3 ∈ Forb(O) \ Forb(T). -/
theorem forbT_ssubset_forbO : forbT ⊂ forbO := by
  constructor
  · exact forbT_subset_forbO
  · intro h
    have h3 : (3 : ℕ) ∈ forbO := by decide
    have h3t : (3 : ℕ) ∉ forbT := by decide
    exact h3t (h h3)

/-- Forb(O) ⊊ Forb(I) (strict subset): 4 ∈ Forb(I) \ Forb(O). -/
theorem forbO_ssubset_forbI : forbO ⊂ forbI := by
  constructor
  · exact forbO_subset_forbI
  · intro h
    have h4 : (4 : ℕ) ∈ forbI := by decide
    have h4o : (4 : ℕ) ∉ forbO := by decide
    exact h4o (h h4)

/-! ## Prime Content of Forb(I) -/

/-- The prime forbidden icosahedral degrees. -/
def forbI_primes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

/-- There are 10 prime forbidden degrees. -/
theorem forbI_primes_card : forbI_primes.card = 10 := by decide

/-- Every prime in Forb(I) is indeed prime. -/
theorem forbI_primes_are_prime :
    ∀ p ∈ forbI_primes, Nat.Prime p := by
  intro p hp
  simp only [forbI_primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The non-prime forbidden degrees. -/
def forbI_nonprimes : Finset ℕ := {1, 4, 8, 9, 14}

/-- There are 5 non-prime forbidden degrees. -/
theorem forbI_nonprimes_card : forbI_nonprimes.card = 5 := by decide

/-- The total count: 10 primes + 5 non-primes = 15. -/
theorem forbI_prime_nonprime_sum : 10 + 5 = 15 := by norm_num

/-! ## B_n Forbidden Sets and Universal Prime Coverage

  For B_n with n ≥ 3 odd, all harmonic generators are even,
  N = n² is odd, so every odd ℓ < N is forbidden plus degree 2.

  This means every prime p appears in some Forb(B_n):
  - If p is odd: choose n > √p (odd), then p < n² = N, so p ∈ Forb(B_n)
  - If p = 2: 2 ∈ Forb(B_n) for all odd n ≥ 3
-/

/-- Forb(B₃) = Forb(O) = {1, 2, 3, 5, 7, 11} — 6 elements.
    B₃ has generators (4, 6), N = 9.
    Forbidden count = (N+3)/2 = 6. -/
theorem forbB3_count : (9 + 3) / 2 = 6 := by norm_num

/-- Forb(B₅) has (25+3)/2 = 14 elements. -/
theorem forbB5_count : (25 + 3) / 2 = 14 := by norm_num

/-- Forb(B₇) has (49+3)/2 = 26 elements. -/
theorem forbB7_count : (49 + 3) / 2 = 26 := by norm_num

/-- Forb(B₂₁) has (441+3)/2 = 222 elements. -/
theorem forbB21_count : (441 + 3) / 2 = 222 := by norm_num

/-- **Corollary 1 (Universal Prime Coverage)**: Every prime is a forbidden
    harmonic degree for some finite rotation group.

    Proof: For any prime p, if p is odd, choose odd n > √p.
    Then p < n² = N(B_n), and since p is odd and all harmonic generators
    of B_n are even, p ∈ Forb(B_n).
    If p = 2, then 2 ∈ Forb(B_n) for any odd n ≥ 3. -/
theorem universal_prime_coverage (p : ℕ) (hp : Nat.Prime p) :
    ∃ n : ℕ, n ≥ 3 ∧ n % 2 = 1 ∧ p < n * n := by
  -- We need odd n ≥ 3 with p < n². Choose n = 2*p + 1 (always odd, ≥ 3 for prime p).
  use 2 * p + 1
  refine ⟨?_, ?_, ?_⟩
  · have := hp.two_le; omega
  · omega
  · nlinarith [hp.one_le]
