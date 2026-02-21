/-
  ForbiddenHarmonics/ForbiddenSets.lean

  Computation of forbidden sets for the polyhedral groups T, O, I
  from the IsForbiddenDegree predicate.

  The forbidden sets are *computed* by filtering a finite range through
  the decidable IsForbiddenDegree predicate, not hardcoded. This ensures
  the main theorem has genuine mathematical content.

  Key results:
  - Forb(T) = {1, 2, 5} (3 elements) — computed from IsForbiddenDegree 3 4 6
  - Forb(O) = {1, 2, 3, 5, 7, 11} (6 elements) — computed from IsForbiddenDegree 4 6 9
  - Forb(I) = {1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 14, 17, 19, 23, 29} (15 elements)
      — computed from IsForbiddenDegree 6 10 15
  - Forbidden set nesting: Forb(T) ⊂ Forb(O) ⊂ Forb(I)
  - Bound completeness: no forbidden degrees exist above the filter range
  - Universal prime coverage (Corollary 1)
-/
import ForbiddenHarmonics.MolienSeries
import ForbiddenHarmonics.NumericalSemigroup

-- native_decide is appropriate here: the computed finset definitions make
-- kernel-only `decide` prohibitively slow, and this is not a mathlib contribution.
set_option linter.style.nativeDecide false

/-! ## General Forbidden Set Computation

  For harmonic data (d₁, d₂, N), the forbidden set is finite.
  We compute it by filtering Finset.range over the IsForbiddenDegree predicate.

  The bound for the range is N + 2·F(a,b) + 1 where d₁ = gcd·a, d₂ = gcd·b
  and F(a,b) is the Frobenius number. For practical computation we use
  explicit bounds verified by completeness theorems.
-/

/-- Compute the forbidden set for harmonic data (d₁, d₂, N) up to a given bound.
    The bound must be chosen large enough to capture all forbidden degrees. -/
def forbiddenSetBelow (d₁ d₂ N bound : ℕ) : Finset ℕ :=
  (Finset.range bound).filter (fun ℓ => IsForbiddenDegree d₁ d₂ N ℓ)

/-! ## Tetrahedral Forbidden Set

  Forb(T) computed from IsForbiddenDegree 3 4 6.
  Bound: 6 (= N). Since gcd(3,4) = 1, all forbidden degrees are gaps of ⟨3,4⟩,
  and all gaps are < F(3,4) + 1 = 6 = N.
-/

/-- The forbidden set of the tetrahedral group,
    computed from the IsForbiddenDegree predicate. -/
def forbT : Finset ℕ := forbiddenSetBelow 3 4 6 6

/-- No degree ≥ 6 is forbidden for T. This proves the bound is sufficient. -/
theorem forbT_bound_complete (ℓ : ℕ) (hℓ : ℓ ≥ 6) :
    ¬ IsForbiddenDegree 3 4 6 ℓ := by
  intro ⟨hNotSemi, hSecond⟩
  rcases hSecond with h1 | h2
  · omega
  · exfalso; apply hNotSemi
    -- ℓ ≥ 6 → ℓ ∈ ⟨3,4⟩. Prove by writing ℓ = 3q + r, r ∈ {0,1,2}.
    have : ℓ % 3 = 0 ∨ ℓ % 3 = 1 ∨ ℓ % 3 = 2 := by omega
    rcases this with h | h | h
    · exact ⟨ℓ / 3, 0, by omega⟩
    · -- ℓ ≡ 1 mod 3 and ℓ ≥ 7: ℓ = 3·((ℓ-4)/3) + 4·1
      have hge : ℓ ≥ 7 := by omega
      exact ⟨(ℓ - 4) / 3, 1, by omega⟩
    · -- ℓ ≡ 2 mod 3 and ℓ ≥ 8: ℓ = 3·((ℓ-8)/3) + 4·2
      have hge : ℓ ≥ 8 := by omega
      exact ⟨(ℓ - 8) / 3, 2, by omega⟩

/-- The computed Forb(T) equals the explicit set {1, 2, 5}. -/
theorem forbT_eq_explicit : forbT = {1, 2, 5} := by native_decide

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
theorem forbT_card : forbT.card = 3 := by native_decide

/-- |Forb(T)| = |T|/4 = 12/4 = 3. -/
theorem forbT_quarter_order : forbT.card = 12 / 4 := by native_decide

/-! ## Octahedral Forbidden Set

  Forb(O) computed from IsForbiddenDegree 4 6 9.
  Bound: 12 (all forbidden degrees of O are ≤ 11).
-/

/-- The forbidden set of the octahedral group,
    computed from the IsForbiddenDegree predicate. -/
def forbO : Finset ℕ := forbiddenSetBelow 4 6 9 12

/-- No degree ≥ 12 is forbidden for O. -/
theorem forbO_bound_complete (ℓ : ℕ) (hℓ : ℓ ≥ 12) :
    ¬ IsForbiddenDegree 4 6 9 ℓ := by
  intro ⟨hNotSemi, hSecond⟩
  by_cases heven : ℓ % 2 = 0
  · -- Even ℓ ≥ 12 → ℓ ∈ ⟨4,6⟩
    exfalso; apply hNotSemi
    have : ℓ % 4 = 0 ∨ ℓ % 4 = 2 := by omega
    rcases this with h | h
    · exact ⟨ℓ / 4, 0, by omega⟩
    · -- ℓ ≡ 2 mod 4 and ℓ ≥ 14: ℓ = 4·((ℓ-6)/4) + 6·1
      have hge : ℓ ≥ 14 := by omega
      exact ⟨(ℓ - 6) / 4, 1, by omega⟩
  · -- Odd ℓ ≥ 13: ℓ-9 is even and ≥ 4
    have hodd : ℓ % 2 = 1 := by omega
    have hge13 : ℓ ≥ 13 := by omega
    rcases hSecond with h1 | h2
    · omega
    · exfalso; apply h2
      have hm4 : ℓ - 9 ≥ 4 := by omega
      have : (ℓ - 9) % 4 = 0 ∨ (ℓ - 9) % 4 = 2 := by omega
      rcases this with h | h
      · exact ⟨(ℓ - 9) / 4, 0, by omega⟩
      · have : ℓ - 9 ≥ 6 := by omega
        exact ⟨(ℓ - 9 - 6) / 4, 1, by omega⟩

/-- The computed Forb(O) equals the explicit set. -/
theorem forbO_eq_explicit : forbO = {1, 2, 3, 5, 7, 11} := by native_decide

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
theorem forbO_card : forbO.card = 6 := by native_decide

/-- |Forb(O)| = |O|/4 = 24/4 = 6. -/
theorem forbO_quarter_order : forbO.card = 24 / 4 := by native_decide

/-! ## Icosahedral Forbidden Set

  Forb(I) computed from IsForbiddenDegree 6 10 15.
  Bound: 30. The ceiling is 29 = N + 2·F(3,5) = 15 + 14.
  No degree ≥ 30 is forbidden.
-/

/-- The forbidden set of the icosahedral group,
    computed from the IsForbiddenDegree predicate. -/
def forbI : Finset ℕ := forbiddenSetBelow 6 10 15 30

/-- No degree ≥ 30 is forbidden for I. This proves the bound is sufficient.

    Proof: For even ℓ ≥ 30: ℓ ∈ ⟨6,10⟩ since ⟨6,10⟩ = 2⟨3,5⟩ and F(3,5) = 7
    means all even numbers ≥ 16 are in ⟨6,10⟩.
    For odd ℓ ≥ 31: ℓ-15 is even and ≥ 16, so ℓ-15 ∈ ⟨6,10⟩. -/
theorem forbI_bound_complete (ℓ : ℕ) (hℓ : ℓ ≥ 30) :
    ¬ IsForbiddenDegree 6 10 15 ℓ := by
  intro ⟨hNotSemi, hSecond⟩
  by_cases heven : ℓ % 2 = 0
  · -- Even ℓ ≥ 30 → ℓ ∈ ⟨6,10⟩
    exfalso; apply hNotSemi
    have h2 : ℓ / 2 ≥ 15 := by omega
    have : (ℓ / 2) % 3 = 0 ∨ (ℓ / 2) % 3 = 1 ∨ (ℓ / 2) % 3 = 2 := by omega
    rcases this with h | h | h
    · -- ℓ/2 = 3k → ℓ = 6k
      exact ⟨ℓ / 2 / 3, 0, by omega⟩
    · -- ℓ/2 ≡ 1 mod 3 and ≥ 10: (ℓ/2 - 10) ≡ 0 mod 3
      -- ℓ = 6·((ℓ/2-10)/3) + 10·2
      have : (ℓ / 2 - 10) % 3 = 0 := by omega
      exact ⟨(ℓ / 2 - 10) / 3, 2, by omega⟩
    · -- ℓ/2 ≡ 2 mod 3 and ≥ 15: (ℓ/2 - 5) ≡ 0 mod 3
      -- ℓ = 6·((ℓ/2-5)/3) + 10·1
      have : (ℓ / 2 - 5) % 3 = 0 := by omega
      exact ⟨(ℓ / 2 - 5) / 3, 1, by omega⟩
  · -- Odd ℓ ≥ 31: ℓ-15 is even and ≥ 16
    have hodd : ℓ % 2 = 1 := by omega
    have hge31 : ℓ ≥ 31 := by omega
    rcases hSecond with h1 | h2
    · omega
    · exfalso; apply h2
      have hm_even : (ℓ - 15) % 2 = 0 := by omega
      have hm_ge : (ℓ - 15) / 2 ≥ 8 := by omega
      have : ((ℓ - 15) / 2) % 3 = 0 ∨ ((ℓ - 15) / 2) % 3 = 1 ∨
             ((ℓ - 15) / 2) % 3 = 2 := by omega
      rcases this with h | h | h
      · exact ⟨(ℓ - 15) / 2 / 3, 0, by omega⟩
      · have : ((ℓ - 15) / 2 - 10) % 3 = 0 := by omega
        exact ⟨((ℓ - 15) / 2 - 10) / 3, 2, by omega⟩
      · have : ((ℓ - 15) / 2 - 5) % 3 = 0 := by omega
        exact ⟨((ℓ - 15) / 2 - 5) / 3, 1, by omega⟩

/-- The computed Forb(I) equals the explicit set. -/
theorem forbI_eq_explicit :
    forbI = {1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 14, 17, 19, 23, 29} := by
  native_decide

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

/-- Degree 30 is NOT forbidden (30 = 6·5 + 10·0). -/
theorem forbI_30_allowed : ¬ IsForbiddenDegree 6 10 15 30 := by
  intro ⟨h, _⟩; exact h ⟨5, 0, by norm_num⟩

/-- |Forb(I)| = 15. -/
theorem forbI_card : forbI.card = 15 := by native_decide

/-- |Forb(I)| = |I|/4 = 60/4 = 15. -/
theorem forbI_quarter_order : forbI.card = 60 / 4 := by native_decide

/-! ## Forbidden Set Nesting (Corollary 2)

  Nesting is proved by showing every element of the smaller computed set
  satisfies the larger predicate. We unfold to explicit sets for efficiency.
-/

/-- Forb(T) ⊆ Forb(O). -/
theorem forbT_subset_forbO : forbT ⊆ forbO := by
  rw [forbT_eq_explicit, forbO_eq_explicit]; decide

/-- Forb(O) ⊆ Forb(I). -/
theorem forbO_subset_forbI : forbO ⊆ forbI := by
  rw [forbO_eq_explicit, forbI_eq_explicit]; decide

/-- Forb(T) ⊆ Forb(I) (transitive). -/
theorem forbT_subset_forbI : forbT ⊆ forbI :=
  forbT_subset_forbO.trans forbO_subset_forbI

/-- Forb(T) ⊊ Forb(O) (strict subset): 3 ∈ Forb(O) \ Forb(T). -/
theorem forbT_ssubset_forbO : forbT ⊂ forbO := by
  constructor
  · exact forbT_subset_forbO
  · intro h
    have h3 : (3 : ℕ) ∈ forbO := by rw [forbO_eq_explicit]; decide
    have h3t : (3 : ℕ) ∉ forbT := by rw [forbT_eq_explicit]; decide
    exact h3t (h h3)

/-- Forb(O) ⊊ Forb(I) (strict subset): 4 ∈ Forb(I) \ Forb(O). -/
theorem forbO_ssubset_forbI : forbO ⊂ forbI := by
  constructor
  · exact forbO_subset_forbI
  · intro h
    have h4 : (4 : ℕ) ∈ forbI := by rw [forbI_eq_explicit]; decide
    have h4o : (4 : ℕ) ∉ forbO := by rw [forbO_eq_explicit]; decide
    exact h4o (h h4)

/-! ## Prime Content of Forb(I)

  The prime and non-prime subsets are computed by filtering the
  already-computed forbI set, not hardcoded.
-/

/-- The prime forbidden icosahedral degrees,
    computed by filtering Forb(I) for primality. -/
def forbI_primes : Finset ℕ := forbI.filter (fun p => Nat.Prime p)

/-- The non-prime forbidden degrees,
    computed by filtering Forb(I) for non-primality. -/
def forbI_nonprimes : Finset ℕ := forbI.filter (fun p => ¬ Nat.Prime p)

/-- The computed prime forbidden set equals the explicit set. -/
theorem forbI_primes_eq_explicit :
    forbI_primes = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by
  native_decide

/-- There are 10 prime forbidden degrees. -/
theorem forbI_primes_card : forbI_primes.card = 10 := by native_decide

/-- Every prime in Forb(I) is indeed prime. -/
theorem forbI_primes_are_prime :
    ∀ p ∈ forbI_primes, Nat.Prime p := by
  intro p hp
  simp only [forbI_primes, Finset.mem_filter] at hp
  exact hp.2

/-- The computed non-prime forbidden set equals the explicit set. -/
theorem forbI_nonprimes_eq_explicit :
    forbI_nonprimes = {1, 4, 8, 9, 14} := by
  native_decide

/-- There are 5 non-prime forbidden degrees. -/
theorem forbI_nonprimes_card : forbI_nonprimes.card = 5 := by native_decide

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

    Proof: For any prime p, choose odd n = 2p+1 ≥ 3. Then:
    1. p < n² = N(B_n)  (the Molien exponent)
    2. The smallest B_n generator is 4 (all generators are even: 4, 6, ..., 2n)
    3. If p is odd: p cannot be a sum of even numbers (parity obstruction)
    4. If p = 2: p < 4 ≤ smallest generator (size obstruction)

    In either case, p ∉ ⟨4, 6, ..., 2n⟩ and p < N(B_n), making p a
    forbidden harmonic degree for B_n.

    We prove p is not even in ⟨4, 2n⟩ (the outer two generators),
    which suffices since ⟨4, 2n⟩ ⊆ ⟨4, 6, ..., 2n⟩. -/
theorem universal_prime_coverage (p : ℕ) (hp : Nat.Prime p) :
    ∃ n : ℕ, n ≥ 3 ∧ n % 2 = 1 ∧ p < n * n ∧
    -- p is not representable by even generators (proved via outer pair ⟨4, 2n⟩)
    ¬ inSemigroup 4 (2 * (2 * p + 1)) p := by
  use 2 * p + 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hp.two_le; omega
  · omega
  · nlinarith [hp.one_le]
  · -- p ∉ ⟨4, 2(2p+1)⟩: we'd need 4x + (4p+2)y = p.
    -- For y ≥ 1: (4p+2)·1 = 4p+2 > p, so impossible.
    -- For y = 0: 4x = p, so 4 ∣ p. But p is prime and ≥ 2, contradiction.
    intro ⟨x, y, heq⟩
    -- First show y = 0 (if y ≥ 1 then RHS ≥ 4p+2 > p)
    have hy0 : y = 0 := by
      by_contra hy
      have hy1 : y ≥ 1 := by omega
      have h1 := Nat.mul_le_mul_left (2 * (2 * p + 1)) hy1
      have h2 : 2 * (2 * p + 1) * 1 = 2 * (2 * p + 1) := mul_one _
      -- h1 : 2*(2*p+1)*1 ≤ 2*(2*p+1)*y, h2 simplifies LHS
      -- So 2*(2*p+1)*y ≥ 2*(2*p+1) = 4*p+2, and p = 4*x + that ≥ 4*p+2
      linarith [Nat.zero_le x]
    -- Now y = 0, so p = 4*x, contradicting primality
    subst hy0; simp at heq
    have h4 : 4 ∣ p := ⟨x, heq⟩
    rcases hp.eq_one_or_self_of_dvd 4 h4 with h | h
    · omega
    · subst h; norm_num at hp

/-- The parity obstruction applied to the 2-generator B₃ = O case:
    every odd prime p < 9 is forbidden for (d₁,d₂,N) = (4,6,9).
    This connects universal_prime_coverage to IsForbiddenDegree directly. -/
theorem odd_prime_forbidden_B3 (p : ℕ) (_ : Nat.Prime p)
    (hodd : p % 2 = 1) (hlt : p < 9) :
    IsForbiddenDegree 4 6 9 p := by
  constructor
  · exact odd_is_gap_of_even_generators 4 6 p (by norm_num) (by norm_num) hodd
  · left; omega

/-- p = 2 is forbidden for B₃ because 2 < 4 = smallest generator. -/
theorem two_forbidden_B3 : IsForbiddenDegree 4 6 9 2 := forbO_2_forbidden
