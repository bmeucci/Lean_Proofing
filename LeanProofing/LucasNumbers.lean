/-
  LeanProofing/LucasNumbers.lean

  General Lucas number theory: the algebraic foundation of the closure condition.
  Corresponds to Section 3 (Number-Theoretic Foundation) of the paper (v11).

  Key results:
  - Lucas numbers defined by recurrence: L(0)=2, L(1)=1, L(n+2)=L(n+1)+L(n)
  - Integrality is automatic (defined as ℤ-valued)
  - Specific values: L(2)=3, L(4)=7, L(6)=18, L(8)=47, L(16)=2207, L(24)=103682
  - Connection to golden ratio: φⁿ + ψⁿ = L(n) (proved by two-step induction)
  - General algebraic closure (Theorem 5.2): φ^{8ℓ} + φ^{-8ℓ} = L(8ℓ) ∈ ℤ for all ℓ
  - Self-similar phase structure (Proposition 3.1): (1 - φ⁻ⁿ) * φⁿ = φⁿ - 1

  The specific case ℓ=1 recovers belt_identity from GoldenRatio.lean: L(8) = 47.
  The case ℓ=6 gives L(48), the first icosahedral harmonic degree (Section 7).
-/

import LeanProofing.GoldenRatio
import Mathlib.Tactic

/-! ## Lucas Numbers (Definition 3.1 of the paper) -/

/-- The Lucas numbers, defined by the recurrence L(0)=2, L(1)=1, L(n+2)=L(n+1)+L(n).
    Defined as ℤ-valued: integrality is automatic (Theorem 3.1 of the paper). -/
def lucasNumber : ℕ → ℤ
  | 0     => 2
  | 1     => 1
  | (n+2) => lucasNumber (n+1) + lucasNumber n

/-- **Theorem 3.1**: The Lucas numbers satisfy the Fibonacci recurrence. -/
theorem lucas_recurrence (n : ℕ) :
    lucasNumber (n+2) = lucasNumber (n+1) + lucasNumber n := rfl

/-- Initial values. -/
@[simp] theorem lucas_zero  : lucasNumber 0  = 2  := rfl
@[simp] theorem lucas_one   : lucasNumber 1  = 1  := rfl

/-- The sequence: 2, 1, 3, 4, 7, 11, 18, 29, 47, 76, ... -/
@[simp] theorem lucas_two   : lucasNumber 2  = 3  := rfl
@[simp] theorem lucas_three : lucasNumber 3  = 4  := rfl
@[simp] theorem lucas_four  : lucasNumber 4  = 7  := rfl
@[simp] theorem lucas_five  : lucasNumber 5  = 11 := rfl
@[simp] theorem lucas_six   : lucasNumber 6  = 18 := rfl
@[simp] theorem lucas_seven : lucasNumber 7  = 29 := rfl

/-- **Theorem 3.2 (The Critical Identity)**: L(8) = 47.
    This is the fundamental case of the general closure theorem (ℓ=1). -/
@[simp] theorem lucas_eight : lucasNumber 8 = 47 := rfl

-- Intermediate values proved by explicit recurrence chains (avoids native_decide)
private lemma lrec (n : ℕ) : lucasNumber (n+2) = lucasNumber (n+1) + lucasNumber n := rfl

/-- L(16) = 2207. This is the ℓ=2 case: φ^16 + φ^{-16} = 2207. -/
theorem lucas_sixteen : lucasNumber 16 = 2207 := by
  have h7  := lucas_seven; have h8 := lucas_eight
  have h9  : lucasNumber 9  = 76   := by linarith [lrec 7]
  have h10 : lucasNumber 10 = 123  := by linarith [lrec 8]
  have h11 : lucasNumber 11 = 199  := by linarith [lrec 9]
  have h12 : lucasNumber 12 = 322  := by linarith [lrec 10]
  have h13 : lucasNumber 13 = 521  := by linarith [lrec 11]
  have h14 : lucasNumber 14 = 843  := by linarith [lrec 12]
  have h15 : lucasNumber 15 = 1364 := by linarith [lrec 13]
  linarith [lrec 14]

/-- L(24) = 103682. This is the ℓ=3 case: φ^24 + φ^{-24} = 103682. -/
theorem lucas_twentyfour : lucasNumber 24 = 103682 := by
  have h7  := lucas_seven; have h8 := lucas_eight
  have h9  : lucasNumber 9  = 76    := by linarith [lrec 7]
  have h10 : lucasNumber 10 = 123   := by linarith [lrec 8]
  have h11 : lucasNumber 11 = 199   := by linarith [lrec 9]
  have h12 : lucasNumber 12 = 322   := by linarith [lrec 10]
  have h13 : lucasNumber 13 = 521   := by linarith [lrec 11]
  have h14 : lucasNumber 14 = 843   := by linarith [lrec 12]
  have h15 : lucasNumber 15 = 1364  := by linarith [lrec 13]
  have h16 : lucasNumber 16 = 2207  := by linarith [lrec 14]
  have h17 : lucasNumber 17 = 3571  := by linarith [lrec 15]
  have h18 : lucasNumber 18 = 5778  := by linarith [lrec 16]
  have h19 : lucasNumber 19 = 9349  := by linarith [lrec 17]
  have h20 : lucasNumber 20 = 15127 := by linarith [lrec 18]
  have h21 : lucasNumber 21 = 24476 := by linarith [lrec 19]
  have h22 : lucasNumber 22 = 39603 := by linarith [lrec 20]
  have h23 : lucasNumber 23 = 64079 := by linarith [lrec 21]
  linarith [lrec 22]

/-- L(48) = 10749957122. The ℓ=6 case: φ^48 + φ^{-48} = L(48).
    Degree 48 is significant: ℓ=6 is the first non-trivial icosahedral harmonic
    degree (Poole's invariant P, Section 7 of the paper). -/
theorem lucas_fortyeight : lucasNumber 48 = 10749957122 := by
  have h7  := lucas_seven; have h8 := lucas_eight
  have h9  : lucasNumber 9  = 76         := by linarith [lrec 7]
  have h10 : lucasNumber 10 = 123        := by linarith [lrec 8]
  have h11 : lucasNumber 11 = 199        := by linarith [lrec 9]
  have h12 : lucasNumber 12 = 322        := by linarith [lrec 10]
  have h13 : lucasNumber 13 = 521        := by linarith [lrec 11]
  have h14 : lucasNumber 14 = 843        := by linarith [lrec 12]
  have h15 : lucasNumber 15 = 1364       := by linarith [lrec 13]
  have h16 : lucasNumber 16 = 2207       := by linarith [lrec 14]
  have h17 : lucasNumber 17 = 3571       := by linarith [lrec 15]
  have h18 : lucasNumber 18 = 5778       := by linarith [lrec 16]
  have h19 : lucasNumber 19 = 9349       := by linarith [lrec 17]
  have h20 : lucasNumber 20 = 15127      := by linarith [lrec 18]
  have h21 : lucasNumber 21 = 24476      := by linarith [lrec 19]
  have h22 : lucasNumber 22 = 39603      := by linarith [lrec 20]
  have h23 : lucasNumber 23 = 64079      := by linarith [lrec 21]
  have h24 : lucasNumber 24 = 103682     := by linarith [lrec 22]
  have h25 : lucasNumber 25 = 167761     := by linarith [lrec 23]
  have h26 : lucasNumber 26 = 271443     := by linarith [lrec 24]
  have h27 : lucasNumber 27 = 439204     := by linarith [lrec 25]
  have h28 : lucasNumber 28 = 710647     := by linarith [lrec 26]
  have h29 : lucasNumber 29 = 1149851    := by linarith [lrec 27]
  have h30 : lucasNumber 30 = 1860498    := by linarith [lrec 28]
  have h31 : lucasNumber 31 = 3010349    := by linarith [lrec 29]
  have h32 : lucasNumber 32 = 4870847    := by linarith [lrec 30]
  have h33 : lucasNumber 33 = 7881196    := by linarith [lrec 31]
  have h34 : lucasNumber 34 = 12752043   := by linarith [lrec 32]
  have h35 : lucasNumber 35 = 20633239   := by linarith [lrec 33]
  have h36 : lucasNumber 36 = 33385282   := by linarith [lrec 34]
  have h37 : lucasNumber 37 = 54018521   := by linarith [lrec 35]
  have h38 : lucasNumber 38 = 87403803   := by linarith [lrec 36]
  have h39 : lucasNumber 39 = 141422324  := by linarith [lrec 37]
  have h40 : lucasNumber 40 = 228826127  := by linarith [lrec 38]
  have h41 : lucasNumber 41 = 370248451  := by linarith [lrec 39]
  have h42 : lucasNumber 42 = 599074578  := by linarith [lrec 40]
  have h43 : lucasNumber 43 = 969323029  := by linarith [lrec 41]
  have h44 : lucasNumber 44 = 1568397607 := by linarith [lrec 42]
  have h45 : lucasNumber 45 = 2537720636 := by linarith [lrec 43]
  have h46 : lucasNumber 46 = 4106118243 := by linarith [lrec 44]
  have h47 : lucasNumber 47 = 6643838879 := by linarith [lrec 45]
  linarith [lrec 46]

/-! ## Connection to the Golden Ratio -/

noncomputable section

/-- **Theorem 3.1 (integrality, general form)**: For all n, φⁿ + ψⁿ = L(n) as real numbers.

    Proof by two-step induction: both sides satisfy the same recurrence
    with the same initial conditions.

    Base case n=0: φ⁰+ψ⁰ = 2 = L(0). ✓
    Base case n=1: φ¹+ψ¹ = φ+ψ = 1 = L(1). ✓
    Step: φ^{n+2}+ψ^{n+2} = (φ^{n+1}+ψ^{n+1}) + (φⁿ+ψⁿ) = L(n+1)+L(n) = L(n+2). ✓
    (uses φ²=φ+1 and ψ²=ψ+1) -/
theorem phi_pow_add_psi_pow (n : ℕ) : φ ^ n + ψ ^ n = (lucasNumber n : ℝ) := by
  -- Prove simultaneously for n and n+1 by paired induction
  suffices h : ∀ m : ℕ,
      φ ^ m + ψ ^ m = (lucasNumber m : ℝ) ∧
      φ ^ (m+1) + ψ ^ (m+1) = (lucasNumber (m+1) : ℝ) from (h n).1
  intro m
  induction m with
  | zero =>
    constructor
    · -- φ⁰ + ψ⁰ = 2 = L(0)
      simp [lucasNumber]; norm_num
    · -- φ¹ + ψ¹ = 1 = L(1)
      simp [lucasNumber]
      have := φ_add_ψ
      push_cast
      linarith
  | succ k ih =>
    obtain ⟨ihk, ihk1⟩ := ih
    constructor
    · -- shift: the (k+1) case is already ihk1
      exact ihk1
    · -- prove the (k+2) case using the recurrence
      have hφ := φ_pow_succ_succ k
      have hψ := ψ_pow_succ_succ k
      have h_rec : (lucasNumber (k+2) : ℝ) = lucasNumber (k+1) + lucasNumber k := by
        exact_mod_cast lucas_recurrence k
      linarith

/-- For even exponents, ψⁿ = φ⁻ⁿ.
    Since φ·ψ = -1 we have ψ = -φ⁻¹, so ψⁿ = (-1)ⁿ φ⁻ⁿ = φ⁻ⁿ when n is even. -/
theorem psi_pow_even_eq_phi_inv_pow (n : ℕ) : ψ ^ (2*n) = φ⁻¹ ^ (2*n) := by
  have h : ψ = -φ⁻¹ := by linarith [φ_inv_eq_neg_ψ]
  rw [h, neg_pow, show (-1 : ℝ) ^ (2 * n) = 1 from by rw [pow_mul]; norm_num, one_mul]

/-! ## The General Algebraic Closure Theorem -/

/-- **Theorem 5.2 (General Algebraic Closure)**: For all ℓ : ℕ,
    φ^{8ℓ} + φ^{-8ℓ} = L(8ℓ) ∈ ℤ.

    This generalises the belt identity (ℓ=1: L(8)=47) to all harmonic degrees.
    The key step is that φ^{-8ℓ} = ψ^{8ℓ} (since 8ℓ is even and φ·ψ = -1). -/
theorem general_algebraic_closure (ℓ : ℕ) :
    φ ^ (8*ℓ) + φ⁻¹ ^ (8*ℓ) = (lucasNumber (8*ℓ) : ℝ) := by
  -- Step 1: φ⁻¹^{8ℓ} = ψ^{8ℓ} (since 8ℓ is even)
  have h_inv : φ⁻¹ ^ (8*ℓ) = ψ ^ (8*ℓ) := by
    rw [φ_inv_eq_neg_ψ, neg_pow, show (-1 : ℝ) ^ (8 * ℓ) = 1 from by
      rw [pow_mul]; norm_num, one_mul]
  rw [h_inv]
  -- Step 2: φ^{8ℓ} + ψ^{8ℓ} = L(8ℓ)
  exact phi_pow_add_psi_pow (8*ℓ)

/-- The ℓ=1 case recovers the belt identity. -/
theorem general_closure_ell_one :
    φ ^ 8 + φ⁻¹ ^ 8 = (47 : ℝ) := by
  have h := general_algebraic_closure 1
  have : (8 : ℕ) * 1 = 8 := by norm_num
  rw [this, lucas_eight] at h
  exact_mod_cast h

/-- The ℓ=2 case: φ^16 + φ^{-16} = 2207. -/
theorem general_closure_ell_two :
    φ ^ 16 + φ⁻¹ ^ 16 = (2207 : ℝ) := by
  have h := general_algebraic_closure 2
  have : (8 : ℕ) * 2 = 16 := by norm_num
  rw [this, lucas_sixteen] at h
  exact_mod_cast h

/-- The ℓ=6 case: φ^48 + φ^{-48} = L(48), the first icosahedral harmonic degree. -/
theorem general_closure_ell_six :
    φ ^ 48 + φ⁻¹ ^ 48 = (10749957122 : ℝ) := by
  have h := general_algebraic_closure 6
  have : (8 : ℕ) * 6 = 48 := by norm_num
  rw [this, lucas_fortyeight] at h
  exact_mod_cast h

/-! ## Self-Similar Phase Structure (Proposition 3.1) -/

/-- **Proposition 3.1 (Self-Similar Phase Structure)**: For any n,
    (1 - φ⁻ⁿ) * φⁿ = φⁿ - 1.

    Interpretation: writing {φⁿ} for the fractional part of φⁿ, we have
    {φⁿ} = 1 - φ⁻ⁿ (since φⁿ + φ⁻ⁿ = L(n) is an integer for even n).
    Therefore {φⁿ}/φ⁻ⁿ = (1-φ⁻ⁿ)/φ⁻ⁿ = φⁿ - 1.
    The overshoot and undershoot are algebraically locked by φ's minimal polynomial.

    This lemma gives the algebraic identity without reference to floor functions. -/
theorem self_similar_phase (n : ℕ) : (1 - φ⁻¹ ^ n) * φ ^ n = φ ^ n - 1 := by
  have hne : φ ^ n ≠ 0 := pow_ne_zero _ φ_ne_zero
  have h : φ⁻¹ ^ n * φ ^ n = 1 := by
    rw [← mul_pow]
    simp [inv_mul_cancel₀ φ_ne_zero]
  nlinarith [h]

/-- The ratio form: the fractional offset equals φⁿ - 1 times the inverse power.
    Concretely at n=8: the ratio {φ⁸}/φ⁻⁸ = φ⁸ - 1 ≈ 45.978. -/
theorem self_similar_ratio (n : ℕ) (hn : 0 < n) :
    (φ ^ n - 1) / φ⁻¹ ^ n = φ ^ (2*n) - φ ^ n := by
  have hpow_pos : 0 < φ⁻¹ ^ n := pow_pos (inv_pos.mpr φ_pos) _
  rw [div_eq_iff (ne_of_gt hpow_pos)]
  have h : φ⁻¹ ^ n * φ ^ n = 1 := by
    rw [← mul_pow]; simp [inv_mul_cancel₀ φ_ne_zero]
  have h2n : φ ^ (2*n) = φ ^ n * φ ^ n := by rw [two_mul, pow_add]
  rw [h2n]
  nlinarith [h]

end

/-! ## The Fibonacci-Lucas Arithmetic Connection (Remark 5.4) -/

/-- The Fibonacci numbers (for reference in Remark 5.4). -/
def fibNumber : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | (n+2) => fibNumber (n+1) + fibNumber n

@[simp] theorem fib_seven : fibNumber 7 = 13 := rfl

/-- **Remark 5.4**: The arithmetic relation 60 = L(8) + F(7) = 47 + 13.
    This connects Lucas numbers, Fibonacci numbers, and |I| = 60 in one identity.
    Note: the paper flags this as arithmetically trivial but geometrically suggestive;
    the algebraic closure proof does NOT depend on it. -/
theorem lucas8_plus_fib7_eq_ico_order :
    lucasNumber 8 + fibNumber 7 = (60 : ℤ) := by decide

/-- The decomposition: L(8) = 47 is just below |I| = 60, with gap = F(7) = 13. -/
theorem stellation_gap_to_ico_bound :
    (60 : ℤ) - lucasNumber 8 = fibNumber 7 := by decide
