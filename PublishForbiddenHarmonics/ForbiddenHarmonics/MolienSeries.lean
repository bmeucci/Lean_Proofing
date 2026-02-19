/-
  ForbiddenHarmonics/MolienSeries.lean

  The harmonic Molien series and forbidden degree predicate.

  The harmonic Molien series for a 3D polyhedral rotation group G is:
    H_G(t) = (1 + t^N) / ((1 - t^{d₁})(1 - t^{d₂}))

  The coefficient [t^ℓ]H_G(t) counts the dimension of the
  G-invariant harmonic space at degree ℓ.

  A degree ℓ is forbidden when this coefficient is zero.

  Key result (Lemma 1): S^G = S^W ⊕ Q · S^W decomposition gives the formula.
-/
import ForbiddenHarmonics.Basic
import ForbiddenHarmonics.NumericalSemigroup

/-! ## Molien Coefficient

  For a 3D polyhedral group with harmonic degrees (d₁, d₂) and Molien exponent N:
    [t^ℓ]H_G(t) = R(ℓ) + R(ℓ - N)
  where R(k) counts the number of representations k = d₁·x + d₂·y with x, y ≥ 0.

  Note: R(k) = 0 for k < 0 by convention.
-/

/-! ## Forbidden Degree Predicate (Prop version) -/

/-- Propositional version: degree ℓ is forbidden for harmonic data (d₁, d₂, N). -/
def IsForbiddenDegree (d₁ d₂ N ℓ : ℕ) : Prop :=
  ¬ inSemigroup d₁ d₂ ℓ ∧ (ℓ < N ∨ ¬ inSemigroup d₁ d₂ (ℓ - N))

/-- The forbidden predicate is decidable. -/
instance (d₁ d₂ N ℓ : ℕ) : Decidable (IsForbiddenDegree d₁ d₂ N ℓ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Verification of the Molien Formula Structure

  For the 3D case, the Molien series H_G(t) = (1 + t^N) / ((1-t^{d₁})(1-t^{d₂}))
  expands as: coefficient of t^ℓ = R(ℓ) + R(ℓ - N)
  where R(k) = #{(x,y) : ℕ² | k = d₁·x + d₂·y}.
-/

/-- The Molien formula relates forbidden degrees to semigroup gaps:
    For the tetrahedral group (d₁=3, d₂=4, N=6), degree ℓ is forbidden
    iff ℓ ∉ ⟨3,4⟩ and (ℓ < 6 or ℓ-6 ∉ ⟨3,4⟩). -/
theorem molien_tetrahedral_forbidden_1 : IsForbiddenDegree 3 4 6 1 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem molien_tetrahedral_forbidden_2 : IsForbiddenDegree 3 4 6 2 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

theorem molien_tetrahedral_forbidden_5 : IsForbiddenDegree 3 4 6 5 := by
  constructor
  · unfold inSemigroup; push_neg; intro x y; omega
  · left; omega

/-- Degree 3 is NOT forbidden for the tetrahedral group (3 = 3·1 + 4·0). -/
theorem molien_tetrahedral_allowed_3 : ¬ IsForbiddenDegree 3 4 6 3 := by
  intro ⟨h, _⟩; exact h ⟨1, 0, by norm_num⟩
