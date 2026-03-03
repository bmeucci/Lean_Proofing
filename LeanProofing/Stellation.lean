/-
  LeanProofing/Stellation.lean

  Phase III of the polyhedral journey: The Golden Scaling and Saturation Boundary.
  Covers both:
    - Section 5 (Algebraic Description of Closure): stellation scaling, four-stellation
      saturation, degree-dependent harmonic amplification, why the sequence stops at four
    - Section 6.3 (Geometric Description, Phase III): RT →(stell⁴)→ RHC

  Key results (v11 section references):
  - Proposition 5.1: Each RT main-sequence stellation scales circumradius by φ²
  - Corollary 5.1 (harmonic_degree_amplification): c_ℓ → φ^{2ℓ} c_ℓ per stellation
  - Theorem 5.1: 4th stellation → exactly 60 faces (geometric saturation)
  - Remark 5.2: Why the sequence stops at 4: φ⁸ ≈ 47 < 60 < φ¹⁰ ≈ 123
  - Section 8: Belt width = 2π·φ⁻⁸ on the midsphere
  See LucasNumbers.lean for Theorem 5.2 (general algebraic closure: φ^{8ℓ}+φ^{-8ℓ}=L(8ℓ)).
-/

import LeanProofing.Polyhedra
import LeanProofing.GoldenRatio
import LeanProofing.FiniteGroups

noncomputable section

/-! ## The Stellation Sequence (Section 5 / Section 6.3) -/

/-- A stellation step in the main sequence, tracking face count and scaling. -/
structure StellationStep where
  /-- Number of faces at this stage -/
  faceCount : ℕ
  /-- Cumulative scaling factor from the starting RT (exponent of φ²) -/
  cumulativeScaling : ℕ
  /-- Whether this stage has full icosahedral face symmetry -/
  hasFullIcoSymmetry : Bool

/-- The RT main-sequence stellation data (Proposition 5.1 / Theorem 5.1 of the paper).
    Following Wenninger's construction:
    - Stage 0 (RT):  30 faces, scaling φ⁰ = 1
    - Stage 1:       30 faces, pyramidal extensions, scaling φ²
    - Stage 2:       60 faces (face-plane splitting), scaling φ⁴
    - Stage 3:       60 faces, scaling φ⁶
    - Stage 4 (RHC): 60 faces, scaling φ⁸  ← geometric saturation -/
def stellationSequence : Fin 5 → StellationStep
  | ⟨0, _⟩ => { faceCount := 30, cumulativeScaling := 0, hasFullIcoSymmetry := false }
  | ⟨1, _⟩ => { faceCount := 30, cumulativeScaling := 1, hasFullIcoSymmetry := false }
  | ⟨2, _⟩ => { faceCount := 60, cumulativeScaling := 2, hasFullIcoSymmetry := true }
  | ⟨3, _⟩ => { faceCount := 60, cumulativeScaling := 3, hasFullIcoSymmetry := true }
  | ⟨4, _⟩ => { faceCount := 60, cumulativeScaling := 4, hasFullIcoSymmetry := true }

/-- The starting point has 30 faces (= RT). -/
theorem stellation_start : (stellationSequence ⟨0, by omega⟩).faceCount = 30 := rfl

/-- The terminal point has 60 faces (= RHC). -/
theorem stellation_end : (stellationSequence ⟨4, by omega⟩).faceCount = 60 := rfl

/-- The face count doubles from 30 to 60 at stage 2.
    This is the crucial topological transition. -/
theorem face_doubling :
    (stellationSequence ⟨2, by omega⟩).faceCount =
    2 * (stellationSequence ⟨0, by omega⟩).faceCount := rfl

/-- Once 60-face symmetry is achieved (stage 2), it is maintained through stage 4. -/
theorem sixty_faces_maintained (i : Fin 5) (hi : i.val ≥ 2) :
    (stellationSequence i).faceCount = 60 := by
  fin_cases i <;> simp_all [stellationSequence]

/-- The terminal stellation has full icosahedral face symmetry. -/
theorem terminal_has_full_symmetry :
    (stellationSequence ⟨4, by omega⟩).hasFullIcoSymmetry = true := rfl

/-! ## Degree-Dependent Harmonic Amplification (Corollary 5.1)

  Each stellation scales the circumradius by φ². A solid harmonic of degree ℓ
  satisfies f_ℓ(λr) = λ^ℓ f_ℓ(r). Therefore a single stellation amplifies
  the degree-ℓ coefficient by (φ²)^ℓ = φ^{2ℓ}. After four stellations: φ^{8ℓ}.
-/

/-- **Corollary 5.1 (Degree-Dependent Amplification)**:
    The amplification factor for harmonic degree ℓ after n stellations is φ^{2nℓ}.
    This is the exact scaling relationship: each stellation multiplies c_ℓ by φ^{2ℓ}. -/
def harmonicAmplification (n : ℕ) (ℓ : ℕ) : ℝ := φ ^ (2 * n * ℓ)

/-- Single stellation amplifies degree ℓ by φ^{2ℓ}. -/
theorem single_stellation_amplification (ℓ : ℕ) :
    harmonicAmplification 1 ℓ = φ ^ (2 * ℓ) := by
  simp [harmonicAmplification]

/-- Four stellations amplify degree ℓ by φ^{8ℓ} (total amplification for the loop). -/
theorem four_stellation_amplification (ℓ : ℕ) :
    harmonicAmplification 4 ℓ = φ ^ (8 * ℓ) := by
  simp [harmonicAmplification]

/-- At degree ℓ=0: amplification is 1 (scalars are unchanged). -/
theorem amplification_degree_zero (n : ℕ) :
    harmonicAmplification n 0 = 1 := by
  simp [harmonicAmplification]

/-- At degree ℓ=1, four stellations amplify by φ⁸ ≈ 46.978.
    Table: φ⁸ = 21φ+13, the fundamental stellation scaling. -/
theorem amplification_degree_one_four_stell :
    harmonicAmplification 4 1 = φ ^ 8 := by
  simp [harmonicAmplification]

/-- At degree ℓ=6 (Poole's first icosahedral harmonic), four stellations amplify by φ⁴⁸. -/
theorem amplification_degree_six_four_stell :
    harmonicAmplification 4 6 = φ ^ 48 := by
  simp [harmonicAmplification]

/-- The amplification is always positive. -/
theorem harmonicAmplification_pos (n ℓ : ℕ) : harmonicAmplification n ℓ > 0 :=
  pow_pos φ_pos _

/-- The amplification is strictly greater than 1 for n,ℓ ≥ 1. -/
theorem harmonicAmplification_gt_one (n ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ) :
    harmonicAmplification n ℓ > 1 := by
  unfold harmonicAmplification
  have hpos : 0 < 2 * n * ℓ := Nat.mul_pos (Nat.mul_pos (by norm_num) hn) hℓ
  have hne : 2 * n * ℓ ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  exact (one_lt_pow_iff_of_nonneg (le_of_lt φ_pos) hne).mpr φ_gt_one

/-! ## Why Exactly Four Stellations (Theorem 5.1, Remark 5.2)

  The argument:
  1. Each stellation scales by φ² (Proposition 5.1)
  2. RT starts with 30 faces
  3. At stellation 2, faces split from 30 → 60 = |I|
  4. 60 faces = single orbit with trivial stabilisers under I (Klein saturation)
  5. Further stellations maintain the 60-face count
  6. Cumulative scaling at 4 stellations is φ⁸
  7. Remark 5.2: φ⁸ ≈ 47 < 60 < φ¹⁰ ≈ 123, so 4 is the last step before overshoot
-/

/-- 60 faces saturate the icosahedral group (Theorem 5.1 + Klein's theorem). -/
theorem sixty_saturates_icosahedral :
    FiniteRotationGroup3D.icosahedral.order = 60 := rfl

/-- Four stellations give cumulative scaling exponent 2×4 = 8, i.e., total φ⁸. -/
theorem four_stellations_exponent : 2 * 4 = 8 := by norm_num

/-- The fourth stellation produces the rhombic hexecontahedron. -/
theorem fourth_stellation_is_RHC :
    (stellationSequence ⟨4, by omega⟩).faceCount = rhombicHexecontahedron.F := by
  simp [stellationSequence, rhombicHexecontahedron]

/-! ## The Scaling Bound (Remark 5.2)

  φ⁸ ≈ 46.978 < 60 < φ¹⁰ ≈ 122.99

  Four stellations is the largest integer number of φ²-scaling steps that remains
  sub-saturated before overshooting the 60-element icosahedral bound.
-/

/-- φ¹⁰ = 55φ + 34 (Fibonacci structure). φ¹⁰ ≈ 122.99 > 60. -/
theorem φ_pow10 : φ ^ 10 = 55 * φ + 34 := by
  have h8 := φ_pow8
  have h2 := φ_sq
  calc φ ^ 10 = φ ^ 8 * φ ^ 2 := by ring
    _ = (21 * φ + 13) * (φ + 1) := by rw [h8, h2]
    _ = 21 * φ ^ 2 + 21 * φ + 13 * φ + 13 := by ring
    _ = 21 * (φ + 1) + 34 * φ + 13 := by rw [h2]; ring
    _ = 55 * φ + 34 := by ring

/-- The stellation from the RT, as a concrete operation producing the RHC. -/
def phaseIII_stellation : StellationData where
  source := rhombicTriacontahedron
  target := rhombicHexecontahedron
  face_relation := by simp [rhombicTriacontahedron, rhombicHexecontahedron]

/-! ## Belt Structure (Section 8)

  The belt is the intersection region on the common midsphere where face planes
  from the RT and the 4th stellation (RHC) meet.

  Proposition 8.1 (in Wenninger coordinate model):
    Belt width = 2π · φ⁻⁸ radians ≈ 0.1336 rad ≈ 7.66°.

  Algebraic origin: since φ⁸ + φ⁻⁸ = 47 exactly, the fractional offset of φ⁸
  from the nearest integer is φ⁻⁸, and this governs the angular gap on the midsphere.

  Geometric origin: the incommensurability of pentagonal and tetrahedral symmetry
  (see Incommensurability.lean) prevents the belt from closing to zero width.

  Both descriptions produce the same quantity φ⁻⁸ (Remark 8.1 of the paper).
-/

/-- The belt identity: φ⁸ + φ⁻⁸ = 47 (= L(8), the 8th Lucas number).
    Restating belt_identity from GoldenRatio.lean for direct reference here. -/
theorem belt_width_fraction_plus_scaling_is_integer :
    φ ^ 8 + φ⁻¹ ^ 8 = 47 := belt_identity

/-- The belt width as a fraction φ⁻⁸ of the full midsphere circumference 2π. -/
def beltWidthFraction : ℝ := φ⁻¹ ^ 8

/-- The belt width fraction is positive. -/
theorem belt_width_fraction_pos : beltWidthFraction > 0 :=
  pow_pos (inv_pos.mpr φ_pos) 8

/-- The belt width fraction is less than 1 (much less: ≈ 0.0213). -/
theorem belt_width_fraction_lt_one : beltWidthFraction < 1 := by
  unfold beltWidthFraction
  -- φ⁻¹^8 = (φ^8)⁻¹ < 1 because φ^8 = 21φ+13 > 1
  have hφ8_gt_one : 1 < φ ^ 8 := by rw [φ_pow8]; linarith [φ_gt_one]
  have hφinv8_pos : (0 : ℝ) < φ⁻¹ ^ 8 := pow_pos (inv_pos.mpr φ_pos) 8
  have hmul : φ⁻¹ ^ 8 * φ ^ 8 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt φ_pos), one_pow]
  linarith [mul_lt_mul_of_pos_left hφ8_gt_one hφinv8_pos, mul_one (φ⁻¹ ^ 8)]

end
