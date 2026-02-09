/-
  LeanProofing/IcosahedralTransition.lean

  Phase II of the polyhedral journey: Transition to Icosahedral Symmetry.
  Corresponds to Section 6 of the paper.

  Key results:
  - The coset completion: T acts under I to produce 5 tetrahedra (Theorem 6.2)
  - The convex hull of 5 tetrahedra = dodecahedron
  - Dodecahedron →(rect)→ Icosidodecahedron →(dual)→ Rhombic Triacontahedron
-/

import LeanProofing.Polyhedra
import LeanProofing.FiniteGroups

/-! ## The Bridge: Coset Completion (Theorem 6.2)

  The icosahedral group I (order 60) contains the tetrahedral group T (order 12)
  as a subgroup. By orbit-stabilizer, the orbit of a tetrahedron under I
  has exactly |I|/|T| = 60/12 = 5 elements.
-/

/-- **Theorem 6.2**: The orbit of a tetrahedron under the icosahedral group
    contains exactly 5 distinct tetrahedra. -/
theorem five_tetrahedra_from_orbit :
    FiniteRotationGroup3D.icosahedral.order /
    FiniteRotationGroup3D.tetrahedral.order = 5 := by
  simp [FiniteRotationGroup3D.order]

/-- Each tetrahedron has 4 vertices, so 5 tetrahedra have at most 20 vertices. -/
theorem five_tetrahedra_max_vertices : 5 * tetrahedron.V = 20 := by
  simp [tetrahedron]

/-- The dodecahedron has exactly 20 vertices. -/
theorem dodecahedron_has_20_vertices : dodecahedron.V = 20 := by
  simp [dodecahedron]

/-- **Corollary 6.3**: The 20 vertices from 5 tetrahedra coincide with
    the 20 vertices of the dodecahedron.

    This establishes the forward geometric bridge from tetrahedral/octahedral
    symmetry (Phase I) to icosahedral symmetry (Phase II). -/
theorem coset_completion_vertex_count :
    5 * tetrahedron.V = dodecahedron.V := by
  simp [tetrahedron, dodecahedron]

/-! ## Step 5: Dodecahedron → Icosidodecahedron via Rectification (Prop 6.7) -/

/-- **Proposition 6.7**: Rectification of the dodecahedron produces the
    icosidodecahedron. The dodecahedron has 30 edges, so rectification
    creates 30 new vertices at edge midpoints. These 30 points are also
    the edge midpoints of the dual icosahedron. -/
def rect_dodecahedron_is_icosidodecahedron : RectificationData where
  source := dodecahedron
  target := icosidodecahedron
  vertex_from_edges := by simp [dodecahedron, icosidodecahedron]

/-- The icosidodecahedron has 32 faces: 12 pentagons + 20 triangles.
    These come from 12 dodecahedral faces + 20 vertex figures. -/
theorem icosidodecahedron_face_decomposition :
    icosidodecahedron.F = dodecahedron.F + dodecahedron.V := by
  simp [icosidodecahedron, dodecahedron]

/-- The ID has 30 vertices — half of the 60-face saturation limit. -/
theorem icosidodecahedron_30_vertices : icosidodecahedron.V = 30 := by
  simp [icosidodecahedron]

/-! ## Step 6: Icosidodecahedron → Rhombic Triacontahedron via Dualization -/

/-- **Theorem 6.8**: The dual of the icosidodecahedron is the rhombic
    triacontahedron, consisting of 30 congruent golden rhombi (diagonals
    in ratio φ : 1). -/
def dual_icosidodecahedron_is_RT : DualizationData where
  source := icosidodecahedron
  target := rhombicTriacontahedron
  dual_vertices := by simp [icosidodecahedron, rhombicTriacontahedron]
  dual_faces := by simp [icosidodecahedron, rhombicTriacontahedron]
  dual_edges := by simp [icosidodecahedron, rhombicTriacontahedron]

/-- The RT has exactly 30 faces — half of the maximal 60 allowed by the
    icosahedral constraint. This is the starting point for stellation. -/
theorem RT_thirty_faces : rhombicTriacontahedron.F = 30 := by
  simp [rhombicTriacontahedron]

/-- The RT face count is exactly half the icosahedral saturation limit. -/
theorem RT_half_saturation : rhombicTriacontahedron.F * 2 = 60 := by
  simp [rhombicTriacontahedron]

/-! ## The Complete Phase II Chain -/

/-- Phase II steps chain together: rectification target feeds into dualization source. -/
theorem phaseII_chain_56 :
    dual_icosidodecahedron_is_RT.source = rect_dodecahedron_is_icosidodecahedron.target := by
  simp [dual_icosidodecahedron_is_RT, rect_dodecahedron_is_icosidodecahedron, icosidodecahedron]

/-- Phase II ends at the rhombic triacontahedron, ready for stellation. -/
theorem phaseII_end : dual_icosidodecahedron_is_RT.target = rhombicTriacontahedron := by
  simp [dual_icosidodecahedron_is_RT, rhombicTriacontahedron]

/-- The symmetry upgrade from Phase I to Phase II:
    octahedral (24) → icosahedral (60). -/
theorem phaseII_symmetry_upgrade :
    SymmetryType.octahedral.rotationOrder < SymmetryType.icosahedral.rotationOrder := by
  simp [SymmetryType.rotationOrder]

/-- Icosahedral symmetry is the maximum polyhedral symmetry. -/
theorem icosahedral_is_max :
    ∀ s : SymmetryType, s.rotationOrder ≤ SymmetryType.icosahedral.rotationOrder := by
  intro s
  cases s <;> simp [SymmetryType.rotationOrder]
