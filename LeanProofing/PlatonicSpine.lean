/-
  LeanProofing/PlatonicSpine.lean

  Phase I of the polyhedral journey: The Platonic Spine.
  Corresponds to Section 5 of the paper.

  The chain:
    Tetrahedron →(rect)→ Octahedron →(dual)→ Cube
    →(rect)→ Cuboctahedron →(dual)→ Rhombic Dodecahedron

  Each step is proved by verifying vertex/edge/face counts under
  rectification and dualization.
-/

import LeanProofing.Polyhedra

/-! ## Step 1: Tetrahedron → Octahedron via Rectification (Proposition 5.1) -/

/-- **Proposition 5.1**: The rectification of a regular tetrahedron produces
    a regular octahedron.

    The tetrahedron has 6 edges, so rectification creates 6 new vertices at
    edge midpoints. Each of the 4 original vertices is truncated to reveal a
    triangular face, while each of the 4 original triangular faces becomes a
    smaller triangle. Result: 6 vertices, 12 edges, 8 faces = octahedron. -/
def rect_tetrahedron_is_octahedron : RectificationData where
  source := tetrahedron
  target := octahedron
  vertex_from_edges := by simp [tetrahedron, octahedron]

/-- The octahedron has the correct face count from rectification. -/
theorem rect_tetra_faces :
    octahedron.F = tetrahedron.F + tetrahedron.V := by
  simp [octahedron, tetrahedron]

/-! ## Step 2: Octahedron → Cube via Dualization (Proposition 5.2) -/

/-- **Proposition 5.2**: The octahedron and cube are dual polyhedra.

    The octahedron has 6 vertices and 8 faces. Its dual has 8 vertices
    (one per octahedral face) and 6 faces (one per octahedral vertex).
    Each dual face has 4 edges (since octahedral vertices have degree 4),
    so the dual has 6 square faces = cube. -/
def dual_octahedron_is_cube : DualizationData where
  source := octahedron
  target := cube
  dual_vertices := by simp [octahedron, cube]
  dual_faces := by simp [octahedron, cube]
  dual_edges := by simp [octahedron, cube]

/-! ## Step 3: Cube → Cuboctahedron via Rectification (Proposition 5.3) -/

/-- **Proposition 5.3**: The rectification of a cube produces a cuboctahedron.

    The cube has 12 edges, yielding 12 new vertices at edge midpoints.
    Each of the 8 cubic vertices is truncated to reveal a triangular face.
    Each of the 6 square faces becomes a smaller square.
    Result: 12 vertices, 24 edges, 14 faces (8 triangles + 6 squares). -/
def rect_cube_is_cuboctahedron : RectificationData where
  source := cube
  target := cuboctahedron
  vertex_from_edges := by simp [cube, cuboctahedron]

/-- The cuboctahedron has the correct face count from rectification. -/
theorem rect_cube_faces :
    cuboctahedron.F = cube.F + cube.V := by
  simp [cuboctahedron, cube]

/-! ## Step 4: Cuboctahedron → Rhombic Dodecahedron via Dualization (Prop 5.4) -/

/-- **Proposition 5.4**: The dual of the cuboctahedron is the rhombic dodecahedron.

    The cuboctahedron has 14 faces → dual has 14 vertices.
    It has 12 vertices → dual has 12 faces.
    Each vertex has degree 4 → each dual face has 4 edges (rhombi).
    The diagonal ratio is √2 : 1, not involving the golden ratio. -/
def dual_cuboctahedron_is_rhombicDodecahedron : DualizationData where
  source := cuboctahedron
  target := rhombicDodecahedron
  dual_vertices := by simp [cuboctahedron, rhombicDodecahedron]
  dual_faces := by simp [cuboctahedron, rhombicDodecahedron]
  dual_edges := by simp [cuboctahedron, rhombicDodecahedron]

/-! ## The Complete Phase I Chain -/

/-- Phase I begins at the tetrahedron and ends at the rhombic dodecahedron. -/
theorem phaseI_start : rect_tetrahedron_is_octahedron.source = tetrahedron := by
  simp [rect_tetrahedron_is_octahedron, tetrahedron]

theorem phaseI_chain_12 :
    dual_octahedron_is_cube.source =
    rect_tetrahedron_is_octahedron.target := by
  simp [dual_octahedron_is_cube,
        rect_tetrahedron_is_octahedron, octahedron]

theorem phaseI_chain_23 : rect_cube_is_cuboctahedron.source = dual_octahedron_is_cube.target := by
  simp [rect_cube_is_cuboctahedron, dual_octahedron_is_cube, cube]

theorem phaseI_chain_34 :
    dual_cuboctahedron_is_rhombicDodecahedron.source =
    rect_cube_is_cuboctahedron.target := by
  simp [dual_cuboctahedron_is_rhombicDodecahedron,
        rect_cube_is_cuboctahedron, cuboctahedron]

theorem phaseI_end : dual_cuboctahedron_is_rhombicDodecahedron.target = rhombicDodecahedron := by
  simp [dual_cuboctahedron_is_rhombicDodecahedron, rhombicDodecahedron]

/-- The symmetry upgrades through Phase I:
    tetrahedral (12) → octahedral (24) throughout. -/
theorem phaseI_symmetry_expansion :
    SymmetryType.tetrahedral.rotationOrder < SymmetryType.octahedral.rotationOrder := by
  simp [SymmetryType.rotationOrder]
