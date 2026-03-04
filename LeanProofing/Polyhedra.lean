/-
  LeanProofing/Polyhedra.lean

  Combinatorial definitions of polyhedra and their fundamental operations.
  Provides the vocabulary for the entire polyhedral journey.

  A polyhedron is characterized by its vertex count V, edge count E,
  face count F, and symmetry group. Euler's formula V - E + F = 2
  constrains these for convex polyhedra.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Polyhedron as Combinatorial Data -/

/-- A combinatorial polyhedron, characterized by vertex, edge, and face counts.
    The `euler` field is a proof that this combinatorial data is consistent with
    a topological polyhedron: it satisfies Euler's formula V + F = E + 2.
    This means the Lean code asserts "this data is consistent with a polyhedron"
    rather than merely storing numbers. -/
structure Polyhedron where
  /-- Number of vertices -/
  V : ℕ
  /-- Number of edges -/
  E : ℕ
  /-- Number of faces -/
  F : ℕ
  /-- Whether the polyhedron is convex -/
  isConvex : Bool
  /-- Name for display purposes -/
  name : String
  /-- Euler's formula: every combinatorial polyhedron (homeomorphic to S²)
      satisfies V + F = E + 2. This field is a proof obligation at definition time. -/
  euler : V + F = E + 2

/-- DecidableEq for Polyhedron: equality is decided by the data fields;
    the euler proof field is handled by Lean's proof irrelevance. -/
instance : DecidableEq Polyhedron := fun a b =>
  if hV : a.V = b.V then
    if hE : a.E = b.E then
      if hF : a.F = b.F then
        if hC : a.isConvex = b.isConvex then
          if hN : a.name = b.name then
            isTrue (by
              cases a; cases b
              simp only at hV hE hF hC hN
              subst hV; subst hE; subst hF; subst hC; subst hN
              rfl)
          else isFalse (fun h => hN (congrArg Polyhedron.name h))
        else isFalse (fun h => hC (congrArg Polyhedron.isConvex h))
      else isFalse (fun h => hF (congrArg Polyhedron.F h))
    else isFalse (fun h => hE (congrArg Polyhedron.E h))
  else isFalse (fun h => hV (congrArg Polyhedron.V h))

/-- The symmetry type of a polyhedron. -/
inductive SymmetryType where
  | tetrahedral   -- Td, order 24 (with reflections), T order 12 (rotations)
  | octahedral    -- Oh, order 48 (with reflections), O order 24 (rotations)
  | icosahedral   -- Ih, order 120 (with reflections), I order 60 (rotations)
  deriving DecidableEq, Repr

/-- The order of the rotation-only subgroup for each symmetry type. -/
def SymmetryType.rotationOrder : SymmetryType → ℕ
  | .tetrahedral => 12
  | .octahedral => 24
  | .icosahedral => 60

/-- The order of the full symmetry group (including reflections). -/
def SymmetryType.fullOrder : SymmetryType → ℕ
  | .tetrahedral => 24
  | .octahedral => 48
  | .icosahedral => 120

/-! ## Euler's Formula -/

/-- Euler's formula for convex polyhedra: V - E + F = 2. -/
def satisfiesEuler (P : Polyhedron) : Prop :=
  P.V + P.F = P.E + 2

/-! ## The Platonic Solids -/

/-- The regular tetrahedron: 4 vertices, 6 edges, 4 triangular faces. -/
def tetrahedron : Polyhedron :=
  { V := 4, E := 6, F := 4, isConvex := true, name := "Tetrahedron", euler := by norm_num }

/-- The regular octahedron: 6 vertices, 12 edges, 8 triangular faces. -/
def octahedron : Polyhedron :=
  { V := 6, E := 12, F := 8, isConvex := true, name := "Octahedron", euler := by norm_num }

/-- The cube: 8 vertices, 12 edges, 6 square faces. -/
def cube : Polyhedron :=
  { V := 8, E := 12, F := 6, isConvex := true, name := "Cube", euler := by norm_num }

/-- The regular dodecahedron: 20 vertices, 30 edges, 12 pentagonal faces. -/
def dodecahedron : Polyhedron :=
  { V := 20, E := 30, F := 12, isConvex := true, name := "Dodecahedron", euler := by norm_num }

/-- The regular icosahedron: 12 vertices, 30 edges, 20 triangular faces. -/
def icosahedron : Polyhedron :=
  { V := 12, E := 30, F := 20, isConvex := true, name := "Icosahedron", euler := by norm_num }

/-! ## Archimedean Solids (appearing in the journey) -/

/-- The cuboctahedron: 12 vertices, 24 edges, 14 faces (8 tri + 6 sq). -/
def cuboctahedron : Polyhedron :=
  { V := 12, E := 24, F := 14, isConvex := true, name := "Cuboctahedron", euler := by norm_num }

/-- The icosidodecahedron: 30 vertices, 60 edges, 32 faces (20 tri + 12 pent). -/
def icosidodecahedron : Polyhedron :=
  { V := 30, E := 60, F := 32, isConvex := true, name := "Icosidodecahedron",
    euler := by norm_num }

/-- The rhombicosidodecahedron: 60 vertices, 120 edges, 62 faces. -/
def rhombicosidodecahedron : Polyhedron :=
  { V := 60, E := 120, F := 62, isConvex := true, name := "Rhombicosidodecahedron",
    euler := by norm_num }

/-! ## Catalan Solids (duals of Archimedean solids) -/

/-- The rhombic dodecahedron: 14 vertices, 24 edges, 12 rhombic faces. -/
def rhombicDodecahedron : Polyhedron :=
  { V := 14, E := 24, F := 12, isConvex := true, name := "Rhombic Dodecahedron",
    euler := by norm_num }

/-- The rhombic triacontahedron: 32 vertices, 60 edges, 30 golden-rhombic faces. -/
def rhombicTriacontahedron : Polyhedron :=
  { V := 32, E := 60, F := 30, isConvex := true, name := "Rhombic Triacontahedron",
    euler := by norm_num }

/-- The deltoidal hexecontahedron: 62 vertices, 120 edges, 60 kite faces. -/
def deltoidalHexecontahedron : Polyhedron :=
  { V := 62, E := 120, F := 60, isConvex := true, name := "Deltoidal Hexecontahedron",
    euler := by norm_num }

/-! ## Non-convex Polyhedra from Stellation -/

/-- The rhombic hexecontahedron: 62 vertices, 120 edges, 60 golden-rhombic faces.
    This is the non-convex star polyhedron from the stellation sequence.
    Non-convex but topologically spherical: still satisfies V + F = E + 2. -/
def rhombicHexecontahedron : Polyhedron :=
  { V := 62, E := 120, F := 60, isConvex := false, name := "Rhombic Hexecontahedron",
    euler := by norm_num }

/-! ## Euler's Formula Verification -/

-- The satisfiesEuler theorems now follow directly from the euler field baked
-- into each polyhedron definition. No simp needed: the proof is in the struct.
theorem tetrahedron_euler : satisfiesEuler tetrahedron := tetrahedron.euler
theorem octahedron_euler : satisfiesEuler octahedron := octahedron.euler
theorem cube_euler : satisfiesEuler cube := cube.euler
theorem dodecahedron_euler : satisfiesEuler dodecahedron := dodecahedron.euler
theorem icosahedron_euler : satisfiesEuler icosahedron := icosahedron.euler
theorem cuboctahedron_euler : satisfiesEuler cuboctahedron := cuboctahedron.euler
theorem icosidodecahedron_euler : satisfiesEuler icosidodecahedron := icosidodecahedron.euler
theorem rhombicDodecahedron_euler : satisfiesEuler rhombicDodecahedron := rhombicDodecahedron.euler
theorem rhombicTriacontahedron_euler : satisfiesEuler rhombicTriacontahedron :=
  rhombicTriacontahedron.euler
theorem deltoidalHexecontahedron_euler : satisfiesEuler deltoidalHexecontahedron :=
  deltoidalHexecontahedron.euler

/-! ## Polyhedral Operations -/

/-- Rectification places new vertices at edge midpoints.
    A polyhedron with E edges, where each vertex has degree d, produces:
    V' = E, E' = 2E, F' = F + V (original faces + vertex figures). -/
structure RectificationData where
  source : Polyhedron
  target : Polyhedron
  /-- Rectification creates one vertex per edge of the source -/
  vertex_from_edges : target.V = source.E

/-- Dualization swaps vertices and faces.
    The dual P* has V* = F, F* = V, and E* = E. -/
structure DualizationData where
  source : Polyhedron
  target : Polyhedron
  /-- Dual has as many vertices as the source has faces -/
  dual_vertices : target.V = source.F
  /-- Dual has as many faces as the source has vertices -/
  dual_faces : target.F = source.V
  /-- Dual has the same number of edges -/
  dual_edges : target.E = source.E

/-- Stellation extends face planes outward, potentially changing the face count. -/
structure StellationData where
  source : Polyhedron
  target : Polyhedron
  /-- Stellation preserves or changes face count -/
  face_relation : target.F ≥ source.F

/-- Continuous deformation preserves combinatorial type. -/
structure DeformationData where
  source : Polyhedron
  target : Polyhedron
  /-- Same number of vertices -/
  same_vertices : target.V = source.V
  /-- Same number of edges -/
  same_edges : target.E = source.E
  /-- Same number of faces -/
  same_faces : target.F = source.F

/-- Subset extraction selects vertices forming a smaller polyhedron. -/
structure ExtractionData where
  source : Polyhedron
  target : Polyhedron
  /-- The extracted polyhedron has fewer or equal vertices -/
  fewer_vertices : target.V ≤ source.V
