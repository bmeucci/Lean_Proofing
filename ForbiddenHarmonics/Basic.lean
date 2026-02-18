/-
  ForbiddenHarmonics/Basic.lean

  Foundational definitions for the formalization of
  "Every Prime is a Forbidden Harmonic" by Shiva Meucci.

  Key definitions:
  - FiniteRotationGroup3D (reused from first project's design)
  - PolyhedralHarmonicData (Chevalley degree pairs for 3D polyhedral groups)
  - Concrete data for T, O, I
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-! ## Finite Rotation Groups in 3D (Klein's Classification) -/

/-- Klein's classification of finite rotation groups in SO(3). -/
inductive FiniteRotationGroup3D where
  | cyclic (n : ℕ) (hn : n ≥ 1) : FiniteRotationGroup3D
  | dihedral (n : ℕ) (hn : n ≥ 2) : FiniteRotationGroup3D
  | tetrahedral : FiniteRotationGroup3D
  | octahedral : FiniteRotationGroup3D
  | icosahedral : FiniteRotationGroup3D
  deriving DecidableEq

namespace FiniteRotationGroup3D

/-- The order (number of elements) of each finite rotation group. -/
def order : FiniteRotationGroup3D → ℕ
  | cyclic n _ => n
  | dihedral n _ => 2 * n
  | tetrahedral => 12
  | octahedral => 24
  | icosahedral => 60

/-- A rotation group is polyhedral if it is tetrahedral, octahedral, or icosahedral. -/
def isPolyhedral : FiniteRotationGroup3D → Bool
  | tetrahedral => true
  | octahedral => true
  | icosahedral => true
  | _ => false

@[simp] theorem tetrahedral_order : tetrahedral.order = 12 := rfl
@[simp] theorem octahedral_order : octahedral.order = 24 := rfl
@[simp] theorem icosahedral_order : icosahedral.order = 60 := rfl

@[simp] theorem tetrahedral_isPolyhedral : tetrahedral.isPolyhedral = true := rfl
@[simp] theorem octahedral_isPolyhedral : octahedral.isPolyhedral = true := rfl
@[simp] theorem icosahedral_isPolyhedral : icosahedral.isPolyhedral = true := rfl

end FiniteRotationGroup3D

/-! ## Polyhedral Harmonic Data

  For a 3D polyhedral rotation group G with parent reflection group W,
  the harmonic Chevalley degrees are (d₁, d₂) where:
  - The parent W has invariant degrees (2, d₁, d₂)
  - d₁ · d₂ = |G|
  - N = d₁ + d₂ - 1 is the Molien exponent
-/

/-- The harmonic Chevalley degrees for a 3D polyhedral group. -/
structure PolyhedralHarmonicData where
  /-- First harmonic generator degree -/
  d₁ : ℕ
  /-- Second harmonic generator degree -/
  d₂ : ℕ
  /-- Group order -/
  groupOrder : ℕ
  /-- Molien exponent N = d₁ + d₂ - 1 -/
  molienExp : ℕ
  /-- d₁ · d₂ = |G| -/
  hProduct : d₁ * d₂ = groupOrder
  /-- N = d₁ + d₂ - 1 -/
  hMolienExp : molienExp = d₁ + d₂ - 1
  /-- d₁ ≥ 2 -/
  hd₁ : d₁ ≥ 2
  /-- d₂ ≥ d₁ -/
  hd₂ : d₂ ≥ d₁

/-- Tetrahedral harmonic data: (d₁, d₂) = (3, 4), N = 6, |T| = 12 -/
def tetrahedralData : PolyhedralHarmonicData where
  d₁ := 3
  d₂ := 4
  groupOrder := 12
  molienExp := 6
  hProduct := by norm_num
  hMolienExp := by norm_num
  hd₁ := by norm_num
  hd₂ := by norm_num

/-- Octahedral harmonic data: (d₁, d₂) = (4, 6), N = 9, |O| = 24 -/
def octahedralData : PolyhedralHarmonicData where
  d₁ := 4
  d₂ := 6
  groupOrder := 24
  molienExp := 9
  hProduct := by norm_num
  hMolienExp := by norm_num
  hd₁ := by norm_num
  hd₂ := by norm_num

/-- Icosahedral harmonic data: (d₁, d₂) = (6, 10), N = 15, |I| = 60 -/
def icosahedralData : PolyhedralHarmonicData where
  d₁ := 6
  d₂ := 10
  groupOrder := 60
  molienExp := 15
  hProduct := by norm_num
  hMolienExp := by norm_num
  hd₁ := by norm_num
  hd₂ := by norm_num

/-! ## Basic verification of harmonic data -/

theorem tetrahedral_product :
    tetrahedralData.d₁ * tetrahedralData.d₂ = 12 := by
  norm_num [tetrahedralData]

theorem octahedral_product :
    octahedralData.d₁ * octahedralData.d₂ = 24 := by
  norm_num [octahedralData]

theorem icosahedral_product :
    icosahedralData.d₁ * icosahedralData.d₂ = 60 := by
  norm_num [icosahedralData]

theorem tetrahedral_N : tetrahedralData.molienExp = 6 := by norm_num [tetrahedralData]
theorem octahedral_N : octahedralData.molienExp = 9 := by norm_num [octahedralData]
theorem icosahedral_N : icosahedralData.molienExp = 15 := by norm_num [icosahedralData]

/-- The gcd of the icosahedral harmonic degrees is 2. -/
theorem icosahedral_gcd : Nat.gcd 6 10 = 2 := by decide

/-- The gcd of the octahedral harmonic degrees is 2. -/
theorem octahedral_gcd : Nat.gcd 4 6 = 2 := by decide

/-- The gcd of the tetrahedral harmonic degrees is 1. -/
theorem tetrahedral_gcd : Nat.gcd 3 4 = 1 := by decide
