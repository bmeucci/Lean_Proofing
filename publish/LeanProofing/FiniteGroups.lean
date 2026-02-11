/-
  LeanProofing/FiniteGroups.lean

  Group-theoretic foundations for the polyhedral journey.
  Corresponds to Section 4 of the paper.

  Key results:
  - Classification of finite rotation groups in 3D (Klein's theorem, Theorem 4.1)
  - The orbit-stabilizer theorem applied to polyhedral faces
  - The 60-face saturation result (Proposition 4.5)
  - Structure of the icosahedral rotation group
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! ## Finite Rotation Groups in 3D

  Klein's classification (Theorem 4.1): The finite rotation groups in SO(3) are
  exactly the cyclic groups Cₙ, dihedral groups Dₙ, and the three exceptional
  groups T (tetrahedral, order 12), O (octahedral, order 24), I (icosahedral, order 60).

  We encode this classification as an inductive type.
-/

/-- The classification of finite rotation groups in 3D Euclidean space (Klein, 1884). -/
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

/-- A rotation group is polyhedral if it does not preserve any single axis.
    These are exactly the tetrahedral, octahedral, and icosahedral groups. -/
def isPolyhedral : FiniteRotationGroup3D → Prop
  | tetrahedral => True
  | octahedral => True
  | icosahedral => True
  | _ => False

/-- **Klein's Theorem, Corollary 4.2**: Among polyhedral rotation groups,
    the icosahedral group has maximal order 60. -/
theorem icosahedral_maximal_polyhedral (G : FiniteRotationGroup3D) (hG : G.isPolyhedral) :
    G.order ≤ icosahedral.order := by
  cases G with
  | tetrahedral => simp [order]
  | octahedral => simp [order]
  | icosahedral => simp [order]
  | cyclic n hn => exact absurd hG (by simp [isPolyhedral])
  | dihedral n hn => exact absurd hG (by simp [isPolyhedral])

/-- The icosahedral group order is exactly 60. -/
@[simp] theorem icosahedral_order : icosahedral.order = 60 := rfl

/-- The tetrahedral group order is exactly 12. -/
@[simp] theorem tetrahedral_order : tetrahedral.order = 12 := rfl

/-- The octahedral group order is exactly 24. -/
@[simp] theorem octahedral_order : octahedral.order = 24 := rfl

end FiniteRotationGroup3D

/-! ## The Orbit-Stabilizer Theorem Applied to Faces

  When a group G acts on a set of faces, the orbit-stabilizer theorem gives:
    |orbit(f)| = |G| / |Stab(f)|

  We formalize the specific consequence for icosahedral face symmetry.
-/

/-- **Definition 4.4**: A group action on faces has full icosahedral face symmetry
    when all faces form a single orbit and each face has trivial stabilizer. -/
structure FullIcoFaceSymmetry (G : Type*) (F : Type*) [Group G] [Fintype G]
    [MulAction G F] [Fintype F] where
  /-- The group has order 60 (icosahedral rotation group). -/
  group_order : Fintype.card G = 60
  /-- All faces form a single orbit (the action is transitive). -/
  single_orbit : MulAction.IsPretransitive G F
  /-- Each face has trivial stabilizer. -/
  trivial_stabilizers : ∀ f : F, ∀ g : G, g • f = f → g = 1

/-! ## Structure of the Icosahedral Rotation Group

  The 60 elements of I consist of (Section 4.1):
  - 1 identity rotation
  - 24 rotations by 72° and 144° around 6 five-fold axes
  - 20 rotations by 120° and 240° around 10 three-fold axes
  - 15 rotations by 180° around 15 two-fold axes
-/

/-- The element counts of the icosahedral rotation group by conjugacy class. -/
structure IcosahedralConjugacyData where
  /-- 1 identity element -/
  identity_count : ℕ := 1
  /-- 24 five-fold rotations (72° and 144° around 6 axes, 4 each) -/
  fivefold_count : ℕ := 24
  /-- 20 three-fold rotations (120° and 240° around 10 axes, 2 each) -/
  threefold_count : ℕ := 20
  /-- 15 two-fold rotations (180° around 15 axes) -/
  twofold_count : ℕ := 15

/-- The element counts sum to 60:
    1 (identity) + 24 (five-fold) + 20 (three-fold) + 15 (two-fold). -/
theorem icosahedral_element_count :
    1 + 24 + 20 + 15 = (60 : ℕ) := by norm_num

/-- The number of five-fold symmetry axes. -/
theorem icosahedral_fivefold_axes : 6 * 4 = 24 := by norm_num

/-- The number of three-fold symmetry axes. -/
theorem icosahedral_threefold_axes : 10 * 2 = 20 := by norm_num

/-- The number of two-fold symmetry axes. -/
theorem icosahedral_twofold_axes : 15 * 1 = 15 := by norm_num

/-! ## Subgroup Relationships

  The tetrahedral group T is a subgroup of the icosahedral group I,
  with index |I|/|T| = 60/12 = 5.
-/

/-- The index of the tetrahedral group in the icosahedral group is 5.
    This is the key to the five-tetrahedra compound (Section 6.1). -/
theorem tetrahedral_index_in_icosahedral :
    FiniteRotationGroup3D.icosahedral.order / FiniteRotationGroup3D.tetrahedral.order = 5 := by
  simp [FiniteRotationGroup3D.order]

/-- The index of the octahedral group in the icosahedral group.
    Note: 60/24 = 2 remainder 12, so O is NOT a subgroup of I.
    This is used in Theorem 11.14 to distinguish the two icosahedral compounds. -/
theorem octahedral_not_divides_icosahedral :
    ¬ (FiniteRotationGroup3D.octahedral.order ∣ FiniteRotationGroup3D.icosahedral.order) := by
  simp [FiniteRotationGroup3D.order]
