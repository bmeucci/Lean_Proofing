/-
  LeanProofing: Formal verification of
  "The Golden-Ratio Polyhedral Journey: A Complete Forward Loop from
   Tetrahedron to Maximum Complexity and Return"
  by Shiva Meucci (January 2026)

  Module structure mirrors the paper's sections:
  1. GoldenRatio       - Number-theoretic foundation (Section 3)
  2. FiniteGroups       - Finite rotation groups and orbit-stabilizer (Section 4)
  3. Polyhedra          - Combinatorial polyhedral definitions
  4. PlatonicSpine      - Phase I: Tetra → Octa → Cube → CO → RD (Section 5)
  5. IcosahedralTransition - Phase II: Coset completion to icosahedral (Section 6)
  6. Stellation         - Phase III: Golden scaling to 60-face saturation (Section 7)
  7. ForwardReturn      - Phase IV: Harmonic relaxation and return (Section 11)
  8. Incommensurability - Non-periodic closure (Section 12)
  9. Synthesis          - Complete forward loop theorem (Section 13)
-/

import LeanProofing.GoldenRatio
import LeanProofing.FiniteGroups
import LeanProofing.Polyhedra
import LeanProofing.PlatonicSpine
import LeanProofing.IcosahedralTransition
import LeanProofing.Stellation
import LeanProofing.ForwardReturn
import LeanProofing.Incommensurability
import LeanProofing.Synthesis
