/-
  ForbiddenHarmonics: Formal verification of
  "Every Prime is a Forbidden Harmonic"
  by Shiva Meucci (2026)

  Module structure mirrors the paper's results:
  1. Basic               - Foundational definitions (rotation groups, harmonic data)
  2. ChevalleyDegrees    - Coxeter types and Chevalley degree data
  3. NumericalSemigroup   - Numerical semigroups, Frobenius numbers, gaps
  4. MolienSeries        - Harmonic Molien series and forbidden degree predicate
  5. ForbiddenSets       - Explicit forbidden sets for T, O, I
  6. CountingTheorem     - |G|/4 formula (Theorem 3)
  7. Decomposition       - 7+4+4 decomposition of Forb(I)
  8. Uniqueness          - Saturation and icosahedral uniqueness (Theorem 4)
  9. Simplicity          - A₅ simplicity forces concentration
  10. KleinBridge        - Binary icosahedral group and Klein invariants
  11. ModularForms       - Dimension formula for M_k(SL₂(ℤ))
  12. Splitting          - Quadratic residue checks for p ≤ 29
  13. Synthesis          - Main theorem: complete chain
-/

import ForbiddenHarmonics.Basic
import ForbiddenHarmonics.ChevalleyDegrees
import ForbiddenHarmonics.NumericalSemigroup
import ForbiddenHarmonics.MolienSeries
import ForbiddenHarmonics.ForbiddenSets
import ForbiddenHarmonics.CountingTheorem
import ForbiddenHarmonics.Decomposition
import ForbiddenHarmonics.Uniqueness
import ForbiddenHarmonics.Simplicity
import ForbiddenHarmonics.KleinBridge
import ForbiddenHarmonics.ModularForms
import ForbiddenHarmonics.Splitting
import ForbiddenHarmonics.Synthesis
