/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.List.Sort

/-!
# Binary-icosahedral subsystem-orbit certificate

This module records the compressed orbit histograms obtained by restricting
the two indicated O8+(2) subsystem coset actions to the four triality-aligned
projective A5 rows in TomLib. The external table-of-marks calculation is
documented, with a rerunnable script and raw output, in
Certificates/A5_SUBSYSTEM_ORBITS_CERTIFICATE.md.

Lean checks the internal finite certificate: the row labels, full coset-action
degrees, distinct histogram keys, degree-five and degree-six multiplicities,
and the total of twelve degree-five (D4)^2 orbits. Identification of the
TomLib rows with the geometric E8 subsystem actions remains at the external
certificate boundary. This file does not assert the outer-triality conclusion
for the order-three stabilizer action on the individual D4 factors.
-/

namespace RiemannResearch.E8

/-- Compressed subsystem-orbit data for one projective binary-icosahedral
row. A histogram entry (degree, multiplicity) records that many orbits of
the given degree. -/
structure A5SubsystemOrbitDatum where
  tableClass : ℕ
  d4d4OrbitHistogram : List (ℕ × ℕ)
  a4a4OrbitHistogram : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Total cardinality represented by a compressed orbit histogram. -/
def orbitHistogramTotal (histogram : List (ℕ × ℕ)) : ℕ :=
  (histogram.map fun entry => entry.1 * entry.2).sum

/-- Multiplicity of a specified orbit degree in a compressed histogram. -/
def orbitDegreeMultiplicity (degree : ℕ) (histogram : List (ℕ × ℕ)) : ℕ :=
  ((histogram.filter fun entry => entry.1 = degree).map Prod.snd).sum

/-- The four projective A5 rows and their compressed (D4)^2 and (A4)^2
subsystem-orbit histograms. TomLib positions are one-based. -/
def binaryIcosahedralSubsystemOrbitData : List A5SubsystemOrbitDatum := [
  { tableClass := 4013
    d4d4OrbitHistogram :=
      [(5, 5), (10, 15), (15, 10), (20, 10), (30, 15), (60, 10)]
    a4a4OrbitHistogram := [(6, 6), (30, 90), (60, 156)] },
  { tableClass := 4014
    d4d4OrbitHistogram :=
      [(5, 5), (10, 15), (15, 10), (20, 10), (30, 15), (60, 10)]
    a4a4OrbitHistogram := [(6, 6), (30, 90), (60, 156)] },
  { tableClass := 4015
    d4d4OrbitHistogram := [(5, 1), (10, 7), (15, 6), (30, 31), (60, 8)]
    a4a4OrbitHistogram := [(6, 6), (10, 6), (20, 6), (30, 84), (60, 156)] },
  { tableClass := 4017
    d4d4OrbitHistogram := [(5, 1), (10, 7), (15, 6), (30, 31), (60, 8)]
    a4a4OrbitHistogram := [(6, 6), (10, 6), (20, 6), (30, 84), (60, 156)] }
]

/-- Kernel-checked consistency of the compressed table-of-marks data. The
histogram totals are the full coset-action degrees. -/
theorem binaryIcosahedralSubsystemOrbitData_certificate :
    (binaryIcosahedralSubsystemOrbitData.map fun row => row.tableClass) =
        [4013, 4014, 4015, 4017] ∧
      (binaryIcosahedralSubsystemOrbitData.map fun row =>
        orbitHistogramTotal row.d4d4OrbitHistogram) =
          [1575, 1575, 1575, 1575] ∧
      (binaryIcosahedralSubsystemOrbitData.map fun row =>
        orbitHistogramTotal row.a4a4OrbitHistogram) =
          [12096, 12096, 12096, 12096] ∧
      ∀ row ∈ binaryIcosahedralSubsystemOrbitData,
        (row.d4d4OrbitHistogram.map Prod.fst).Nodup ∧
          (row.a4a4OrbitHistogram.map Prod.fst).Nodup := by
  decide

/-- The four projective A5 rows have respectively 5, 5, 1, and 1
degree-five (D4)^2 subsystem orbits. This is the numerical orbit count in
PDF Proposition 6.17. -/
theorem binaryIcosahedral_degreeFiveOrbit_multiplicities :
    (binaryIcosahedralSubsystemOrbitData.map fun row =>
      orbitDegreeMultiplicity 5 row.d4d4OrbitHistogram) = [5, 5, 1, 1] := by
  decide

/-- Every projective A5 row has six degree-six (A4)^2 subsystem orbits. -/
theorem binaryIcosahedral_degreeSixOrbit_multiplicities :
    (binaryIcosahedralSubsystemOrbitData.map fun row =>
      orbitDegreeMultiplicity 6 row.a4a4OrbitHistogram) = [6, 6, 6, 6] := by
  decide

/-- There are twelve degree-five (D4)^2 orbits across the four projective
A5 rows. -/
theorem binaryIcosahedral_degreeFiveOrbit_total :
    (binaryIcosahedralSubsystemOrbitData.map fun row =>
      orbitDegreeMultiplicity 5 row.d4d4OrbitHistogram).sum = 12 := by
  decide

/-- Each of the four projective A5 rows has both a degree-five (D4)^2
orbit and a degree-six (A4)^2 orbit, the finite orbit input to PDF
Proposition 6.16. -/
theorem binaryIcosahedralSubsystemOrbitData_has_small_orbits :
    ∀ row ∈ binaryIcosahedralSubsystemOrbitData,
      0 < orbitDegreeMultiplicity 5 row.d4d4OrbitHistogram ∧
        0 < orbitDegreeMultiplicity 6 row.a4a4OrbitHistogram := by
  decide

end RiemannResearch.E8
