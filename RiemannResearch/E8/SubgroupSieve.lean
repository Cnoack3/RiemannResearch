/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.List.Sort
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD
import RiemannResearch.GroupTheory.KernelConjugator
import RiemannResearch.GroupTheory.OrbitDegreeGcd
import RiemannResearch.GroupTheory.PerfectCore

/-!
# The O8+(2) subgroup sieve

This module records the finite certificate data for the subsystem sieve in the
TomLib table of marks for O8+(2) and proves the reusable logical deductions in
Lean.

The certificate was reproduced with GAP 4.16.0 and TomLib 1.2.11. The exact
script, output, versions, and hashes are documented in
`Certificates/O8_PLUS_2_SUBGROUP_SIEVE_CERTIFICATE.md`. The table-of-marks
computation finds
11,171 subgroup classes, 313 classes avoiding the first seven subsystem
stabilizers, and 303 after the (A1)^8 stabilizer is included. Among the 303
classes, 150 have trivial perfect core and the remaining 153 map to 31 perfect
core classes of 14 abstract types.

The orbit-degree conclusion admits a substantially shorter proof than the
original 303-row computation. For any subgroup, its orbits in the three
subsystem coset actions partition sets of cardinalities 135, 11200, and 12096.
Since these totals have gcd one, all orbit degrees have gcd one uniformly.

The Lean declarations below kernel-check the uniform argument, the generic
perfect-core reduction imported above, and the internal consistency of the
finite certificate. Identification of the numerical class positions with the
TomLib table is certified by the separately rerunnable GAP computation. The
matching of the eight selected columns with the geometric E8 subsystem
stabilizers uses Totaro's classification and source-level matching; it is not
a formal construction of the 174,182,400-element group or its root actions in
Lean.

The maximal-overgroup classification is stated up to the full orthogonal
group. `KernelConjugator` supplies the abstract parity correction used to move
a conjugator into the even subgroup without changing the conjugated subsystem
stabilizer.

The correlated Weyl-cover and marker computation, including its shared
triality alignment, is recorded in
`Certificates/O8_PLUS_2_COVER_MARKER_CERTIFICATE.md`.
-/

open scoped BigOperators

namespace RiemannResearch.E8

/-- The three subsystem stabilizer orders in PDF Theorem 5.16 have
the stated indices in the E8 Weyl group. -/
theorem serreIIProgram_fullWeylSubsystem_index_products :
    5160960 * 135 = 696729600 ∧
      62208 * 11200 = 696729600 ∧
      57600 * 12096 = 696729600 := by
  norm_num

/-- The degree-one cycle identity in PDF Corollary 5.17. -/
theorem serreIIProgram_threeSubsystem_bezout :
    (-1417 : ℤ) * 135 + 16 * 11200 + 12096 = 1 := by
  norm_num

/-- The three subsystem degrees in PDF Theorem 5.16 have gcd one. -/
theorem serreIIProgram_threeSubsystem_gcd :
    Nat.gcd (Nat.gcd 135 11200) 12096 = 1 := by
  norm_num

/-- All five displayed Bezout identities in PDF Theorem 6.9. -/
theorem serreIIProgram_survivorEnvelope_bezout :
    (-73 : ℤ) * 135 - 2 * 1120 + 12096 = 1 ∧
      (15 : ℤ) * 15 - 5 * 1120 + 5376 = 1 ∧
      (-17 : ℤ) * 135 - 2 * 1120 + 4536 = 1 ∧
      (-57 : ℤ) * 135 - 2 * 40 + 7776 = 1 ∧
      (13 : ℤ) * 25 - 9 * 36 = 1 := by
  norm_num

/-- The five survivor-envelope degree rows in PDF Theorem 6.9 have gcd one. -/
theorem serreIIProgram_survivorEnvelope_gcd :
    Nat.gcd (Nat.gcd 135 1120) 12096 = 1 ∧
      Nat.gcd (Nat.gcd 15 1120) 5376 = 1 ∧
      Nat.gcd (Nat.gcd 135 1120) 4536 = 1 ∧
      Nat.gcd (Nat.gcd 135 40) 7776 = 1 ∧
      Nat.gcd 25 36 = 1 := by
  norm_num

/-- One of the three triality-related choices of the seven original subsystem
stabilizer columns and the corresponding (A1)^8 column in TomLib. -/
structure SubsystemSieveConfiguration where
  sevenStabilizerClasses : List ℕ
  a1EightClass : ℕ
  deriving DecidableEq, Repr

/-- The three triality-related table-of-marks configurations. -/
def omegaEightPlusTwoSubsystemConfigurations :
    List SubsystemSieveConfiguration := [
  { sevenStabilizerClasses := [11170, 11165, 11164, 11156, 11074, 11155, 11077]
    a1EightClass := 11152 },
  { sevenStabilizerClasses := [11169, 11166, 11163, 11158, 11076, 11155, 11077]
    a1EightClass := 11153 },
  { sevenStabilizerClasses := [11168, 11167, 11162, 11157, 11075, 11155, 11077]
    a1EightClass := 11154 }]

/-- Every triality configuration has exactly seven initial subsystem columns. -/
theorem omegaEightPlusTwoSubsystemConfigurations_shape :
    omegaEightPlusTwoSubsystemConfigurations.length = 3 ∧
      ∀ cfg ∈ omegaEightPlusTwoSubsystemConfigurations,
        cfg.sevenStabilizerClasses.length = 7 := by
  decide

/-- The 303 subsystem-free class positions for the first triality
configuration. TomLib positions are one-based. -/
def omegaEightPlusTwoSubsystemFreeClassPositions : List ℕ :=
  [
    409, 410, 1362, 1363, 1365, 1366, 1374, 1375, 1612, 1613,
    1615, 1616, 1618, 1619, 3659, 3660, 3664, 3665, 4012, 4013,
    4015, 4016, 4021, 4022, 4025, 4026, 4028, 4029, 4030, 4031,
    5927, 5928, 5937, 5938, 5968, 5969, 5971, 5972, 6508, 6509,
    6510, 6511, 6514, 6515, 6523, 6524, 6526, 6527, 6532, 6533,
    6535, 6536, 7682, 7683, 7688, 7689, 7690, 7691, 7693, 7694,
    7724, 7725, 7739, 7740, 7758, 7759, 7760, 7761, 7763, 7764,
    7800, 7801, 7802, 7803, 8444, 8445, 8447, 8448, 8450, 8451,
    8453, 8454, 8456, 8457, 8463, 8464, 9236, 9237, 9245, 9246,
    9248, 9249, 9254, 9255, 9257, 9258, 9263, 9264, 9270, 9271,
    9278, 9279, 9281, 9282, 9285, 9286, 9287, 9288, 9290, 9291,
    9292, 9293, 9329, 9330, 9332, 9333, 9334, 9335, 9338, 9339,
    9340, 9341, 9344, 9345, 9346, 9347, 9669, 9670, 9672, 9673,
    10009, 10010, 10012, 10013, 10039, 10040, 10041, 10042, 10048, 10049,
    10051, 10052, 10093, 10094, 10096, 10097, 10100, 10101, 10102, 10103,
    10104, 10105, 10152, 10153, 10154, 10155, 10157, 10158, 10160, 10161,
    10163, 10164, 10165, 10166, 10379, 10380, 10382, 10383, 10385, 10386,
    10449, 10450, 10492, 10493, 10498, 10499, 10501, 10502, 10503, 10504,
    10510, 10511, 10512, 10513, 10514, 10515, 10516, 10517, 10522, 10523,
    10531, 10532, 10553, 10554, 10555, 10556, 10603, 10604, 10606, 10607,
    10743, 10744, 10746, 10747, 10749, 10750, 10752, 10753, 10782, 10783,
    10784, 10785, 10787, 10788, 10796, 10797, 10798, 10799, 10814, 10815,
    10816, 10817, 10822, 10823, 10825, 10826, 10843, 10844, 10853, 10854,
    10914, 10915, 10916, 10917, 10920, 10921, 10923, 10924, 10925, 10926,
    10929, 10930, 10931, 10932, 10934, 10935, 10943, 10944, 10960, 10961,
    10963, 10964, 10967, 10968, 10997, 10998, 11000, 11001, 11002, 11003,
    11006, 11007, 11009, 11010, 11062, 11063, 11065, 11066, 11075, 11076,
    11102, 11103, 11104, 11105, 11108, 11109, 11111, 11112, 11115, 11116,
    11118, 11119, 11120, 11121, 11134, 11135, 11136, 11137, 11139, 11140,
    11149, 11150, 11157, 11158, 11160, 11161, 11162, 11163, 11166, 11167,
    11168, 11169, 11171,
  ]

/-- The ten additional classes removed by the (A1)^8 stabilizer in the first
triality configuration. -/
def omegaEightPlusTwoRemovedByA1EightClassPositions : List ℕ :=
  [9667, 9668, 10592, 10593, 10912, 11044, 11045, 11058, 11061, 11152]

/-- Kernel-checked row counts, distinctness, disjointness, and table-position
range for the 313 to 303 certificate. -/
theorem omegaEightPlusTwoSubsystemFreeClassPositions_certificate :
    omegaEightPlusTwoSubsystemFreeClassPositions.length = 303 ∧
      omegaEightPlusTwoRemovedByA1EightClassPositions.length = 10 ∧
      (omegaEightPlusTwoSubsystemFreeClassPositions ++
        omegaEightPlusTwoRemovedByA1EightClassPositions).length = 313 ∧
      (omegaEightPlusTwoSubsystemFreeClassPositions ++
        omegaEightPlusTwoRemovedByA1EightClassPositions).Nodup ∧
      (omegaEightPlusTwoSubsystemFreeClassPositions ++
        omegaEightPlusTwoRemovedByA1EightClassPositions).all
          (fun x => decide (1 ≤ x ∧ x ≤ 11171)) = true := by
  refine ⟨by
      set_option maxRecDepth 10000 in
        decide,
    by decide,
    by
      set_option maxRecDepth 10000 in
        decide,
    ?_, ?_⟩
  · have hsurvivors :
        List.IsChain (fun x y : ℕ => x < y)
          omegaEightPlusTwoSubsystemFreeClassPositions := by
      set_option maxRecDepth 10000 in
        decide
    have hremoved :
        List.IsChain (fun x y : ℕ => x < y)
          omegaEightPlusTwoRemovedByA1EightClassPositions := by
      decide
    apply hsurvivors.sortedLT.nodup.append hremoved.sortedLT.nodup
    have hnot : ∀ x,
        x ∈ omegaEightPlusTwoRemovedByA1EightClassPositions →
          x ∉ omegaEightPlusTwoSubsystemFreeClassPositions :=
      List.all_iff_forall_prop.mp (by
        set_option maxRecDepth 10000 in
          decide)
    intro x hxSurvivor hxRemoved
    exact hnot x hxRemoved hxSurvivor
  · set_option maxRecDepth 10000 in
      decide

/-- One perfect-core row in the table-of-marks certificate. -/
structure PerfectCoreClassDatum where
  tableClass : ℕ
  order : ℕ
  multiplicity : ℕ
  deriving DecidableEq, Repr

/-- The 31 perfect core classes for the first triality configuration, with
order and multiplicity among the 153 nonsolvable survivors. -/
def omegaEightPlusTwoPerfectCoreClassData : List PerfectCoreClassDatum := [
  { tableClass := 4012, order := 60, multiplicity := 17 },
  { tableClass := 4013, order := 60, multiplicity := 17 },
  { tableClass := 4015, order := 60, multiplicity := 10 },
  { tableClass := 4016, order := 60, multiplicity := 10 },
  { tableClass := 9329, order := 360, multiplicity := 10 },
  { tableClass := 9330, order := 360, multiplicity := 10 },
  { tableClass := 10379, order := 960, multiplicity := 11 },
  { tableClass := 10380, order := 960, multiplicity := 11 },
  { tableClass := 10743, order := 1920, multiplicity := 5 },
  { tableClass := 10744, order := 1920, multiplicity := 5 },
  { tableClass := 10843, order := 2520, multiplicity := 2 },
  { tableClass := 10844, order := 2520, multiplicity := 2 },
  { tableClass := 10914, order := 3600, multiplicity := 5 },
  { tableClass := 10915, order := 3600, multiplicity := 5 },
  { tableClass := 11062, order := 11520, multiplicity := 5 },
  { tableClass := 11063, order := 11520, multiplicity := 5 },
  { tableClass := 11102, order := 20160, multiplicity := 2 },
  { tableClass := 11103, order := 20160, multiplicity := 2 },
  { tableClass := 11104, order := 20160, multiplicity := 1 },
  { tableClass := 11105, order := 20160, multiplicity := 1 },
  { tableClass := 11120, order := 25920, multiplicity := 4 },
  { tableClass := 11121, order := 25920, multiplicity := 4 },
  { tableClass := 11160, order := 161280, multiplicity := 1 },
  { tableClass := 11161, order := 161280, multiplicity := 1 },
  { tableClass := 11162, order := 181440, multiplicity := 1 },
  { tableClass := 11163, order := 181440, multiplicity := 1 },
  { tableClass := 11166, order := 1290240, multiplicity := 1 },
  { tableClass := 11167, order := 1290240, multiplicity := 1 },
  { tableClass := 11168, order := 1451520, multiplicity := 1 },
  { tableClass := 11169, order := 1451520, multiplicity := 1 },
  { tableClass := 11171, order := 174182400, multiplicity := 1 }]

/-- Kernel-checked internal consistency of the perfect-core compression:
31 core classes, total multiplicity 153, and 14 distinct core orders. -/
theorem omegaEightPlusTwoPerfectCoreClassData_certificate :
    omegaEightPlusTwoPerfectCoreClassData.length = 31 ∧
      (omegaEightPlusTwoPerfectCoreClassData.map
        (fun row => row.tableClass)).Nodup ∧
      (omegaEightPlusTwoPerfectCoreClassData.map
        (fun row => row.multiplicity)).sum = 153 ∧
      (omegaEightPlusTwoPerfectCoreClassData.map
        (fun row => row.order)).toFinset.card = 14 ∧
      ∀ row ∈ omegaEightPlusTwoPerfectCoreClassData,
        row.tableClass ∈ omegaEightPlusTwoSubsystemFreeClassPositions := by
  decide

/-- The smallest projective perfect-core order in the certificate is 60. -/
theorem omegaEightPlusTwoPerfectCoreClassData_order_floor :
    (∃ row ∈ omegaEightPlusTwoPerfectCoreClassData, row.order = 60) ∧
      ∀ row ∈ omegaEightPlusTwoPerfectCoreClassData, 60 ≤ row.order := by
  decide

/-- The certificate multiplicities give the displayed 150 + 153 = 303
compression. -/
theorem omegaEightPlusTwoPerfectCore_compression_count :
    150 + (omegaEightPlusTwoPerfectCoreClassData.map
      (fun row => row.multiplicity)).sum = 303 := by
  decide

/-- One row of the joint Weyl-cover and mod-two marker certificate. The table
class is recorded only after the cover and module have been aligned with the
same TomLib isomorphism; triality may permute these positions between runs. -/
structure PerfectCoreLiftDatum where
  tableClass : ℕ
  projectiveOrder : ℕ
  liftOrder : ℕ
  derivedOrder : ℕ
  fixedModTwoDimension : ℕ
  deriving DecidableEq, Repr

/-- The 31 rows selected by one triality-aligned run of the joint certificate.
The GAP script dynamically finds the aligned triality configuration. -/
def omegaEightPlusTwoPerfectCoreLiftData : List PerfectCoreLiftDatum := [
  { tableClass := 4013, projectiveOrder := 60, liftOrder := 120,
    derivedOrder := 120, fixedModTwoDimension := 0 },
  { tableClass := 4014, projectiveOrder := 60, liftOrder := 120,
    derivedOrder := 120, fixedModTwoDimension := 0 },
  { tableClass := 4015, projectiveOrder := 60, liftOrder := 120,
    derivedOrder := 120, fixedModTwoDimension := 0 },
  { tableClass := 4017, projectiveOrder := 60, liftOrder := 120,
    derivedOrder := 120, fixedModTwoDimension := 0 },
  { tableClass := 9329, projectiveOrder := 360, liftOrder := 720,
    derivedOrder := 720, fixedModTwoDimension := 0 },
  { tableClass := 9331, projectiveOrder := 360, liftOrder := 720,
    derivedOrder := 720, fixedModTwoDimension := 0 },
  { tableClass := 10378, projectiveOrder := 960, liftOrder := 1920,
    derivedOrder := 1920, fixedModTwoDimension := 0 },
  { tableClass := 10380, projectiveOrder := 960, liftOrder := 1920,
    derivedOrder := 1920, fixedModTwoDimension := 0 },
  { tableClass := 10744, projectiveOrder := 1920, liftOrder := 3840,
    derivedOrder := 3840, fixedModTwoDimension := 0 },
  { tableClass := 10745, projectiveOrder := 1920, liftOrder := 3840,
    derivedOrder := 3840, fixedModTwoDimension := 0 },
  { tableClass := 10843, projectiveOrder := 2520, liftOrder := 5040,
    derivedOrder := 5040, fixedModTwoDimension := 0 },
  { tableClass := 10845, projectiveOrder := 2520, liftOrder := 5040,
    derivedOrder := 5040, fixedModTwoDimension := 0 },
  { tableClass := 10913, projectiveOrder := 3600, liftOrder := 7200,
    derivedOrder := 7200, fixedModTwoDimension := 0 },
  { tableClass := 10914, projectiveOrder := 3600, liftOrder := 7200,
    derivedOrder := 7200, fixedModTwoDimension := 0 },
  { tableClass := 11063, projectiveOrder := 11520, liftOrder := 23040,
    derivedOrder := 23040, fixedModTwoDimension := 0 },
  { tableClass := 11064, projectiveOrder := 11520, liftOrder := 23040,
    derivedOrder := 23040, fixedModTwoDimension := 0 },
  { tableClass := 11102, projectiveOrder := 20160, liftOrder := 40320,
    derivedOrder := 40320, fixedModTwoDimension := 0 },
  { tableClass := 11104, projectiveOrder := 20160, liftOrder := 40320,
    derivedOrder := 40320, fixedModTwoDimension := 0 },
  { tableClass := 11106, projectiveOrder := 20160, liftOrder := 40320,
    derivedOrder := 40320, fixedModTwoDimension := 0 },
  { tableClass := 11107, projectiveOrder := 20160, liftOrder := 40320,
    derivedOrder := 40320, fixedModTwoDimension := 0 },
  { tableClass := 11121, projectiveOrder := 25920, liftOrder := 51840,
    derivedOrder := 51840, fixedModTwoDimension := 0 },
  { tableClass := 11122, projectiveOrder := 25920, liftOrder := 51840,
    derivedOrder := 51840, fixedModTwoDimension := 0 },
  { tableClass := 11159, projectiveOrder := 161280, liftOrder := 322560,
    derivedOrder := 322560, fixedModTwoDimension := 0 },
  { tableClass := 11161, projectiveOrder := 161280, liftOrder := 322560,
    derivedOrder := 322560, fixedModTwoDimension := 0 },
  { tableClass := 11162, projectiveOrder := 181440, liftOrder := 362880,
    derivedOrder := 362880, fixedModTwoDimension := 0 },
  { tableClass := 11164, projectiveOrder := 181440, liftOrder := 362880,
    derivedOrder := 362880, fixedModTwoDimension := 0 },
  { tableClass := 11165, projectiveOrder := 1290240, liftOrder := 2580480,
    derivedOrder := 2580480, fixedModTwoDimension := 0 },
  { tableClass := 11167, projectiveOrder := 1290240, liftOrder := 2580480,
    derivedOrder := 2580480, fixedModTwoDimension := 0 },
  { tableClass := 11168, projectiveOrder := 1451520, liftOrder := 2903040,
    derivedOrder := 2903040, fixedModTwoDimension := 0 },
  { tableClass := 11170, projectiveOrder := 1451520, liftOrder := 2903040,
    derivedOrder := 2903040, fixedModTwoDimension := 0 },
  { tableClass := 11171, projectiveOrder := 174182400,
    liftOrder := 348364800, derivedOrder := 348364800,
    fixedModTwoDimension := 0 }]

/-- Kernel-checked consistency of the 31 joint certificate rows. Equality of
the lift and derived orders is the finite datum used by the external
central-extension nonsplitting criterion; fixed dimension zero is the datum
used by the marker-freeness criterion. -/
theorem omegaEightPlusTwoPerfectCoreLiftData_certificate :
    omegaEightPlusTwoPerfectCoreLiftData.length = 31 ∧
      (omegaEightPlusTwoPerfectCoreLiftData.map
        (fun row => row.tableClass)).Nodup ∧
      ∀ row ∈ omegaEightPlusTwoPerfectCoreLiftData,
        row.liftOrder = 2 * row.projectiveOrder ∧
          row.derivedOrder = row.liftOrder ∧
          row.fixedModTwoDimension = 0 := by
  decide

/-- The smallest actual residual lift in the joint certificate has order 120. -/
theorem omegaEightPlusTwoPerfectCoreLiftData_order_floor :
    (∃ row ∈ omegaEightPlusTwoPerfectCoreLiftData, row.liftOrder = 120) ∧
      ∀ row ∈ omegaEightPlusTwoPerfectCoreLiftData, 120 ≤ row.liftOrder := by
  decide

/-- Given the three finite orbit packets arising by restricting the indicated
O8+(2) coset actions to a subgroup, any common divisor of all their degrees is
one. The signature deliberately takes the orbit-indexing types and their
partition-sum identities as inputs; construction of those actions is outside
this arithmetic certificate. -/
theorem omegaEightPlusTwo_subsystemOrbitDegree_commonDivisor_eq_one
    {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    {d₁ : ι₁ → ℕ} {d₂ : ι₂ → ℕ} {d₃ : ι₃ → ℕ} {c : ℕ}
    (hc₁ : ∀ i, c ∣ d₁ i) (hc₂ : ∀ i, c ∣ d₂ i)
    (hc₃ : ∀ i, c ∣ d₃ i)
    (h₁ : ∑ i, d₁ i = 135) (h₂ : ∑ i, d₂ i = 11200)
    (h₃ : ∑ i, d₃ i = 12096) :
    c = 1 := by
  exact RiemannResearch.GroupTheory.eq_one_of_dvd_three_partition_degrees
    hc₁ hc₂ hc₃ h₁ h₂ h₃ serreIIProgram_threeSubsystem_gcd

end RiemannResearch.E8
