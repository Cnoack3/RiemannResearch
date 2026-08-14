/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Data.ZMod.Basic
import RiemannResearch.E8.GroupSchemeFoundation
import RiemannResearch.E8.SubgroupSieve

/-!
# Matrices for the thirty-one perfect-core survivors in O8+(2)

This module imports the sixty-four integral generator matrices in the
fundamental-weight basis for the thirty-one rows of
`omegaEightPlusTwoPerfectCoreLiftData`.  The matrices act on row vectors from
the right.  Their simple-root/coroot-basis matrices are deliberately not
duplicated: `rootBasisMatrix` derives them by conjugating with the E8 Cartan
matrix and its integral inverse.

The persisted finite checks below certify the table alignment, matrix count,
and preservation of the E8 weight Gram matrix.  Executable definitions also
expose determinant, generator-order, quadratic-form, and fixed-vector checks
for follow-up certificates without duplicating the data.  This module does not
certify the orders of the generated groups or identify the abstract perfect
cores; those remain the separate GAP/TomLib/SLA calculation recorded by the
surrounding development.

Source: the user-supplied aligned GAP/TomLib/SLA export, matrix payload SHA-256
`6ef5273be299f2a62fea298728d87e93e08a9e2924f404531e3f6619090c61e2`
(14 August 2026).  Lean independently evaluates all local matrix and mod-two
claims stated in this module.
-/

open Matrix

namespace RiemannResearch.E8.PerfectCoreMatrixCertificate

abbrev I8 := Fin 8
abbrev Mat8 := Matrix I8 I8 ℤ
abbrev F2 := ZMod 2
abbrev Vec8F2 := I8 → F2
abbrev Mat8F2 := Matrix I8 I8 F2

/-- One integral generator and its claimed exact order. -/
structure GeneratorDatum where
  order : ℕ
  matrix : Mat8
  deriving DecidableEq

/-- Matrix data aligned with one row of the perfect-core lift table. -/
structure PerfectCoreMatrixDatum where
  tableClass : ℕ
  projectiveOrder : ℕ
  liftOrder : ℕ
  generators : List GeneratorDatum
  deriving DecidableEq

/-- The thirty-one aligned rows, containing sixty-four weight-basis matrices. -/
def perfectCoreMatrixData : List PerfectCoreMatrixDatum := [
  { tableClass := 4013, projectiveOrder := 60, liftOrder := 120,
    generators := [
      { order := 10, matrix := ![
              ![-1, 1, 2, -1, 0, 0, -1, 0],
              ![-1, 2, 2, -1, 0, -1, -1, 0],
              ![-2, 2, 3, -1, 0, -1, -2, 1],
              ![-3, 3, 4, -1, 0, -2, -2, 0],
              ![-3, 3, 3, -1, 0, -1, -2, 0],
              ![-2, 2, 2, 0, -1, 0, -2, 0],
              ![-1, 2, 1, 0, -1, 0, -1, 0],
              ![0, 1, 0, 0, 0, 0, -1, 0]
            ] },
      { order := 4, matrix := ![
              ![-1, 0, 2, -2, 1, 1, -1, 0],
              ![-1, 1, 3, -3, 1, 1, -1, -1],
              ![-2, 1, 4, -4, 2, 1, -2, 0],
              ![-3, 2, 6, -6, 3, 1, -2, -1],
              ![-3, 2, 5, -5, 2, 1, -1, -1],
              ![-3, 1, 4, -3, 1, 1, -1, -1],
              ![-2, 1, 3, -2, 0, 1, -1, 0],
              ![-1, 1, 1, -1, 0, 1, -1, 0]
            ] }
    ] },
  { tableClass := 4014, projectiveOrder := 60, liftOrder := 120,
    generators := [
      { order := 10, matrix := ![
              ![1, 1, -1, 0, 1, -2, 1, -1],
              ![1, 2, -1, 0, 1, -3, 1, 0],
              ![2, 2, -1, 0, 1, -4, 2, -1],
              ![3, 3, -2, 0, 2, -6, 3, -1],
              ![2, 2, -1, 0, 2, -5, 2, -1],
              ![2, 2, -1, 0, 1, -3, 1, -1],
              ![1, 2, 0, -1, 1, -2, 1, -1],
              ![1, 1, 0, -1, 1, -1, 0, 0]
            ] },
      { order := 4, matrix := ![
              ![-1, 1, 1, 0, 0, -1, 0, -1],
              ![-2, 1, 2, 0, 0, -2, 0, 0],
              ![-2, 1, 2, 1, -1, -2, 0, -1],
              ![-3, 2, 3, 1, -1, -4, 1, -1],
              ![-3, 1, 3, 1, -1, -3, 1, -1],
              ![-2, 1, 2, 1, -1, -2, 0, 0],
              ![-1, 1, 2, 0, -1, -1, 0, 0],
              ![0, 0, 1, 0, 0, -1, 0, 0]
            ] }
    ] },
  { tableClass := 4015, projectiveOrder := 60, liftOrder := 120,
    generators := [
      { order := 5, matrix := ![
              ![0, 0, 1, -1, -1, 1, 1, 0],
              ![-1, -1, 2, -1, -1, 1, 2, -1],
              ![0, -1, 2, -2, -1, 2, 2, -1],
              ![-1, -2, 4, -3, -1, 2, 3, -1],
              ![0, -2, 3, -2, -1, 1, 3, -1],
              ![0, -1, 2, -2, 0, 0, 3, -1],
              ![0, -1, 1, -1, 0, 0, 2, -1],
              ![0, 0, 1, -1, 0, 0, 1, -1]
            ] },
      { order := 4, matrix := ![
              ![0, 1, 1, -1, 1, -1, -1, 0],
              ![1, 2, 0, -1, 1, -1, -2, 1],
              ![0, 3, 1, -2, 2, -2, -2, 1],
              ![1, 4, 1, -2, 2, -3, -3, 2],
              ![1, 3, 0, -1, 2, -3, -2, 1],
              ![1, 2, 0, -1, 2, -2, -2, 1],
              ![1, 2, 0, -1, 1, -1, -1, 0],
              ![1, 1, 0, -1, 1, -1, 0, 0]
            ] }
    ] },
  { tableClass := 4017, projectiveOrder := 60, liftOrder := 120,
    generators := [
      { order := 5, matrix := ![
              ![-2, -1, 1, 0, 0, 1, 0, -1],
              ![-2, -1, 2, -1, 0, 1, 1, -2],
              ![-3, -2, 2, -1, 1, 1, 1, -2],
              ![-4, -2, 3, -2, 1, 2, 1, -3],
              ![-3, -2, 2, -1, 0, 2, 1, -2],
              ![-3, -1, 2, -1, 0, 1, 1, -1],
              ![-2, -1, 1, 0, 0, 0, 1, -1],
              ![-1, 0, 0, 0, 0, 0, 1, -1]
            ] },
      { order := 4, matrix := ![
              ![1, 1, -1, -1, 1, -1, 2, -1],
              ![1, 1, -1, -2, 3, -2, 2, -1],
              ![2, 2, -1, -3, 3, -2, 3, -2],
              ![2, 2, -1, -4, 5, -4, 5, -3],
              ![2, 1, -1, -3, 4, -3, 4, -3],
              ![1, 1, -1, -2, 3, -2, 3, -3],
              ![0, 1, 0, -2, 2, -1, 2, -2],
              ![0, 0, 0, -1, 1, 0, 1, -1]
            ] }
    ] },
  { tableClass := 9329, projectiveOrder := 360, liftOrder := 720,
    generators := [
      { order := 10, matrix := ![
              ![0, 0, 2, -2, 1, 0, 0, -1],
              ![1, 0, 2, -2, 1, 0, 0, -2],
              ![0, 0, 4, -3, 1, 0, 0, -2],
              ![1, -1, 5, -4, 2, 0, 0, -3],
              ![0, -1, 4, -3, 2, 0, 0, -3],
              ![0, -1, 3, -2, 1, 1, -1, -2],
              ![0, -1, 2, -1, 0, 1, 0, -2],
              ![0, 0, 1, -1, 0, 1, 0, -1]
            ] },
      { order := 4, matrix := ![
              ![0, 1, 1, -1, 1, -1, -1, 0],
              ![1, 2, 0, -1, 1, -1, -2, 1],
              ![0, 3, 1, -2, 2, -2, -2, 1],
              ![1, 4, 1, -2, 2, -3, -3, 2],
              ![1, 3, 0, -1, 2, -3, -2, 1],
              ![1, 2, 0, -1, 2, -2, -2, 1],
              ![1, 2, 0, -1, 1, -1, -1, 0],
              ![1, 1, 0, -1, 1, -1, 0, 0]
            ] }
    ] },
  { tableClass := 9331, projectiveOrder := 360, liftOrder := 720,
    generators := [
      { order := 10, matrix := ![
              ![0, 1, 1, -2, 1, 1, -1, -1],
              ![0, 1, 1, -2, 2, 0, -1, -2],
              ![0, 1, 2, -3, 2, 1, -2, -2],
              ![0, 1, 3, -4, 3, 1, -2, -4],
              ![0, 0, 2, -3, 3, 1, -2, -3],
              ![-1, 0, 2, -2, 2, 1, -2, -2],
              ![-1, 0, 2, -2, 2, 0, -1, -1],
              ![0, 0, 1, -1, 1, 0, -1, 0]
            ] },
      { order := 4, matrix := ![
              ![1, 1, -1, -1, 1, -1, 2, -1],
              ![1, 1, -1, -2, 3, -2, 2, -1],
              ![2, 2, -1, -3, 3, -2, 3, -2],
              ![2, 2, -1, -4, 5, -4, 5, -3],
              ![2, 1, -1, -3, 4, -3, 4, -3],
              ![1, 1, -1, -2, 3, -2, 3, -3],
              ![0, 1, 0, -2, 2, -1, 2, -2],
              ![0, 0, 0, -1, 1, 0, 1, -1]
            ] }
    ] },
  { tableClass := 10378, projectiveOrder := 960, liftOrder := 1920,
    generators := [
      { order := 4, matrix := ![
              ![1, 1, -1, -1, 1, -1, 2, -1],
              ![1, 1, -1, -2, 3, -2, 2, -1],
              ![2, 2, -1, -3, 3, -2, 3, -2],
              ![2, 2, -1, -4, 5, -4, 5, -3],
              ![2, 1, -1, -3, 4, -3, 4, -3],
              ![1, 1, -1, -2, 3, -2, 3, -3],
              ![0, 1, 0, -2, 2, -1, 2, -2],
              ![0, 0, 0, -1, 1, 0, 1, -1]
            ] },
      { order := 12, matrix := ![
              ![0, -1, 0, 1, 0, -1, 1, 0],
              ![1, -2, 0, 1, 1, -2, 1, 0],
              ![1, -2, 0, 1, 1, -2, 1, 1],
              ![1, -3, 1, 1, 2, -4, 2, 1],
              ![1, -3, 1, 1, 1, -3, 2, 1],
              ![1, -2, 1, 0, 1, -2, 2, 0],
              ![1, -1, 0, 0, 1, -2, 2, 0],
              ![0, -1, 0, 0, 1, -1, 1, 0]
            ] }
    ] },
  { tableClass := 10380, projectiveOrder := 960, liftOrder := 1920,
    generators := [
      { order := 4, matrix := ![
              ![0, 1, 1, -1, 1, -1, -1, 0],
              ![1, 2, 0, -1, 1, -1, -2, 1],
              ![0, 3, 1, -2, 2, -2, -2, 1],
              ![1, 4, 1, -2, 2, -3, -3, 2],
              ![1, 3, 0, -1, 2, -3, -2, 1],
              ![1, 2, 0, -1, 2, -2, -2, 1],
              ![1, 2, 0, -1, 1, -1, -1, 0],
              ![1, 1, 0, -1, 1, -1, 0, 0]
            ] },
      { order := 12, matrix := ![
              ![0, 1, 0, 0, 0, -1, 1, 0],
              ![-1, 2, 1, -1, 0, -1, 1, 1],
              ![-1, 2, 1, -1, 0, -1, 2, 0],
              ![-1, 3, 2, -2, 0, -2, 3, 1],
              ![-1, 2, 1, -1, 0, -2, 3, 1],
              ![-1, 1, 1, -1, 1, -2, 2, 1],
              ![0, 1, 0, -1, 1, -1, 1, 1],
              ![0, 1, 0, -1, 1, -1, 1, 0]
            ] }
    ] },
  { tableClass := 10744, projectiveOrder := 1920, liftOrder := 3840,
    generators := [
      { order := 20, matrix := ![
              ![1, 0, 1, -1, -1, 1, 0, 1],
              ![2, 1, 0, -1, -2, 2, 0, 1],
              ![3, 0, 0, -1, -2, 2, 0, 2],
              ![5, 1, 0, -2, -3, 3, 0, 2],
              ![4, 1, 0, -1, -3, 2, 0, 2],
              ![3, 1, 0, -1, -2, 2, -1, 2],
              ![2, 1, 0, -1, -1, 1, 0, 1],
              ![1, 1, 0, -1, 0, 0, 0, 1]
            ] },
      { order := 3, matrix := ![
              ![0, -1, 0, 1, 0, 0, -1, 1],
              ![-1, -1, 1, 1, -1, 1, -1, 1],
              ![-1, -1, 1, 1, 0, 0, -1, 1],
              ![-1, -2, 1, 2, -1, 1, -1, 1],
              ![-1, -2, 1, 1, 0, 1, -1, 1],
              ![-1, -2, 1, 1, 0, 0, 0, 1],
              ![-1, -1, 0, 1, 0, 0, 0, 1],
              ![-1, -1, 0, 1, 0, 0, 0, 0]
            ] }
    ] },
  { tableClass := 10745, projectiveOrder := 1920, liftOrder := 3840,
    generators := [
      { order := 20, matrix := ![
              ![-1, 0, 1, -1, 0, 1, 1, -1],
              ![-1, -1, 2, -2, 1, 1, 1, -1],
              ![-2, -1, 2, -2, 1, 2, 1, -2],
              ![-3, -2, 3, -3, 2, 2, 2, -2],
              ![-3, -1, 3, -3, 2, 1, 2, -2],
              ![-3, -1, 3, -2, 1, 1, 1, -1],
              ![-2, -1, 2, -1, 1, 0, 1, -1],
              ![-1, -1, 1, 0, 0, 0, 1, -1]
            ] },
      { order := 3, matrix := ![
              ![0, -1, -1, 1, 0, 1, 0, -2],
              ![1, -1, -2, 1, 0, 2, -1, -2],
              ![0, -1, -2, 1, 0, 3, -1, -3],
              ![1, -2, -4, 2, 0, 4, -1, -4],
              ![1, -2, -3, 1, 1, 3, -1, -3],
              ![1, -2, -2, 1, 0, 3, -1, -2],
              ![1, -1, -2, 1, 0, 2, -1, -1],
              ![0, -1, -1, 1, 0, 1, -1, 0]
            ] }
    ] },
  { tableClass := 10843, projectiveOrder := 2520, liftOrder := 5040,
    generators := [
      { order := 7, matrix := ![
              ![-1, 0, 1, -1, 2, -1, -1, 1],
              ![-2, 1, 1, -1, 2, -1, -1, 1],
              ![-2, 1, 2, -2, 3, -2, -1, 2],
              ![-3, 2, 2, -2, 4, -3, -2, 3],
              ![-3, 2, 2, -2, 3, -2, -2, 3],
              ![-2, 2, 2, -2, 2, -1, -2, 2],
              ![-1, 2, 1, -2, 2, -1, -1, 1],
              ![-1, 1, 1, -1, 1, -1, 0, 0]
            ] },
      { order := 6, matrix := ![
              ![1, -2, 0, 1, -1, 1, 0, 0],
              ![1, -2, 0, 1, -1, 2, -1, 0],
              ![1, -3, 1, 1, -2, 3, -1, 0],
              ![1, -5, 1, 2, -2, 4, -2, 0],
              ![1, -4, 1, 1, -1, 3, -1, -1],
              ![1, -3, 0, 1, -1, 3, -1, -1],
              ![0, -2, 0, 1, -1, 2, 0, -1],
              ![0, -1, 0, 0, 0, 1, 0, 0]
            ] }
    ] },
  { tableClass := 10845, projectiveOrder := 2520, liftOrder := 5040,
    generators := [
      { order := 7, matrix := ![
              ![1, 0, -2, 1, 0, 0, 1, -2],
              ![1, 0, -3, 2, 0, 0, 0, -2],
              ![1, 0, -3, 2, 0, 0, 1, -4],
              ![2, 0, -5, 3, 1, -1, 1, -5],
              ![1, -1, -4, 3, 1, -1, 1, -4],
              ![1, -1, -3, 2, 1, -1, 1, -3],
              ![0, 0, -2, 1, 1, -1, 1, -2],
              ![0, 0, -1, 1, 0, -1, 1, -1]
            ] },
      { order := 6, matrix := ![
              ![1, 0, 0, -1, 1, -1, 1, 1],
              ![0, 0, 1, -2, 2, -1, 1, 1],
              ![1, -1, 1, -2, 2, -1, 1, 2],
              ![1, -1, 1, -3, 3, -1, 2, 2],
              ![1, -1, 1, -3, 3, -1, 2, 1],
              ![1, 0, 1, -3, 2, 0, 1, 1],
              ![0, 0, 1, -2, 1, 0, 1, 1],
              ![0, 0, 0, -1, 1, 0, 0, 1]
            ] }
    ] },
  { tableClass := 10913, projectiveOrder := 3600, liftOrder := 7200,
    generators := [
      { order := 5, matrix := ![
              ![-2, 0, 1, 0, 0, 1, -1, 0],
              ![-2, 0, 0, 1, -1, 2, -1, 0],
              ![-3, 0, 0, 1, 0, 2, -2, 0],
              ![-4, -1, 0, 2, -1, 4, -3, 0],
              ![-3, -1, 0, 1, 0, 3, -2, 0],
              ![-2, 0, 0, 0, 0, 3, -2, 0],
              ![-2, 0, 0, 0, 0, 2, -1, 0],
              ![-1, 0, 0, 0, 0, 1, -1, 1]
            ] },
      { order := 5, matrix := ![
              ![1, -1, -1, 2, -2, 0, 1, 0],
              ![0, -1, -1, 3, -3, 0, 1, 1],
              ![0, -2, -1, 4, -4, 0, 2, 0],
              ![0, -3, -2, 6, -5, -1, 3, 1],
              ![0, -3, -2, 5, -4, 0, 2, 1],
              ![0, -2, -1, 3, -3, 0, 2, 1],
              ![0, -1, -1, 2, -2, 0, 2, 0],
              ![0, -1, 0, 1, -1, 0, 1, 0]
            ] },
      { order := 2, matrix := ![
              ![-1, 0, 1, 0, -1, 1, -1, 0],
              ![0, -1, 1, 0, -1, 1, -1, 0],
              ![-1, -1, 2, 0, -2, 2, -2, 1],
              ![-1, -2, 2, 0, -2, 3, -3, 1],
              ![-1, -2, 1, 1, -2, 2, -2, 1],
              ![-1, -2, 1, 1, -2, 2, -1, 0],
              ![-1, -1, 1, 0, -1, 1, 0, 0],
              ![-1, -1, 1, 0, 0, 0, 0, 0]
            ] }
    ] },
  { tableClass := 10914, projectiveOrder := 3600, liftOrder := 7200,
    generators := [
      { order := 10, matrix := ![
              ![0, 0, 1, 0, 0, -2, 1, 1],
              ![0, 0, 1, 0, 1, -3, 1, 1],
              ![0, 0, 1, 0, 1, -4, 2, 2],
              ![0, 0, 1, 1, 1, -6, 3, 2],
              ![1, 0, 0, 1, 1, -5, 2, 2],
              ![1, 0, 0, 1, 0, -3, 1, 2],
              ![1, 1, 0, 0, 0, -2, 1, 1],
              ![0, 1, 0, 0, 0, -1, 0, 1]
            ] },
      { order := 10, matrix := ![
              ![0, 1, -1, 1, -2, 1, 1, -1],
              ![-1, 2, -1, 1, -2, 1, 1, -2],
              ![-1, 2, -1, 2, -4, 2, 1, -2],
              ![-2, 3, -2, 3, -5, 2, 2, -3],
              ![-2, 2, -2, 3, -4, 2, 1, -2],
              ![-1, 2, -2, 2, -3, 2, 0, -1],
              ![-1, 2, -1, 1, -2, 1, 0, 0],
              ![0, 1, -1, 1, -1, 0, 0, 0]
            ] },
      { order := 2, matrix := ![
              ![1, 0, 0, 0, -1, 1, -1, 0],
              ![0, 0, 0, 1, -2, 1, -1, 0],
              ![1, 0, -1, 1, -2, 2, -2, 0],
              ![0, 0, 0, 1, -3, 3, -3, 0],
              ![0, -1, 0, 1, -2, 2, -2, 0],
              ![0, -1, 0, 1, -2, 2, -1, -1],
              ![0, 0, 0, 0, -1, 1, 0, -1],
              ![0, 0, 0, 0, 0, 0, 0, -1]
            ] }
    ] },
  { tableClass := 11063, projectiveOrder := 11520, liftOrder := 23040,
    generators := [
      { order := 3, matrix := ![
              ![0, 0, 1, 0, 0, -1, 1, -1],
              ![0, 0, 0, 1, 0, -2, 2, -1],
              ![0, 1, 1, 0, 0, -2, 2, -1],
              ![-1, 1, 1, 1, 0, -3, 3, -2],
              ![0, 1, 0, 1, 0, -2, 2, -2],
              ![0, 1, 0, 1, -1, -1, 2, -2],
              ![0, 0, 0, 1, -1, 0, 1, -1],
              ![0, 0, 0, 1, -1, 0, 0, 0]
            ] },
      { order := 10, matrix := ![
              ![-2, -1, 2, 0, 0, 0, -1, 1],
              ![-3, 0, 3, -1, 0, 1, -2, 1],
              ![-4, -1, 4, -1, 0, 1, -2, 1],
              ![-6, -1, 5, -1, 0, 2, -4, 2],
              ![-4, -1, 4, -1, 0, 2, -4, 2],
              ![-3, -1, 3, -1, 0, 2, -3, 2],
              ![-2, -1, 2, -1, 1, 1, -2, 1],
              ![-1, 0, 1, -1, 1, 0, -1, 1]
            ] }
    ] },
  { tableClass := 11064, projectiveOrder := 11520, liftOrder := 23040,
    generators := [
      { order := 3, matrix := ![
              ![0, 1, 1, 0, -2, 1, 0, 0],
              ![-1, 1, 1, 1, -3, 2, -1, 0],
              ![0, 1, 1, 1, -4, 3, -1, 0],
              ![-1, 2, 1, 2, -6, 4, -1, 0],
              ![-1, 2, 1, 1, -5, 4, -1, 0],
              ![-1, 1, 1, 1, -4, 3, 0, -1],
              ![-1, 0, 1, 1, -3, 2, 0, 0],
              ![0, 0, 0, 1, -2, 1, 0, 0]
            ] },
      { order := 10, matrix := ![
              ![1, 0, -1, -1, 2, 0, 0, -1],
              ![1, 0, -1, -1, 2, 1, -1, -2],
              ![1, 0, -1, -2, 4, 0, -1, -2],
              ![2, -1, -2, -2, 5, 1, -2, -3],
              ![1, -1, -1, -2, 4, 1, -1, -3],
              ![1, -1, 0, -2, 3, 1, -1, -2],
              ![0, -1, 0, -1, 2, 1, -1, -1],
              ![0, 0, 0, -1, 1, 1, -1, 0]
            ] }
    ] },
  { tableClass := 11102, projectiveOrder := 20160, liftOrder := 40320,
    generators := [
      { order := 6, matrix := ![
              ![1, -1, 1, 0, 0, -1, 0, 1],
              ![1, -1, 1, 0, 1, -2, 0, 1],
              ![1, -2, 2, 0, 1, -2, -1, 2],
              ![2, -3, 2, 1, 1, -3, -1, 2],
              ![2, -3, 1, 1, 1, -2, -1, 2],
              ![1, -2, 1, 1, 0, -1, -1, 2],
              ![0, -2, 1, 1, 0, -1, 0, 1],
              ![0, -1, 0, 1, 0, -1, 0, 1]
            ] },
      { order := 7, matrix := ![
              ![0, 0, 0, -1, 1, -1, 2, 0],
              ![-1, 0, 0, -1, 2, -2, 2, 1],
              ![-1, 0, 0, -1, 2, -3, 4, 0],
              ![-1, 0, -1, -1, 3, -4, 5, 1],
              ![-1, 0, 0, -1, 2, -3, 4, 1],
              ![-1, -1, 0, 0, 1, -2, 3, 1],
              ![-1, -1, 0, 0, 1, -1, 2, 0],
              ![0, -1, 0, 0, 1, -1, 1, 0]
            ] }
    ] },
  { tableClass := 11104, projectiveOrder := 20160, liftOrder := 40320,
    generators := [
      { order := 6, matrix := ![
              ![0, 0, 0, -1, 2, 0, -1, 0],
              ![0, 1, -1, -1, 3, -1, -1, 0],
              ![-1, 1, 0, -2, 4, -1, -1, 0],
              ![-1, 1, -1, -2, 6, -2, -1, -1],
              ![-1, 1, -1, -2, 5, -1, -1, -1],
              ![-1, 1, -1, -1, 3, 0, -1, -1],
              ![0, 1, -1, -1, 2, 0, 0, -1],
              ![0, 0, -1, 0, 1, 0, 0, 0]
            ] },
      { order := 7, matrix := ![
              ![0, 0, 2, -1, 0, 0, 0, -1],
              ![0, 1, 2, -1, 0, -1, 1, -2],
              ![0, 1, 3, -2, 1, -1, 0, -2],
              ![0, 1, 4, -2, 1, -2, 1, -4],
              ![1, 1, 3, -2, 1, -2, 1, -3],
              ![0, 1, 3, -2, 1, -2, 1, -2],
              ![0, 0, 2, -1, 1, -2, 1, -1],
              ![0, 0, 1, -1, 1, -1, 1, -1]
            ] }
    ] },
  { tableClass := 11106, projectiveOrder := 20160, liftOrder := 40320,
    generators := [
      { order := 3, matrix := ![
              ![-1, 0, 0, 0, 0, 1, 0, -2],
              ![-1, -1, 0, 1, -1, 1, 1, -3],
              ![-1, 0, 0, 0, -1, 2, 1, -4],
              ![-2, -1, 1, 0, -1, 2, 2, -6],
              ![-2, 0, 1, 0, -1, 1, 2, -5],
              ![-1, 0, 0, 0, 0, 0, 2, -4],
              ![0, 0, 0, 0, 0, 0, 1, -3],
              ![0, 0, 0, 0, 0, 0, 1, -2]
            ] },
      { order := 14, matrix := ![
              ![-2, 0, 0, 1, -1, 0, 1, 0],
              ![-2, 1, 0, 0, -1, 0, 2, 0],
              ![-3, 1, 0, 1, -2, 0, 2, 0],
              ![-4, 2, -1, 1, -2, 0, 3, 0],
              ![-3, 2, -1, 1, -2, 0, 3, -1],
              ![-2, 1, -1, 1, -1, -1, 3, -1],
              ![-1, 0, -1, 1, -1, 0, 2, -1],
              ![0, 0, -1, 1, -1, 0, 1, 0]
            ] }
    ] },
  { tableClass := 11107, projectiveOrder := 20160, liftOrder := 40320,
    generators := [
      { order := 6, matrix := ![
              ![0, 2, 0, -1, 0, 0, 0, 1],
              ![-1, 3, 0, -1, 0, 0, -1, 2],
              ![-1, 4, 1, -2, 0, 0, -1, 2],
              ![-2, 5, 1, -2, 0, 0, -2, 4],
              ![-2, 4, 1, -2, 1, -1, -1, 3],
              ![-2, 3, 1, -2, 1, 0, -1, 2],
              ![-2, 2, 1, -1, 0, 0, 0, 1],
              ![-1, 1, 1, -1, 0, 0, 0, 1]
            ] },
      { order := 7, matrix := ![
              ![2, 0, -1, 0, 0, 1, -2, 1],
              ![3, 0, -2, 1, 0, 0, -2, 1],
              ![4, 0, -2, 0, 1, 0, -3, 2],
              ![6, 0, -4, 1, 1, 0, -4, 3],
              ![5, -1, -3, 1, 1, 0, -3, 2],
              ![4, 0, -2, 0, 1, 0, -2, 1],
              ![3, 0, -1, 0, 0, 0, -1, 1],
              ![2, 0, -1, 0, 0, 0, 0, 0]
            ] }
    ] },
  { tableClass := 11121, projectiveOrder := 25920, liftOrder := 51840,
    generators := [
      { order := 12, matrix := ![
              ![-2, 0, 0, 1, 0, -1, 1, 0],
              ![-3, 0, 1, 1, 0, -1, 0, 1],
              ![-4, 0, 1, 1, 0, -1, 1, 1],
              ![-5, 0, 1, 2, 0, -2, 1, 2],
              ![-4, -1, 1, 2, 0, -2, 1, 2],
              ![-3, -1, 1, 1, 1, -2, 1, 1],
              ![-2, -1, 0, 1, 1, -1, 0, 1],
              ![-1, 0, 0, 0, 1, -1, 0, 1]
            ] },
      { order := 4, matrix := ![
              ![1, -1, -1, 0, 0, 1, 0, 1],
              ![1, -2, -1, 1, -1, 1, 1, 1],
              ![2, -3, -2, 1, 0, 1, 1, 1],
              ![3, -4, -3, 2, -1, 1, 2, 2],
              ![2, -3, -3, 2, -1, 1, 2, 1],
              ![1, -3, -2, 2, -1, 1, 1, 1],
              ![1, -2, -1, 1, -1, 1, 1, 0],
              ![0, -1, 0, 0, 0, 0, 1, 0]
            ] }
    ] },
  { tableClass := 11122, projectiveOrder := 25920, liftOrder := 51840,
    generators := [
      { order := 12, matrix := ![
              ![1, -1, -2, 2, -1, 1, -1, 1],
              ![0, -2, -2, 3, -1, 1, -2, 2],
              ![1, -2, -3, 3, -1, 2, -3, 3],
              ![1, -3, -4, 5, -2, 2, -4, 5],
              ![1, -3, -3, 4, -2, 2, -3, 4],
              ![1, -3, -2, 3, -1, 1, -2, 3],
              ![1, -2, -2, 2, 0, 0, -1, 2],
              ![0, -1, -1, 1, 0, 0, 0, 1]
            ] },
      { order := 4, matrix := ![
              ![-1, -2, 2, 0, 0, 0, 0, 0],
              ![-1, -2, 3, -1, 1, 0, -1, 0],
              ![-2, -3, 4, -1, 1, 0, -1, 0],
              ![-3, -4, 6, -2, 2, 0, -1, -1],
              ![-2, -3, 5, -2, 2, -1, 0, -1],
              ![-2, -2, 4, -2, 2, -1, 0, 0],
              ![-2, -1, 3, -1, 1, -1, 0, 0],
              ![-1, -1, 1, 0, 1, -1, 0, 0]
            ] }
    ] },
  { tableClass := 11159, projectiveOrder := 161280, liftOrder := 322560,
    generators := [
      { order := 6, matrix := ![
              ![0, 0, 0, 1, -1, 1, -2, 1],
              ![0, -1, 0, 2, -2, 2, -2, 0],
              ![0, -1, 0, 3, -3, 2, -3, 1],
              ![0, -1, 0, 4, -4, 3, -4, 0],
              ![0, -1, -1, 4, -3, 2, -3, 0],
              ![-1, -1, 0, 3, -2, 1, -2, 0],
              ![-1, 0, 0, 2, -2, 1, -1, 0],
              ![0, 0, 0, 1, -1, 0, 0, 0]
            ] },
      { order := 7, matrix := ![
              ![-1, 2, 1, -2, 0, 1, 0, 0],
              ![-2, 2, 1, -2, 0, 1, 0, 1],
              ![-2, 3, 2, -4, 1, 1, 0, 1],
              ![-3, 5, 2, -5, 1, 1, 0, 2],
              ![-2, 4, 1, -4, 1, 1, 0, 2],
              ![-2, 3, 1, -3, 1, 0, 1, 1],
              ![-1, 2, 1, -2, 0, 0, 1, 1],
              ![-1, 1, 1, -1, 0, 0, 0, 1]
            ] }
    ] },
  { tableClass := 11161, projectiveOrder := 161280, liftOrder := 322560,
    generators := [
      { order := 6, matrix := ![
              ![1, -1, -1, 1, 0, 0, -1, 2],
              ![1, -1, 0, 0, 1, -1, -1, 3],
              ![1, -1, -1, 1, 1, -1, -2, 4],
              ![2, -1, -1, 1, 1, -2, -2, 6],
              ![2, -1, -1, 1, 1, -2, -1, 4],
              ![1, -1, -1, 1, 1, -2, 0, 3],
              ![1, 0, -1, 0, 1, -1, 0, 2],
              ![0, 0, 0, 0, 0, 0, 0, 1]
            ] },
      { order := 7, matrix := ![
              ![1, -1, 0, 0, 1, -1, 1, -1],
              ![0, -1, 0, 0, 2, -2, 2, -2],
              ![1, -1, 0, 0, 2, -3, 3, -2],
              ![1, -2, 0, 0, 4, -5, 4, -3],
              ![0, -2, 1, 0, 3, -4, 3, -2],
              ![0, -1, 1, 0, 2, -3, 2, -2],
              ![0, -1, 0, 1, 1, -2, 1, -1],
              ![0, 0, 0, 0, 1, -1, 0, 0]
            ] }
    ] },
  { tableClass := 11162, projectiveOrder := 181440, liftOrder := 362880,
    generators := [
      { order := 6, matrix := ![
              ![0, -1, 1, 0, 0, 1, -2, 1],
              ![0, 0, 1, -1, 1, 1, -3, 2],
              ![-1, -1, 2, -1, 1, 2, -4, 2],
              ![-1, -1, 2, -1, 2, 2, -6, 3],
              ![0, -1, 1, -1, 2, 2, -5, 2],
              ![0, -1, 0, 0, 1, 2, -4, 2],
              ![0, -1, 0, 0, 1, 1, -2, 1],
              ![0, -1, 0, 0, 1, 0, -1, 1]
            ] },
      { order := 7, matrix := ![
              ![0, 0, 2, -1, 0, 0, 0, -1],
              ![0, 1, 2, -1, 0, -1, 1, -2],
              ![0, 1, 3, -2, 1, -1, 0, -2],
              ![0, 1, 4, -2, 1, -2, 1, -4],
              ![1, 1, 3, -2, 1, -2, 1, -3],
              ![0, 1, 3, -2, 1, -2, 1, -2],
              ![0, 0, 2, -1, 1, -2, 1, -1],
              ![0, 0, 1, -1, 1, -1, 1, -1]
            ] }
    ] },
  { tableClass := 11164, projectiveOrder := 181440, liftOrder := 362880,
    generators := [
      { order := 3, matrix := ![
              ![-1, -1, -1, 2, -1, 0, 1, -1],
              ![0, -1, -2, 2, -1, 0, 2, -2],
              ![-1, -1, -3, 3, -1, 0, 2, -2],
              ![-1, -1, -4, 4, -2, 0, 3, -3],
              ![0, -1, -4, 4, -2, 0, 2, -2],
              ![0, -1, -3, 3, -1, -1, 2, -1],
              ![0, -1, -2, 2, 0, -1, 1, -1],
              ![0, 0, -1, 1, 0, -1, 1, -1]
            ] },
      { order := 7, matrix := ![
              ![2, 0, -1, 0, 0, 1, -2, 1],
              ![3, 0, -2, 1, 0, 0, -2, 1],
              ![4, 0, -2, 0, 1, 0, -3, 2],
              ![6, 0, -4, 1, 1, 0, -4, 3],
              ![5, -1, -3, 1, 1, 0, -3, 2],
              ![4, 0, -2, 0, 1, 0, -2, 1],
              ![3, 0, -1, 0, 0, 0, -1, 1],
              ![2, 0, -1, 0, 0, 0, 0, 0]
            ] }
    ] },
  { tableClass := 11165, projectiveOrder := 1290240, liftOrder := 2580480,
    generators := [
      { order := 4, matrix := ![
              ![-1, 1, 1, 0, -2, 2, -1, 0],
              ![0, 1, 1, 0, -3, 3, -2, 1],
              ![0, 2, 1, 0, -4, 4, -2, 0],
              ![0, 3, 2, 0, -6, 5, -3, 1],
              ![0, 2, 2, 0, -5, 4, -2, 0],
              ![0, 1, 2, 0, -4, 3, -1, 0],
              ![0, 0, 1, 1, -3, 2, -1, 0],
              ![0, 0, 0, 1, -2, 1, 0, 0]
            ] },
      { order := 12, matrix := ![
              ![-2, 1, 0, 1, -1, 0, 0, 0],
              ![-2, 2, 0, 1, -1, -1, 1, -1],
              ![-3, 2, 0, 2, -2, -1, 1, -1],
              ![-4, 3, -1, 3, -2, -2, 2, -2],
              ![-3, 3, -1, 2, -2, -1, 2, -2],
              ![-2, 3, -1, 1, -1, -1, 1, -1],
              ![-1, 2, -1, 1, -1, 0, 0, -1],
              ![0, 1, -1, 1, -1, 0, 0, 0]
            ] }
    ] },
  { tableClass := 11167, projectiveOrder := 1290240, liftOrder := 2580480,
    generators := [
      { order := 8, matrix := ![
              ![-1, 2, 0, 0, -1, 0, 1, -1],
              ![-3, 2, 1, 0, -1, 0, 1, -1],
              ![-3, 3, 0, 0, -1, 0, 2, -2],
              ![-5, 4, 1, 0, -2, 0, 3, -3],
              ![-4, 3, 0, 1, -2, 0, 2, -2],
              ![-3, 2, 0, 1, -2, 1, 1, -2],
              ![-2, 2, 0, 0, -1, 1, 0, -1],
              ![-1, 1, 0, 0, -1, 1, 0, 0]
            ] },
      { order := 12, matrix := ![
              ![0, -2, 1, 1, -1, 0, 0, 1],
              ![0, -3, 1, 1, -1, 1, -1, 2],
              ![0, -4, 1, 2, -1, 0, -1, 3],
              ![0, -6, 2, 2, -1, 1, -2, 4],
              ![-1, -5, 2, 2, -1, 1, -2, 3],
              ![0, -4, 1, 2, -1, 1, -2, 2],
              ![0, -3, 1, 1, 0, 0, -1, 1],
              ![0, -1, 1, 0, 0, 0, -1, 1]
            ] }
    ] },
  { tableClass := 11168, projectiveOrder := 1451520, liftOrder := 2903040,
    generators := [
      { order := 4, matrix := ![
              ![0, 1, -1, -1, 2, -1, 1, -1],
              ![0, 2, -1, -2, 3, -1, 0, -1],
              ![0, 3, -1, -3, 4, -2, 1, -1],
              ![-1, 4, -1, -4, 6, -3, 1, -2],
              ![-1, 3, -1, -3, 5, -3, 1, -1],
              ![-1, 2, -1, -2, 4, -2, 0, 0],
              ![-1, 2, -1, -1, 2, -1, 0, 0],
              ![0, 1, -1, 0, 1, -1, 0, 0]
            ] },
      { order := 7, matrix := ![
              ![2, 0, -1, 0, 0, 1, -2, 1],
              ![3, 0, -2, 1, 0, 0, -2, 1],
              ![4, 0, -2, 0, 1, 0, -3, 2],
              ![6, 0, -4, 1, 1, 0, -4, 3],
              ![5, -1, -3, 1, 1, 0, -3, 2],
              ![4, 0, -2, 0, 1, 0, -2, 1],
              ![3, 0, -1, 0, 0, 0, -1, 1],
              ![2, 0, -1, 0, 0, 0, 0, 0]
            ] }
    ] },
  { tableClass := 11170, projectiveOrder := 1451520, liftOrder := 2903040,
    generators := [
      { order := 4, matrix := ![
              ![-1, 1, 1, -1, 1, -1, 1, -2],
              ![-1, 2, 1, -2, 2, -1, 0, -2],
              ![-2, 3, 2, -3, 2, -1, 1, -3],
              ![-3, 4, 3, -4, 3, -1, 0, -4],
              ![-2, 3, 2, -3, 2, 0, 0, -4],
              ![-1, 3, 1, -2, 1, 0, 0, -3],
              ![-1, 2, 0, -1, 1, 0, 0, -2],
              ![0, 1, 0, -1, 1, 0, 0, -1]
            ] },
      { order := 7, matrix := ![
              ![0, 0, -1, 1, 0, 1, -2, 0],
              ![1, 0, -2, 2, 0, 0, -2, 0],
              ![1, 0, -2, 2, 0, 1, -4, 1],
              ![1, 0, -3, 4, -1, 1, -5, 1],
              ![1, 0, -2, 3, -1, 1, -4, 1],
              ![1, 1, -2, 2, -1, 1, -3, 1],
              ![1, 0, -2, 2, -1, 1, -2, 1],
              ![0, 0, -1, 1, 0, 0, -1, 1]
            ] }
    ] },
  { tableClass := 11171, projectiveOrder := 174182400, liftOrder := 348364800,
    generators := [
      { order := 2, matrix := ![
              ![0, 0, 1, 0, -2, 1, 0, 1],
              ![0, 0, 2, -1, -2, 2, -1, 1],
              ![0, 0, 2, -1, -3, 3, -1, 2],
              ![0, -1, 3, -1, -4, 4, -2, 3],
              ![-1, -1, 3, -1, -3, 3, -1, 2],
              ![-1, -1, 3, -1, -2, 2, -1, 2],
              ![0, -1, 2, -1, -1, 1, 0, 1],
              ![0, -1, 1, 0, -1, 1, 0, 0]
            ] },
      { order := 5, matrix := ![
              ![0, 0, 0, -1, 1, 1, -1, -1],
              ![0, 0, 0, -1, 0, 3, -2, -1],
              ![0, 0, -1, -1, 1, 3, -2, -2],
              ![0, 1, -1, -2, 1, 5, -4, -2],
              ![0, 0, -1, -1, 1, 4, -4, -1],
              ![1, 0, -1, -1, 1, 3, -3, -1],
              ![0, 0, 0, -1, 1, 2, -2, -1],
              ![0, 0, 0, 0, 0, 1, -1, -1]
            ] }
    ] }
]

/-- The flat list of all sixty-four displayed generators. -/
def allGenerators : List GeneratorDatum :=
  perfectCoreMatrixData.flatMap (fun row => row.generators)

/-- Change a weight-basis matrix to the simple-root/coroot basis. -/
def rootBasisMatrix (m : Mat8) : Mat8 :=
  CartanMatrix.E₈ * m * e8CartanInverse

/-- Forget the matrices and retain the already committed perfect-core metadata. -/
def PerfectCoreMatrixDatum.toLiftDatum
    (row : PerfectCoreMatrixDatum) : PerfectCoreLiftDatum :=
  { tableClass := row.tableClass
    projectiveOrder := row.projectiveOrder
    liftOrder := row.liftOrder
    derivedOrder := row.liftOrder
    fixedModTwoDimension := 0 }

/-- Entrywise reduction of an integral matrix modulo two. -/
def reduceModTwo (m : Mat8) : Mat8F2 :=
  fun i j => (m i j : F2)

/-- Right multiplication of a mod-two row vector by a matrix. -/
def rowMul (v : Vec8F2) (m : Mat8F2) : Vec8F2 :=
  fun j => ∑ i, v i * m i j

/-- The common fixed vectors modulo two of a generator packet. -/
def fixedVectors (gens : List GeneratorDatum) : Finset Vec8F2 :=
  Finset.univ.filter fun v =>
    gens.all fun g => decide (rowMul v (reduceModTwo g.matrix) = v)

/-- The canonical representative `0` or `1` of a mod-two scalar. -/
def bitLift (x : F2) : ℤ := x.val

/-- The even E8 norm divided by two, reduced modulo two. -/
def e8QuadraticFormModTwo (v : Vec8F2) : F2 :=
  ((∑ i, ∑ j,
      bitLift (v i) * e8CartanInverse i j * bitLift (v j)) / 2 : ℤ)

/-- Mod-two vectors on which a generator fails to preserve the E8 quadratic form. -/
def quadraticViolations (m : Mat8) : Finset Vec8F2 :=
  Finset.univ.filter fun v =>
    e8QuadraticFormModTwo (rowMul v (reduceModTwo m)) !=
      e8QuadraticFormModTwo v

/-- Boolean certificate that an integral generator preserves the weight Gram matrix. -/
def weightIsometryCheck (g : GeneratorDatum) : Bool :=
  decide (g.matrix * e8CartanInverse * g.matrix.transpose = e8CartanInverse)

/-- Boolean certificate that the derived matrix preserves the root Gram matrix. -/
def rootIsometryCheck (g : GeneratorDatum) : Bool :=
  decide (rootBasisMatrix g.matrix * CartanMatrix.E₈ *
    (rootBasisMatrix g.matrix).transpose = CartanMatrix.E₈)

/-- Boolean certificate that a generator has determinant one. -/
def determinantOneCheck (g : GeneratorDatum) : Bool :=
  decide (g.matrix.det = 1)

/-- Check successive positive powers, accepting the identity first at step `n`. -/
def exactOrderAux (m : Mat8) : ℕ → Mat8 → Bool
  | 0, _ => false
  | 1, p => decide (p * m = 1)
  | n + 2, p =>
      let next := p * m
      decide (next ≠ 1) && exactOrderAux m (n + 1) next

/-- Boolean certificate for the exact, rather than merely dividing, order. -/
def exactOrderCheck (g : GeneratorDatum) : Bool :=
  exactOrderAux g.matrix g.order 1

/-- Boolean certificate that the displayed exponent is an order relation. -/
def orderPowerCheck (g : GeneratorDatum) : Bool :=
  decide (g.matrix ^ g.order = 1)

/-- The data have the statically enforced 8-by-8 shape, thirty-one rows, and
sixty-four generator matrices; every row uses two or three generators. -/
theorem shape_row_and_generator_count :
    Fintype.card I8 = 8 ∧
      perfectCoreMatrixData.length = 31 ∧
      allGenerators.length = 64 ∧
      perfectCoreMatrixData.all
        (fun row => decide (row.generators.length = 2) ||
          decide (row.generators.length = 3)) = true := by
  decide

/-- Forgetting matrices recovers the existing thirty-one-row metadata exactly. -/
theorem perfectCoreMatrixData_metadata :
    perfectCoreMatrixData.map PerfectCoreMatrixDatum.toLiftDatum =
      omegaEightPlusTwoPerfectCoreLiftData := by
  decide

set_option maxHeartbeats 0 in
-- Exact reduction of all sixty-four 8-by-8 matrix identities needs an unrestricted budget.
set_option maxRecDepth 100000 in
/-- All sixty-four displayed generators preserve the integral E8 weight form. -/
theorem allGenerators_weight_isometries :
    allGenerators.all weightIsometryCheck = true := by
  decide

end RiemannResearch.E8.PerfectCoreMatrixCertificate
