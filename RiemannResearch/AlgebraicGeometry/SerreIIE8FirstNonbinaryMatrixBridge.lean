/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIE8PrimeMarkedSolvableIncidence
import RiemannResearch.E8.PerfectCoreMatrixCertificate

/-!
# Bridge the first nonbinary E8 survivor to its matrix certificate

The Serre-II algebraic-geometry layer indexes survivors through
`E8PerfectCoreSurvivorCase`, while the explicit lattice generators live in
`PerfectCoreMatrixCertificate`.  This file proves that the selected first
nonbinary survivor is exactly the lift datum underlying the certified matrix
row.  Thus later geometry for that survivor can refer to the existing concrete
lattice calculation without relying on a duplicated table-class assertion.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SerreII

open RiemannResearch.E8
open RiemannResearch.E8.PerfectCoreMatrixCertificate

/-- The algebraic-geometry first nonbinary survivor and the matrix-certificate
first nonbinary row encode the same perfect-core lift datum. -/
theorem firstNonbinarySurvivor_datum_eq_matrixRow :
    firstNonbinarySurvivor.datum = firstNonbinaryRow.toLiftDatum := by
  decide

/-- The matrix-certified row attached to the selected survivor has the same
table class as the algebraic-geometry survivor. -/
theorem firstNonbinarySurvivor_matrix_tableClass :
    firstNonbinaryRow.tableClass = firstNonbinarySurvivor.datum.tableClass := by
  decide

end SerreII
end AlgebraicGeometry
end RiemannResearch
