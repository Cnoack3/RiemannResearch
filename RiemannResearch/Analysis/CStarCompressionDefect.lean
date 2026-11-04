/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.CompressionProductDefect
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Norm and vanishing of the compression defect

Source: the user-provided `Pasted text(9).txt`, final paper, section 4,
November 4, 2026. The ordered factorization is already in
`CompressionProductDefect`; the C-star identity turns it into an exact norm
formula and a necessary-and-sufficient invariance criterion.
The standard C-star norm identity is Mathlib's
`CStarRing.norm_star_mul_self` (Analysis/CStarAlgebra/Basic).
-/

namespace CStarRing
variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- The complete squared-compression defect has exactly the squared leakage norm. -/
theorem norm_compression_square_defect (P B : A)
    (hP : P * P = P) (hPstar : star P = P) :
    ‖P*star B*B*P - star (P*B*P)*(P*B*P)‖ = ‖(1-P)*B*P‖^2 := by
  rw [StarRing.compression_square_defect P B hP hPstar,
    StarRing.compression_square_defect_factorization P B hP hPstar,
    CStarRing.norm_star_mul_self, pow_two]

/-- No information is lost in passing from the defect to invariance of the range. -/
theorem compression_square_defect_eq_zero_iff (P B : A)
    (hP : P * P = P) (hPstar : star P = P) :
    P*star B*B*P - star (P*B*P)*(P*B*P) = 0 ↔ B*P=P*B*P := by
  rw [StarRing.compression_square_defect P B hP hPstar,
    StarRing.compression_square_defect_factorization P B hP hPstar,
    CStarRing.star_mul_self_eq_zero_iff]
  have he : (1-P)*B*P = B*P-P*B*P := by noncomm_ring
  rw [he, sub_eq_zero]

end CStarRing
