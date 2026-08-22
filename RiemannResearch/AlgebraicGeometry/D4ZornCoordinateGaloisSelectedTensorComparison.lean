/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedHopfDescent

/-!
# Selected tensor comparisons for finite-Galois D4 coordinate descent

This module begins the comparison of the tensor unit and tensor square selected
by effective affine Čech module descent with the canonical finite-Galois
semilinear Čech data used for the D4 related-triple coordinate Hopf maps.  It
records the scalar pure-generator coaction normalization; the full unit and
tensor-square coaction squares remain open.

Source: user-provided D4 Hopf-descent program.
-/

namespace RiemannResearch.AlgebraicGeometry

noncomputable section

open CategoryTheory
open RiemannResearch.GaloisCohomology
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
open scoped TensorProduct

universe u

/-- For the scalar semilinear Galois action, the coaction of a scalar times a
base-field scalar is the corresponding pure tensor. This is the generator
normalization needed to compare the selected Čech tensor unit with canonical
finite-Galois scalar descent. -/
theorem galoisScalarSemilinearCoaction_mul_algebraMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (l : L) (k : K) :
    galoisSemilinearCoaction K L L
        ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
        (l * algebraMap K L k) =
      l ⊗ₜ[K] algebraMap K L k := by
  apply (galoisSemilinearTensorEquiv K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)).injective
  ext σ
  rw [galoisSemilinearTensorEquiv_coaction_apply,
    galoisSemilinearTensorEquiv_tmul_apply]
  simp

end

end RiemannResearch.AlgebraicGeometry
