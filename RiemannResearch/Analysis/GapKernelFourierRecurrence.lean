/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelPolynomialPrimitive

/-! Integer coefficient transport for Fourier transforms of a polynomial
times the Gaussian e^{-πx²}. A factor of two clears the denominator
at each application of the second frequency derivative. -/

namespace RiemannResearch.Analysis.GapKernelFourierRecurrence

open GapKernelPolynomial GapKernelObjective

def diff (q : List ℤ) : List ℤ := indexed 1 q.tail

def drift (q : List ℤ) : List ℤ := add (diff q) (scale (-1) q)

theorem value_drift (q : List ℤ) (x : ℝ) :
    value (drift q) x = value (diff q) x - value q x := by
  simp only [drift, value_add, value_scale, Int.cast_neg, Int.cast_one]
  ring

/-- Twice the polynomial accompanying the transform after multiplication
by πx². The argument of the Fourier-side polynomial is πu². -/
def doubleStep (q : List ℤ) : List ℤ :=
  add (scale (-1) (drift q)) (0 :: scale (-2) (drift (drift q)))

theorem value_doubleStep (q : List ℤ) (x : ℝ) :
    value (doubleStep q) x = -value (drift q) x - 2*x*value (drift (drift q)) x := by
  simp only [doubleStep, value_add, value_scale, value, Int.cast_zero, Int.cast_neg,
    Int.cast_one, Int.cast_ofNat]
  ring

def transport : List ℤ → List ℤ
  | [] => []
  | a :: p => add [(2 : ℤ)^(p.length+1) * a] (doubleStep (transport p))

end RiemannResearch.Analysis.GapKernelFourierRecurrence
