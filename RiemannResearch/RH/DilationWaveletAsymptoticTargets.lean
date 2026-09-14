import RiemannResearch.RH.DilationWaveletNoRiesz
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact binary-wavelet specifications with proved providers

Source: RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md,
and analytic_wavelet_foothold.md, Section 8.
The full adjacent-pair limit and absence of a lower Riesz bound are proved
in `DilationWaveletNoRiesz`. The sharper logarithmic asymptotic is supplied by
`binaryWaveletAdjacentAsymptotic_proved` in `BinaryWaveletAdjacentAsymptotic`.
The complete continuous signed Gram identity is supplied by
`binaryWaveletContinuousGram_proved` in `BinaryWaveletContinuousGram`.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open scoped BigOperators

def binaryWaveletStep (m : ℕ) (x : ℝ) : ℝ := dilationWaveletSequence 2 m ⌊x⌋₊

def binaryWaveletContinuousPrimitive (m : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, binaryWaveletStep m t

def binaryWaveletJump (j : ℕ) : ℝ :=
  if j % 4 = 1 then 1 else if j % 4 = 2 then -2 else if j % 4 = 3 then 1 else 0

/-- Complete continuous signed Gram identity, supplied by
`binaryWaveletContinuousGram_proved` in `BinaryWaveletContinuousGram`. -/
def BinaryWaveletContinuousGramTarget : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    paretoInner (dilationWaveletSequence 2 m) (dilationWaveletSequence 2 n) =
      -(∑' j : ℕ, binaryWaveletContinuousPrimitive m ((j+1) * n) *
        binaryWaveletJump (j+1) / (((j+1 : ℕ) : ℝ) * n)^2) +
      2 * ∫ x in Set.Ioi (n : ℝ),
        binaryWaveletContinuousPrimitive m x * binaryWaveletStep n x / x^3

/-- Exact 6/pi logarithmic leading coefficient with an O(1/n) remainder,
supplied by `binaryWaveletAdjacentAsymptotic_proved` in
`BinaryWaveletAdjacentAsymptotic`. -/
def BinaryWaveletAdjacentAsymptoticTarget : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => ‖normalizedBinaryWavelet (n+1) (by omega) -
      normalizedBinaryWavelet (n+2) (by omega)‖^2 -
      (6 / Real.pi) * Real.log (n+1) / (n+1))
    (fun n : ℕ => (1 : ℝ) / (n+1))

end
end RiemannResearch.RH.Pareto
