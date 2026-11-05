import RiemannResearch.NumberTheory.MertensShiftedTest
import RiemannResearch.RH.MertensShiftedPairing
import RiemannResearch.RH.MertensShiftedTestIdentity
import Mathlib.Analysis.Convex.PathConnected

/-!
# A normal-convergence criterion for the concrete shifted Möbius tests

The boundary sequence may take any complex values in the right half-plane.
The numerical Möbius coefficients give the seed in the identity theorem.
-/
noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.RH.MertensShiftedPairing

open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.NumberTheory.MertensShiftedTest

/-- Local normal convergence and a single boundary dominator suffice for RH. -/
theorem riemannHypothesis_of_actual_shifted_majorants
    (x : ℕ → ℂ) (hx : ∀ j, 0 < (x j).re) (hx0 : Tendsto x atTop (𝓝 0))
    (hlocal : ∀ z : ℂ, 0 < z.re → ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧
      V ⊆ {w : ℂ | 0 < w.re} ∧ ∃ B : ℕ → ℝ, Summable B ∧
        ∀ n w, w ∈ V → ‖witnessCharge n * shiftedTest n w‖ ≤ B n)
    (G : ℕ → ℝ) (hG : Summable G)
    (hboundary : ∀ᶠ j in atTop, ∀ n, ‖witnessCharge n * shiftedTest n (x j)‖ ≤ G n) :
    RiemannHypothesis := by
  have hlin : IsLinearMap ℝ Complex.re := ⟨Complex.reLm.map_add, Complex.reLm.map_smul⟩
  have hconn : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_gt hlin 0).isPreconnected
  refine riemannHypothesis_of_shifted_witness_tests {z : ℂ | 0 < z.re} 2 x shiftedTest
    hconn (by change 0 < (2 : ℂ).re; norm_num) hx differentiableOn_shiftedTest hlocal ?_ ?_
    G hG hboundary
  · have hz : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by change 1 < (2 : ℂ).re; norm_num)
    filter_upwards [hz] with z hz
    refine ⟨shiftedMobiusCoefficient z, ?_, summable_norm_shiftedMobiusCoefficient z hz⟩
    exact fun n => (shiftedMobiusAtomTest_eq_shiftedTest n z (lt_trans zero_lt_one hz)).symm
  · intro n
    cases n with
    | zero => simp [witnessCharge, positiveQWeight]
    | succ n =>
      simpa only [Function.comp_apply, mul_one] using
        (tendsto_const_nhds (x := witnessCharge (n+1))).mul
          ((tendsto_shiftedTest_zero (n+1) (by omega)).comp hx0)

end RiemannResearch.RH.MertensShiftedPairing
