import RiemannResearch.RH.MertensShiftedPairing
import Mathlib.Analysis.PSeriesComplex

/-!
# Cancellation of the absolutely convergent shifted Möbius test

For Re(z)>1 its coefficients are bounded by the summable real p-series
(k^(-Re z)). The actual witness annihilates the entire test in that region.
-/

noncomputable section
namespace RiemannResearch.RH.MertensShiftedPairing

open ZetaTwoHilbert ZetaTwoOptimizerStage

/-- The coefficient of the atom of conductor i+2. -/
def shiftedMobiusCoefficient (z : ℂ) (i : ℕ) : ℂ :=
  -((ArithmeticFunction.moebius (i+2) : ℝ) : ℂ) *
    (((i+2 : ℕ) : ℝ) : ℂ) ^ (-z)

theorem summable_norm_shiftedMobiusCoefficient (z : ℂ) (hz : 1 < z.re) :
    Summable (fun i => ‖shiftedMobiusCoefficient z i‖) := by
  have hs := Real.summable_nat_rpow.mpr (show -z.re < -1 by linarith)
  have ht : Summable (fun i : ℕ => ((i+2 : ℕ) : ℝ) ^ (-z.re)) :=
    (summable_nat_add_iff 2).mpr hs
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ht
  intro i
  have hk : (0 : ℝ) < (i+2 : ℕ) := by positivity
  have hm : |(ArithmeticFunction.moebius (i+2) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := i+2))
  rw [shiftedMobiusCoefficient, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hk, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hk.le _) hm

/-- The absolutely convergent squarefree residue representation of the
shifted test in its seed half-plane. -/
def shiftedMobiusAtomTest (n : ℕ) (z : ℂ) : ℂ :=
  ∑' i, shiftedMobiusCoefficient z i * (qSequence (squarefreeAtom i) n : ℂ)

theorem witnessCharge_shiftedMobiusAtomTest (z : ℂ) (hz : 1 < z.re) :
    ∑' n, witnessCharge n * shiftedMobiusAtomTest n z = 0 :=
  witnessCharge_series_zero (fun n => shiftedMobiusAtomTest n z)
    (shiftedMobiusCoefficient z) (fun _ => rfl) (summable_norm_shiftedMobiusCoefficient z hz)

end RiemannResearch.RH.MertensShiftedPairing
