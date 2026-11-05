import RiemannResearch.RH.MertensActualShiftedCriterion
import RiemannResearch.RH.CRTCarryArithmetic

/-!
# Local majorants for the shifted Möbius test

Interpolation between the bounds `1` and `n/k` for a residue gives a
summable p-series independent of the test parameter in each interior strip.
-/
noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.RH.MertensShiftedPairing

open ZetaTwoHilbert ZetaTwoOptimizerStage
open RiemannResearch.NumberTheory.MertensShiftedTest

private theorem atom_norm_le_interpolant (n i : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖(qSequence (squarefreeAtom i) n : ℂ)‖ ≤ ((n : ℝ) / (i+2 : ℕ)) ^ a := by
  have hk : 0 < (i+2 : ℕ) := by omega
  have ht : 0 ≤ (n : ℝ) / (i+2 : ℕ) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hi : Squarefree (i+2)
  · rw [squarefreeAtom, if_pos hi, qSequence_qResidue,
      abs_of_nonneg (CRTCarryArithmetic.residueFraction_nonneg _ _)]
    by_cases h : (n : ℝ) / (i+2 : ℕ) ≤ 1
    · apply le_trans _ (Real.self_le_rpow_of_le_one ht h ha1)
      rw [Pareto.residueFraction_eq_div_sub_floor _ _ hk]
      exact sub_le_self _ (Nat.cast_nonneg _)
    · exact (CRTCarryArithmetic.residueFraction_lt_one _ _ hk).le.trans
        (Real.one_le_rpow (le_of_not_ge h) ha)
  · simp only [squarefreeAtom, if_neg hi]
    change |qSequenceLinear (0 : QHilbert) n| ≤ _
    simpa using Real.rpow_nonneg ht a

/-- Inside `2η ≤ Re(s)`, the finite shifted Möbius test grows uniformly
at most as `n^(1−η)`. The constant is an explicit p-series. -/
theorem norm_shiftedTest_le_strip (n : ℕ) (s : ℂ) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hs : 2*η ≤ s.re) :
    ‖shiftedTest n s‖ ≤ (n : ℝ) ^ (1-η) *
      ∑' i : ℕ, ((i+2 : ℕ) : ℝ) ^ (-1-η) := by
  let f (i : ℕ) := shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ)
  let p (i : ℕ) := ((i+2 : ℕ) : ℝ) ^ (-1-η)
  have hp : Summable p := (summable_nat_add_iff 2).mpr
    (Real.summable_nat_rpow.mpr (show -1-η < -1 by linarith))
  have hb (i : ℕ) : ‖f i‖ ≤ (n : ℝ) ^ (1-η) * p i := by
    let k : ℝ := (i+2 : ℕ)
    have hk : 0 < k := by dsimp [k]; positivity
    have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ i+2 by omega)
    have hμ : |(ArithmeticFunction.moebius (i+2) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := i+2))
    have hc : ‖shiftedMobiusCoefficient s i‖ ≤ k ^ (-s.re) := by
      rw [shiftedMobiusCoefficient, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hk, Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hk.le _) hμ
    calc
      ‖f i‖ = ‖shiftedMobiusCoefficient s i‖ * ‖(qSequence (squarefreeAtom i) n : ℂ)‖ := norm_mul _ _
      _ ≤ k ^ (-s.re) * ((n : ℝ)/k) ^ (1-η) :=
        mul_le_mul hc (atom_norm_le_interpolant n i (by linarith) (by linarith))
          (norm_nonneg _) (Real.rpow_nonneg hk.le _)
      _ = (n : ℝ) ^ (1-η) * k ^ ((-s.re)-(1-η)) := by
        rw [Real.div_rpow (Nat.cast_nonneg n) hk.le, Real.rpow_sub hk (-s.re) (1-η)]
        ring
      _ ≤ (n : ℝ) ^ (1-η) * p i := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hk1 (show (-s.re)-(1-η) ≤ -1-η by linarith))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hN := hp.mul_left ((n : ℝ) ^ (1-η))
  have hf := Summable.of_nonneg_of_le (fun i => norm_nonneg (f i)) hb hN
  calc
    ‖shiftedTest n s‖ = ‖∑' i, f i‖ := congrArg norm (hasSum_shiftedMobiusAtomTest n s (by linarith)).tsum_eq.symm
    _ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' i, (n : ℝ) ^ (1-η) * p i := hf.tsum_le_tsum hb hN
    _ = _ := tsum_mul_left

/-- Interior normal convergence follows from weighted moments of the actual
charge at every positive power saving. Only the boundary dominator remains. -/
theorem riemannHypothesis_of_actual_shifted_boundary
    (x : ℕ → ℂ) (hx : ∀ j, 0 < (x j).re) (hx0 : Tendsto x atTop (𝓝 0))
    (hcharge : ∀ η : ℝ, 0 < η → η < 1 →
      Summable (fun n : ℕ => ‖witnessCharge n‖ * (n : ℝ) ^ (1-η)))
    (G : ℕ → ℝ) (hG : Summable G)
    (hboundary : ∀ᶠ j in atTop, ∀ n, ‖witnessCharge n * shiftedTest n (x j)‖ ≤ G n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_actual_shifted_majorants x hx hx0 _ G hG hboundary
  intro z hz
  let η : ℝ := min (1/2) (z.re/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hzη : 2*η < z.re := by have hh : η ≤ z.re/4 := min_le_right _ _; linarith
  let C := ∑' i : ℕ, ((i+2 : ℕ) : ℝ) ^ (-1-η)
  refine ⟨{w : ℂ | 2*η < w.re}, isOpen_lt continuous_const Complex.continuous_re,
    hzη, fun w hw => lt_trans (by positivity : 0 < 2*η) hw,
    fun n => (‖witnessCharge n‖ * (n : ℝ) ^ (1-η)) * C, (hcharge η hη hη1).mul_right C, ?_⟩
  intro n w hw
  change ‖witnessCharge n * shiftedTest n w‖ ≤ (‖witnessCharge n‖ * (n : ℝ) ^ (1-η)) * C
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_shiftedTest_le_strip n w η hη hη1 hw.le) (norm_nonneg _)

end RiemannResearch.RH.MertensShiftedPairing
