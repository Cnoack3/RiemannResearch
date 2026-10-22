import RiemannResearch.RH.CommonDilationCoercivity
import RiemannResearch.RH.ParetoCoordinateEvaluation
import Mathlib.Tactic.IntervalCases

/-!
# Escape of common-scale repairs detected by an actual physical coordinate

Source: user-provided argument, `RH_Minimal_Seeds_Continuation_20260916.md`,
Section 11. The coordinate observer below is precisely the physical
Möbius coordinate `α₅(f) = f(5) - f(4) - f(1)`.

The escape theorem is unconditional for every family with its stated
nonvanishing coordinate limit. No RH or sign assumption is used.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

/-- The concrete three-coordinate functional detecting the rough root `5`. -/
def fifthChargeObserver : ThresholdHilbert →L[ℝ] ℝ :=
  physicalEvaluationCLM 4 - physicalEvaluationCLM 3 - physicalEvaluationCLM 0

@[simp] theorem fifthChargeObserver_apply (f : ThresholdHilbert) :
    fifthChargeObserver f =
      hilbertSequence f 5 - hilbertSequence f 4 - hilbertSequence f 1 := by
  simp [fifthChargeObserver, physicalEvaluationCLM_apply]

/-- Weighted Cauchy--Schwarz for the exact three physical coordinates.
The sharp squared dual norm is `30 + 20 + 2 = 52`. -/
theorem fifthChargeObserver_sq_le (f : ThresholdHilbert) :
    |fifthChargeObserver f|^2 ≤ 52 * ‖f‖^2 := by
  have h := Summable.sum_le_tsum ({1, 4, 5} : Finset ℕ)
    (fun n _ => mul_nonneg (positiveWeight_nonneg n)
      (sq_nonneg (hilbertSequence f n)))
    (hilbertSequence_square_summable f)
  rw [← hilbert_norm_weighted_sq] at h
  norm_num [positiveWeight] at h
  change (1 / 2 : ℝ) * hilbertSequence f 1 ^ 2 +
    (1 / 20 * hilbertSequence f 4 ^ 2 + 1 / 30 * hilbertSequence f 5 ^ 2) ≤ ‖f‖ ^ 2 at h
  rw [sq_abs, fifthChargeObserver_apply]
  nlinarith [sq_nonneg (20 * hilbertSequence f 5 + 30 * hilbertSequence f 4),
    sq_nonneg (2 * hilbertSequence f 5 + 30 * hilbertSequence f 1),
    sq_nonneg (2 * hilbertSequence f 4 - 20 * hilbertSequence f 1)]

/-- The actual observer isolates the coefficient of `R₅` in any rough packet.
Squarefreeness is unnecessary for this finite identity. -/
theorem fifthChargeObserver_residue (u : ℕ) (hu : 0 < u)
    (hu6 : Nat.Coprime u 6) :
    fifthChargeObserver (hilbertResidue u hu) = if u = 5 then -5 else 0 := by
  rw [fifthChargeObserver_apply, hilbertResidue_sequence]
  by_cases hlarge : 5 < u
  · norm_num [residue, Nat.mod_eq_of_lt hlarge,
      Nat.mod_eq_of_lt (by omega : 4 < u),
      Nat.mod_eq_of_lt (by omega : 1 < u), show u ≠ 5 by omega]
  · have hub : u ≤ 5 := by omega
    interval_cases u <;> norm_num [Nat.Coprime, residue] at *

/-- The observer is nonzero, so its finite operator norm is positive. -/
theorem fifthChargeObserver_norm_pos : 0 < ‖fifthChargeObserver‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have h := fifthChargeObserver_residue 5 (by norm_num) (by norm_num)
  rw [hzero] at h
  norm_num at h

/-- A signed common-dilation vector controls every continuous observation of
the undilated vector. This applies without restrictions on cancellations. -/
theorem commonDilation_observation_control (A : ℕ) (hA : 2 ≤ A)
    (f : ThresholdHilbert) (q : ℝ) (L : ThresholdHilbert →L[ℝ] ℝ) :
    (A : ℝ) * |L f|^2 ≤
      (1 + 2 * Real.sqrt 2)^2 * ‖L‖^2 *
        ‖hilbertDilation A (by omega) f + q • hilbertResidue A (by omega)‖^2 := by
  have hL : |L f| ≤ ‖L‖ * ‖f‖ := by
    simpa only [Real.norm_eq_abs] using L.le_opNorm f
  have hL2 : |L f|^2 ≤ ‖L‖^2 * ‖f‖^2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ ‖L‖ * ‖f‖)).mpr hL
    simpa only [mul_pow] using h
  have hc := commonDilation_coercivity A hA f q
  have hK : 0 < (1 + 2 * Real.sqrt 2)^2 := by positivity
  rw [div_mul_eq_mul_div] at hc
  have hc' := (div_le_iff₀ hK).mp hc
  have h₁ := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg A)
  have h₂ := mul_le_mul_of_nonneg_left hc' (sq_nonneg ‖L‖)
  nlinarith

/-- The numerical fifth-charge bound in Section 11, still for arbitrary
undilated vectors in the actual weighted Hilbert space. -/
theorem commonDilation_fifthCharge_control (A : ℕ) (hA : 2 ≤ A)
    (f : ThresholdHilbert) (q : ℝ) :
    (A : ℝ) * |fifthChargeObserver f|^2 ≤
      52 * (1 + 2 * Real.sqrt 2)^2 *
        ‖hilbertDilation A (by omega) f + q • hilbertResidue A (by omega)‖^2 := by
  have hobs := fifthChargeObserver_sq_le f
  have hc := commonDilation_coercivity A hA f q
  have hK : 0 < (1 + 2 * Real.sqrt 2)^2 := by positivity
  rw [div_mul_eq_mul_div] at hc
  have hc' := (div_le_iff₀ hK).mp hc
  have hb := mul_le_mul_of_nonneg_left hobs (Nat.cast_nonneg A)
  nlinarith

/-- Every actual common-scale correction escapes to infinity if its
undilated norm remains bounded away from zero. -/
theorem commonDilation_norm_tendsto_atTop
    (A : ℕ → ℕ) (hA : ∀ j, 2 ≤ A j)
    (hAinf : Tendsto A atTop atTop)
    (f : ℕ → ThresholdHilbert) (q : ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hf : ∀ᶠ j in atTop, δ ≤ ‖f j‖) :
    Tendsto (fun j =>
      ‖hilbertDilation (A j) (by have := hA j; omega) (f j) +
        q j • hilbertResidue (A j) (by have := hA j; omega)‖)
      atTop atTop := by
  let K : ℝ := (1 + 2 * Real.sqrt 2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  have hAr : Tendsto (fun j => (A j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hAinf
  apply tendsto_atTop.2
  intro B
  have he := hAr.eventually (eventually_ge_atTop (K * (max B 0 + 1)^2 / δ^2))
  filter_upwards [he, hf] with j hj hfj
  have hc := commonDilation_coercivity (A j) (hA j) (f j) (q j)
  have hnormsq : δ^2 ≤ ‖f j‖^2 :=
    (sq_le_sq₀ (le_of_lt hδ) (norm_nonneg _)).mpr hfj
  have hmul := mul_le_mul_of_nonneg_left hnormsq
    (show 0 ≤ (A j : ℝ) / K by positivity)
  have hthreshold : (max B 0 + 1)^2 ≤ (A j : ℝ) / K * δ^2 := by
    have hprod := (div_le_iff₀ hδ2).mp hj
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hK).mpr
    nlinarith
  have hsquare : (max B 0 + 1)^2 ≤
      ‖hilbertDilation (A j) (by have := hA j; omega) (f j) +
        q j • hilbertResidue (A j) (by have := hA j; omega)‖^2 :=
    hthreshold.trans (hmul.trans hc)
  have hmax : 0 ≤ max B 0 + 1 := by positivity
  have hn := (sq_le_sq₀ hmax (norm_nonneg _)).mp hsquare
  exact (le_trans (le_max_left B 0) (by linarith : max B 0 ≤ max B 0 + 1)).trans hn

/-- If the actual fifth charge tends to a nonzero value, its common outward
repair has norm tending to infinity, independently of every other charge. -/
theorem commonDilation_norm_tendsto_of_fifthCharge
    (A : ℕ → ℕ) (hA : ∀ j, 2 ≤ A j)
    (hAinf : Tendsto A atTop atTop)
    (f : ℕ → ThresholdHilbert) (q : ℕ → ℝ)
    {r : ℝ} (hr : r ≠ 0)
    (hobs : Tendsto (fun j => fifthChargeObserver (f j)) atTop (nhds r)) :
    Tendsto (fun j =>
      ‖hilbertDilation (A j) (by have := hA j; omega) (f j) +
        q j • hilbertResidue (A j) (by have := hA j; omega)‖)
      atTop atTop := by
  have hL := fifthChargeObserver_norm_pos
  have hrabs : 0 < |r| := abs_pos.mpr hr
  let δ : ℝ := (|r| / 2) / ‖fifthChargeObserver‖
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hobsabs := hobs.abs
  have he : ∀ᶠ j in atTop, |r| / 2 < |fifthChargeObserver (f j)| :=
    hobsabs.eventually (lt_mem_nhds (by linarith : |r| / 2 < |r|))
  apply commonDilation_norm_tendsto_atTop A hA hAinf f q hδ
  filter_upwards [he] with j hj
  have hb : |fifthChargeObserver (f j)| ≤ ‖fifthChargeObserver‖ * ‖f j‖ := by
    simpa only [Real.norm_eq_abs] using fifthChargeObserver.le_opNorm (f j)
  dsimp [δ]
  apply (div_le_iff₀ hL).mpr
  nlinarith

/-- Subtracting the common-scale repair from any eventually bounded packet
still makes the norm tend to infinity. -/
theorem commonScale_repaired_norm_tendsto_atTop
    (P C : ℕ → ThresholdHilbert)
    (hC : Tendsto (fun j => ‖C j‖) atTop atTop)
    {B : ℝ} (hP : ∀ᶠ j in atTop, ‖P j‖ ≤ B) :
    Tendsto (fun j => ‖P j - C j‖) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  have he := hC.eventually (eventually_ge_atTop (M + B))
  filter_upwards [he, hP] with j hj hPj
  have ht : ‖C j‖ ≤ ‖P j‖ + ‖P j - C j‖ := by
    have h := norm_sub_le (P j) (P j - C j)
    have heq : P j - (P j - C j) = C j := by abel
    rw [heq] at h
    exact h
  linarith

end
end RiemannResearch.RH.Pareto
