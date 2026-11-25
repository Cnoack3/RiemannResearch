import RiemannResearch.Analysis.DyadicPrimeTentConstants
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Passing to the degree limit of the finite prime tent witnesses

The Fejér multiplier at odd frequency `k < 2*N` is `1-k/(2*N)`.
This module takes only the approximation-degree limit. Its input is an exact
finite sum, after the individual height limits have been taken.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.DyadicZeroWasserstein

def primeFejerConstant (N p : ℕ) : ℝ :=
  (2 * Real.log p / Real.pi ^ 2) * ∑ j ∈ Finset.range N,
    (1 - ((2*j+1 : ℕ) : ℝ) / (2 * (N : ℝ))) *
      ((Real.sqrt (p : ℝ))⁻¹ ^ (2*j+1) / ((2*j+1 : ℕ) : ℝ)^2)

/-- At fixed prime the correction due to the Fejér multiplier is a bounded
partial sum times `(2N)⁻¹`. -/
theorem tendsto_primeFejerConstant {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N => primeFejerConstant N p) atTop (𝓝 (primeTentConstant p)) := by
  let r := (Real.sqrt (p : ℝ))⁻¹
  let k := fun j : ℕ => ((2*j+1 : ℕ) : ℝ)
  let a := fun j : ℕ => r ^ (2*j+1) / (k j)^2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr1 : r < 1 := by
    have hs : 1 < Real.sqrt (p : ℝ) := by
      have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hp1
      simpa using h
    exact (inv_lt_one₀ (lt_trans zero_lt_one hs)).2 hs
  have hgeom : Summable (fun j : ℕ => r ^ (2*j+1)) := by
    have hg := (summable_geometric_of_lt_one (sq_nonneg r)
      (show r^2 < 1 by nlinarith [mul_pos (sub_pos.mpr hr1) (by linarith : 0 < 1+r)] )).mul_right r
    simpa only [pow_succ, pow_mul] using hg
  have ha : Summable a := summable_primeTentTerms hp
  have hka : Summable (fun j => k j * a j) := by
    apply Summable.of_nonneg_of_le _ _ hgeom
    · intro j
      dsimp [k,a]
      positivity
    · intro j
      have hk : 1 ≤ k j := by dsimp [k]; exact_mod_cast (by omega : 1 ≤ 2*j+1)
      have hk0 : 0 < k j := lt_of_lt_of_le zero_lt_one hk
      calc
        k j * a j = r^(2*j+1) / k j := by dsimp [a]; field_simp [hk0.ne']
        _ ≤ _ := div_le_self (pow_nonneg hr _) hk
  have hN : Tendsto (fun N : ℕ => (2 * (N : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [mul_inv, mul_zero, Function.comp_apply] using
      ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2:ℝ)⁻¹)
  have h := (ha.hasSum.tendsto_sum_nat.sub (hN.mul hka.hasSum.tendsto_sum_nat)).const_mul
    (2 * Real.log p / Real.pi ^ 2)
  simp only [zero_mul, sub_zero] at h
  refine h.congr' (Eventually.of_forall ?_)
  intro N
  dsimp [primeFejerConstant, a, k, r]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end RiemannResearch.Analysis.DyadicZeroWasserstein
