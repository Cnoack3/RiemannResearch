import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Growth forced by a critical Mellin cutoff

Source: independently derived assembly of the user's coefficient-mass research
problem, 28 September 2026. The consumer is RH/ProjectedDualMassObstruction.
All scalar envelope and nonzero-cutoff assumptions are displayed in the theorem.
This module makes no zeta or RH assertion.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

private theorem tendsto_zero_of_sq {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun n => f n ^ 2) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (hf _),
    Real.sqrt_zero] using ht

private theorem tendsto_zero_of_fourth {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun n => f n ^ 4) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_zero_of_sq hf
  apply tendsto_zero_of_sq (fun n => sq_nonneg (f n))
  convert h using 1
  funext n
  ring

/-- A nonzero boundary value and the literal Mellin cutoff prohibit a
strictly slower exponential growth envelope for coefficient mass. -/
theorem mass_barrier_of_critical_cutoff
    (φ B Q : ℕ → ℝ) (hφ : Tendsto φ atTop atTop)
    (hB : ∀ n, 0 ≤ B n) (hQ : ∀ n, 0 ≤ Q n)
    (a C D L : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 < L)
    (herror : ∀ᶠ n : ℕ in atTop, Q n ^ 4 ≤ C * B n ^ 2 * Real.exp (-a * φ n))
    (hcut : ∀ n : ℕ, ∀ R : ℝ, 0 < R →
      L ≤ Q n * Real.sqrt R + 2 * (D+B n) * Real.exp (-R/2))
    (b : ℝ) (hba : b < a) :
    Tendsto (fun n => Real.exp (-b * φ n) * B n ^ 2) atTop atTop := by
  have hnot : ∀ K : ℝ, ¬ ∃ᶠ n : ℕ in atTop,
      Real.exp (-b * φ n) * B n ^ 2 ≤ K := by
    intro K hfreq
    choose seq hge hb using frequently_atTop.mp hfreq
    have hs : Tendsto seq atTop atTop := tendsto_atTop_mono hge tendsto_id
    have hφs : Tendsto (fun k => φ (seq k)) atTop atTop := hφ.comp hs
    have hmass (k : ℕ) : B (seq k)^2 ≤ K * Real.exp (b * φ (seq k)) := by
      have he : Real.exp (-b * φ (seq k)) * Real.exp (b * φ (seq k)) = 1 := by
        rw [← Real.exp_add]
        have hz : -b * φ (seq k) + b * φ (seq k) = 0 := by ring
        rw [hz, Real.exp_zero]
      calc
        _ = B (seq k)^2 * (Real.exp (-b * φ (seq k)) *
            Real.exp (b * φ (seq k))) := by rw [he, mul_one]
        _ = (Real.exp (-b * φ (seq k)) * B (seq k)^2) *
            Real.exp (b * φ (seq k)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hb k) (Real.exp_pos _).le
    have hqb : ∀ᶠ k : ℕ in atTop,
        Q (seq k)^4 ≤ C*K*Real.exp (-(a-b)*φ (seq k)) := by
      filter_upwards [hs.eventually herror] with k hk
      calc
        _ ≤ C * B (seq k)^2 * Real.exp (-a * φ (seq k)) := hk
        _ ≤ C * (K * Real.exp (b * φ (seq k))) * Real.exp (-a * φ (seq k)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmass k) hC)
            (Real.exp_pos _).le
        _ = _ := by
          rw [show -(a-b)*φ (seq k) = b*φ (seq k)+(-a*φ (seq k)) by ring,
            Real.exp_add]
          ring
    let c : ℝ := |b|+1
    have hc : 0 < c := by dsimp [c]; positivity
    have hcb : b < c := by dsimp [c]; linarith [le_abs_self b]
    let H : ℕ → ℝ := fun k => Q (seq k) * Real.sqrt (c*φ (seq k))
    let T : ℕ → ℝ := fun k => 2*(D+B (seq k))*Real.exp (-(c*φ (seq k))/2)
    have hH0 : ∀ k, 0 ≤ H k := fun k => mul_nonneg (hQ _) (Real.sqrt_nonneg _)
    have hT0 : ∀ k, 0 ≤ T k := by
      intro k
      exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hD (hB _)))
        (Real.exp_pos _).le
    have hpoly : Tendsto (fun k => φ (seq k)^2 *
        Real.exp (-(a-b)*φ (seq k))) atTop (𝓝 0) := by
      have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (2:ℝ) (a-b) (by linarith)).comp hφs
      simpa only [Function.comp_def, Real.rpow_two] using ht
    have hH4 : Tendsto (fun k => H k ^ 4) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun k => pow_nonneg (hH0 k) 4)) _ (by
        simpa only [mul_zero] using hpoly.const_mul (C*K*c^2))
      filter_upwards [hqb, hφs.eventually_ge_atTop 0] with k hk hpk
      have hsqrt : (Real.sqrt (c*φ (seq k)))^4 = (c*φ (seq k))^2 := by
        calc
          _ = ((Real.sqrt (c*φ (seq k)))^2)^2 := by ring
          _ = _ := by rw [Real.sq_sqrt (mul_nonneg hc.le hpk)]
      change (Q (seq k)*Real.sqrt (c*φ (seq k)))^4 ≤ _
      rw [mul_pow, hsqrt]
      calc
        _ ≤ (C*K*Real.exp (-(a-b)*φ (seq k))) * (c*φ (seq k))^2 :=
          mul_le_mul_of_nonneg_right hk (sq_nonneg _)
        _ = _ := by ring
    have hHt : Tendsto H atTop (𝓝 0) := tendsto_zero_of_fourth hH0 hH4
    have he1 : Tendsto (fun k => Real.exp (-c*φ (seq k))) atTop (𝓝 0) :=
      Real.tendsto_exp_comp_nhds_zero.mpr
        (hφs.const_mul_atTop_of_neg (neg_neg_of_pos hc))
    have he2 : Tendsto (fun k => Real.exp (-(c-b)*φ (seq k))) atTop (𝓝 0) :=
      Real.tendsto_exp_comp_nhds_zero.mpr
        (hφs.const_mul_atTop_of_neg (by linarith))
    have hupper : Tendsto (fun k => 8*D^2*Real.exp (-c*φ (seq k)) +
        8*K*Real.exp (-(c-b)*φ (seq k))) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using (he1.const_mul (8*D^2)).add (he2.const_mul (8*K))
    have hT2 : Tendsto (fun k => T k^2) atTop (𝓝 0) := by
      apply squeeze_zero (fun k => sq_nonneg _) _ hupper
      intro k
      have hm : B (seq k)^2*Real.exp (-c*φ (seq k)) ≤
          K*Real.exp (-(c-b)*φ (seq k)) := by
        calc
          _ ≤ (K*Real.exp (b*φ (seq k)))*Real.exp (-c*φ (seq k)) :=
            mul_le_mul_of_nonneg_right (hmass k) (Real.exp_pos _).le
          _ = _ := by
            rw [show -(c-b)*φ (seq k) = b*φ (seq k)+(-c*φ (seq k)) by ring,
              Real.exp_add]
            ring
      have hsum : (D+B (seq k))^2 ≤ 2*D^2+2*B (seq k)^2 := by
        nlinarith [sq_nonneg (D-B (seq k))]
      have hh := mul_le_mul_of_nonneg_right hsum (Real.exp_pos (-c*φ (seq k))).le
      have he : Real.exp (-(c*φ (seq k))/2)^2 = Real.exp (-c*φ (seq k)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
        ring
      dsimp [T]
      rw [mul_pow, mul_pow, he]
      nlinarith
    have hTt : Tendsto T atTop (𝓝 0) := tendsto_zero_of_sq hT0 hT2
    have hsumt : Tendsto (fun k => H k+T k) atTop (𝓝 0) := by
      simpa only [add_zero] using hHt.add hTt
    obtain ⟨k, hk, hpk⟩ := ((hsumt.eventually_lt_const hL).and
      (hφs.eventually_gt_atTop 0)).exists
    have hlow := hcut (seq k) (c*φ (seq k)) (mul_pos hc hpk)
    change L ≤ H k+T k at hlow
    exact (not_lt_of_ge hlow) hk
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [not_frequently.mp (hnot K)] with n hn
  exact (lt_of_not_ge hn).le

end RiemannResearch.Analysis
