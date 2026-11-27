/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GLSSZeroCounts
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! # Simple zeros from a tested pair sum

Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh, Lemma 7 and §7,
<https://arxiv.org/abs/2306.04799>. The diagonal uses the analytic
multiplicity of each distinct complex zero. The tested pair estimate,
diagonal domination, and remainder bound are explicit hypotheses.
-/

noncomputable section
open Filter Asymptotics Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroCollisionCertificate
open ActualZeroOrdinate

/-- The ordered-pair count on the complex diagonal in BGSTB (7.1). -/
def analyticMultiplicitySquareSum (T : ℝ) : ℕ :=
  ∑ ρ ∈ cutoff T, (zeroMult ρ)^2

/-- Each multiple zero of order m contributes at least 2m to the square sum. -/
theorem twice_count_le_simple_add_analytic_square (T : ℝ) :
    2 * Ncount 0 T ≤ simpleZeroCount T + analyticMultiplicitySquareSum T := by
  classical
  rw [count_eq_sum, Finset.mul_sum]
  calc
    _ ≤ ∑ ρ ∈ cutoff T, ((if zeroMult ρ = 1 then 1 else 0) + (zeroMult ρ)^2) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      by_cases h : zeroMult ρ = 1
      · simp [h]
      · have htwo : 2 ≤ zeroMult ρ := by have := multiplicity_pos hρ; omega
        simpa [h, sq] using Nat.mul_le_mul_right (zeroMult ρ) htwo
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_boole]; rfl

/-- The Section 7 deduction with k = 2πK(0), A the complete tested sum
in Lemma 7 and S its signed remainder. Any certified p with a < (2-p)k
is an eventual lower bound for the analytic simple-zero proportion. -/
theorem simple_proportion_of_bgstb_pair_bound {A S : ℝ → ℝ} {k a p : ℝ} (hk : 0 < k)
    (hA : Tendsto (fun T : ℝ => A T / (Ncount 0 T : ℝ)) atTop (𝓝 a))
    (hS : S =o[atTop] (fun T : ℝ => (Ncount 0 T : ℝ) / Real.exp 1))
    (hdiag : ∀ᶠ T : ℝ in atTop, k * (analyticMultiplicitySquareSum T : ℝ) ≤ A T - S T)
    (hp : a < (2 - p) * k) :
    ∀ᶠ T : ℝ in atTop, p < (simpleZeroCount T : ℝ) / (Ncount 0 T : ℝ) := by
  have hSN : S =o[atTop] (fun T : ℝ => (Ncount 0 T : ℝ)) := by
    apply hS.trans_isBigO
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards with T
    have hn : (0 : ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg (div_nonneg hn (Real.exp_pos 1).le)]
      using div_le_self hn (Real.one_le_exp zero_le_one)
  have hlim : Tendsto (fun T : ℝ => A T / (Ncount 0 T : ℝ) - S T / (Ncount 0 T : ℝ))
      atTop (𝓝 a) := by simpa using hA.sub hSN.tendsto_div_nhds_zero
  filter_upwards [hlim.eventually (gt_mem_nhds hp), hdiag, eventually_count_pos] with T hbound hd hN
  have hn : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hN
  have hr : A T - S T < (2 - p) * k * (Ncount 0 T : ℝ) := (div_lt_iff₀ hn).mp
    (by simpa only [sub_div] using hbound)
  have hm : (analyticMultiplicitySquareSum T : ℝ) < (2 - p) * (Ncount 0 T : ℝ) := by
    by_contra! h
    have hm' := mul_le_mul_of_nonneg_left h hk.le
    linarith only [hd, hr, hm']
  have hf : (2 : ℝ) * (Ncount 0 T : ℝ) ≤
      (simpleZeroCount T : ℝ) + (analyticMultiplicitySquareSum T : ℝ) := by
    exact_mod_cast twice_count_le_simple_add_analytic_square T
  exact (lt_div_iff₀ hn).mpr (by linarith only [hm, hf])

/--
info: 'RiemannResearch.Analysis.ActualZeroCollisionCertificate.simple_proportion_of_bgstb_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simple_proportion_of_bgstb_pair_bound

end RiemannResearch.Analysis.ActualZeroCollisionCertificate
