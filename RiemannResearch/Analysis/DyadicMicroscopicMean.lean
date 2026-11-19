/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.DyadicHorizontalMean
import RiemannResearch.Analysis.ConreyHorizontalStopLoss

/-! # The cumulative microscopic mean under the sampled dyadic input -/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem microscopicExcess_zero_eq_firstMark {T : ℝ} (hT : 1 < T) :
    microscopicExcess T 0 = displacementMoment T 1 * Real.log T := by
  have hterm (c : Copies T) : max (copyDisplacement T c * Real.log T - 0) 0 =
      copyDisplacement T c * Real.log T := by
    rw [sub_zero]
    exact max_eq_left (mul_nonneg (abs_nonneg (c.1.1.re-1/2)) (Real.log_pos hT).le)
  simp only [microscopicExcess,hterm,displacementMoment,pow_one]
  rw [← Finset.sum_mul]
  ring

/-- The cumulative one-sided cap converts to the scaled mark using the
count ratio tending to one. -/
theorem microscopicExcess_zero_mean_of_oneSided
    (hMean : MeanUpper oneSidedHeightMean ((32133/100000)/(2*Real.pi))) :
    MeanUpper (fun T => microscopicExcess T 0) (64266/100000) := by
  let c : ℝ := (32133/100000)/(2*Real.pi)
  let m : ℝ := 64266/100000
  let R (T : ℝ) := (Ncount 0 T : ℝ)/(T*Real.log T/(2*Real.pi))
  have hr : Tendsto R atTop (𝓝 1) := tendsto_count_div_mainTerm
  have hc : MeanUpper oneSidedHeightMean c := hMean
  have hmc : (4*Real.pi)*c = m := by dsimp only [c,m]; field_simp [Real.pi_ne_zero] <;> ring
  intro ε hε
  have hden : 0<m+ε := by dsimp only [m]; positivity
  have hnum : 0<m+ε/2 := by dsimp only [m]; positivity
  have hq : (m+ε/2)/(m+ε) < 1 := (div_lt_one hden).mpr (by linarith only [hε])
  filter_upwards [hc (ε/(8*Real.pi)) (by positivity),
    hr.eventually (Ioi_mem_nhds hq),eventually_gt_atTop (1:ℝ)] with T hF hR hT
  change (m+ε/2)/(m+ε) < R T at hR
  have hR0 : 0<R T := (div_pos hnum hden).trans hR
  have hN : (Ncount 0 T : ℝ) ≠ 0 := by intro hz; simp [R,hz] at hR0
  change microscopicExcess T 0 ≤ m+ε
  rw [microscopicExcess_zero_eq_firstMark hT]
  apply le_of_mul_le_mul_right _ hR0
  rw [show (displacementMoment T 1*Real.log T)*R T=(4*Real.pi)*oneSidedHeightMean T
    by exact firstMark_mul_countRatio_eq hT hN]
  calc
    _ ≤ (4*Real.pi)*(c+ε/(8*Real.pi)) := mul_le_mul_of_nonneg_left hF (by positivity)
    _ = m+ε/2 := by rw [mul_add,hmc]; field_simp [Real.pi_ne_zero] <;> ring
    _ ≤ _ := by linarith only [((div_lt_iff₀ hden).mp hR)]

/-- The published density route supplies the initial bound for the dyadic
iteration, giving the manuscript's mark cap on the actual copies. -/
theorem microscopicExcess_zero_of_manuscriptDyadic {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) (hm : ManuscriptDyadicRightCap) :
    MeanUpper (fun T => microscopicExcess T 0) (64266/100000) :=
  microscopicExcess_zero_mean_of_oneSided (cumulative_right_mean_of_manuscript ha hD hm)

/-- An upper dyadic recurrence propagates one bound on [H,2H] all the way
to infinity. It provides the bounded initial value for geometric iteration. -/
theorem meanUpper_of_dyadic_compact {f : ℝ → ℝ} {b : ℝ}
    (hc : ∀ H : ℝ, 0 < H → ∃ A : ℝ, ∀ t ∈ Icc H (2*H), f t ≤ A)
    (hd : MeanUpper (fun T => 2*f (2*T)-f T) b) : MeanUpper f b := by
  apply meanUpper_of_dyadic _ hd
  obtain ⟨H₁,hH₁⟩ := eventually_atTop.mp (hd 1 zero_lt_one)
  let H := max 1 H₁
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨A,hA⟩ := hc H hH
  let B := max A (b+1)
  have hb : ∀ n : ℕ, ∀ t : ℝ, H≤t → t≤(2:ℝ)^n*(2*H) → f t ≤ B := by
    intro n
    induction n with
    | zero =>
      intro t ht hthi
      exact (hA t ⟨ht,by simpa using hthi⟩).trans (le_max_left _ _)
    | succ n ih =>
      intro t ht hthi
      by_cases hseed : t≤2*H
      · exact (hA t ⟨ht,hseed⟩).trans (le_max_left _ _)
      have hh : H≤t/2 := by linarith only [hseed]
      have ih' := ih (t/2) hh (by rw [pow_succ] at hthi; linarith only [hthi])
      have hstep := hH₁ (t/2) ((le_max_right 1 H₁).trans hh)
      change 2*f (2*(t/2))-f (t/2) ≤ b+1 at hstep
      rw [show 2*(t/2)=t by ring] at hstep
      exact (show f t ≤ B by linarith only [hstep,ih',show b+1≤B from le_max_right _ _])
  refine ⟨B,?_⟩
  filter_upwards [eventually_ge_atTop H] with T hT
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  obtain ⟨n,hn⟩ := (hpow.eventually_ge_atTop (T/(2*H))).exists
  exact hb n T hT ((div_le_iff₀ (by positivity)).mp hn)

theorem oneSidedHeightMean_compact (H : ℝ) (hH : 0 < H) :
    ∃ A : ℝ, ∀ T ∈ Icc H (2*H), oneSidedHeightMean T ≤ A := by
  refine ⟨(Ncount 0 (2*H) : ℝ)/H,?_⟩
  intro T hT
  have ht : 0 < T := hH.trans_le hT.1
  have hn : (Ncount 0 T : ℝ) ≤ Ncount 0 (2*H) := by
    exact_mod_cast Ncount_mono (show (0:ℝ)≤0 by rfl) hT.2
  unfold oneSidedHeightMean
  rw [realSum_eq_copies]
  have hs : (∑ c : Copies T, max (c.1.1.re-1/2) 0) ≤ (Ncount 0 T : ℝ) := by
    calc
      _ ≤ ∑ _ : Copies T, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro c _
        have hd := displacement_lt_half c.1.2
        exact max_le ((le_abs_self _).trans (by linarith only [hd] : |c.1.1.re-1/2|≤1)) zero_le_one
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,one_mul,card_copies]
  exact (div_le_div_of_nonneg_right (hs.trans hn) ht.le).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hH hT.1)

/-- The manuscript dyadic bound alone controls the cumulative mean. -/
theorem cumulative_right_mean_of_manuscript_only (hm : ManuscriptDyadicRightCap) :
    MeanUpper oneSidedHeightMean ((32133/100000)/(2*Real.pi)) := by
  apply meanUpper_of_dyadic_compact oneSidedHeightMean_compact
  intro ε hε
  have hp : 0 < 2*Real.pi := by positivity
  filter_upwards [hm ((2*Real.pi)*ε) (mul_pos hp hε),eventually_gt_atTop (0:ℝ)] with T h ht
  rw [dyadicMean_eq_mass ht]
  have hn := (le_div_iff₀ hp).mpr (show ((rightDisplacementMass (2*T)-rightDisplacementMass T)/T)*
      (2*Real.pi) ≤ (32133/100000)+(2*Real.pi)*ε by simpa only [mul_comm] using h)
  exact hn.trans_eq (by field_simp [hp.ne'] <;> ring)

/-- The scaled absolute-displacement mean bound needs only the manuscript
dyadic premise on the actual zero copies. -/
theorem microscopicExcess_zero_of_manuscript_only (hm : ManuscriptDyadicRightCap) :
    MeanUpper (fun T => microscopicExcess T 0) (64266/100000) :=
  microscopicExcess_zero_mean_of_oneSided (cumulative_right_mean_of_manuscript_only hm)

end RiemannResearch.Analysis.ActualZeroOrdinate
