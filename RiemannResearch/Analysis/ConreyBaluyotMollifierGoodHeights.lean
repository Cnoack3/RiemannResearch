/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotHorizontalArgument

/-!
# Nearby zero-free heights for the actual mollified zeta

For an analytic function nonzero at the center of a suitable compact disk,
the zero divisor has finite support. Avoiding its finite set of ordinates
gives zero-free horizontal segments at arbitrarily close heights.

The actual specialization is uniform in the coupled sigma,y strip. The
mollifier parameters remain fixed while the height moves. The Littlewood
boundary-limit passage is not asserted here.
-/

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- A finite set cannot fill a nonempty real open interval. -/
theorem exists_between_not_finset (S : Finset ℝ) (a b : ℝ) (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ x ∉ S := by
  classical
  induction S using Finset.induction_on generalizing a b with
  | empty =>
      refine ⟨(a + b) / 2, by linarith, by linarith, ?_⟩
      simp
  | @insert z S hz ih =>
      obtain ⟨x, hax, hxb, hxS⟩ := ih a b hab
      by_cases hxz : x = z
      · obtain ⟨y, hay, hyx, hyS⟩ := ih a x hax
        have hyz : y ≠ z := by intro he; rw [← hxz] at he; linarith
        refine ⟨y, hay, lt_trans hyx hxb, ?_⟩
        simpa only [Finset.mem_insert, not_or] using And.intro hyz hyS
      · refine ⟨x, hax, hxb, ?_⟩
        simpa only [Finset.mem_insert, not_or] using And.intro hxz hxS

/-- An analytic function nonzero at the right-hand center has a zero-free
horizontal segment at arbitrarily close heights, as long as the surrounding
closed disk has the indicated geometric margin. -/
theorem exists_zero_free_horizontal_near_of_analytic_disk
    (f : ℂ → ℂ) (a b T δ R : ℝ) (hab : a ≤ b) (hδ : 0 < δ)
    (hR : b - a + δ ≤ R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall ((b : ℂ) + (T : ℂ) * I) R))
    (hc : f ((b : ℂ) + (T : ℂ) * I) ≠ 0) :
    ∃ t : ℝ, |t - T| < δ ∧ ∀ x ∈ Set.Icc a b, f ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
  classical
  let c : ℂ := (b : ℂ) + (T : ℂ) * I
  let U := Metric.closedBall c |R|
  let D := MeromorphicOn.divisor f U
  have hRpos : 0 < R := by linarith
  have hf' : AnalyticOnNhd ℂ f U := by
    simpa only [U, abs_of_pos hRpos] using hf
  have hmer : MeromorphicOn f U := fun z hz => (hf' z hz).meromorphicAt
  have hfin : D.support.Finite :=
    hmer.divisor_support_finite_of_subset (isCompact_closedBall c |R|) (Subset.rfl)
  let S : Finset ℝ := hfin.toFinset.image Complex.im
  obtain ⟨t, ht1, ht2, htS⟩ :=
    exists_between_not_finset S (T - δ) (T + δ) (by linarith)
  have ht : |t - T| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  refine ⟨t, ht, ?_⟩
  intro x hx hz
  let w : ℂ := (x : ℂ) + (t : ℂ) * I
  have hxabs : |x - b| ≤ b - a := by
    rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1]
  have hnorm : ‖w - c‖ ≤ |x - b| + |t - T| := by
    simpa [w, c] using Complex.norm_le_abs_re_add_abs_im (w - c)
  have hw : w ∈ U := by
    change w ∈ Metric.closedBall c |R|
    rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos]
    linarith [ht.le]
  have hp := divisor_pos_of_zero_of_center_ne_zero hf' hc hw hz
  have hn : D w ≠ 0 := ne_of_gt hp
  have hwS : w ∈ D.support := by
    have hh : w ∈ Function.support (fun z : ℂ => D z) := Function.mem_support.mpr hn
    simpa [Function.locallyFinsuppWithin.support] using hh
  have himS : t ∈ S := by
    apply Finset.mem_image.mpr
    refine ⟨w, hfin.mem_toFinset.mpr hwS, ?_⟩
    simp [w]
  exact htS himS

/-- For fixed mollifier parameters, arbitrarily close zero-free horizontal
segments exist uniformly on the proved parameter strip. -/
theorem exists_uniform_mollifiedZeta_zero_free_heights
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ L : ℝ, b ≤ L → ∀ T : ℝ, L + 1 ≤ T →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ t : ℝ, |t - T| < δ ∧
              ∀ x ∈ Set.Icc (1 / 2 : ℝ) L,
                mollifiedZeta σ y ε ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
  obtain ⟨η, Y, b, hη, hη', hY, hb, hanchor⟩ :=
    exists_uniform_mollifiedZeta_right_real_lower hε
  refine ⟨η, Y, b, hη, hη', hY, hb, ?_⟩
  intro y hy σ hσ hση L hL T hT δ hδ hδ'
  let c : ℂ := (L : ℂ) + (T : ℂ) * I
  let R : ℝ := L - 1 / 4
  have hR0 : 0 < R := by dsimp [R]; linarith
  have hf : AnalyticOnNhd ℂ (mollifiedZeta σ y ε) (Metric.closedBall c R) := by
    intro w hw
    have hd : ‖w - c‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have him : |w.im - T| ≤ R := by
      have hh := (Complex.abs_im_le_norm (w - c)).trans hd
      simpa [c] using hh
    have him0 : 0 < w.im := by
      have hh := (abs_le.mp him).1
      dsimp [R] at hh
      linarith
    have hne : w ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    exact analyticAt_mollifiedZeta σ y ε hne
  have hcRe : (1 / 2 : ℝ) ≤ (mollifiedZeta σ y ε c).re :=
    hanchor y hy σ hσ hση c (by simp [c]; linarith)
  have hc : mollifiedZeta σ y ε c ≠ 0 := by
    intro he
    rw [he] at hcRe
    norm_num at hcRe
  exact exists_zero_free_horizontal_near_of_analytic_disk
    (mollifiedZeta σ y ε) (1 / 2) L T δ R
    (by linarith) hδ (by dsimp [R]; linarith) hf hc

end RiemannResearch.Analysis.ConreyBaluyot
