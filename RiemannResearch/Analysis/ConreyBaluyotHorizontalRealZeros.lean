/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMollifiedJensen

/-!
# Real-part zeros of the actual mollified zeta

The analytic-order/divisor comparison adapts the argument in
Hadamard/OrderOne/ZeroCountingBounds.lean, ported from Nicholas Bulka's
li-criterion-rh-equivalence-lean under the Apache 2.0 license.

Jensen's divisor bound now controls the finite number of distinct real-part
zeros on the horizontal segment. The argument-variation and boundary-limit
steps are not proved here.
-/

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Every distinct zero of a nontrivial analytic function contributes at least
one to its divisor on a closed disk. -/
theorem divisor_pos_of_zero_of_center_ne_zero
    {f : ℂ → ℂ} {c u : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c |r|))
    (hc : f c ≠ 0) (hu : u ∈ Metric.closedBall c |r|) (hz : f u = 0) :
    (0 : ℤ) < MeromorphicOn.divisor f (Metric.closedBall c |r|) u := by
  let U := Metric.closedBall c |r|
  let D := MeromorphicOn.divisor f U
  have hmer : MeromorphicOn f U := fun z hz => (hf z hz).meromorphicAt
  have han : AnalyticAt ℂ f u := hf u hu
  have hcU : c ∈ U := by simp [U, Metric.mem_closedBall, abs_nonneg r]
  have horderc : analyticOrderAt f c = 0 := (hf c hcU).analyticOrderAt_eq_zero.2 hc
  have horderc' : analyticOrderAt f c ≠ ⊤ := by simp [horderc]
  have hpre : IsPreconnected U := (convex_closedBall c |r|).isPreconnected
  have horder : analyticOrderAt f u ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected hpre hcU hu horderc'
  have hdiv : D u = (meromorphicOrderAt f u).untop₀ :=
    MeromorphicOn.divisor_apply hmer hu
  have hmerorder : meromorphicOrderAt f u = (analyticOrderAt f u).map (↑) :=
    han.meromorphicOrderAt_eq
  have horder0 : analyticOrderAt f u ≠ 0 := han.analyticOrderAt_ne_zero.2 hz
  cases hAU : analyticOrderAt f u with
  | top => exact False.elim (horder (by simp [hAU]))
  | coe n =>
      have hn : n ≠ 0 := by
        intro hn0
        apply horder0
        simp [hAU, hn0]
      have hDu : D u = (n : ℤ) := by simp [hdiv, hmerorder, hAU]
      change 0 < D u
      rw [hDu]
      exact_mod_cast Nat.pos_of_ne_zero hn

/-- A finite set of distinct zeros in a closed disk has cardinality at most
the sum of the analytic divisor in that disk. -/
theorem card_le_divisor_finsum_of_zeros
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c |r|)) (hc : f c ≠ 0)
    (S : Finset ℂ) (hS : ∀ u ∈ S, u ∈ Metric.closedBall c |r| ∧ f u = 0) :
    (S.card : ℝ) ≤
      ((∑ᶠ u : ℂ, MeromorphicOn.divisor f (Metric.closedBall c |r|) u : ℤ) : ℝ) := by
  classical
  let U := Metric.closedBall c |r|
  let D := MeromorphicOn.divisor f U
  have hmer : MeromorphicOn f U := fun z hz => (hf z hz).meromorphicAt
  have hfin : D.support.Finite :=
    hmer.divisor_support_finite_of_subset (isCompact_closedBall c |r|) (Subset.rfl)
  let sD := hfin.toFinset
  have hnonneg : ∀ u : ℂ, (0 : ℤ) ≤ D u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hpos : ∀ u ∈ S, (1 : ℤ) ≤ D u := by
    intro u hu
    have hh := hS u hu
    have hp := divisor_pos_of_zero_of_center_ne_zero hf hc hh.1 hh.2
    change 0 < D u at hp
    omega
  have hsub : S ⊆ sD := by
    intro u hu
    apply hfin.mem_toFinset.mpr
    have hn : D u ≠ 0 := by have := hpos u hu; omega
    have hn' : u ∈ Function.support (fun z : ℂ => D z) := Function.mem_support.mpr hn
    simpa [Function.locallyFinsuppWithin.support] using hn'
  have hsupp : Function.support (fun u : ℂ => D u) ⊆ sD := by
    intro u hu
    apply hfin.mem_toFinset.mpr
    simpa [Function.locallyFinsuppWithin.support] using hu
  have hsum : (∑ᶠ u : ℂ, D u) = ∑ u ∈ sD, D u :=
    finsum_eq_sum_of_support_subset (f := fun u : ℂ => D u) (s := sD) hsupp
  have hcard : (S.card : ℤ) ≤ ∑ᶠ u : ℂ, D u := by
    calc
      _ = ∑ _u ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ u ∈ S, D u := Finset.sum_le_sum hpos
      _ ≤ ∑ u ∈ sD, D u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hnonneg u)
      _ = _ := hsum.symm
  exact_mod_cast hcard

/-- On the real axis the symmetrization is exactly the embedded real part. -/
theorem heightSymmetrization_realAxis_eq (f : ℂ → ℂ) (T x : ℝ) :
    heightSymmetrization f T (x : ℂ) =
      ((f ((x : ℂ) + (T : ℂ) * I)).re : ℂ) := by
  apply Complex.ext
  · simp [heightSymmetrization_realAxis]
  · simp [heightSymmetrization, Complex.div_ofNat_im]

/-- Points on a horizontal segment at which the real part vanishes. -/
def horizontalRealZeros (f : ℂ → ℂ) (T a b : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Icc a b ∧ (f ((x : ℂ) + (T : ℂ) * I)).re = 0}

/-- The Jensen divisor estimate gives an actual finite real-part zero count.
It does not itself control a continuous argument of the original function. -/
theorem horizontalRealZeros_jensen_bound
    (f : ℂ → ℂ) (T b a r R M : ℝ)
    (hr : 0 < r) (hrR : r < R) (hT : R + 1 ≤ T)
    (ha : a ≤ b - R) (hM : 1 ≤ M)
    (hf : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ f w)
    (hbound : ∀ w : ℂ, a ≤ w.re → 1 ≤ w.im → |w.im - T| ≤ R → ‖f w‖ ≤ M)
    (hcenter : (1 / 2 : ℝ) ≤ (f ((b : ℂ) + (T : ℂ) * I)).re) :
    ∃ hZ : (horizontalRealZeros f T (b - r) b).Finite,
      (hZ.toFinset.card : ℝ) ≤ Real.log (2 * M) / Real.log (R / r) := by
  classical
  let g := heightSymmetrization f T
  let U := Metric.closedBall (b : ℂ) |r|
  let D := MeromorphicOn.divisor g U
  have hrT : |r| < T := by rw [abs_of_pos hr]; linarith
  have han : AnalyticOnNhd ℂ g U :=
    analyticOnNhd_heightSymmetrization_closedBall f T b |r| hrT hf
  have hc' : (1 / 2 : ℝ) ≤ (g (b : ℂ)).re := by
    change (1 / 2 : ℝ) ≤ (heightSymmetrization f T (b : ℂ)).re
    simpa only [heightSymmetrization_realAxis] using hcenter
  have hc : g (b : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hmer : MeromorphicOn g U := fun z hz => (han z hz).meromorphicAt
  have hDf : D.support.Finite :=
    hmer.divisor_support_finite_of_subset (isCompact_closedBall (b : ℂ) |r|) (Subset.rfl)
  have hpre : ((fun x : ℝ => (x : ℂ)) ⁻¹' D.support).Finite :=
    hDf.preimage Complex.ofReal_injective.injOn
  have hpoint : ∀ x ∈ horizontalRealZeros f T (b - r) b,
      (x : ℂ) ∈ U ∧ g (x : ℂ) = 0 := by
    intro x hx
    rcases hx with ⟨hxI, hx0⟩
    constructor
    · change (x : ℂ) ∈ Metric.closedBall (b : ℂ) |r|
      rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact abs_le.mpr ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    · change heightSymmetrization f T (x : ℂ) = 0
      rw [heightSymmetrization_realAxis_eq, hx0]
      simp
  have hZ : (horizontalRealZeros f T (b - r) b).Finite := hpre.subset (by
    intro x hx
    have hh := hpoint x hx
    have hp := divisor_pos_of_zero_of_center_ne_zero han hc hh.1 hh.2
    have hD : D (x : ℂ) ≠ 0 := ne_of_gt hp
    have hS : (x : ℂ) ∈ Function.support (fun z : ℂ => D z) :=
      Function.mem_support.mpr hD
    simpa [Function.locallyFinsuppWithin.support] using hS)
  refine ⟨hZ, ?_⟩
  let S : Finset ℂ := hZ.toFinset.image (fun x : ℝ => (x : ℂ))
  have hS : ∀ u ∈ S, u ∈ U ∧ g u = 0 := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact hpoint x (hZ.mem_toFinset.mp hx)
  have hcard : S.card = hZ.toFinset.card :=
    Finset.card_image_of_injective _ Complex.ofReal_injective
  have hcount := card_le_divisor_finsum_of_zeros han hc S hS
  have hj := heightSymmetrization_jensen_bound f T b a r R M
    hr hrR hT ha hM hf hbound hcenter
  calc
    (hZ.toFinset.card : ℝ) = (S.card : ℝ) := by rw [hcard]
    _ ≤ ((∑ᶠ u : ℂ, D u : ℤ) : ℝ) := hcount
    _ ≤ _ := hj

/-- Uniform logarithmic upper bound for the number of real-part zeros of
the actual mollified zeta on the horizontal segment. The continuous
phase and its displacement are handled by the downstream phase modules. -/
theorem exists_uniform_mollifiedZeta_horizontalRealZeros_bound
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧ 0 < C ∧
      (∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ s : ℂ, b ≤ s.re →
          1 / 2 ≤ (mollifiedZeta σ y ε s).re) ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ T : ℝ, b + 1 ≤ T →
          ∃ hZ : (horizontalRealZeros (mollifiedZeta σ y ε) T (1 / 2) b).Finite,
            (hZ.toFinset.card : ℝ) ≤
              Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
                Real.log ((b - 1 / 4) / (b - 1 / 2)) := by
  obtain ⟨η1, Y1, C, hη1, hη1', hY1, hC, hg⟩ :=
    exists_uniform_mollifiedZeta_linear_growth
  obtain ⟨η2, Y2, b, hη2, hη2', hY2, hb, hanchor⟩ :=
    exists_uniform_mollifiedZeta_right_real_lower hε
  let η := min η1 η2
  let Y := max Y1 Y2
  refine ⟨η, Y, b, C, by dsimp [η]; exact lt_min hη1 hη2,
    by dsimp [η]; exact (min_le_left _ _).trans_lt hη1',
    by dsimp [Y]; exact hY1.trans_le (le_max_left _ _),
    hb, hC, ?_, ?_⟩
  · intro y hy σ hσ hση s hs
    exact hanchor y ((le_max_right _ _).trans hy) σ hσ
      (by dsimp [η] at hση; linarith [min_le_right η1 η2]) s hs
  · intro y hy σ hσ hση T hT
    have hy1 : Y1 ≤ y := (le_max_left _ _).trans hy
    have hy2 : Y2 ≤ y := (le_max_right _ _).trans hy
    have hy0 : 0 ≤ y := by dsimp [Y] at hy; linarith [le_max_left Y1 Y2]
    have hs1 : σ ≤ 1 / 2 + η1 := by
      dsimp [η] at hση
      linarith [min_le_left η1 η2]
    have hs2 : σ ≤ 1 / 2 + η2 := by
      dsimp [η] at hση
      linarith [min_le_right η1 η2]
    let r := b - 1 / 2
    let R := b - 1 / 4
    let M := 1 + C * (T + R) * y
    have hr : 0 < r := by dsimp [r]; linarith
    have hrR : r < R := by dsimp [r, R]; linarith
    have hTR : R + 1 ≤ T := by dsimp [R]; linarith
    have ha : (1 / 4 : ℝ) ≤ b - R := by dsimp [R]; linarith
    have hTR0 : 0 ≤ T + R := by dsimp [R]; linarith
    have hM : 1 ≤ M := by
      dsimp [M]
      have hp : 0 ≤ C * (T + R) * y :=
        mul_nonneg (mul_nonneg hC.le hTR0) hy0
      linarith
    have hbound : ∀ w : ℂ, (1 / 4 : ℝ) ≤ w.re → 1 ≤ w.im →
        |w.im - T| ≤ R → ‖mollifiedZeta σ y ε w‖ ≤ M := by
      intro w hw hwi hnear
      have habs : |w.im| ≤ T + R := by
        rw [abs_of_nonneg (by linarith : 0 ≤ w.im)]
        have hn := (abs_le.mp hnear).2
        linarith
      have hgrowth := hg y hy1 σ hσ hs1 ε w hw
        (by rw [abs_of_nonneg (by linarith : 0 ≤ w.im)]; exact hwi)
      calc
        _ ≤ C * |w.im| * y := hgrowth
        _ ≤ C * (T + R) * y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hC.le) hy0
        _ ≤ M := by dsimp [M]; linarith
    have hc : (1 / 2 : ℝ) ≤ (mollifiedZeta σ y ε ((b : ℂ) + (T : ℂ) * I)).re :=
      hanchor y hy2 σ hσ hs2 _ (by simp)
    have hh := horizontalRealZeros_jensen_bound (mollifiedZeta σ y ε) T b (1 / 4) r R M
      hr hrR hTR ha hM
      (fun w hw => differentiableAt_mollifiedZeta_of_im_pos σ y ε hw) hbound hc
    have heq : b - r = (1 / 2 : ℝ) := by dsimp [r]; ring
    simpa only [heq, r, R, M] using hh
end RiemannResearch.Analysis.ConreyBaluyot
