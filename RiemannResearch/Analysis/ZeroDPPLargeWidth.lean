import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! Restoring all self-pairs after thinning. The large-width argument
takes the height limit at each fixed integer width before increasing the
width. The local third moment and the zeta-specific count comparison are
analytic inputs to the application. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace RiemannResearch.Analysis.DPPLargeWidth

/-- Expectation on the joint law of observation point and marks.
The corrected projected count moment is E[X²]+E[Z-X]. -/
theorem restored_count_loss_ge {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z X : Ω → ℝ)
    (hZ : MemLp Z 2 μ) (hX : MemLp X 2 μ)
    (hdom : ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ X ω ≤ Z ω) :
    (∫ ω, Z ω - X ω ∂μ)^2 - (∫ ω, Z ω - X ω ∂μ) ≤
      (∫ ω, Z ω ^ 2 ∂μ) - ((∫ ω, X ω ^ 2 ∂μ) + (∫ ω, Z ω - X ω ∂μ)) := by
  have hj := ProbabilityTheory.variance_nonneg (Z-X) μ
  rw [ProbabilityTheory.variance_eq_sub (hZ.sub hX)] at hj
  change 0 ≤ (∫ ω, (Z ω - X ω)^2 ∂μ) - (∫ ω, Z ω - X ω ∂μ)^2 at hj
  have hH : Integrable (fun ω => (Z ω - X ω)^2) μ := (hZ.sub hX).integrable_sq
  have hXS : Integrable (fun ω => (X ω)^2) μ := hX.integrable_sq
  have hZS : Integrable (fun ω => (Z ω)^2) μ := hZ.integrable_sq
  have hm : (∫ ω, (Z ω - X ω)^2 + (X ω)^2 ∂μ) ≤ (∫ ω, (Z ω)^2 ∂μ) := by
    apply integral_mono_ae (hH.add hXS) hZS
    filter_upwards [hdom] with ω hω
    change (Z ω - X ω)^2 + (X ω)^2 ≤ (Z ω)^2
    nlinarith [mul_nonneg hω.1 (sub_nonneg.mpr hω.2)]
  rw [integral_add hH hXS] at hm
  linarith

/-- Integrate the pointwise count-loss inequality on [k,k+1].
The first restored diagonal correction is r*d throughout the interval. -/
theorem integrated_restored_loss_ge (k d : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d)
    (full projected : ℝ → ℝ)
    (hf : IntervalIntegrable full volume k (k+1))
    (hp : IntervalIntegrable projected volume k (k+1))
    (hl : ∀ r ∈ Set.Icc k (k+1), (r*d)^2-r*d ≤ full r - projected r) :
    k^2*d^2-(k+1)*d ≤
      (∫ r in k..k+1, full r) - (∫ r in k..k+1, projected r) := by
  rw [← intervalIntegral.integral_sub hf hp]
  have hunit : (∫ _r in k..k+1, k^2*d^2-(k+1)*d) = k^2*d^2-(k+1)*d := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  rw [← hunit]
  apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hf.sub hp)
  intro r hr
  change k^2*d^2-(k+1)*d ≤ full r - projected r
  have hrk := mul_le_mul_of_nonneg_right hr.1 hd
  have hrt := mul_le_mul_of_nonneg_right hr.2 hd
  have hs := mul_self_le_mul_self (mul_nonneg hk hd) hrk
  nlinarith only [hs, hrt, hl r hr]

/-- An arbitrarily small relative second-moment error on cofinally many
unit-width intervals forces the omitted occurrence density to vanish.
Only an eventual height bound for each chosen width is required. -/
theorem vacancy_tendsto_of_large_width_bounds {ι : Type*} {l : Filter ι}
    (d : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ᶠ t in l, 0 ≤ d t ∧ d t ≤ D)
    (henv : ∀ η : ℝ, 0 < η → ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧
      ∀ᶠ t in l, (k:ℝ)^2 * (d t)^2 - ((k:ℝ)+1)*d t ≤ η*(k:ℝ)^2) :
    Tendsto d l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε^2 / 2 := by positivity
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max 1 (2*D/(ε^2/2)))
  obtain ⟨k, hk₀k, hkt⟩ := henv (ε^2/2) hη k₀
  have hk₀k' : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk₀k
  have hlarge := hk₀.trans_le hk₀k'
  have h1 : 1 < (k:ℝ) := (le_max_left _ _).trans_lt hlarge
  have hk : 0 < (k:ℝ) := lt_trans zero_lt_one h1
  have hkD : 2*D < (k:ℝ) * (ε^2/2) :=
    (div_lt_iff₀ hη).1 ((le_max_right _ _).trans_lt hlarge)
  filter_upwards [hd,hkt] with t hdt ht
  have hsmall : ((k:ℝ)+1)*d t < (k:ℝ)^2*(ε^2/2) := by
    calc
      _ ≤ ((k:ℝ)+1)*D := mul_le_mul_of_nonneg_left hdt.2 (by positivity)
      _ ≤ (k:ℝ)*(2*D) := by nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) hD]
      _ < (k:ℝ)*((k:ℝ)*(ε^2/2)) := mul_lt_mul_of_pos_left hkD hk
      _ = _ := by ring
  have hsqk : (k:ℝ)^2*(d t)^2 < (k:ℝ)^2*ε^2 := by nlinarith only [ht,hsmall]
  have hsq : (d t)^2 < ε^2 := (mul_lt_mul_iff_right₀ (sq_pos_of_pos hk)).1 hsqk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hdt.1]
  by_contra! hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hdt.1 hε.le)]

/-- Version with separate finite-height Jensen, full-minus-projected
envelope, and subquadratic-error hypotheses. -/
theorem vacancy_tendsto_of_subquadratic_comparison {ι : Type*} {l : Filter ι}
    (d : ι → ℝ) (full projected : ℕ → ι → ℝ) (e : ℕ → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hd : ∀ᶠ t in l, 0 ≤ d t ∧ d t ≤ D)
    (hpen : ∀ k : ℕ, 0 < k → ∀ᶠ t in l,
      (k:ℝ)^2 * (d t)^2 - ((k:ℝ)+1)*d t ≤ full k t - projected k t)
    (hupper : ∀ k : ℕ, 0 < k → ∀ᶠ t in l, full k t - projected k t ≤ e k*(k:ℝ)^2)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto d l (𝓝 0) := by
  apply vacancy_tendsto_of_large_width_bounds d D hD hd
  intro η hη k₀
  obtain ⟨k,hk,hlt⟩ := ((eventually_ge_atTop (max k₀ 1)).and
    (he.eventually (gt_mem_nhds hη))).exists
  have hpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hk)
  refine ⟨k, (le_max_left _ _).trans hk, ?_⟩
  filter_upwards [hpen k hpos,hupper k hpos] with t hp hu
  exact (hp.trans hu).trans (mul_le_mul_of_nonneg_right hlt.le (sq_nonneg _))

/-- The full statistic needs an upper estimate at all sufficiently large
widths. The projected statistic only needs a lower estimate at a cofinal
set of widths. The two estimates are centered at the same second moment. -/
theorem vacancy_tendsto_of_cofinal_projected_lower {ι : Type*} {l : Filter ι}
    (d : ι → ℝ) (full projected : ℕ → ι → ℝ) (center : ℕ → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hd : ∀ᶠ t in l, 0 ≤ d t ∧ d t ≤ D)
    (hpen : ∀ k : ℕ, 0 < k → ∀ᶠ t in l,
      (k:ℝ)^2 * (d t)^2 - ((k:ℝ)+1)*d t ≤ full k t - projected k t)
    (hfull : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ᶠ t in l,
      full k t ≤ center k + η*(k:ℝ)^2)
    (hprojected : ∀ η : ℝ, 0 < η → ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧
      ∀ᶠ t in l, center k - η*(k:ℝ)^2 ≤ projected k t) : Tendsto d l (𝓝 0) := by
  apply vacancy_tendsto_of_large_width_bounds d D hD hd
  intro η hη k₀
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨K,hK⟩ := eventually_atTop.1 (hfull (η/2) hhalf)
  obtain ⟨k,hk,hp⟩ := hprojected (η/2) hhalf (max (max k₀ 1) K)
  have hkk : max k₀ 1 ≤ k := (le_max_left _ _).trans hk
  have hKk : K ≤ k := (le_max_right _ _).trans hk
  have hpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hkk)
  refine ⟨k,(le_max_left _ _).trans hkk,?_⟩
  filter_upwards [hpen k hpos,hK k hKk,hp] with t hJ hF hP
  nlinarith only [hJ,hF,hP]

/--
info: 'RiemannResearch.Analysis.DPPLargeWidth.restored_count_loss_ge'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms restored_count_loss_ge

/--
info: 'RiemannResearch.Analysis.DPPLargeWidth.integrated_restored_loss_ge'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrated_restored_loss_ge

/--
info: 'RiemannResearch.Analysis.DPPLargeWidth.vacancy_tendsto_of_subquadratic_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vacancy_tendsto_of_subquadratic_comparison

/--
info: 'RiemannResearch.Analysis.DPPLargeWidth.vacancy_tendsto_of_cofinal_projected_lower'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vacancy_tendsto_of_cofinal_projected_lower

end RiemannResearch.Analysis.DPPLargeWidth
