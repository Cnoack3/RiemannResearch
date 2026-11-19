/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSizeBiasedDisplacement
import RiemannResearch.Analysis.ActualSelbergDensityInterpolation

/-!
# Horizontal moment rates along a family of heights

The Gabriel–Littlewood estimate in Chourasiya and Simonič, Theorem 1,
<https://arxiv.org/abs/2507.15184>, supplies the three-log density bound.
Size-biased Jensen on the actual multiplicity law leaves two logarithms
after normalization. The rate argument follows SparseHorizontalMomentModulus20261119.md.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

local notation "m₁" => (fun t : ℝ => displacementMoment t 1 * Real.log t)
local notation "m₂" => (fun t : ℝ => displacementMoment t 2 * Real.log t ^ 2)
local notation "M₁" => (fun t : ℝ => Real.log (1 / m₁ t))
local notation "ell" => (fun t : ℝ => Real.log (Real.log t))

/-- At every tilt below 4/3, the surplus in the normalized exponential
first moment is at most two powers of log T. -/
theorem exists_sizeBiased_log_sq_cap_of_ingham {a : ℝ} (ha : 0 < a) (hab : a < 4 / 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop,
      microscopicSizeBiasedTilt t a ≤ K * Real.log t ^ 2 := by
  obtain ⟨C, hC, hd⟩ := (uniformLogLossDensity_iff_power _ _).mp ingham_tangent_density_log_loss
  obtain ⟨b, hb, hn⟩ := exists_count_normalization
  let K := 2 * C * (4 / 3) / (4 / 3 - a) ^ 2 / b
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  filter_upwards [hd, hn, eventually_gt_atTop (1 : ℝ)] with t hd hn ht
  have hL := Real.log_pos ht
  have hN : 0 < (Ncount 0 t : ℝ) := lt_of_lt_of_le (by positivity) hn
  have hD : SelbergDensityBound t (C * Real.log t ^ 2) (4 / 3) := by
    intro σ hσ
    apply (hd σ hσ).trans_eq
    rw [show Real.log t ^ (3 : ℝ) = Real.log t ^ (3 : ℕ) by norm_cast]
    ring
  apply (microscopicSizeBiasedTilt_le_of_selberg ht (by positivity) ha hab hD).trans
  apply (div_le_iff₀ hN).mpr
  calc
    _ = (K * Real.log t ^ 2) * (b * t * Real.log t) := by
      dsimp [K]
      field_simp [hb.ne', (sub_pos.mpr hab).ne']
    _ ≤ (K * Real.log t ^ 2) * (Ncount 0 t : ℝ) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ _ := by gcongr; linarith

private theorem log_reciprocal_tendsto {ι : Type*} {l : Filter ι} {m : ι → ℝ}
    (hm : Tendsto m l (𝓝 0)) (hp : ∀ᶠ i in l, 0 < m i) :
    Tendsto (fun i => Real.log (1 / m i)) l atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [hp, hm.eventually (Iio_mem_nhds (Real.exp_pos (-b)))] with i hi hs
  have hz := Real.log_le_log hi hs.le
  rw [Real.log_exp] at hz
  rw [Real.log_div one_ne_zero hi.ne', Real.log_one]
  linarith

private theorem log_cap_div_mean {K L m : ℝ} (hK : 0 < K) (hL : 0 < L) (hm : 0 < m) :
    Real.log (K * L ^ 2 / m) =
      Real.log K + 2 * Real.log L + Real.log (1 / m) := by
  rw [Real.log_div (mul_pos hK (pow_pos hL _)).ne' hm.ne',
    Real.log_mul hK.ne' (pow_pos hL _).ne', Real.log_pow,
    Real.log_div one_ne_zero hm.ne', Real.log_one]
  push_cast
  ring

private theorem normalize_log_bound {a m M : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hM : 0 < M) (u v : ℝ) :
    ((m / a) * (u + 2 * v + M)) / (m * M) =
      (1 + u / M + 2 * (v / M)) / a := by
  field_simp [hm.ne', hM.ne', ha.ne']
  ring

/-- With d the limiting ratio log log T / log(1/m), every c above
(3/4)(1+2d) bounds the scaled second moment eventually. The filter
allows a sparse sequence of heights with positive vanishing mean. -/
theorem actual_secondMoment_ratio_le_of_ingham_rate
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    (hm : Tendsto (fun i => m₁ (T i)) l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < m₁ (T i)) {d c : ℝ} (hd : 0 ≤ d)
    (hr : Tendsto (fun i => ell (T i) / M₁ (T i)) l (𝓝 d))
    (hc : (3 / 4) * (1 + 2 * d) < c) :
    ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c := by
  have hv : 0 < 1 + 2 * d := by linarith
  have hc0 : 0 < c := lt_trans (mul_pos (by norm_num) hv) hc
  have hx : (1 + 2 * d) / c < 4 / 3 := (div_lt_iff₀ hc0).mpr (by linarith only [hc])
  obtain ⟨a, hlo, hhi⟩ := exists_between hx
  have ha := (div_pos hv hc0).trans hlo
  have hac := (div_lt_iff₀ hc0).mp hlo
  obtain ⟨K, hK, hcap⟩ := exists_sizeBiased_log_sq_cap_of_ingham ha hhi
  have hM := log_reciprocal_tendsto hm hp
  have hk : Tendsto (fun i => Real.log K / M₁ (T i)) l (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := Real.log K)).mul (tendsto_inv_atTop_zero.comp hM)
  have hlim := hk.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hr)
  have hsmall := hlim.eventually (Iio_mem_nhds (show 0 + 2 * d < a * c - 1 by linarith only [hac]))
  filter_upwards [hp, hT.eventually hcap, hT.eventually eventually_count_pos,
    hT.eventually (eventually_gt_atTop (1 : ℝ)), hM.eventually (eventually_gt_atTop (0 : ℝ)),
    hsmall] with i hi hcap hn ht hMpos hs
  let t := T i
  have hL : 0 < Real.log t := Real.log_pos ht
  have hN : 0 < (Ncount 0 t : ℝ) := by exact_mod_cast hn
  have hraw := FiniteSizeBiasedExponential.secondMoment_le_log_of_tilt ha hi
    ((actual_sizeBiased_exp ht.le hN hi).trans hcap)
  have hlog : Real.log (K * Real.log t ^ 2 / m₁ t) =
      Real.log K + 2 * ell t + M₁ t := log_cap_div_mean hK hL hi
  change m₂ t ≤ (m₁ t / a) * Real.log (K * Real.log t ^ 2 / m₁ t) at hraw
  rw [hlog] at hraw
  change Real.log K / M₁ t + 2 * (ell t / M₁ t) < a * c - 1 at hs
  calc
    m₂ t / (m₁ t * M₁ t) ≤ ((m₁ t / a) * (Real.log K + 2 * ell t + M₁ t)) / (m₁ t * M₁ t) :=
      div_le_div_of_nonneg_right hraw (mul_pos hi hMpos).le
    _ = (1 + Real.log K / M₁ t + 2 * (ell t / M₁ t)) / a :=
      normalize_log_bound ha hi hMpos _ _
    _ ≤ c := (div_le_iff₀ ha).mpr (by linarith only [hs, mul_comm a c])

/-- The coefficient 3/4 requires only the proved Ingham estimate when
log log T is little-o of log(1/m). -/
theorem actual_secondMoment_ratio_le_of_fast_mean
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    (hm : Tendsto (fun i => m₁ (T i)) l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < m₁ (T i))
    (hr : Tendsto (fun i => ell (T i) / M₁ (T i)) l (𝓝 0))
    {c : ℝ} (hc : 3 / 4 < c) :
    ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c :=
  actual_secondMoment_ratio_le_of_ingham_rate hT hm hp le_rfl hr (by simpa using hc)

/-- For a finite positive limit λ of log(1/m)/log log T, choose the
stronger of Conrey–Baluyot and Ingham. Their coefficients agree at λ=12. -/
theorem actual_secondMoment_ratio_le_of_loglog_rate
    (hD : ConreyBaluyotDensityHypothesis)
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    (hm : Tendsto (fun i => m₁ (T i)) l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < m₁ (T i)) {r c : ℝ} (hr : 0 < r)
    (hlim : Tendsto (fun i => M₁ (T i) / ell (T i)) l (𝓝 r))
    (hc : min (7 / 8) ((3 / 4) * (1 + 2 / r)) < c) :
    ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c := by
  rcases min_lt_iff.mp hc with h | h
  · apply FiniteSizeBiasedExponential.eventually_secondMoment_ratio_le_of_tilts_lt_eight_sevenths
      h hm hp
    intro a ha ha'
    obtain ⟨K, hK, hb⟩ := exists_actual_sizeBiased_cap_of_conreyBaluyot hD ha ha'
    refine ⟨K, hK, ?_⟩
    filter_upwards [hp, hT.eventually hb, hT.eventually eventually_count_pos,
      hT.eventually (eventually_gt_atTop (1 : ℝ))] with i hi hb hn ht
    exact (actual_sizeBiased_exp ht.le (by exact_mod_cast hn) hi).trans hb.1
  · apply actual_secondMoment_ratio_le_of_ingham_rate hT hm hp (inv_nonneg.mpr hr.le)
    · simpa only [inv_div] using hlim.inv₀ hr.ne'
    · simpa only [div_eq_mul_inv] using h

end RiemannResearch.Analysis.ActualZeroOrdinate
