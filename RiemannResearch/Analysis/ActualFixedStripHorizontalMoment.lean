/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualPolynomialHorizontalMoment
import RiemannResearch.Analysis.ActualLewkoDensity

/-!
# Six fixed-strip rates for polynomially small microscopic mean

The analytic inputs are the separately named Guth–Maynard hypothesis
(Theorem 1.2, doi:10.4007/annals.2026.203.2.6) and Lewko's registered
estimate (Palomar PALOMAR-2026-10-11-000010 v1). This file inverts their
pointwise minimum with strict exponent slack at a fixed abscissa.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

local notation "m₁" => (fun T : ℝ => displacementMoment T 1 * Real.log T)
local notation "m₂" => (fun T : ℝ => displacementMoment T 2 * Real.log T ^ 2)
local notation "M₁" => (fun T : ℝ => Real.log (1 / m₁ T))

/-- Transfer any fixed-abscissa count with exponent E strictly below 1-p.
The epsilon in the count is chosen before the height limit. -/
theorem actual_secondMoment_ratio_le_of_fixed_density_exponent
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    {p σ E c : ℝ} (hp : 0 < p) (hσ : 1 / 2 ≤ σ) (hE : E < 1 - p)
    (hc : (σ - 1 / 2) / p < c) (hm : ∀ᶠ i in l, 0 < m₁ (T i))
    (hr : Tendsto (fun i => M₁ (T i) / Real.log (T i)) l (𝓝 p))
    (hcount : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      rightInclusiveCount t σ ≤ C * t ^ (E + ε)) :
    ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c := by
  let ε := (1 - p - E) / 2
  let d := 1 - (E + ε)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hpd : p < d := by dsimp [d, ε]; linarith
  obtain ⟨C, hC, hd⟩ := hcount ε hε
  obtain ⟨b, hb, hn⟩ := exists_count_normalization
  apply actual_secondMoment_ratio_le_of_fixed_cut hT hp hpd (sub_nonneg.mpr hσ)
    (K := 2 * C / b) (by positivity) hc hm hr
  suffices H : ∀ᶠ t : ℝ in atTop, strictTail t (σ - 1 / 2) / (Ncount 0 t : ℝ) ≤
      (2 * C / b) * Real.log t ^ 2 * Real.exp (-d * Real.log t) from hT.eventually H
  filter_upwards [hn, hd, eventually_ge_atTop (Real.exp 1)] with t hn hd ht
  have ht0 := (Real.exp_pos 1).trans_le ht
  have hL : 1 ≤ Real.log t := by simpa using Real.log_le_log (Real.exp_pos 1) ht
  have hLp : 0 < Real.log t := zero_lt_one.trans_le hL
  have hN : 0 < (Ncount 0 t : ℝ) := lt_of_lt_of_le (by positivity) hn
  have htail := strictTail_le_twice_inclusive t (σ - 1 / 2) (sub_nonneg.mpr hσ)
  rw [show 1 / 2 + (σ - 1 / 2) = σ by ring] at htail
  have H := htail.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  have he : t ^ (E + ε) = t * Real.exp (-d * Real.log t) := by
    rw [Real.rpow_def_of_pos ht0, show Real.log t * (E + ε) =
      Real.log t + (-d * Real.log t) by dsimp [d]; ring,
      Real.exp_add, Real.exp_log ht0]
  rw [he] at H
  have hn' : b * t ≤ (Ncount 0 t : ℝ) :=
    (le_mul_of_one_le_right (mul_nonneg hb.le ht0.le) hL).trans hn
  have hK : 0 ≤ 2 * C / b := by positivity
  have hlog : 1 ≤ Real.log t ^ (2 : ℕ) := one_le_pow₀ hL
  apply (div_le_iff₀ hN).mpr
  apply H.trans
  calc
    _ = ((2 * C / b) * Real.exp (-d * Real.log t)) * (b * t) := by field_simp [hb.ne'] <;> ring
    _ ≤ ((2 * C / b) * Real.exp (-d * Real.log t)) * (Ncount 0 t : ℝ) :=
      mul_le_mul_of_nonneg_left hn' (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hN.le
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK hlog) (Real.exp_pos _).le

/-- The abscissa approached from the right. The branch with value 3/4
preserves the jump in Lewko's estimate. -/
def horizontalStripCrossing (p : ℝ) : ℝ :=
  if p < 5 / 17 then (1 + 2 * p) / (2 + p)
  else if p < 5 / 14 then (15 + 3 * p) / (25 - 7 * p)
  else if p < 2 / 5 then (5 + 4 * p) / 9
  else if p < 4 / 9 then (12 + 3 * p) / (20 - 5 * p)
  else if p < 1 / 2 then 3 / 4
  else 3 / (5 - 2 * p)

private theorem fixed_combined_count (hG : GuthMaynardDensityHypothesis)
    (hL : LewkoDensityHypothesis) {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      rightInclusiveCount t σ ≤ C * t ^ (lewkoGuthMaynardCoefficient σ * (1 - σ) + ε) := by
  unfold lewkoGuthMaynardCoefficient
  rcases le_total (lewkoDensityCoefficient σ) (15 / (3 + 5 * σ)) with h | h
  · rw [min_eq_left h]
    obtain ⟨C,hC,H⟩ := fixed_lewko_density hL hσ hε
    exact ⟨C,hC,(eventually_ge_atTop (2 : ℝ)).mono fun t ht => H t ht⟩
  · rw [min_eq_right h, show 15 / (3 + 5 * σ) * (1 - σ) = guthMaynardExponent σ by
      unfold guthMaynardExponent; ring]
    exact hG σ hσ ε hε

/-- Strict eventual form of all six inverse branches, counting every zero
occurrence. For p=1 the physical support suffices. -/
theorem actual_secondMoment_ratio_le_of_lewko_guthMaynard
    (hG : GuthMaynardDensityHypothesis) (hL : LewkoDensityHypothesis)
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    {p c : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hm : ∀ᶠ i in l, 0 < m₁ (T i))
    (hr : Tendsto (fun i => M₁ (T i) / Real.log (T i)) l (𝓝 p))
    (hc : (horizontalStripCrossing p - 1 / 2) / p < c) :
    ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c := by
  let s := horizontalStripCrossing p
  have hsc : s < 1 / 2 + c * p := by
    have h := (div_lt_iff₀ hp).mp hc
    dsimp [s]
    linarith
  have transfer {v : ℝ} (hs : 1 / 2 ≤ s) (hv : s < v) (hv1 : v ≤ 1)
      (hexp : ∀ σ : ℝ, s < σ → σ < v → lewkoGuthMaynardCoefficient σ * (1 - σ) < 1 - p) :
      ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c := by
    obtain ⟨σ, hlow, hhigh⟩ := exists_between (lt_min hv hsc)
    have H : σ ∈ Icc (1 / 2 : ℝ) 1 := ⟨hs.trans hlow.le, (hhigh.trans_le (min_le_left _ _)).le.trans hv1⟩
    apply actual_secondMoment_ratio_le_of_fixed_density_exponent hT hp H.1
      (hexp σ hlow (hhigh.trans_le (min_le_left _ _)))
      ((div_lt_iff₀ hp).mpr (by linarith only [hhigh.trans_le (min_le_right _ _)])) hm hr
    exact fixed_combined_count hG hL H
  by_cases h₁ : p < 5 / 17
  · apply actual_secondMoment_ratio_le_of_polynomial_mean hT hp hp1 _ hm hr
    have hden : 0 < 2 + p := by positivity
    have heq : (horizontalStripCrossing p - 1 / 2) / p = 3 / (4 + 2 * p) := by
      rw [horizontalStripCrossing, if_pos h₁, show 4 + 2 * p=2 * (2 + p) by ring]
      field_simp [hp.ne', hden.ne'] <;> ring
    rwa [← heq]
  by_cases h₂ : p < 5 / 14
  · have hden : 0 < 25 - 7 * p := by linarith
    have hs : s = (15 + 3 * p) / (25 - 7 * p) := by simp [s,horizontalStripCrossing,h₁,h₂]
    have hLo : 9 / 13 ≤ s := by rw [hs]; apply (le_div_iff₀ hden).mpr; linarith
    have hHi : s < 5 / 7 := by rw [hs]; apply (div_lt_iff₀ hden).mpr; linarith
    apply transfer (by linarith) hHi (by norm_num)
    intro σ hσ hs'
    have hi := (div_lt_iff₀ hden).mp (hs ▸ hσ)
    rw [lewkoGuthMaynardCoefficient_eq ⟨by linarith,by linarith⟩,
      if_neg (by linarith), if_pos hs'.le, div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < 7 * σ + 3)).mpr
    nlinarith only [hi]
  by_cases h₃ : p < 2 / 5
  · have hs : s = (5 + 4 * p) / 9 := by simp [s,horizontalStripCrossing,h₁,h₂,h₃]
    have hLo : 5 / 7 ≤ s := by rw [hs]; linarith
    have hHi : s < 11 / 15 := by rw [hs]; linarith
    apply transfer (by linarith) hHi (by norm_num)
    intro σ hσ hs'
    rw [lewkoGuthMaynardCoefficient_eq ⟨by linarith,by linarith⟩,
      if_neg (by linarith), if_neg (by linarith), if_pos hs'.le]
    rw [hs] at hσ
    linarith
  by_cases h₄ : p < 4 / 9
  · have hden : 0 < 20 - 5 * p := by linarith
    have hs : s = (12 + 3 * p) / (20 - 5 * p) := by simp [s,horizontalStripCrossing,h₁,h₂,h₃,h₄]
    have hLo : 11 / 15 ≤ s := by rw [hs]; apply (le_div_iff₀ hden).mpr; linarith
    have hHi : s < 3 / 4 := by rw [hs]; apply (div_lt_iff₀ hden).mpr; linarith
    apply transfer (by linarith) hHi (by norm_num)
    intro σ hσ hs'
    have hi := (div_lt_iff₀ hden).mp (hs ▸ hσ)
    rw [lewkoGuthMaynardCoefficient_eq ⟨by linarith,by linarith⟩,
      if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_pos hs'.le,
      div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < 3 + 5 * σ)).mpr
    nlinarith only [hi]
  by_cases h₅ : p < 1 / 2
  · have hs : s = 3 / 4 := by
      dsimp only [s]
      rw [horizontalStripCrossing, if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_pos h₅]
    apply transfer (by rw [hs]; norm_num) (v := 1) (by rw [hs]; norm_num) le_rfl
    intro σ hσ hs'
    rw [hs] at hσ
    rw [lewkoGuthMaynardCoefficient_eq ⟨by linarith,hs'.le⟩,
      if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
      div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < 2 * σ)).mpr
    nlinarith only [hσ, mul_nonneg (sub_nonneg.mpr h₅.le) (by linarith : 0 ≤ 2 * σ)]
  have hs : s = 3 / (5 - 2 * p) := by
    dsimp only [s]
    rw [horizontalStripCrossing, if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅]
  rcases lt_or_eq_of_le hp1 with hlt | rfl
  · have hden : 0 < 5 - 2 * p := by linarith
    have hLo : 3 / 4 ≤ s := by rw [hs]; apply (le_div_iff₀ hden).mpr; linarith
    have hHi : s < 1 := by rw [hs]; apply (div_lt_iff₀ hden).mpr; linarith
    apply transfer (by linarith) hHi le_rfl
    intro σ hσ hs'
    have hi := (div_lt_iff₀ hden).mp (hs ▸ hσ)
    rw [lewkoGuthMaynardCoefficient_eq ⟨by linarith,hs'.le⟩,
      if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
      div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < 2 * σ)).mpr
    nlinarith only [hi]
  · apply actual_secondMoment_ratio_le_of_polynomial_mean hT hp hp1 _ hm hr
    change (s - 1 / 2) / 1 < c at hc
    rw [hs] at hc
    norm_num at hc ⊢
    exact hc

end RiemannResearch.Analysis.ActualZeroOrdinate
