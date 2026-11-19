/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualInghamLittlewoodDensity
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Inverting a fixed physical strip at polynomially small microscopic mean

The count of Chourasiya and Simonič, Theorem 1, arXiv:2507.15184, has
exponent 3(1-σ)/(2-σ). See SparseHorizontalMomentModulus20261119.md for
the fixed-strip splitting argument. Every height law counts multiplicity.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

local notation "m₁" => (fun T : ℝ => displacementMoment T 1 * Real.log T)
local notation "m₂" => (fun T : ℝ => displacementMoment T 2 * Real.log T ^ 2)
local notation "M₁" => (fun T : ℝ => Real.log (1 / m₁ T))

/-- A fixed physical cut charges the central part to the true first moment.
The strict upper tail preserves copies with displacement equal to the cut. -/
theorem displacement_second_le_fixed_cut (T : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    displacementMoment T 2 ≤ u * displacementMoment T 1 +
      strictTail T u / (Ncount 0 T : ℝ) := by
  unfold displacementMoment strictTail FiniteStrictTail.tail
  rw [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hpos : 0 ≤ copyDisplacement T j := abs_nonneg _
  have hcap : copyDisplacement T j < 1 / 2 := displacement_lt_half j.1.2
  simp only [pow_one]
  split_ifs with h
  · nlinarith only [mul_nonneg hu hpos, mul_nonneg (sub_nonneg.mpr hcap.le) hpos, hcap]
  · have hle := not_lt.mp h
    nlinarith only [mul_nonneg (sub_nonneg.mpr hle) hpos]

/-- Fixed-cut normalized tail from the full curved Ingham exponent. -/
theorem exists_ingham_fixed_cut_cap {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (1 / 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      strictTail T u / (Ncount 0 T : ℝ) ≤ K * Real.log T ^ 2 *
        Real.exp (-(2 * u / (3 / 2 - u)) * Real.log T) := by
  obtain ⟨C,hC,hc⟩ := exists_ingham_littlewood_density_all_heights
  obtain ⟨b,hb,hn⟩ := exists_count_normalization
  refine ⟨2 * C / b, by positivity, ?_⟩
  filter_upwards [hn, eventually_ge_atTop (max 2 (Real.exp 1))] with T hn hT
  have ht2 := (le_max_left (2 : ℝ) (Real.exp 1)).trans hT
  have ht : 0 < T := by linarith
  have hL : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  have hL0 := zero_lt_one.trans_le hL
  have hN : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hn
  let d := 2 * u / (3 / 2 - u)
  have hd : 0 ≤ d := div_nonneg (by linarith [hu.1]) (by linarith [hu.2])
  have den : 0 < 3 / 2 - u := by linarith [hu.2]
  have he : 3 * (1 - (1 / 2 + u)) / (2 - (1 / 2 + u)) = 1 - d := by
    dsimp only [d]
    rw [show 2 - (1 / 2 + u) = 3 / 2 - u by ring]
    apply (div_eq_iff den.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ den.ne']
    ring
  have hs : 1 / 2 + u ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have H := hc T ht2 (1 / 2 + u) hs
  dsimp only at H
  rw [he] at H
  have logpow : Real.log T ^ (2 + (1 - d)) ≤ Real.log T ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith)
  have powid : T ^ (1 - d) = T * Real.exp (-d * Real.log T) := by
    rw [Real.rpow_def_of_pos ht, show Real.log T * (1 - d)=Real.log T + (-d * Real.log T) by ring,
      Real.exp_add, Real.exp_log ht]
  have tail := (strictTail_le_twice_inclusive T u hu.1).trans
    (mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le))
      (by norm_num : (0 : ℝ) ≤ 2))
  rw [powid] at tail
  apply (div_le_iff₀ hN).mpr
  apply tail.trans
  calc
    _ ≤ 2 * (C * ((T * Real.exp (-d * Real.log T)) * Real.log T ^ (3 : ℕ))) := by gcongr
    _ = (2 * C / b * Real.log T ^ 2 * Real.exp (-d * Real.log T)) * (b * T * Real.log T) := by
      field_simp [hb.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

private theorem cubic_exp_decay {ι : Type*} {l : Filter ι} {L : ι → ℝ}
    (hL : Tendsto L l atTop) {e : ℝ} (he : 0 < e) (K : ℝ) :
    Tendsto (fun i => K * L i ^ 3 * Real.exp (-(e * L i))) l (𝓝 0) := by
  have htop : Tendsto (fun i => e * L i) l atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 hL) (b / e)] with i hi
    simpa only [mul_comm] using (div_le_iff₀ he).mp hi
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp htop).const_mul (K / e ^ 3)
  convert h using 1
  · funext i
    dsimp only [Function.comp_apply]
    field_simp [he.ne'] <;> ring
  · ring

/-- Transfer a fixed-strip tail exponent d>p. The same statement can use a
stronger literature count after normalizing it by the actual copy count. -/
theorem actual_secondMoment_ratio_le_of_fixed_cut
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    {p d u c K : ℝ} (hp : 0 < p) (hpd : p < d) (hu : 0 ≤ u) (hK : 0 ≤ K)
    (hc : u / p < c) (hm : ∀ᶠ i in l, 0 < m₁ (T i))
    (hr : Tendsto (fun i => M₁ (T i) / Real.log (T i)) l (𝓝 p))
    (htail : ∀ᶠ i in l, strictTail (T i) u / (Ncount 0 (T i) : ℝ) ≤
      K * Real.log (T i) ^ 2 * Real.exp (-d * Real.log (T i))) :
    ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c := by
  let e := (d - p) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have htop := Real.tendsto_log_atTop.comp hT
  have hE := cubic_exp_decay htop he K
  have hrinv : Tendsto (fun i => Real.log (T i) / M₁ (T i)) l (𝓝 p⁻¹) := by
    simpa only [inv_div] using hr.inv₀ hp.ne'
  have H := ((tendsto_const_nhds (x := u)).add hE).mul hrinv
  have Hc := H.eventually_lt_const (show (u + 0) * p⁻¹ < c by simpa [div_eq_mul_inv] using hc)
  filter_upwards [Hc, hm, htail, hT.eventually (eventually_gt_atTop (1 : ℝ)),
    hr.eventually (Ioi_mem_nhds hp), hr.eventually_lt_const (show p < d - e by dsimp [e]; linarith)]
    with i hc' hm ht hheight hpos hsmall
  let t := T i
  let L := Real.log t
  have hL : 0 < L := Real.log_pos hheight
  have hM : 0 < M₁ t := (div_pos_iff.mp hpos).elim (fun h => h.1) (fun h => False.elim ((not_lt_of_ge hL.le) h.2))
  have hlog : M₁ t < (d - e) * L := (div_lt_iff₀ hL).mp hsmall
  have hmul : Real.exp (-d * L) ≤ m₁ t * Real.exp (-(e * L)) := by
    rw [mul_comm (m₁ t)]
    apply (div_le_iff₀ hm).mp
    calc
      Real.exp (-d * L) / m₁ t = Real.exp (-d * L + M₁ t) := by
        rw [Real.exp_add]
        change _ = Real.exp (-d * L) * Real.exp (Real.log (1 / m₁ t))
        rw [Real.exp_log (one_div_pos.mpr hm)]
        ring
      _ ≤ Real.exp (-(e * L)) := Real.exp_le_exp.mpr (by linarith only [hlog])
  have htail' := ht.trans (mul_le_mul_of_nonneg_left hmul (by positivity))
  have hb := (displacement_second_le_fixed_cut t hu).trans (add_le_add le_rfl htail')
  have hraw := mul_le_mul_of_nonneg_right hb (sq_nonneg L)
  apply le_trans _ hc'.le
  change m₂ t / (m₁ t * M₁ t) ≤ (u + K * L ^ 3 * Real.exp (-(e * L))) * (L / M₁ t)
  apply (div_le_iff₀ (mul_pos hm hM)).mpr
  calc
    _ ≤ (u * displacementMoment t 1 + K * L ^ 2 * (m₁ t * Real.exp (-(e * L)))) * L ^ 2 := hraw
    _ = _ := by
      change (u * displacementMoment t 1 + K * L ^ 2 * (displacementMoment t 1 * L * Real.exp (-(e * L)))) * L ^ 2 =
        ((u + K * L ^ 3 * Real.exp (-(e * L))) * (L / M₁ t)) * (displacementMoment t 1 * L * M₁ t)
      field_simp [hM.ne'] <;> ring

/-- The nonlinear branch gives 3/(4+2p), including the support endpoint p=1. -/
theorem actual_secondMoment_ratio_le_of_polynomial_mean
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    {p c : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hc : 3 / (4 + 2 * p) < c)
    (hm : ∀ᶠ i in l, 0 < m₁ (T i))
    (hr : Tendsto (fun i => M₁ (T i) / Real.log (T i)) l (𝓝 p)) :
    ∀ᶠ i in l, m₂ (T i) / (m₁ (T i) * M₁ (T i)) ≤ c := by
  rcases lt_or_eq_of_le hp1 with hp' | rfl
  · let v := 3 * p / (4 + 2 * p)
    have den : 0 < 4 + 2 * p := by positivity
    have hv : 0 < v := div_pos (by positivity) den
    have hv1 : v < 1 / 2 := (div_lt_iff₀ den).mpr (by linarith)
    have hvc : v < c * p := by
      have hh := mul_lt_mul_of_pos_right hc hp
      exact lt_of_eq_of_lt (by dsimp [v]; ring) hh
    obtain ⟨u,hvu,hu⟩ := exists_between (lt_min hv1 hvc)
    have hu0 := hv.trans hvu
    have hu1 := hu.trans_le (min_le_left _ _)
    have hdu : p < 2 * u / (3 / 2 - u) := by
      have hcross := (div_lt_iff₀ den).mp hvu
      apply (lt_div_iff₀ (by linarith : 0 < 3 / 2 - u)).mpr
      nlinarith only [hcross]
    obtain ⟨K,hK,H⟩ := exists_ingham_fixed_cut_cap ⟨hu0.le,hu1.le⟩
    exact actual_secondMoment_ratio_le_of_fixed_cut hT hp hdu hu0.le hK.le
      ((div_lt_iff₀ hp).mpr (hu.trans_le (min_le_right _ _))) hm hr (hT.eventually H)
  · apply actual_secondMoment_ratio_le_of_fixed_cut hT (p := 1) zero_lt_one
      (d := 2) (by norm_num) (u := 1 / 2) (by norm_num) (K := 0) le_rfl
      (by norm_num at hc ⊢; exact hc) hm hr
    exact Eventually.of_forall fun i => by rw [strictTail_half]; simp

end RiemannResearch.Analysis.ActualZeroOrdinate
