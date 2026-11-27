/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSelbergTransitionWindow
import RiemannResearch.Analysis.ActualCriticalFarStrip
import RiemannResearch.Analysis.ActualInghamSlopeFrontier

/-! # The one-logarithm transition and the curved dyadic Selberg bound

The exact transition uses the repository's actual all-heights Ingham bound.
[Paper 184, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/184/v1)
supplies the written dyadic one-log estimate. This module exposes that estimate as a premise
whenever it is used. The 5/6 example uses the fixed-abscissa density input from the
[zero-density exponent table](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html).
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroDensityRate

/-- The positive root at which the Ingham profile first pays for one logarithm. -/
def selbergTransitionDisplacement (a T : ℝ) : ℝ :=
  let L := Real.log T
  let B := (4 - 3 * a) * L + 8 * Real.log L
  (Real.sqrt (B ^ 2 + 48 * a * L * Real.log L) - B) / (4 * a * L)

private theorem quadratic_positive_root {A B U d : ℝ} (hA : 0 < A) (hU : 0 < U) (hd : 0 ≤ d) :
    (Real.sqrt (B ^ 2 + 4 * A * U) - B) / (2 * A) ≤ d ↔ 0 ≤ A * d ^ 2 + B * d - U := by
  let R := Real.sqrt (B ^ 2 + 4 * A * U)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR : R ^ 2 = B ^ 2 + 4 * A * U := Real.sq_sqrt (by positivity)
  have hbig : -B < R := by
    by_contra! hn
    have hh := mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ -B + R by linarith only [hn, hR0])
    nlinarith only [hh, hR, mul_pos hA hU]
  have hplus : 0 < 2 * A * d + B + R := by nlinarith only [hbig, mul_nonneg hA.le hd]
  have hid : (2 * A * d + B - R) * (2 * A * d + B + R) = (4 * A) * (A * d ^ 2 + B * d - U) := by
    nlinarith only [hR]
  rw [div_le_iff₀ (show 0 < 2 * A by positivity)]
  change R - B ≤ d * (2 * A) ↔ _
  constructor
  · intro h
    have hm := mul_nonneg (show 0 ≤ 2 * A * d + B - R by linarith only [h]) hplus.le
    rw [hid] at hm
    exact nonneg_of_mul_nonneg_right hm (by positivity)
  · intro h
    have hm := mul_nonneg (show 0 ≤ 4 * A by positivity) h
    rw [← hid] at hm
    have hi := nonneg_of_mul_nonneg_left hm hplus
    linarith only [hi]

/-- Exact comparison for any positive target slope, including height-dependent slopes. -/
theorem ingham_one_log_iff_transition_displacement {T a d : ℝ}
    (hT : Real.exp 1 < T) (ha : 0 < a) (hd : d ∈ Icc (0 : ℝ) (1 / 2)) :
    let q := 3 * (1 - (1 / 2 + d)) / (2 - (1 / 2 + d))
    T ^ q * (Real.log T) ^ (2 + q) ≤ T ^ (1 - a * d) * Real.log T ↔ selbergTransitionDisplacement a T ≤ d := by
  let L := Real.log T
  let l := Real.log L
  have hT1 : 1 < T := (show 1 < Real.exp 1 by simpa using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)).trans hT
  have hL1 : 1 < L := by simpa [L] using Real.log_lt_log (Real.exp_pos 1) hT
  have hL : 0 < L := zero_lt_one.trans hL1
  have hl : 0 < l := Real.log_pos hL1
  have hden : 0 < 3 - 2 * d := by linarith only [hd.2]
  have hr : inghamRate d * (3 - 2 * d) = 4 * d := div_mul_cancel₀ _ hden.ne'
  have hleft : (2 - inghamRate d) * (3 - 2 * d) = 6 - 8 * d := by rw [sub_mul, hr]; ring
  have hright : (inghamRate d - a * d) * (3 - 2 * d) = (4 - 3 * a) * d + 2 * a * d ^ 2 := by rw [sub_mul, hr]; ring
  have hroot := quadratic_positive_root (A := 2 * a * L) (B := (4 - 3 * a) * L + 8 * l) (U := 6 * l)
    (show 0 < 2 * a * L by positivity) (show 0 < 6 * l by positivity) hd.1
  have hs : selbergTransitionDisplacement a T ≤ d ↔
      0 ≤ (2 * a * L) * d ^ 2 + ((4 - 3 * a) * L + 8 * l) * d - 6 * l := by
    simpa only [selbergTransitionDisplacement, ← show 2 * (2 * a * L) = 4 * a * L by ring,
      ← show 4 * (2 * a * L) * (6 * l) = 48 * a * L * l by ring, L, l] using hroot
  dsimp only
  have he := ingham_profile_le_selberg_iff (a := a) (q := 3 * (1 - (1 / 2 + d)) / (2 - (1 / 2 + d))) (σ := 1 / 2 + d) hT1
  rw [show 1 / 2 + d - 1 / 2 = d by ring, tExponent_eq_one_sub_rate d hden.ne'] at he
  rw [tExponent_eq_one_sub_rate d hden.ne', he, hs]
  have hstep : (2 - inghamRate d) * l ≤ (inghamRate d - a * d) * L ↔
      (6 - 8 * d) * l ≤ ((4 - 3 * a) * d + 2 * a * d ^ 2) * L := by
    have hu : (2 - inghamRate d) * l * (3 - 2 * d) = (6 - 8 * d) * l := by rw [← hleft]; ring
    have hv : (inghamRate d - a * d) * L * (3 - 2 * d) = ((4 - 3 * a) * d + 2 * a * d ^ 2) * L := by rw [← hright]; ring
    rw [← hu, ← hv]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_right h hden.le
    · intro h
      by_contra! h'
      exact (not_lt_of_ge h) (mul_lt_mul_of_pos_right h' hden)
  rw [show 1 + (1 - inghamRate d) = 2 - inghamRate d by ring, show 1 - (1 - inghamRate d) = inghamRate d by ring]
  change (2 - inghamRate d) * l ≤ (inghamRate d - a * d) * L ↔ _
  rw [hstep]
  constructor <;> intro h <;> nlinarith only [h]

/-- An absolute constant suffices everywhere beyond the exact transition. -/
theorem exists_actual_selberg_above_transition :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 2 (Real.exp 1) < T → ∀ a : ℝ, 0 < a →
      ∀ d ∈ Icc (0 : ℝ) (1 / 2), selbergTransitionDisplacement a T ≤ d →
        rightInclusiveCount T (1 / 2 + d) ≤ C * T ^ (1 - a * d) * Real.log T := by
  obtain ⟨C, hC, h⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨C, hC, ?_⟩
  intro T hT a ha d hd ht
  have hσ : 1 / 2 + d ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith only [hd.1], by linarith only [hd.2]⟩
  have hpow := (ingham_one_log_iff_transition_displacement ((le_max_right _ _).trans_lt hT) ha hd).mpr ht
  rw [mul_assoc]
  exact (h T ((le_max_left _ _).trans hT.le) _ hσ).trans
    (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hpow) hC.le)


/-- The only remaining one-logarithm count for a fixed positive slope lies
strictly between the total - count range and the exact curved transition. -/
theorem uniformSelbergDensity_iff_exact_transition {a : ℝ} (ha : 0 < a) (M : ℝ) :
    UniformSelbergDensity a ↔ ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧
      ∀ T : ℝ, H ≤ T → ∀ d ∈ Icc (0 : ℝ) (1 / 2),
        M < d * Real.log T → d < selbergTransitionDisplacement a T →
        rightInclusiveCount T (1 / 2 + d) ≤ C * T ^ (1 - a * d) * Real.log T := by
  constructor
  · rintro ⟨C, H, hC, hH, h⟩
    refine ⟨C, H, hC, hH, ?_⟩
    intro T hT d hd _ _
    have hσ : 1 / 2 + d ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hd.1], by linarith [hd.2]⟩
    simpa only [show 1 / 2 + d - 1 / 2 = d by ring] using h T hT _ hσ
  · rintro ⟨C, H, hC, hH, hm⟩
    obtain ⟨A, hA, hnear⟩ := exists_selberg_form_on_logarithmic_strip a M ha.le
    obtain ⟨B, hB, hfar⟩ := exists_actual_selberg_above_transition
    let K := max A (max B C)
    let U := max H (9 + Real.exp 1)
    have hHU : H ≤ U := le_max_left _ _
    refine ⟨K, U, hA.le.trans (le_max_left _ _), hH.trans_le hHU, ?_⟩
    intro T hT σ hσ
    let d := σ - 1 / 2
    have hd : d ∈ Icc (0 : ℝ) (1 / 2) := ⟨sub_nonneg.mpr hσ.1, by dsimp [d]; linarith only [hσ.2]⟩
    have hσ' : 1 / 2 + d = σ := by dsimp [d]; ring
    have ht := hH.trans_le (hHU.trans hT)
    have hT9 : 9 ≤ T := by linarith only [(le_max_right H (9 + Real.exp 1)).trans hT, Real.exp_pos 1]
    have hTE : max 2 (Real.exp 1) < T := max_lt (by linarith only [hT9]) (by linarith only [(le_max_right H (9 + Real.exp 1)).trans hT])
    have lift_bound {E : ℝ} (hE : E ≤ K) : E * T ^ (1 - a * d) * Real.log T ≤ K * T ^ (1 - a * d) * Real.log T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg (zero_le_one.trans ht.le) _)) (Real.log_pos ht).le
    by_cases hlow : d * Real.log T ≤ M
    · exact (hnear T hT9 σ hlow).trans (lift_bound (le_max_left _ _))
    by_cases hmid : d < selbergTransitionDisplacement a T
    · have hh := hm T (hHU.trans hT) d hd (lt_of_not_ge hlow) hmid
      rw [hσ'] at hh
      exact hh.trans (lift_bound ((le_max_right _ _).trans (le_max_right _ _)))
    · have hh := hfar T hTE a ha d hd (le_of_not_gt hmid)
      rw [hσ'] at hh
      exact hh.trans (lift_bound ((le_max_left _ _).trans (le_max_right _ _)))

/-- Under the dyadic one-log input the full curved exponent assembles
uniformly down to any fixed positive height exponent. -/
theorem dyadic_one_log_curved_density (hw : DyadicInghamOneLog) {η : ℝ} (hη : 0 < η) :
    ∃ K H : ℝ, 0 ≤ K ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      rightInclusiveCount T σ ≤ K * T ^ (max η (3 * (1 - σ) / (2 - σ))) * Real.log T := by
  obtain ⟨D, H, hD, hH, hwin⟩ := hw
  let r := (2 : ℝ) ^ (-η)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    simpa [r] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (show - η < 0 by linarith)
  let A := (Ncount 0 (2 * H) : ℝ) / Real.log H
  have hA : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) (Real.log_pos hH).le
  let K := (A + D) / (1 - r)
  have hden : 0 < 1 - r := by linarith
  have hK : 0 ≤ K := div_nonneg (add_nonneg hA hD) hden.le
  have hK' : K * (1 - r) = A + D := div_mul_cancel₀ _ hden.ne'
  have hAK : A ≤ K := by nlinarith only [hK', mul_nonneg hK hr0, hD]
  have hscale : K * r + D ≤ K := by linarith only [hK', hA]
  refine ⟨K, H, hK, hH, ?_⟩
  intro T hT σ hσ
  let q := 3 * (1 - σ) / (2 - σ)
  let e := max η q
  have hq : 0 ≤ q := div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hσ.2)) (by linarith only [hσ.2])
  have he := le_max_left η q
  apply bound_of_dyadic_power_log (fun t => rightInclusiveCount t σ) hH hK (hη.le.trans he)
    (rightInclusiveCount_monotone_height σ) ?_ (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg he)) hscale ?_ T hT
  · exact (rightInclusiveCount_le_count _ _).trans ((le_of_eq (div_mul_cancel₀ _ (Real.log_pos hH).ne').symm).trans
      (mul_le_mul_of_nonneg_right hAK (Real.log_pos hH).le))
  · intro S hS
    have hSH : H ≤ S / 2 := by linarith only [hS]
    have hS1 : 1 < S / 2 := hH.trans_le hSH
    have hST : S / 2 ≤ S := by linarith only [hS1]
    rw [← rightInclusiveWindow_eq_sub hST]
    by_cases hs : σ < 1
    · have hwin' := hwin (S / 2) hSH σ ⟨hσ.1, hs⟩
      rw [show 2 * (S / 2) = S by ring] at hwin'
      have hp := (Real.rpow_le_rpow (zero_lt_one.trans hS1).le hST hq).trans
        (Real.rpow_le_rpow_of_exponent_le (hS1.le.trans hST) (le_max_right η q))
      exact hwin'.trans (mul_le_mul (mul_le_mul_of_nonneg_left hp hD) (Real.log_le_log (zero_lt_one.trans hS1) hST)
        (Real.log_nonneg hS1.le) (mul_nonneg hD (Real.rpow_nonneg (zero_le_one.trans (hS1.le.trans hST)) _)))
    · have heq : σ = 1 := le_antisymm hσ.2 (le_of_not_gt hs)
      subst σ
      have hz : rightInclusiveWindow (S / 2) S 1 = 0 := by
        unfold rightInclusiveWindow realSum
        apply Finset.sum_eq_zero
        intro ρ hρ
        simp [not_le_of_gt ((mem_cutoff.mp hρ).1.2.2)]
      rw [hz]
      exact mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (zero_le_one.trans (hS1.le.trans hST)) _))
        (Real.log_nonneg (hS1.le.trans hST))


/-- The sharp supporting-line price retains one logarithm when its height
exponent is bounded away from zero. The constants are uniform in the slope. -/
theorem dyadic_one_log_priced_density (hw : DyadicInghamOneLog) {η : ℝ} (hη : 0 < η) :
    ∃ K H : ℝ, 0 ≤ K ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ a b d : ℝ, d ∈ Icc (0 : ℝ) (1 / 2) →
      a * d ≤ inghamRate d + b → η ≤ 1 + b - a * d →
      rightInclusiveCount T (1 / 2 + d) ≤ K * T ^ (1 + b - a * d) * Real.log T := by
  obtain ⟨K, H, hK, hH, h⟩ := dyadic_one_log_curved_density hw hη
  refine ⟨K, H, hK, hH, ?_⟩
  intro T ht a b d hd hprice hfloor
  have hσ : 1 / 2 + d ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hi := h T ht _ hσ
  rw [tExponent_eq_one_sub_rate d (by linarith only [hd.2])] at hi
  have hT := hH.trans_le ht
  exact hi.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT.le (max_le hfloor (by linarith only [hprice]))) hK)
    (Real.log_pos hT).le)

/-- A one-logarithm count holds on the full strip even with a slope excess
c / sqrt(log T). The prefactor records the dependence on c explicitly. -/
theorem dyadic_one_log_moving_selberg (hw : DyadicInghamOneLog) :
    ∃ K H : ℝ, 0 ≤ K ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ c : ℝ, ∀ d ∈ Icc (0 : ℝ) (1 / 2),
      rightInclusiveCount T (1 / 2 + d) ≤ K * T * Real.log T * Real.exp (9 * c ^ 2 / 32)*
        Real.exp (-((4 / 3) * Real.log T + c * Real.sqrt (Real.log T)) * d) := by
  obtain ⟨K, H, hK, hH, h⟩ := dyadic_one_log_curved_density hw (η := 1 / 9) (by norm_num)
  refine ⟨K, H, hK, hH, ?_⟩
  intro T hT c d hd
  have ht := hH.trans_le hT
  let L := Real.log T
  have hL : 0 < L := Real.log_pos ht
  have hσ : 1 / 2 + d ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hd.1], by linarith [hd.2]⟩
  let Q := 1 - (4 / 3) * d - (8 / 9) * d ^ 2
  have hq : 3 * (1 - (1 / 2 + d)) / (2 - (1 / 2 + d)) ≤ Q := by
    apply (div_le_iff₀ (by linarith only [hd.2])).mpr
    dsimp only [Q]
    nlinarith only [pow_nonneg hd.1 3]
  have hfloor : (1 / 9 : ℝ) ≤ Q := by
    dsimp only [Q]
    nlinarith only [hd.2, pow_le_pow_left₀ hd.1 hd.2 2]
  have hR : (Real.sqrt L * d) ^ 2 = L * d ^ 2 := by rw [mul_pow, Real.sq_sqrt hL.le]
  have harg : L * Q ≤ L + 9 * c ^ 2 / 32 - ((4 / 3) * L + c * Real.sqrt L) * d := by
    dsimp only [Q]
    nlinarith only [sq_nonneg (Real.sqrt L * d - 9 * c / 16), hR]
  have he := (Real.rpow_le_rpow_of_exponent_le ht.le (max_le hfloor hq)).trans
    ((le_of_eq (Real.rpow_def_of_pos (zero_lt_one.trans ht) Q)).trans (Real.exp_le_exp.mpr harg))
  change _ ≤ Real.exp (Real.log T + 9 * c ^ 2 / 32 - ((4 / 3) * L + c * Real.sqrt L) * d) at he
  have hsplit : Real.exp (Real.log T + 9 * c ^ 2 / 32 - ((4 / 3) * L + c * Real.sqrt L) * d) =
      T * Real.exp (9 * c ^ 2 / 32) * Real.exp (-(((4 / 3) * L + c * Real.sqrt L) * d)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log (zero_lt_one.trans ht)]
  rw [hsplit] at he
  apply (h T hT _ hσ).trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK) hL.le).trans_eq
  dsimp only [L]
  rw [neg_mul]
  ring


/-- The fixed-abscissa literature input in the repository gives a slope
above two at real part 5 / 6. The implicit constant may depend on the slope. -/
theorem one_log_five_sixths_of_far_density (h : TaoBourgainFarDensityHypothesis)
    {a : ℝ} (ha : a < 21 / 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      rightInclusiveCount T (5 / 6) ≤ C * T ^ (1 - a / 3) * Real.log T := by
  let ε := 1 - a / 3 - 3 / 10
  have hε : 0 < ε := by dsimp [ε]; linarith only [ha]
  obtain ⟨C, hC, hh⟩ := h (5 / 6) ⟨by norm_num, by norm_num⟩ ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hh, Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)] with T ht hL hT
  have he : farDensityCoefficient (5 / 6) * (1 - 5 / 6) + ε = 1 - a / 3 := by
    norm_num [farDensityCoefficient, ε]
    <;> ring
  rw [he] at ht
  exact ht.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hL (mul_nonneg hC.le (Real.rpow_nonneg hT.le _)))


/-- With the site's dyadic one-log count the same growing tilt is
available from order four, with the improved order - dependent constant. -/
theorem dyadic_one_log_tilted_moment_loglog (hw : DyadicInghamOneLog)
    (p : ℕ) (hp : 3 ≤ p) (v : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hc' : c < (4 / 3) * Real.sqrt ((p : ℝ) - 2))
    (hv : ∀ᶠ T : ℝ in atTop, 0 ≤ v T ∧ v T ≤ (4 / 3) * Real.log T +
      c * Real.sqrt (Real.log (Real.log T)) * Real.sqrt (Real.log T)) :
    Tendsto (fun T : ℝ => (∑ i : Copies T, copyDisplacement T i ^ (p + 1) *
      Real.exp (v T * copyDisplacement T i)) / T) atTop (𝓝 0) := by
  apply tendsto_tilted_moment_loglog_of_power 1 _ p (by omega) v hc (by simpa using hc') hv
  obtain ⟨K, H, hK, hH, h⟩ := dyadic_one_log_moving_selberg hw
  let C := 2 * (K + 1)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop H] with T ht
  intro s p v hv L q hvq
  have hT := zero_lt_one.trans (hH.trans_le ht)
  have hL : 0 < L := Real.log_pos (hH.trans_le ht)
  have htail (d : ℝ) (hd : d ∈ Icc (0 : ℝ) (1 / 2)) :
      strictTail T d ≤ (C * Real.exp (9 * s ^ 2 / 32) * T * L) * Real.exp (-q * d) := by
    have hi := (strictTail_le_twice_inclusive T d hd.1).trans
      (mul_le_mul_of_nonneg_left (h T ht s d hd) (by norm_num))
    change strictTail T d ≤ 2 * (K * T * L * Real.exp (9 * s ^ 2 / 32) * Real.exp (-q * d)) at hi
    apply hi.trans
    calc
      _ = (2 * K) * (T * L * Real.exp (9 * s ^ 2 / 32) * Real.exp (-q * d)) := by ring
      _ ≤ C * (T * L * Real.exp (9 * s ^ 2 / 32) * Real.exp (-q * d)) :=
        mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
      _ = _ := by ring
  have hi := tiltedMoment_le_expTail p (show 0 ≤ C * Real.exp (9 * s ^ 2 / 32) * T * L by positivity) hv hvq htail
  apply (div_le_iff₀ hT).mpr
  apply hi.trans_eq
  rw [pow_one]
  ring

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_iff_exact_transition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformSelbergDensity_iff_exact_transition

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.dyadic_one_log_moving_selberg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dyadic_one_log_moving_selberg

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.dyadic_one_log_tilted_moment_loglog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dyadic_one_log_tilted_moment_loglog

end RiemannResearch.Analysis.ActualZeroOrdinate
