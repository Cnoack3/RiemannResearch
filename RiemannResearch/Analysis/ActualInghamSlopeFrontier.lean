/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualInghamCriticalTilt
import RiemannResearch.Analysis.NonlinearZeroDensityRate
import RiemannResearch.Analysis.ActualSelbergTransitionWindow

/-! # Uniform slopes and moving tilts from the curved Ingham estimate

The actual zero-density input is the all-heights Ingham estimate in the
repository. Chourasiya and Simonič give its height and logarithmic powers
in [Theorem 1](https://arxiv.org/abs/2507.15184). The supporting-line
identities and the growing frequency window are derived here.
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZeroDensityRate

/-- The exact supporting-line defect, in the slope parameter a = 4r²/3. -/
theorem ingham_support_defect {d : ℝ} (hd : d ≤ 1 / 2) (r : ℝ) :
    inghamRate d - (4 / 3) * r ^ 2 * d + 2 * (r - 1) ^ 2 =
      2 * (1 - r * (1 - (2 / 3) * d)) ^ 2 / (1 - (2 / 3) * d) := by
  have h : 3 - 2 * d ≠ 0 := by linarith
  have h' : 1 - (2 / 3) * d ≠ 0 := by linarith
  unfold inghamRate
  have hn : 3 - d * 2 ≠ 0 := by linarith
  field_simp [h, h', hn] <;> ring_nf <;> field_simp [hn, h] <;> ring

/-- The middle branch of the optimal loss on the closed displacement interval. -/
theorem ingham_middle_price {r b : ℝ} (hr : 1 ≤ r) (hr' : r ≤ 3 / 2) :
    (∀ d ∈ Icc (0 : ℝ) (1 / 2), (4 / 3) * r ^ 2 * d ≤ inghamRate d + b) ↔ 2 * (r - 1) ^ 2 ≤ b := by
  have hpos : 0 < r := by linarith
  let d := (3 / 2) * (1 - 1 / r)
  have hr1 : 1 / r ≤ 1 := (div_le_one hpos).mpr hr
  have hr2 : (2 / 3 : ℝ) ≤ 1 / r := (le_div_iff₀ hpos).mpr (by linarith)
  have hd : d ∈ Icc (0 : ℝ) (1 / 2) := ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
  have hz : 1 - r * (1 - (2 / 3) * d) = 0 := by dsimp [d]; field_simp; ring
  constructor
  · intro h
    have he := ingham_support_defect hd.2 r
    rw [hz] at he
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, zero_div] at he
    linarith only [he, h d hd]
  · intro h d hd
    have he := ingham_support_defect hd.2 r
    have hden : 0 < 1 - (2 / 3) * d := by linarith [hd.2]
    have hn : 0 ≤ 2 * (1 - r * (1 - (2 / 3) * d)) ^ 2 / (1 - (2 / 3) * d) := by positivity
    linarith only [h, he, hn]

theorem ingham_low_price {a b : ℝ} (ha : a ≤ 4 / 3) :
    (∀ d ∈ Icc (0 : ℝ) (1 / 2), a * d ≤ inghamRate d + b) ↔ 0 ≤ b := by
  constructor
  · intro h
    simpa [inghamRate] using h 0 ⟨le_rfl, by norm_num⟩
  · intro hb d hd
    have h := (ingham_middle_price (r := 1) (b := b) le_rfl (by norm_num)).2 (by simpa using hb) d hd
    have h' := mul_le_mul_of_nonneg_right ha hd.1
    nlinarith only [h, h']

theorem ingham_high_price {a b : ℝ} (ha : 3 ≤ a) :
    (∀ d ∈ Icc (0 : ℝ) (1 / 2), a * d ≤ inghamRate d + b) ↔ a / 2 - 1 ≤ b := by
  constructor
  · intro h
    have hi := h (1 / 2) ⟨by norm_num, le_rfl⟩
    norm_num [inghamRate] at hi
    linarith only [hi]
  · intro hb d hd
    have hi := (ingham_middle_price (r := 3 / 2) (b := 1 / 2) (by norm_num) le_rfl).2 (by norm_num) d hd
    have hm := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hd.2)
    nlinarith only [hb, hi, hm]

end RiemannResearch.Analysis.ZeroDensityRate
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroDensityRate

/-- The exact affine price can be used at all heights and slopes with one
constant. Both height and logarithmic exponents enter the exponential weight. -/
theorem exists_ingham_priced_density :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 2 (Real.exp 1) ≤ T →
      ∀ a b : ℝ, (∀ d ∈ Icc (0 : ℝ) (1 / 2), a * d ≤ inghamRate d + b) →
      ∀ d ∈ Icc (0 : ℝ) (1 / 2), rightInclusiveCount T (1 / 2 + d) ≤
        C * T * (Real.log T) ^ 3 * Real.exp ((Real.log T + Real.log (Real.log T)) * (b - a * d)) := by
  obtain ⟨C, hC, h⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨C, hC, ?_⟩
  intro T hT a b hab d hd
  have h2 := (le_max_left (2 : ℝ) (Real.exp 1)).trans hT
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  have hL : 0 < Real.log T := zero_lt_one.trans_le hL1
  have hM : 0 ≤ Real.log T + Real.log (Real.log T) := add_nonneg hL.le (Real.log_nonneg hL1)
  have hσ : 1 / 2 + d ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have he := tExponent_eq_one_sub_rate d (by linarith [hd.2])
  have hc := (h T h2 _ hσ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
  rw [he, show 2 + (1 - inghamRate d) = 3 - inghamRate d by ring, inghamPower_eq_expDecay hT0 hL] at hc
  apply hc.trans
  rw [← mul_assoc, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left (hab d hd) hM]

/-- On a fixed right substrip every slope strictly below its left-end secant
has a one - log bound, uniformly up to real part one. -/
theorem eventually_ingham_substrip_one_log {d₀ a : ℝ} (hd₀ : 0 < d₀)
    (h₀ : d₀ ≤ 1 / 2) (ha : a < 4 / (3 - 2 * d₀)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d ∈ Icc d₀ (1 / 2),
      rightInclusiveCount T (1 / 2 + d) ≤ C * T ^ (1 - a * d) * Real.log T := by
  obtain ⟨C, hC, h⟩ := exists_selberg_count_of_ingham_profile_comparison
  let margin := (4 / (3 - 2 * d₀) - a) * d₀
  have hm : 0 < margin := mul_pos (sub_pos.mpr ha) hd₀
  have hz := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hz.eventually (gt_mem_nhds (show 0 < margin / 2 by positivity)),
    eventually_ge_atTop (max 2 (Real.exp 1))] with T hv hT
  intro d hd
  have h2 := (le_max_left (2 : ℝ) (Real.exp 1)).trans hT
  have hL1 : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  have hL := zero_lt_one.trans_le hL1
  have hLL := Real.log_nonneg hL1
  have hden : 0 < 3 - 2 * d := by linarith [hd.2]
  have hm' : 4 / (3 - 2 * d₀) ≤ 4 / (3 - 2 * d) :=
    div_le_div_of_nonneg_left (by norm_num) hden (by linarith [hd.1])
  have hrs : margin ≤ inghamRate d - a * d := by
    unfold margin inghamRate
    have hm1 := mul_le_mul_of_nonneg_left hd.1 (sub_nonneg.mpr ha.le)
    have hm2 := mul_le_mul_of_nonneg_right hm' (hd₀.le.trans hd.1)
    rw [show 4 * d / (3 - 2 * d) = (4 / (3 - 2 * d)) * d by ring]
    nlinarith only [hm1, hm2]
  have hσ : 1 / 2 + d ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hrate : 0 ≤ inghamRate d := div_nonneg (mul_nonneg (by norm_num) (hd₀.le.trans hd.1)) hden.le
  have he := tExponent_eq_one_sub_rate d hden.ne'
  have hlog : Real.log (Real.log T) < margin / 2 * Real.log T :=
    (div_lt_iff₀ hL).mp (show Real.log (Real.log T) / Real.log T < margin / 2 from hv)
  simpa only [show 1 / 2 + d - 1 / 2 = d by ring] using h T h2 (1 / 2 + d) hσ a (by
    rw [he, show 1 / 2 + d - 1 / 2 = d by ring]
    nlinarith only [mul_nonneg hrate hLL, hlog, mul_le_mul_of_nonneg_right hrs hL.le])

/-- Transfer a power of log T in the tilted count to the growing critical window. -/
theorem tendsto_tilted_moment_loglog_of_power (m : ℕ)
    (hbase : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, ∀ p : ℕ, ∀ v : ℝ, 0 ≤ v →
      let L := Real.log T
      let q := (4 / 3) * L + s * Real.sqrt L
      v < q → (∑ i : Copies T, copyDisplacement T i ^ (p + 1) * Real.exp (v * copyDisplacement T i)) / T ≤
        C * Real.exp (9 * s ^ 2 / 32) * L ^ m * (((p + 1).factorial : ℝ) * q / (q - v) ^ (p + 2)))
    (p : ℕ) (hp : 2 * m < p) (v : ℝ → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hc' : c < (4 / 3) * Real.sqrt ((p : ℝ) - 2 * (m : ℝ)))
    (hv : ∀ᶠ T : ℝ in atTop, 0 ≤ v T ∧ v T ≤ (4 / 3) * Real.log T +
      c * Real.sqrt (Real.log (Real.log T)) * Real.sqrt (Real.log T)) :
    Tendsto (fun T : ℝ => (∑ i : Copies T, copyDisplacement T i ^ (p + 1) *
      Real.exp (v T * copyDisplacement T i)) / T) atTop (𝓝 0) := by
  obtain ⟨b, hcb, hb⟩ := exists_between hc'
  have hb0 : 0 < b := hc.trans_lt hcb
  have hp' : 2 * (m : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : 0 ≤ (p : ℝ) - 2 * (m : ℝ) := by linarith
  let e : ℝ := (m : ℝ) - (p : ℝ) / 2 + 9 * b ^ 2 / 32
  have he : e < 0 := by
    have hu : 0 < (4 / 3 : ℝ) * Real.sqrt ((p : ℝ) - 2 * (m : ℝ)) + b := by positivity
    have hh := mul_pos (sub_pos.mpr hb) hu
    dsimp [e]
    nlinarith only [hh, Real.sq_sqrt hp0]
  obtain ⟨C, hC, h⟩ := hbase
  let K := C * ((p + 1).factorial : ℝ) * (4 / 3 + b)
  have hz : Tendsto (fun T : ℝ => K * (Real.log T) ^ e) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, neg_neg] using
      ((tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp Real.tendsto_log_atTop).const_mul K
  apply squeeze_zero' _ _ hz
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T ht
    exact div_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg
      (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) ht.le
  · have hB := Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
    filter_upwards [hv, hB.eventually_ge_atTop (1 / (b - c)), h, eventually_ge_atTop (max 2 (Real.exp 1))]
      with T ht hB hmoment hT
    let L := Real.log T
    let U := Real.sqrt (Real.log L)
    let R := Real.sqrt L
    let q := (4 / 3) * L + b * U * R
    have hL1 : 1 ≤ L := by simpa [L] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
    have hL := zero_lt_one.trans_le hL1
    have hR : 0 < R := Real.sqrt_pos.mpr hL
    have hRsq : R ^ 2 = L := Real.sq_sqrt hL.le
    have hUsq : U ^ 2 = Real.log L := Real.sq_sqrt (Real.log_nonneg hL1)
    have hUR : U ≤ R := Real.sqrt_le_sqrt (le_trans (Real.log_le_sub_one_of_pos hL) (by linarith))
    have hg : 1 ≤ U * (b - c) := (div_le_iff₀ (sub_pos.mpr hcb)).mp hB
    have hgap : R ≤ q - v T := by
      have hwidth : v T ≤ (4 / 3) * L + c * U * R := ht.2
      dsimp only [q]
      nlinarith only [hwidth, mul_le_mul_of_nonneg_right hg hR.le]
    have hvq : v T < q := by linarith [hgap]
    have hq0 : 0 ≤ q := ht.1.trans hvq.le
    have hq : q ≤ (4 / 3 + b) * L := by
      dsimp only [q]
      have hu := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUR hR.le) hb0.le
      rw [← sq R, hRsq] at hu
      nlinarith only [hu]
    have hE : Real.exp (9 * (b * U) ^ 2 / 32) = L ^ (9 * b ^ 2 / 32) := by
      rw [Real.rpow_def_of_pos hL]
      congr 1
      rw [mul_pow, hUsq]
      ring
    have hnat : R ^ (p + 2) = L ^ (((p : ℝ) + 2) / 2) := by
      rw [show R = L ^ (1 / 2 : ℝ) by exact Real.sqrt_eq_rpow _, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
      congr 1
      push_cast
      ring
    have hh := hmoment (b * U) p (v T) ht.1 hvq
    change _ ≤ C * Real.exp (9 * (b * U) ^ 2 / 32) * L ^ m * (((p + 1).factorial : ℝ) * q / (q - v T) ^ (p + 2)) at hh
    apply hh.trans
    rw [hE]
    have hpw := pow_le_pow_left₀ hR.le hgap (p + 2)
    calc
      _ ≤ C * L ^ (9 * b ^ 2 / 32) * L ^ m * ((((p + 1).factorial : ℝ) * ((4 / 3 + b) * L)) / R ^ (p + 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hq0) (pow_pos hR _) hpw).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) (pow_pos hR _).le)
      _ = K * L ^ e := by
        rw [hnat]
        have hprod : L ^ (9 * b ^ 2 / 32) * L ^ m * L / L ^ (((p : ℝ) + 2) / 2) = L ^ e := by
          calc
            _ = L ^ (9 * b ^ 2 / 32) * L ^ (m : ℝ) * L ^ (1 : ℝ) / L ^ (((p : ℝ) + 2) / 2) := by rw [Real.rpow_natCast, Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_sub hL]; congr 1; dsimp [e]; ring
        dsimp only [K]
        calc
          _ = (C * ((p + 1).factorial : ℝ) * (4 / 3 + b)) * (L ^ (9 * b ^ 2 / 32) * L ^ m * L / L ^ (((p : ℝ) + 2) / 2)) := by ring
          _ = _ := by rw [hprod]

/-- High horizontal moments can tolerate a growing excess above the Ingham
frequency tangent. The allowable constant depends on the order. -/
theorem tendsto_tilted_moment_loglog_window (p : ℕ) (hp : 7 ≤ p) (v : ℝ → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hc' : c < (4 / 3) * Real.sqrt ((p : ℝ) - 6))
    (hv : ∀ᶠ T : ℝ in atTop, 0 ≤ v T ∧ v T ≤ (4 / 3) * Real.log T +
      c * Real.sqrt (Real.log (Real.log T)) * Real.sqrt (Real.log T)) :
    Tendsto (fun T : ℝ => (∑ i : Copies T, copyDisplacement T i ^ (p + 1) *
      Real.exp (v T * copyDisplacement T i)) / T) atTop (𝓝 0) := by
  apply tendsto_tilted_moment_loglog_of_power 3 _ p (by omega) v hc (by norm_num at ⊢; exact hc') hv
  obtain ⟨C, hC, h⟩ := exists_ingham_tilted_moment_sqrt_window
  exact ⟨C, hC, (eventually_ge_atTop (max 2 (Real.exp 1))).mono fun T hT => h T hT⟩

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_tilted_moment_loglog_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_tilted_moment_loglog_window

end RiemannResearch.Analysis.ActualZeroOrdinate
