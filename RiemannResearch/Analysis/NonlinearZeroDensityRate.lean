/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact scalar algebra for the nonlinear Ingham density rate

These scalar statements assert no zero-density estimate for the actual zeta
function. They organize the exponent and cutoff algebra used by a density
consumer after its explicit analytic density premise has been supplied.
Source for the exponent: Chourasiya--Simonic, arXiv:2507.15184v2,
Theorem 1 and Table 1, https://arxiv.org/html/2507.15184v2.
The tangent and quadratic cutoff identities below are algebraic deductions.
-/

namespace RiemannResearch.Analysis.ZeroDensityRate

noncomputable def inghamRate (s : ℝ) : ℝ := 4 * s / (3 - 2 * s)

/-- The exact exponent of T at sigma = 1/2+s. -/
theorem tExponent_eq_one_sub_rate (s : ℝ) (hs : 3 - 2 * s ≠ 0) :
    3 * (1 - (1 / 2 + s)) / (2 - (1 / 2 + s)) = 1 - inghamRate s := by
  have hs_c : 3 - s * 2 ≠ 0 := by simpa [mul_comm] using hs
  have hs' : 2 - (1 / 2 + s) ≠ 0 := by
    intro h
    apply hs
    linarith
  unfold inghamRate
  field_simp [hs, hs', hs_c] <;> ring_nf <;> field_simp [hs, hs', hs_c] <;> ring

/-- The exact logarithmic exponent equals 3 minus the same rate. Thus the
combined decay parameter is log T + log(log T). -/
theorem logExponent_eq_three_sub_rate (s : ℝ) (hs : 3 - 2 * s ≠ 0) :
    (7 - 5 * (1 / 2 + s)) / (2 - (1 / 2 + s)) = 3 - inghamRate s := by
  have hs_c : 3 - s * 2 ≠ 0 := by simpa [mul_comm] using hs
  have hs' : 2 - (1 / 2 + s) ≠ 0 := by
    intro h
    apply hs
    linarith
  unfold inghamRate
  field_simp [hs, hs', hs_c] <;> ring_nf <;> field_simp [hs, hs', hs_c] <;> ring

/-- The nonlinear gain beyond the coarse linear rate 4s/3. -/
theorem inghamRate_linear_remainder (s : ℝ) (hs : 3 - 2 * s ≠ 0) :
    inghamRate s = 4 * s / 3 + 8 * s ^ 2 / (3 * (3 - 2 * s)) := by
  have hs_c : 3 - s * 2 ≠ 0 := by simpa [mul_comm] using hs
  unfold inghamRate
  field_simp [hs, hs_c] <;> ring_nf <;> field_simp [hs, hs_c] <;> ring

/-- Exact tangent remainder. Its denominator is positive throughout the
nontrivial-zero displacement range, giving a tangent exponential envelope. -/
theorem inghamRate_tangent_identity (δ s : ℝ)
    (hδ : 3 - 2 * δ ≠ 0) (hs : 3 - 2 * s ≠ 0) :
    inghamRate s - inghamRate δ - (12 / (3 - 2 * δ) ^ 2) * (s - δ) =
      24 * (s - δ) ^ 2 / ((3 - 2 * δ) ^ 2 * (3 - 2 * s)) := by
  have hδ_c : 3 - δ * 2 ≠ 0 := by simpa [mul_comm] using hδ
  have hs_c : 3 - s * 2 ≠ 0 := by simpa [mul_comm] using hs
  unfold inghamRate
  field_simp [hδ, hs, hδ_c, hs_c] <;> ring_nf <;>
    field_simp [hδ, hs, hδ_c, hs_c] <;> ring

theorem inghamRate_tangent_le {δ s : ℝ} (hδs : δ ≤ s) (hs : s ≤ 1 / 2) :
    inghamRate δ + (12 / (3 - 2 * δ) ^ 2) * (s - δ) ≤ inghamRate s := by
  have hδ₀ : 0 < 3 - 2 * δ := by linarith
  have hs₀ : 0 < 3 - 2 * s := by linarith
  have he := inghamRate_tangent_identity δ s (ne_of_gt hδ₀) (ne_of_gt hs₀)
  have hn : 0 ≤ 24 * (s - δ) ^ 2 / ((3 - 2 * δ) ^ 2 * (3 - 2 * s)) := by
    positivity
  linarith

/-- Weighted tangent bound for the logarithm of an exponential density
envelope. The local slope is 12M/(3-2δ)^2-ell. -/
theorem weighted_tangent_le {M δ s : ℝ} (ell : ℝ) (hM : 0 ≤ M)
    (hδs : δ ≤ s) (hs : s ≤ 1 / 2) :
    M * inghamRate δ - ell * δ +
        (12 * M / (3 - 2 * δ) ^ 2 - ell) * (s - δ) ≤
      M * inghamRate s - ell * s := by
  have h := mul_le_mul_of_nonneg_left (inghamRate_tangent_le hδs hs) hM
  calc
    _ = M * (inghamRate δ + (12 / (3 - 2 * δ) ^ 2) * (s - δ)) - ell * s := by ring
    _ ≤ _ := sub_le_sub_right h _

/-- The optimized nonlinear cutoff is characterized by a quadratic whose
coefficients have no singularity at ell=0. -/
theorem cutoff_margin_identity (M ell R δ : ℝ) (hδ : 3 - 2 * δ ≠ 0) :
    M * inghamRate δ - ell * δ - R =
      (2 * ell * δ ^ 2 + (4 * M - 3 * ell + 2 * R) * δ - 3 * R) /
        (3 - 2 * δ) := by
  have hδ_c : 3 - δ * 2 ≠ 0 := by simpa [mul_comm] using hδ
  unfold inghamRate
  field_simp [hδ, hδ_c] <;> ring_nf <;> field_simp [hδ, hδ_c] <;> ring

theorem cutoff_margin_eq_of_quadratic {M ell R δ : ℝ}
    (hδ : 3 - 2 * δ ≠ 0)
    (hq : 2 * ell * δ ^ 2 + (4 * M - 3 * ell + 2 * R) * δ - 3 * R = 0) :
    M * inghamRate δ - ell * δ = R := by
  have he := cutoff_margin_identity M ell R δ hδ
  rw [hq, zero_div] at he
  linarith

/-- Numerically stable positive root of 2ell*δ^2+B*δ-3R. -/
noncomputable def stableCutoff (ell B R : ℝ) : ℝ :=
  6 * R / (B + Real.sqrt (B ^ 2 + 24 * ell * R))

theorem stableCutoff_quadratic {ell B R : ℝ}
    (hell : 0 ≤ ell) (hB : 0 < B) (hR : 0 ≤ R) :
    2 * ell * (stableCutoff ell B R) ^ 2 + B * stableCutoff ell B R - 3 * R = 0 := by
  let w : ℝ := Real.sqrt (B ^ 2 + 24 * ell * R)
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hw₂ : w ^ 2 = B ^ 2 + 24 * ell * R := Real.sq_sqrt (by positivity)
  have hden : B + w ≠ 0 := ne_of_gt (by linarith : 0 < B + w)
  change 2 * ell * (6 * R / (B + w)) ^ 2 + B * (6 * R / (B + w)) - 3 * R = 0
  have he : 2 * ell * (6 * R / (B + w)) ^ 2 + B * (6 * R / (B + w)) - 3 * R =
      3 * R * (B ^ 2 + 24 * ell * R - w ^ 2) / (B + w) ^ 2 := by
    field_simp [hden] <;> ring
  rw [he, hw₂]
  ring

theorem stableCutoff_margin {M ell R : ℝ}
    (hell : 0 ≤ ell) (hR : 0 ≤ R) (hB : 0 < 4 * M - 3 * ell + 2 * R)
    (hδ : 3 - 2 * stableCutoff ell (4 * M - 3 * ell + 2 * R) R ≠ 0) :
    M * inghamRate (stableCutoff ell (4 * M - 3 * ell + 2 * R) R) -
      ell * stableCutoff ell (4 * M - 3 * ell + 2 * R) R = R := by
  exact cutoff_margin_eq_of_quadratic hδ (stableCutoff_quadratic hell hB hR)

/-- For a prescribed good correction argument z=ell*δ, the admissible support
budget is a different quadratic in ell. Here H may later be log L. -/
theorem fixed_center_budget_identity (M ell p H z : ℝ)
    (hell : ell ≠ 0) (hden : 3 * ell - 2 * z ≠ 0) :
    M * inghamRate (z / ell) - z - ell - p * H =
      -(3 * ell ^ 2 + (z + 3 * p * H) * ell -
          (4 * M * z + 2 * z ^ 2 + 2 * p * H * z)) / (3 * ell - 2 * z) := by
  have hden_c : -(z * 2) + ell * 3 ≠ 0 := by
    rw [show -(z * 2) + ell * 3 = 3 * ell - 2 * z by ring]
    exact hden
  have hden' : 3 - 2 * (z / ell) ≠ 0 := by
    intro h
    apply hden
    have he : (3 - 2 * (z / ell)) * ell = 3 * ell - 2 * z := by
      field_simp [hell] <;> ring
    rw [h, zero_mul] at he
    exact he.symm
  have hden'_c : 3 - (z / ell) * 2 ≠ 0 := by simpa [mul_comm] using hden'
  unfold inghamRate
  field_simp [hell, hden, hden', hden_c, hden'_c] <;> ring_nf <;>
    field_simp [hell, hden, hden', hden_c, hden'_c] <;> ring

theorem fixed_center_budget_nonneg_iff {M ell p H z : ℝ}
    (hell : ell ≠ 0) (hden : 0 < 3 * ell - 2 * z) :
    (0 ≤ M * inghamRate (z / ell) - z - ell - p * H) ↔
      3 * ell ^ 2 + (z + 3 * p * H) * ell -
        (4 * M * z + 2 * z ^ 2 + 2 * p * H * z) ≤ 0 := by
  rw [fixed_center_budget_identity M ell p H z hell (ne_of_gt hden)]
  constructor
  · intro h
    have h' := (le_div_iff₀ hden).mp h
    linarith
  · intro h
    apply (le_div_iff₀ hden).2
    linarith

end RiemannResearch.Analysis.ZeroDensityRate

noncomputable section

namespace RiemannResearch.Analysis.ZeroDensityRate

theorem stableCutoff_nonneg {ell B R : ℝ} (hB : 0 < B) (hR : 0 ≤ R) :
    0 ≤ stableCutoff ell B R := by
  unfold stableCutoff
  apply div_nonneg
  · positivity
  · exact le_of_lt (add_pos_of_pos_of_nonneg hB (Real.sqrt_nonneg _))

/-- The stable root has an exact comparison test against any nonnegative bound. -/
theorem stableCutoff_le_iff {ell B R t : ℝ}
    (hell : 0 ≤ ell) (hB : 0 < B) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    stableCutoff ell B R ≤ t ↔ 3 * R ≤ 2 * ell * t ^ 2 + B * t := by
  let δ := stableCutoff ell B R
  have hδ : 0 ≤ δ := stableCutoff_nonneg hB hR
  have hq : 2 * ell * δ ^ 2 + B * δ - 3 * R = 0 :=
    stableCutoff_quadratic hell hB hR
  change δ ≤ t ↔ _
  constructor
  · intro hδt
    have hsq : δ ^ 2 ≤ t ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hδt) (add_nonneg ht hδ)
      nlinarith
    have hqm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * ell)
    have hlm := mul_le_mul_of_nonneg_left hδt (le_of_lt hB)
    nlinarith
  · intro hbound
    by_contra hnot
    have hlt : t < δ := lt_of_not_ge hnot
    have hstrict : 0 < B * (δ - t) := mul_pos hB (sub_pos.mpr hlt)
    have hsq : t ^ 2 ≤ δ ^ 2 := by
      have hp := mul_nonneg (le_of_lt (sub_pos.mpr hlt)) (add_nonneg hδ ht)
      nlinarith
    have hqm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * ell)
    nlinarith

/-- This is sharp: the root stays in the physical displacement range precisely
when the requested margin is at most the endpoint margin. -/
theorem stableCutoff_half_iff {M ell R : ℝ}
    (hell : 0 ≤ ell) (hR : 0 ≤ R) (hB : 0 < 4 * M - 3 * ell + 2 * R) :
    stableCutoff ell (4 * M - 3 * ell + 2 * R) R ≤ 1 / 2 ↔
      R ≤ M - ell / 2 := by
  rw [stableCutoff_le_iff hell hB hR (by positivity : 0 ≤ (1 / 2 : ℝ))]
  constructor <;> intro h <;> nlinarith

theorem stableCutoff_range {M ell R : ℝ}
    (hell : 0 ≤ ell) (hR : 0 ≤ R) (hB : 0 < 4 * M - 3 * ell + 2 * R)
    (hbudget : R ≤ M - ell / 2) :
    0 ≤ stableCutoff ell (4 * M - 3 * ell + 2 * R) R ∧
      stableCutoff ell (4 * M - 3 * ell + 2 * R) R ≤ 1 / 2 := by
  exact ⟨stableCutoff_nonneg hB hR,
    (stableCutoff_half_iff hell hR hB).mpr hbudget⟩

/-- No nonsingular-denominator premise is needed when the requested margin
is within the physical range. -/
theorem stableCutoff_margin_of_budget {M ell R : ℝ}
    (hell : 0 ≤ ell) (hR : 0 ≤ R) (hB : 0 < 4 * M - 3 * ell + 2 * R)
    (hbudget : R ≤ M - ell / 2) :
    M * inghamRate (stableCutoff ell (4 * M - 3 * ell + 2 * R) R) -
      ell * stableCutoff ell (4 * M - 3 * ell + 2 * R) R = R := by
  apply stableCutoff_margin hell hR hB
  have hδ := (stableCutoff_range hell hR hB hbudget).2
  exact ne_of_gt (by linarith)

theorem weighted_exp_tangent_le {M δ s : ℝ} (ell : ℝ) (hM : 0 ≤ M)
    (hδs : δ ≤ s) (hs : s ≤ 1 / 2) :
    Real.exp (ell * s - M * inghamRate s) ≤
      Real.exp (ell * δ - M * inghamRate δ) *
        Real.exp (-(12 * M / (3 - 2 * δ) ^ 2 - ell) * (s - δ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := weighted_tangent_le ell hM hδs hs
  nlinarith only [h]

theorem exp_inghamRate_tangent_le {M δ s : ℝ} (hM : 0 ≤ M)
    (hδs : δ ≤ s) (hs : s ≤ 1 / 2) :
    Real.exp (-M * inghamRate s) ≤
      Real.exp ((12 * M / (3 - 2 * δ) ^ 2) * δ - M * inghamRate δ) *
        Real.exp (-(12 * M / (3 - 2 * δ) ^ 2) * s) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := weighted_tangent_le (0 : ℝ) hM hδs hs
  nlinarith only [h]

theorem margin_exp_cancellation {M ell R δ : ℝ}
    (hmargin : M * inghamRate δ - ell * δ = R) :
    Real.exp ell * Real.exp (ell * δ - M * inghamRate δ) = Real.exp (ell - R) := by
  rw [← Real.exp_add]
  congr 1
  linarith

/-- The tangent slope exceeds the secant slope by an exact positive term. -/
theorem localSlope_margin_identity (M ell δ : ℝ) (hδ : 3 - 2 * δ ≠ 0) :
    δ * (12 * M / (3 - 2 * δ) ^ 2 - ell) -
        (M * inghamRate δ - ell * δ) = 8 * M * δ ^ 2 / (3 - 2 * δ) ^ 2 := by
  have hδc : 3 - δ * 2 ≠ 0 := by simpa [mul_comm] using hδ
  unfold inghamRate
  field_simp [hδ, hδc] <;> ring_nf <;> field_simp [hδ, hδc] <;> ring

/-- A strictly positive cutoff margin automatically gives the integrable
weighted tangent slope, even without the coarse condition ell < 4M/3. -/
theorem localSlope_pos_of_margin {M ell R δ : ℝ}
    (hM : 0 ≤ M) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hR : 0 < R)
    (hmargin : M * inghamRate δ - ell * δ = R) :
    ell < 12 * M / (3 - 2 * δ) ^ 2 := by
  have hden : 3 - 2 * δ ≠ 0 := ne_of_gt (by linarith)
  have he := localSlope_margin_identity M ell δ hden
  have hnonneg : 0 ≤ 8 * M * δ ^ 2 / (3 - 2 * δ) ^ 2 := by positivity
  by_contra hnot
  have hp : δ * (12 * M / (3 - 2 * δ) ^ 2 - ell) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hδ0 (sub_nonpos.mpr (le_of_not_gt hnot))
  linarith

theorem stableCutoff_localSlope_pos {M ell R : ℝ}
    (hell : 0 ≤ ell) (hR : 0 < R) (hB : 0 < 4 * M - 3 * ell + 2 * R)
    (hbudget : R ≤ M - ell / 2) :
    ell < 12 * M / (3 - 2 * stableCutoff ell (4 * M - 3 * ell + 2 * R) R) ^ 2 := by
  have hr := stableCutoff_range hell (le_of_lt hR) hB hbudget
  exact localSlope_pos_of_margin (by linarith) hr.1 hr.2 hR
    (stableCutoff_margin_of_budget hell (le_of_lt hR) hB hbudget)

/-- Exact source power budget, retaining the log(log T) gain. -/
theorem inghamPower_eq_expDecay {T L s : ℝ} (hT : 0 < T) (hL : 0 < L) :
    T ^ (1 - inghamRate s) * L ^ (3 - inghamRate s) =
      T * L ^ (3 : ℕ) * Real.exp (-(Real.log T + Real.log L) * inghamRate s) := by
  rw [Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hL,
    show T = Real.exp (Real.log T) from (Real.exp_log hT).symm,
    show L = Real.exp (Real.log L) from (Real.exp_log hL).symm]
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Real.log_exp]
  ring

theorem inghamRate_le_two_thirds {s : ℝ} (hs : s ≤ 3 / 8) :
    inghamRate s ≤ 2 / 3 := by
  have hden : 0 < 3 - 2 * s := by linarith
  unfold inghamRate
  apply (div_le_iff₀ hden).mpr
  linarith

theorem inghamRate_le_two_over_47 {s : ℝ} (hs : s ≤ 1 / 32) :
    inghamRate s ≤ 2 / 47 := by
  have hden : 0 < 3 - 2 * s := by linarith
  unfold inghamRate
  apply (div_le_iff₀ hden).mpr
  linarith

/-- Exact inverse of the nonlinear count-only exponent budget.
This algebraic definition asserts no actual zero-density estimate. -/
noncomputable def countCutoff (M S : ℝ) : ℝ := 3*S/(4*M+2*S)
theorem countCutoff_nonneg {M S : ℝ} (hM : 0 < M) (hS : 0 ≤ S) :
    0 ≤ countCutoff M S := by unfold countCutoff; positivity
theorem countCutoff_rate {M S : ℝ} (hM : 0 < M) (hS : 0 ≤ S) :
    M * inghamRate (countCutoff M S) = S := by
  have hd : 4*M+2*S ≠ 0 := ne_of_gt (by positivity)
  have hm : M ≠ 0 := ne_of_gt hM
  have hden : 3-2*countCutoff M S = 12*M/(4*M+2*S) := by
    unfold countCutoff
    field_simp [hd]
    ring
  unfold inghamRate
  rw [hden]
  unfold countCutoff
  field_simp [hd, hm]
  ring
theorem countCutoff_le_iff {M S t : ℝ} (hM : 0 < M) (hS : 0 ≤ S) :
    countCutoff M S ≤ t ↔ 3*S ≤ t*(4*M+2*S) := by
  unfold countCutoff
  exact div_le_iff₀ (by positivity)
theorem countCutoff_smallRange {M S : ℝ} (hM : 0 < M) (hS : 0 ≤ S) :
    countCutoff M S ≤ 1/32 ↔ 47*S ≤ 2*M := by
  rw [countCutoff_le_iff hM hS]
  constructor <;> intro h <;> nlinarith
/-- The inverse-rate cutoff is the least cutoff meeting the count-only
exponent budget, not merely a sufficient root. -/
theorem countCutoff_le_iff_rate {M S t : ℝ}
    (hM : 0 < M) (hS : 0 ≤ S) (ht : t ≤ 1/2) :
    countCutoff M S ≤ t ↔ S ≤ M*inghamRate t := by
  have htden : 0 < 3-2*t := by linarith
  have hr : M*inghamRate t = (4*M*t)/(3-2*t) := by
    unfold inghamRate
    simp only [div_eq_mul_inv]
    ring
  rw [countCutoff_le_iff hM hS, hr, le_div_iff₀ htden]
  constructor <;> intro h <;> nlinarith
theorem countCutoff_exp_cancellation {M A ω : ℝ}
    (hM : 0 < M) (hA : 0 < A) (hS : 0 ≤ Real.log A + ω) :
    A * Real.exp (-M*inghamRate (countCutoff M (Real.log A + ω))) =
      Real.exp (-ω) := by
  rw [show -M*inghamRate (countCutoff M (Real.log A+ω)) =
    -(M*inghamRate (countCutoff M (Real.log A+ω))) by ring,
    countCutoff_rate hM hS]
  rw [show A = Real.exp (Real.log A) from (Real.exp_log hA).symm,
    ← Real.exp_add]
  simp only [Real.log_exp]
  congr 1
  ring

open Filter

theorem countCutoff_le_ratio {M S : ℝ} (hM : 0 < M) (hS : 0 ≤ S) :
    countCutoff M S ≤ (3/4)* (S/M) := by
  unfold countCutoff
  calc
    _ ≤ 3*S/(4*M) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = _ := by field_simp [hM.ne']

theorem countCutoff_tendsto_zero {α : Type*} {F : Filter α} (M S : α → ℝ)
    (hM : ∀ᶠ t in F, 0 < M t) (hS : ∀ᶠ t in F, 0 ≤ S t)
    (hratio : Tendsto (fun t => S t/M t) F (nhds 0)) :
    Tendsto (fun t => countCutoff (M t) (S t)) F (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hM, hS] with t hm hs
    exact countCutoff_nonneg hm hs
  · filter_upwards [hM, hS] with t hm hs
    exact countCutoff_le_ratio hm hs
  · simpa using hratio.const_mul (3/4 : ℝ)

/-- The least nonnegative inverse-rate cutoff; negative requested margins
use cutoff zero rather than an artificial positivity hypothesis. -/
noncomputable def positiveCountCutoff (M A ω : ℝ) : ℝ :=
  countCutoff M (max 0 (Real.log A+ω))

theorem positiveCountCutoff_nonneg {M : ℝ} (A ω : ℝ) (hM : 0 < M) :
    0 ≤ positiveCountCutoff M A ω :=
  countCutoff_nonneg hM (le_max_left _ _)

theorem positiveCountCutoff_exp_le {M A ω : ℝ} (hM : 0 < M) (hA : 0 < A) :
    A*Real.exp (-M*inghamRate (positiveCountCutoff M A ω)) ≤ Real.exp (-ω) := by
  unfold positiveCountCutoff
  rw [show -M*inghamRate (countCutoff M (max 0 (Real.log A+ω))) =
      -(M*inghamRate (countCutoff M (max 0 (Real.log A+ω)))) by ring,
    countCutoff_rate hM (le_max_left _ _),
    show A = Real.exp (Real.log A) from (Real.exp_log hA).symm,
    ← Real.exp_add]
  simp only [Real.log_exp]
  apply Real.exp_le_exp.mpr
  have h := le_max_right 0 (Real.log A+ω)
  linarith


/-- The exact least-cutoff characterization for the nonlinear count-only
margin, including a possibly negative requested logarithmic margin. -/
theorem positiveCountCutoff_le_iff_margin {M A ω t : ℝ}
    (hM : 0 < M) (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    positiveCountCutoff M A ω ≤ t ↔ Real.log A+ω ≤ M*inghamRate t := by
  unfold positiveCountCutoff
  rw [countCutoff_le_iff_rate hM (le_max_left _ _) ht]
  have hi : 0 ≤ inghamRate t := by
    have hd : 0 < 3-2*t := by linarith
    unfold inghamRate
    positivity
  constructor
  · intro h
    exact (le_max_right _ _).trans h
  · intro h
    exact max_le (mul_nonneg hM.le hi) h

theorem positiveCountCutoff_tendsto_zero {α : Type*} {F : Filter α}
    (M A ω : α → ℝ) (hM : ∀ᶠ t in F, 0 < M t)
    (hratio : Tendsto (fun t => max 0 (Real.log (A t)+ω t)/M t) F (nhds 0)) :
    Tendsto (fun t => positiveCountCutoff (M t) (A t) (ω t)) F (nhds 0) :=
  countCutoff_tendsto_zero M _ hM (Eventually.of_forall fun _ => le_max_left _ _) hratio
/-- Shrinking inverse margins eventually lie in the source's first near-line
interval, without importing any analytic density assertion. -/
theorem positiveCountCutoff_eventually_nearLine {α : Type*} {F : Filter α}
    (M A ω : α → ℝ) (hM : ∀ᶠ t in F, 0 < M t)
    (hratio : Tendsto (fun t => max 0 (Real.log (A t)+ω t)/M t) F (nhds 0)) :
    ∀ᶠ t in F, 0 ≤ positiveCountCutoff (M t) (A t) (ω t) ∧
      positiveCountCutoff (M t) (A t) (ω t) ≤ 1/32 := by
  filter_upwards [hM, (positiveCountCutoff_tendsto_zero M A ω hM hratio).eventually_le_const
    (by norm_num : (0 : ℝ) < 1/32)] with t hm ht
  exact ⟨positiveCountCutoff_nonneg _ _ hm, ht⟩

end RiemannResearch.Analysis.ZeroDensityRate

namespace RiemannResearch.Analysis.ZeroDensityRate
/-- Exact difference of the nonlinear rates. -/
theorem inghamRate_sub_identity (a b : ℝ)
    (ha : 3-2*a ≠ 0) (hb : 3-2*b ≠ 0) :
    inghamRate b-inghamRate a = 12*(b-a)/((3-2*b)*(3-2*a)) := by
  have ha' : 3-a*2 ≠ 0 := by simpa [mul_comm] using ha
  have hb' : 3-b*2 ≠ 0 := by simpa [mul_comm] using hb
  unfold inghamRate
  field_simp [ha, hb, ha', hb']
  ring

theorem inghamRate_mono_of_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1/2) :
    inghamRate a ≤ inghamRate b := by
  have ha0 : 0 < 3-2*a := by linarith
  have hb0 : 0 < 3-2*b := by linarith
  have he := inghamRate_sub_identity a b ha0.ne' hb0.ne'
  have hn : 0 ≤ 12*(b-a)/((3-2*b)*(3-2*a)) := by positivity
  linarith

theorem positiveCountCutoff_exp_le_of_le {M A ω δ : ℝ}
    (hM : 0 < M) (hA : 0 < A)
    (hcut : positiveCountCutoff M A ω ≤ δ) (hδ : δ ≤ 1/2) :
    A*Real.exp (-M*inghamRate δ) ≤ Real.exp (-ω) := by
  have hr := inghamRate_mono_of_le hcut hδ
  have he : Real.exp (-M*inghamRate δ) ≤
      Real.exp (-M*inghamRate (positiveCountCutoff M A ω)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_left he hA.le).trans (positiveCountCutoff_exp_le hM hA)
end RiemannResearch.Analysis.ZeroDensityRate
