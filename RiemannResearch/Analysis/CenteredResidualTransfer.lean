import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Signed residual transfer and quantitative model floors

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The algebraic statements apply to the exact arithmetic decomposition Q = M + R.
They do not prove an analytic model estimate, an actual prime-pair estimate,
or RH. Every analytic bound is an explicit argument of the theorem that uses it.

The dyadic series statements formalize the summability mechanism behind the
annular Fourier tail. Establishing the Fourier estimate for the actual von
Mangoldt vector is a separate analytic input.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.CenteredResidualTransfer

variable {ι : Type*}

/-- A signed upper bound at a nonnegative reference scale. -/
def UpperControlled (scale f : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i, f i ≤ C * scale i

/-- A two-sided bound at a nonnegative reference scale. -/
def AbsControlled (scale f : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i, |f i| ≤ C * scale i

theorem residual_floor_of_model_envelope
    {Q M R scale error : ι → ℝ} {c : ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (hQ : ∀ i, 0 ≤ Q i)
    (hmodel : ∀ i, |M i - c * scale i| ≤ error i) :
    ∀ i, -c * scale i - error i ≤ R i := by
  intro i
  have hm := (abs_le.mp (hmodel i)).2
  have hq := hQ i
  have hd := hdecomp i
  linarith

/-- An explicit finite-index strengthening of the signed residual floor. -/
theorem residual_floor_of_uniform_model_error
    {Q M R scale : ι → ℝ} {c K : ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (hQ : ∀ i, 0 ≤ Q i)
    (hmodel : ∀ i, |M i - c * scale i| ≤ K) :
    ∀ i, -c * scale i - K ≤ R i :=
  residual_floor_of_model_envelope hdecomp hQ hmodel

theorem energy_upper_of_residual_upper
    {Q M R scale error : ι → ℝ} {c C : ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (hmodel : ∀ i, |M i - c * scale i| ≤ error i)
    (hresidual : ∀ i, R i ≤ C * scale i) :
    ∀ i, Q i ≤ (c + C) * scale i + error i := by
  intro i
  have hm := (abs_le.mp (hmodel i)).2
  have hr := hresidual i
  have hd := hdecomp i
  nlinarith

theorem residual_upper_of_energy_upper
    {Q M R scale error : ι → ℝ} {c C : ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (hmodel : ∀ i, |M i - c * scale i| ≤ error i)
    (henergy : ∀ i, Q i ≤ C * scale i) :
    ∀ i, R i ≤ (C - c) * scale i + error i := by
  intro i
  have hm := (abs_le.mp (hmodel i)).1
  have hq := henergy i
  have hd := hdecomp i
  nlinarith

/-- If an actual spectral energy estimate is supplied, its full error is
transported to the actual pair residual; neither source of error is dropped. -/
theorem residual_error_of_model_and_energy_error
    {Q M R scale energyError modelError : ι → ℝ} {spectral c : ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (henergy : ∀ i, |Q i - spectral * scale i| ≤ energyError i)
    (hmodel : ∀ i, |M i - c * scale i| ≤ modelError i) :
    ∀ i, |R i - (spectral - c) * scale i| ≤ energyError i + modelError i := by
  intro i
  have hq := abs_le.mp (henergy i)
  have hm := abs_le.mp (hmodel i)
  have hd := hdecomp i
  apply abs_le.mpr
  constructor <;> nlinarith [hq.1, hq.2, hm.1, hm.2]

/-- The residual's limiting coefficient is the actual energy coefficient
minus the signed model coefficient. Both limits are explicit hypotheses. -/
theorem tendsto_residual_ratio_of_model_and_energy
    {Q M R scale : ι → ℝ} {F : Filter ι} {spectral c : ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (henergy : Tendsto (fun i => Q i / scale i) F (𝓝 spectral))
    (hmodel : Tendsto (fun i => M i / scale i) F (𝓝 c)) :
    Tendsto (fun i => R i / scale i) F (𝓝 (spectral - c)) := by
  have heq : (fun i => R i / scale i) =
      (fun i => Q i / scale i - M i / scale i) := by
    funext i
    have hr : R i = Q i - M i := by linarith [hdecomp i]
    rw [hr, sub_div]
  rw [heq]
  exact henergy.sub hmodel

/-- Model control transfers signed upper control in both directions.
Positivity of Q is not needed for this equivalence. -/
theorem upperControlled_energy_iff_residual
    {Q M R scale : ι → ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (hmodel : AbsControlled scale M) :
    UpperControlled scale Q ↔ UpperControlled scale R := by
  obtain ⟨B, hB, hm⟩ := hmodel
  constructor
  · rintro ⟨C, hC, hq⟩
    refine ⟨C + B, add_nonneg hC hB, ?_⟩
    intro i
    have hb := (abs_le.mp (hm i)).1
    have he := hq i
    have hd := hdecomp i
    nlinarith
  · rintro ⟨C, hC, hr⟩
    refine ⟨C + B, add_nonneg hC hB, ?_⟩
    intro i
    have hb := (abs_le.mp (hm i)).2
    have he := hr i
    have hd := hdecomp i
    nlinarith

/-- With a nonnegative actual energy, the lower residual bound is automatic. -/
theorem absControlled_residual_of_signed_upper
    {Q M R scale : ι → ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (hQ : ∀ i, 0 ≤ Q i)
    (hscale : ∀ i, 0 ≤ scale i)
    (hmodel : AbsControlled scale M)
    (hresidual : UpperControlled scale R) :
    AbsControlled scale R := by
  obtain ⟨B, hB, hm⟩ := hmodel
  obtain ⟨C, hC, hr⟩ := hresidual
  refine ⟨B + C, add_nonneg hB hC, ?_⟩
  intro i
  apply abs_le.mpr
  have hb := (abs_le.mp (hm i)).2
  have he := hr i
  have hq := hQ i
  have hd := hdecomp i
  have hBg := mul_nonneg hB (hscale i)
  have hCg := mul_nonneg hC (hscale i)
  constructor <;> nlinarith

/-- A negative limiting model coefficient precludes a subscale residual.
For the annular arithmetic application the reference scale is log X and
the model convergence is an explicit analytic input. -/
theorem not_tendsto_residual_ratio_zero
    {Q M R scale : ι → ℝ} {F : Filter ι} [NeBot F] {c : ℝ}
    (hdecomp : ∀ i, Q i = M i + R i)
    (hQ : ∀ i, 0 ≤ Q i)
    (hscale : ∀ᶠ i in F, 0 < scale i)
    (hc : c < 0)
    (hmodel : Tendsto (fun i => M i / scale i) F (𝓝 c)) :
    ¬ Tendsto (fun i => R i / scale i) F (𝓝 0) := by
  intro hresidual
  have hlim : Tendsto (fun i => Q i / scale i) F (𝓝 c) := by
    have heq : (fun i => Q i / scale i) =
        (fun i => M i / scale i + R i / scale i) := by
      funext i
      rw [hdecomp i, add_div]
    rw [heq]
    simpa only [add_zero] using hmodel.add hresidual
  have hnonneg : ∀ᶠ i in F, 0 ≤ Q i / scale i := by
    filter_upwards [hscale] with i hi
    exact div_nonneg (hQ i) (le_of_lt hi)
  have hcnonneg : 0 ≤ c := ge_of_tendsto hlim hnonneg
  linarith

/-- The abstract ratio in the dyadic Fourier estimate X^(-5δ) log X. -/
def dyadicRatio (δ : ℝ) : ℝ := Real.exp (-(5 * δ) * Real.log 2)

theorem dyadicRatio_pos (δ : ℝ) : 0 < dyadicRatio δ :=
  Real.exp_pos _

theorem dyadicRatio_lt_one {δ : ℝ} (hδ : 0 < δ) : dyadicRatio δ < 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dyadicRatio
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (by linarith) hl

/-- A log factor does not spoil a strictly decaying dyadic geometric bound. -/
theorem summable_linear_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hn : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hg : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  convert hn.add hg using 1
  funext n
  ring

/-- Exact quantitative sum of the generic dyadic envelope. -/
theorem hasSum_linear_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) (1 / (1 - r) ^ 2) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hden : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hg := hasSum_geometric_of_norm_lt_one hr
  have hfun : (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) =
      (fun n : ℕ => (n : ℝ) * r ^ n + r ^ n) := by
    funext n
    ring
  have hvalue : r / (1 - r) ^ 2 + (1 - r)⁻¹ = 1 / (1 - r) ^ 2 := by
    field_simp [hden]
    ring
  rw [hfun, ← hvalue]
  exact hn.add hg

theorem summable_dyadic_fourier_envelope {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * dyadicRatio δ ^ n) :=
  summable_linear_geometric (le_of_lt (dyadicRatio_pos δ)) (dyadicRatio_lt_one hδ)

/-- Any actual nonnegative dyadic energies satisfying the specified analytic
envelope have a finite sum. The envelope estimate is not hidden in the proof. -/
theorem summable_of_linear_geometric_bound
    {energy : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (henergy : ∀ n, 0 ≤ energy n)
    (hbound : ∀ n, energy n ≤ C * (((n : ℝ) + 1) * r ^ n)) :
    Summable energy :=
  ((summable_linear_geometric hr0 hr1).mul_left C).of_nonneg_of_le henergy hbound

/-- The analytic estimate's envelope itself cannot be summable at or beyond
the cutoff threshold. This does not assert divergence of actual high-frequency
energy: a divergent upper envelope provides no such lower bound. -/
theorem not_summable_linear_geometric_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  intro hs
  have hp : ∀ n : ℕ, 1 ≤ r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hprod := mul_nonneg (sub_nonneg.mpr ih) (sub_nonneg.mpr hr)
        nlinarith
  have hb : ∀ᶠ n : ℕ in atTop, 1 ≤ ((n : ℝ) + 1) * r ^ n := by
    filter_upwards [] with n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hprod := mul_nonneg hn (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hp n))
    nlinarith [hp n]
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hs.tendsto_atTop_zero hb
  norm_num at hbad

end RiemannResearch.Analysis.CenteredResidualTransfer
