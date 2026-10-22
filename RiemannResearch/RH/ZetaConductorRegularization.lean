import RiemannResearch.RH.ArithmeticConductorCommonZeros
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp

/-!
# Entire arithmetic zeta-conductor multipliers

Source: user-provided argument, Sections 4 and 10.4 of
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.
The source supplies the intended multiplier `zeta(s) (1/n - n^(-s))`.
Mathlib's actual `riemannZeta_residue_one` supplies the pole residue; Riemann's
removable-singularity theorem supplies analyticity at the missing point.

This module proves the value at one, entire regularity, individual vanishing
orders in the critical strip, and the exact common vanishing order of the
two entire multipliers. It does not assume any zeta-zero simplicity statement.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannResearch.RH.ZetaConductorRegularization

open ArithmeticConductorCommonZeros

theorem hasDerivAt_conductorSymbol (n : ℕ) (s : ℂ) :
    HasDerivAt (conductorSymbol n)
      ((Real.log n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))) s := by
  have hd := (((hasDerivAt_id s).neg.mul_const (Real.log n : ℂ)).cexp).const_sub
    ((n : ℂ)⁻¹)
  simp only [Pi.neg_apply, id_eq] at hd
  convert hd using 1 <;> first | rfl | ring

theorem analyticAt_conductorSymbol (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (conductorSymbol n) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Filter.Eventually.of_forall fun t =>
    (hasDerivAt_conductorSymbol n t).differentiableAt

theorem hasDerivAt_conductorSymbol_one (n : ℕ) (hn : 0 < n) :
    HasDerivAt (conductorSymbol n) ((Real.log n : ℂ) / n) 1 := by
  have he : Complex.exp (-(1 : ℂ) * (Real.log n : ℂ)) = (n : ℂ)⁻¹ := by
    exact (sub_eq_zero.mp (conductorSymbol_one n hn)).symm
  simpa only [he, div_eq_mul_inv] using hasDerivAt_conductorSymbol n 1

/-- The actual punctured multiplier has the required limit, including its sign. -/
theorem tendsto_zeta_mul_conductorSymbol_one (n : ℕ) (hn : 0 < n) :
    Tendsto (fun s => riemannZeta s * conductorSymbol n s) (𝓝[≠] 1)
      (𝓝 ((Real.log n : ℂ) / n)) := by
  have hd := (hasDerivAt_conductorSymbol_one n hn).tendsto_slope
  have hprod := riemannZeta_residue_one.mul hd
  simp only [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  rw [slope_def_field, conductorSymbol_one n hn, sub_zero]
  field_simp [sub_ne_zero.mpr hs1]

/-- The removable continuation of the actual zeta-conductor product. -/
def conductorZeta (n : ℕ) (s : ℂ) : ℂ :=
  if s = 1 then (Real.log n : ℂ) / n else riemannZeta s * conductorSymbol n s

@[simp] theorem conductorZeta_one (n : ℕ) :
    conductorZeta n 1 = (Real.log n : ℂ) / n := by
  simp [conductorZeta]

theorem conductorZeta_of_ne_one (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    conductorZeta n s = riemannZeta s * conductorSymbol n s := by
  simp [conductorZeta, hs]

/-- Every actual zeta zero away from the pole annihilates the multiplier. -/
theorem conductorZeta_eq_zero_of_zeta_zero (n : ℕ) {s : ℂ}
    (hs : s ≠ 1) (hz : riemannZeta s = 0) : conductorZeta n s = 0 := by
  rw [conductorZeta_of_ne_one n hs, hz, zero_mul]

/-- The other polar value is evaluated without a limit or a zeta hypothesis. -/
@[simp] theorem conductorZeta_zero (n : ℕ) :
    conductorZeta n 0 = (1 - (n : ℂ)⁻¹) / 2 := by
  rw [conductorZeta_of_ne_one n (by norm_num : (0 : ℂ) ≠ 1), riemannZeta_zero]
  simp only [conductorSymbol, neg_zero, zero_mul, Complex.exp_zero]
  ring

theorem conductorZeta_eventuallyEq (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    conductorZeta n =ᶠ[𝓝 s] fun t => riemannZeta t * conductorSymbol n t := by
  filter_upwards [compl_singleton_mem_nhds hs] with t ht
  exact conductorZeta_of_ne_one n ht

theorem analyticAt_conductorZeta_of_ne_one (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (conductorZeta n) s := by
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  exact (hz.mul (analyticAt_conductorSymbol n s)).congr
    (conductorZeta_eventuallyEq n hs).symm

theorem continuousAt_conductorZeta_one (n : ℕ) (hn : 0 < n) :
    ContinuousAt (conductorZeta n) 1 := by
  rw [continuousAt_iff_punctured_nhds, conductorZeta_one]
  apply (tendsto_zeta_mul_conductorSymbol_one n hn).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (conductorZeta_of_ne_one n hs).symm

/-- Entire regularity is proved using the zeta residue, not postulated. -/
theorem analyticAt_conductorZeta (n : ℕ) (hn : 0 < n) (s : ℂ) :
    AnalyticAt ℂ (conductorZeta n) s := by
  by_cases hs : s = 1
  · subst s
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (analyticAt_conductorZeta_of_ne_one n ht).differentiableAt
    · exact continuousAt_conductorZeta_one n hn
  · exact analyticAt_conductorZeta_of_ne_one n hs

theorem differentiable_conductorZeta (n : ℕ) (hn : 0 < n) :
    Differentiable ℂ (conductorZeta n) :=
  fun s => (analyticAt_conductorZeta n hn s).differentiableAt

theorem conductorZeta_one_ne_zero (n : ℕ) (hn : 1 < n) :
    conductorZeta n 1 ≠ 0 := by
  rw [conductorZeta_one]
  apply div_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).ne'
  · have hn0 : n ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hn)
    exact_mod_cast hn0

/-- The removable point contributes no zero, and hence no common zero. -/
theorem analyticOrderAt_conductorZeta_one (n : ℕ) (hn : 1 < n) :
    analyticOrderAt (conductorZeta n) 1 = 0 := by
  exact (analyticAt_conductorZeta n (lt_trans Nat.zero_lt_one hn) 1).analyticOrderAt_eq_zero.mpr
    (conductorZeta_one_ne_zero n hn)

/-- Every artificial conductor zero is simple. -/
theorem analyticOrderAt_conductorSymbol_of_zero (n : ℕ) (hn : 1 < n)
    (s : ℂ) (hs : conductorSymbol n s = 0) :
    analyticOrderAt (conductorSymbol n) s = 1 := by
  have hd : deriv (conductorSymbol n) s ≠ 0 := by
    rw [(hasDerivAt_conductorSymbol n s).deriv]
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr
        (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).ne'
    · exact Complex.exp_ne_zero _
  simpa only [hs, sub_zero] using
    (analyticAt_conductorSymbol n s).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd

/-- Away from the removable point, all multiplicities add exactly. -/
theorem analyticOrderAt_conductorZeta (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt (conductorZeta n) s =
      analyticOrderAt riemannZeta s + analyticOrderAt (conductorSymbol n) s := by
  rw [analyticOrderAt_congr (conductorZeta_eventuallyEq n hs)]
  exact analyticOrderAt_mul (analyticOn_riemannZeta s hs)
    (analyticAt_conductorSymbol n s)

/-- A nonzero conductor factor preserves every zeta-zero multiplicity. -/
theorem analyticOrderAt_conductorZeta_of_symbol_ne_zero (n : ℕ) {s : ℂ}
    (hs : s ≠ 1) (hp : conductorSymbol n s ≠ 0) :
    analyticOrderAt (conductorZeta n) s = analyticOrderAt riemannZeta s := by
  rw [analyticOrderAt_conductorZeta n hs,
    (analyticAt_conductorSymbol n s).analyticOrderAt_eq_zero.mpr hp, add_zero]

/-- In particular, this multiplicity identity holds throughout the open critical strip. -/
theorem analyticOrderAt_conductorZeta_of_re_ne_one (n : ℕ) (hn : 1 < n)
    (s : ℂ) (hs : s.re ≠ 1) :
    analyticOrderAt (conductorZeta n) s = analyticOrderAt riemannZeta s := by
  apply analyticOrderAt_conductorZeta_of_symbol_ne_zero n
  · intro h; apply hs; simp [h]
  · exact conductorSymbol_ne_zero_of_re_ne_one n hn s hs

/-- Conductors two and three have exactly the zeta zeros after the actual removal at one. -/
theorem conductorZeta_two_three_common_zero_iff (s : ℂ) :
    (conductorZeta 2 s = 0 ∧ conductorZeta 3 s = 0) ↔
      s ≠ 1 ∧ riemannZeta s = 0 := by
  constructor
  · rintro ⟨h2, h3⟩
    have hs : s ≠ 1 := by
      intro h
      subst s
      exact (conductorZeta_one_ne_zero 2 (by norm_num)) h2
    refine ⟨hs, (common_conductor_products_zero_iff (riemannZeta s) s hs).mp ?_⟩
    simpa only [conductorZeta_of_ne_one _ hs] using And.intro h2 h3
  · rintro ⟨hs, hz⟩
    exact ⟨conductorZeta_eq_zero_of_zeta_zero 2 hs hz,
      conductorZeta_eq_zero_of_zeta_zero 3 hs hz⟩

/-- The common multiplicity (minimum of the two orders) equals the zeta multiplicity. -/
theorem min_analyticOrderAt_conductorZeta_two_three {s : ℂ} (hs : s ≠ 1) :
    min (analyticOrderAt (conductorZeta 2) s) (analyticOrderAt (conductorZeta 3) s) =
      analyticOrderAt riemannZeta s := by
  rcases conductorSymbol_two_or_three_ne_zero s hs with h2 | h3
  · rw [analyticOrderAt_conductorZeta_of_symbol_ne_zero 2 hs h2,
      analyticOrderAt_conductorZeta 3 hs]
    exact min_eq_left (le_add_of_nonneg_right zero_le)
  · rw [analyticOrderAt_conductorZeta_of_symbol_ne_zero 3 hs h3,
      analyticOrderAt_conductorZeta 2 hs]
    exact min_eq_right (le_add_of_nonneg_right zero_le)

/-- No multiplier germ is identically zero: all its zero multiplicities are finite. -/
theorem analyticOrderAt_conductorZeta_ne_top (n : ℕ) (hn : 1 < n) (s : ℂ) :
    analyticOrderAt (conductorZeta n) s ≠ ⊤ := by
  have hf : AnalyticOnNhd ℂ (conductorZeta n) Set.univ :=
    fun z _ => analyticAt_conductorZeta n (lt_trans Nat.zero_lt_one hn) z
  apply hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (1 : ℂ)) (Set.mem_univ s)
  rw [analyticOrderAt_conductorZeta_one n hn]
  simp

/-- In particular, the exact zeta multiplicities used above are finite. -/
theorem analyticOrderAt_riemannZeta_ne_top_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  intro hz
  apply analyticOrderAt_conductorZeta_ne_top 2 (by norm_num) s
  rw [analyticOrderAt_conductorZeta 2 hs, hz]
  simp

end RiemannResearch.RH.ZetaConductorRegularization
