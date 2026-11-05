import RiemannResearch.Analysis.VinogradovKorobovProfile
import RiemannResearch.RH.MertensVKFirstMoment

/-!
# Displacement criteria at the explicit Lee–Leong coefficient

E. S. Lee and N. Leong, *New explicit bounds for Mertens function and the
reciprocal of the Riemann zeta-function*, arXiv:2208.06141v5, Theorem 1.1,
equation (11) in the PDF, https://arxiv.org/pdf/2208.06141v5.
The HTML also gives the general estimate in Theorem 2.2, equation (23),
with the row W = 53.99 of Table 1. The proposition below records the
published arithmetic input with its explicit range and prefactor.
-/

noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert QSquarefreeDisplacementRigidity

/-- The leading coefficient of the explicit ordinary Mertens bound. -/
def leeLeongRate : ℝ := (5 / (3 * (53.99 : ℝ) ^ 3)) ^ (1 / 5 : ℝ)

/-- The external arithmetic estimate in the product form printed in (11). -/
def LeeLeongMertensEstimate : Prop :=
  ∀ x : ℝ, Real.exp (Real.exp 10.01) ≤ x →
    |M x| < 25.85 * x * Real.log x *
      Real.exp (-(((5 / (3 * (53.99 : ℝ) ^ 3)) *
        (1 - Real.log 53.99 / Real.log (Real.log x))⁻¹) ^ (1 / 5 : ℝ) * vkProfile x))

/-- The positive correction in (11) absorbs the factor 25.85 log x at the
full leading coefficient. -/
theorem mertens_vk_of_leeLeong (h : LeeLeongMertensEstimate) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ (1 * Real.exp (-leeLeongRate * vkProfile x)) * x := by
  have hbase : 0 < 5 / (3 * (53.99 : ℝ) ^ 3) := by positivity
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos hbase _
  have hr : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  have hk : (0 : ℝ) < leeLeongRate * Real.log 53.99 / 5 := by positivity
  have hL : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hfactored : ∀ᶠ x : ℝ in atTop, |M x| ≤ 25.85 * x * Real.log x *
      Real.exp (-(leeLeongRate *
        (1 - Real.log 53.99 / Real.log (Real.log x)) ^ (-(1 / 5 : ℝ)) * vkProfile x)) := by
    filter_upwards [eventually_ge_atTop (Real.exp (Real.exp (10.01 : ℝ))),
      hL.eventually (eventually_gt_atTop (Real.log (53.99 : ℝ)))] with x hx hlog
    have hlogpos : 0 < Real.log (Real.log x) := hr.trans hlog
    have hδ : 0 ≤ 1 - Real.log 53.99 / Real.log (Real.log x) :=
      sub_nonneg.mpr ((div_le_one hlogpos).mpr hlog.le)
    have he := (h x hx).le
    rw [Real.mul_rpow hbase.le (inv_nonneg.mpr hδ), Real.inv_rpow hδ,
      ← Real.rpow_neg hδ] at he
    exact he
  have hz := vk_second_order_of_variable_coefficient M leeLeongRate (Real.log 53.99)
    25.85 0 hA (by norm_num) hk hfactored
  filter_upwards [hz] with x hx
  calc
    |M x| ≤ x * Real.exp (-leeLeongRate * vkProfile x) := by
      simpa only [zero_mul, sub_zero] using hx
    _ = (1 * Real.exp (-leeLeongRate * vkProfile x)) * x := by ring

/-- At every fixed interior coefficient the pure weighted displacement
moment is equivalent to vanishing of the squarefree projection residual. -/
theorem residual_zero_iff_leeLeong_displacement_moment (h : LeeLeongMertensEstimate)
    (c : ℝ) (hc : 0 < c) (hca : c < leeLeongRate) :
    ZetaTwoOptimizerStage.limitingResidual = 0 ↔
      Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
        Real.exp (-c * vkProfile (n : ℝ))) * |qSequence displacement n|) :=
  residual_zero_iff_vk_displacement_absolute_moment leeLeongRate c 1 hc hca
    (mertens_vk_of_leeLeong h)

/-- The pure weighted first moment suffices under the exact external estimate. -/
theorem riemannHypothesis_of_leeLeong_displacement_moment (h : LeeLeongMertensEstimate)
    (c : ℝ) (hc : 0 < c) (hca : c < leeLeongRate)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-c * vkProfile (n : ℝ))) * |qSequence displacement n|)) : RiemannHypothesis :=
  riemannHypothesis_of_vk_displacement_absolute_moment leeLeongRate c 1 hc hca
    (mertens_vk_of_leeLeong h) hd

/-- An eventual pointwise displacement envelope at any rate below the
printed leading coefficient implies RH. -/
theorem riemannHypothesis_of_leeLeong_exponential_displacement (h : LeeLeongMertensEstimate)
    (b D : ℝ) (hb : 0 < b) (hba : b < leeLeongRate)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * vkProfile (n : ℝ))) : RiemannHypothesis :=
  riemannHypothesis_of_vk_first_moment_exponential_displacement leeLeongRate b 1 D hb hba
    (mertens_vk_of_leeLeong h) hd

end RiemannResearch.RH.QMertensFirstMoment
