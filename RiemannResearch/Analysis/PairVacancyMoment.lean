import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Pair-statistic transfer from averaged vacancies and a third moment

Source for the number-theoretic application: Arias de Reyna--Rodgers,
On convergence of points to limiting processes, with an application to zeta
zeros, https://arxiv.org/abs/2311.13441, Theorem 34 and Corollary 35 (Fujii's
microscopic count moments). That analytic input is external here.

These generic measure-theoretic statements are proved from the elementary
Young inequality for 0 <= d <= z. They retain every integrability, moment
and vacancy assumption; the theorem does not prove a zeta-zero moment bound,
vanishing actual vacancies, or a sine-kernel limit.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.PairVacancyMoment

theorem count_vacancy_young (z d a : ℝ) (hd : 0 ≤ d) (hdz : d ≤ z) (ha : 0 < a) :
    2*z*d ≤ a*z^3+d/a := by
  have h1 := mul_nonneg hd (sq_nonneg (a*z-1))
  have h2 := mul_nonneg (sub_nonneg.mpr hdz) (sq_nonneg (a*z))
  have h3 : a*(2*z*d) ≤ a^2*z^3+d := by nlinarith
  apply (mul_le_mul_iff_right₀ ha).mp
  calc
    a*(2*z*d) ≤ a^2*z^3+d := by nlinarith [h3]
    _ = a*(a*z^3+d/a) := by field_simp

theorem integral_pair_error_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f z d : Ω → ℝ) (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (hf : Integrable f ν) (hz : Integrable (fun x => (z x) ^ 3) ν)
    (hd : Integrable d ν)
    (hpos : ∀ x, 0 ≤ d x) (hle : ∀ x, d x ≤ z x)
    (herr : ∀ x, |f x| ≤ 2 * M * z x * d x) :
    |∫ x, f x ∂ν| ≤ M*(a*(∫ x, (z x) ^ 3 ∂ν)+(∫ x, d x ∂ν)/a) := by
  have hg : Integrable (fun x => M*(a*(z x) ^ 3+d x/a)) ν :=
    ((hz.const_mul a).add (hd.div_const a)).const_mul M
  have habs : Integrable (fun x => |f x|) ν := by simpa only [Real.norm_eq_abs] using hf.norm
  calc
    _ ≤ ∫ x, |f x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, M*(a*(z x) ^ 3+d x/a) ∂ν := by
      apply integral_mono habs hg
      intro x
      calc
        |f x| ≤ 2 * M * z x * d x := herr x
        _ = M*(2*z x * d x) := by ring
        _ ≤ M*(a*(z x) ^ 3+d x/a) :=
          mul_le_mul_of_nonneg_left (count_vacancy_young _ _ _ (hpos x) (hle x) ha) hM
    _ = _ := by
      rw [integral_const_mul, integral_add (hz.const_mul a) (hd.div_const a),
        integral_const_mul, integral_div]

theorem tendsto_zero_of_young_bounds {β : Type*} {l : Filter β}
    (f d : β → ℝ) (M C : ℝ) (hM : 0 < M) (hC : 0 < C)
    (hd : Tendsto d l (𝓝 0))
    (hb : ∀ a : ℝ, 0 < a → ∀ t, |f t| ≤ M*(a*C+d t/a)) :
    Tendsto f l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let a := ε/(4*M*C)
  have ha : 0 < a := by dsimp [a]; positivity
  have hac : M*(a*C) = ε/4 := by dsimp [a]; field_simp
  have htol : 0 < a*ε/(4*M) := by positivity
  filter_upwards [(tendsto_order.mp hd).2 (a*ε/(4*M)) htol] with t ht
  have hs : M*(d t/a) < ε/4 := by
    calc
      _ < M*((a*ε/(4*M))/a) :=
        mul_lt_mul_of_pos_left ((div_lt_div_iff_of_pos_right ha).mpr ht) hM
      _ = ε/4 := by field_simp
  rw [Real.dist_eq, sub_zero]
  calc
    |f t| ≤ M*(a*C+d t/a) := hb a ha t
    _ = ε/4+M*(d t/a) := by rw [mul_add, hac]
    _ < ε/4+ε/4 := by linarith
    _ < ε := by linarith

theorem integral_tendsto_zero_of_vacancy {β Ω : Type*} [MeasurableSpace Ω]
    {l : Filter β} (ν : β → Measure Ω) (f z d : β → Ω → ℝ)
    (M C : ℝ) (hM : 0 < M) (hC : 0 < C)
    (hf : ∀ t, Integrable (f t) (ν t))
    (hz : ∀ t, Integrable (fun x => (z t x) ^ 3) (ν t))
    (hd : ∀ t, Integrable (d t) (ν t))
    (hpos : ∀ t x, 0 ≤ d t x) (hle : ∀ t x, d t x ≤ z t x)
    (herr : ∀ t x, |f t x| ≤ 2 * M * z t x * d t x)
    (hmoment : ∀ t, (∫ x, (z t x) ^ 3 ∂ν t) ≤ C)
    (hvacancy : Tendsto (fun t => ∫ x, d t x ∂ν t) l (𝓝 0)) :
    Tendsto (fun t => ∫ x, f t x ∂ν t) l (𝓝 0) := by
  apply tendsto_zero_of_young_bounds _ _ M C hM hC hvacancy
  intro a ha t
  apply (integral_pair_error_le (ν t) (f t) (z t) (d t) M a hM.le ha
    (hf t) (hz t) (hd t) (hpos t) (hle t) (herr t)).trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  have h := mul_le_mul_of_nonneg_left (hmoment t) ha.le
  linarith
end RiemannResearch.Analysis.PairVacancyMoment
