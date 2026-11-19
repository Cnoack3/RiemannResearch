import RiemannResearch.Analysis.OrdinateWindowVariance
import RiemannResearch.Analysis.PairVacancyMoment

/-! Triangle-weighted deletion estimates on a finite translated window. The third count
moment in the bound can be supplied for actual ordinates by Arias de Reyna and Rodgers,
*On convergence of points to limiting processes*, Corollary 35, after dyadic summation.
All finite identities below include repeated locations. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ZeroDPPTriangleVacancy
open OrdinateWindowVariance PairVacancyMoment
variable {ι : Type*} [Fintype ι]

def weightedWindow (v x : ι → ℝ) (T h t : ℝ) : ℝ :=
  ∑ i, v i * windowPulse T h (x i) t

def triangle (h x y : ℝ) : ℝ := max (h - |x-y|) 0

private theorem window_nonneg (T h x t : ℝ) : 0 ≤ windowPulse T h x t := by
  unfold windowPulse pulse Set.indicator
  split_ifs <;> norm_num

theorem integral_weighted_window (v x : ι → ℝ) {T h : ℝ} (hh : 0 ≤ h)
    (hx : ∀ i, h ≤ x i ∧ x i ≤ T) :
    (∫ t, weightedWindow v x T h t) = h * ∑ i, v i := by
  unfold weightedWindow
  rw [integral_finsetSum _ (fun i _ => (windowPulse_integrable T h (x i)).const_mul (v i))]
  simp_rw [integral_const_mul, windowPulse, integral_pulse, min_eq_right (hx _).2,
    max_eq_right (sub_nonneg.mpr (hx _).1), sub_sub_cancel, max_eq_left hh]
  rw [← Finset.sum_mul, mul_comm]

private theorem mixed_integrable (v x : ι → ℝ) (T h : ℝ) :
    Integrable (fun t => windowCount Finset.univ x T h t * weightedWindow v x T h t) := by
  simp only [weightedWindow, windowCount, Finset.sum_mul, Finset.mul_sum,
      mul_left_comm (windowPulse _ _ _ _)]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (windowPulse_mul_integrable T h (x j) (x i)).const_mul (v i)

/-- Exact integrated product, including the diagonal and both endpoint support conditions. -/
theorem integral_count_mul_weightedWindow (v x : ι → ℝ) {T h : ℝ}
    (hx : ∀ i, h ≤ x i ∧ x i ≤ T) :
    (∫ t, windowCount Finset.univ x T h t * weightedWindow v x T h t) =
      ∑ i, ∑ j, v j * triangle h (x i) (x j) := by
  simp only [weightedWindow, windowCount, Finset.sum_mul, Finset.mul_sum,
    mul_left_comm (windowPulse _ _ _ _)]
  conv_rhs => rw [Finset.sum_comm]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (windowPulse_mul_integrable T h (x j) (x i)).const_mul (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ =>
    (windowPulse_mul_integrable T h (x j) (x i)).const_mul (v i))]
  simp_rw [integral_const_mul, windowPulse, pulse_mul, integral_pulse, min_eq_right (hx _).2,
    max_eq_right (sub_nonneg.mpr (hx _).1), overlap_triangle, triangle]

/-- The third moment controls every pair test dominated by a triangle, even when
several labels are at the same location. The pointwise deletion probability can be
bounded by the sum of the two marginal vacancies without any independence assumption. -/
theorem pair_loss_le_third_moment (v x : ι → ℝ) {T h C : ℝ}
    (hh : 0 ≤ h) (hC : 0 ≤ C) (hx : ∀ i, h ≤ x i ∧ x i ≤ T)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (f : ι → ι → ℝ)
    (hf : ∀ i j, f i j ≤ C * (v i + v j) * triangle h (x i) (x j))
    (hthird : Integrable (fun t => (windowCount Finset.univ x T h t) ^ 3)) :
    (∑ i, ∑ j, f i j) ≤ 2 * C * Real.sqrt
      ((∫ t, (windowCount Finset.univ x T h t) ^ 3) * (h * ∑ i, v i)) := by
  let z := windowCount Finset.univ x T h
  let d := weightedWindow v x T h
  have hd t : 0 ≤ d t := Finset.sum_nonneg fun i _ => mul_nonneg (hv i).1 (window_nonneg ..)
  have hdz t : d t ≤ z t := Finset.sum_le_sum fun i _ =>
    mul_le_of_le_one_left (window_nonneg ..) (hv i).2
  have hz t : 0 ≤ z t := (hd t).trans (hdz t)
  have hint : Integrable d := integrable_finsetSum _ fun i _ =>
    (windowPulse_integrable T h (x i)).const_mul (v i)
  have hmix := mixed_integrable v x T h
  have hb := integral_pair_error_le_sqrt volume (fun t => 2*C*(z t*d t)) z d C hC
    (hmix.const_mul (2*C)) hthird hint hd hdz (fun t => by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (mul_nonneg (hz t) (hd t)))]
      exact le_of_eq (by ring))
  have hi := (le_abs_self _).trans hb
  rw [integral_const_mul,
    show (∫ t, d t) = h * ∑ i, v i from integral_weighted_window v x hh hx,
    show (∫ t, z t*d t) = _ from integral_count_mul_weightedWindow v x hx] at hi
  have hswap : (∑ i, ∑ j, v i * triangle h (x i) (x j)) =
      ∑ i, ∑ j, v j * triangle h (x i) (x j) := by
    rw [Finset.sum_comm]; simp_rw [triangle, abs_sub_comm]
  calc
    _ ≤ ∑ i, ∑ j, C * (v i + v j) * triangle h (x i) (x j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hf i j
    _ = 2*C*(∑ i, ∑ j, v j * triangle h (x i) (x j)) := by
      have he (i j : ι) : C * (v i + v j) * triangle h (x i) (x j) =
          C * (v i * triangle h (x i) (x j) + v j * triangle h (x i) (x j)) := by ring
      simp_rw [he, ← Finset.mul_sum, Finset.sum_add_distrib, hswap]; ring
    _ ≤ _ := hi

/-- The integrated unfolded triangle weight is bounded by the physical triangle at
its upper endpoint. This monotone domination is used only for the deletion error. -/
theorem integrated_weight_le {a b L : ℝ} (hab : a ≤ b) (hL : 0 < L) (x y : ℝ) :
    (∫ r in a..b, triangle (r/L) x y) ≤ (b-a) * triangle (b/L) x y := by
  have hcont : Continuous (fun r : ℝ => triangle (r/L) x y) := by unfold triangle; fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (hcont.intervalIntegrable a b) (g := fun _ : ℝ => triangle (b/L) x y) intervalIntegrable_const
    (fun r hr => max_le_max_right 0 (sub_le_sub_right (div_le_div_of_nonneg_right hr.2 hL.le) _))
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hi

/-- The exact width-integrated deletion probability is bounded by the third moment
at the upper width and the number of omitted labels. Set the self-label loss to zero. -/
theorem interval_pair_loss_le (v x : ι → ℝ) {T a b L : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hL : 0 < L) (hx : ∀ i, b/L ≤ x i ∧ x i ≤ T) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (omission : ι → ι → ℝ) (ho : ∀ i j, 0 ≤ omission i j ∧ omission i j ≤ v i + v j)
    (hthird : Integrable (fun t => (windowCount Finset.univ x T (b/L) t) ^ 3)) :
    (∑ i, ∑ j, (∫ r in a..b, triangle (r/L) (x i) (x j)) * omission i j) ≤
      2 * (b-a) * Real.sqrt ((∫ t, (windowCount Finset.univ x T (b/L) t) ^ 3) *
        ((b/L) * ∑ i, v i)) := by
  apply pair_loss_le_third_moment v x (div_nonneg (ha.trans hab) hL.le)
    (sub_nonneg.mpr hab) hx hv _ _ hthird
  intro i j
  calc
    _ ≤ ((b-a) * triangle (b/L) (x i) (x j)) * (v i + v j) :=
      mul_le_mul (integrated_weight_le hab hL _ _) (ho i j).2 (ho i j).1
        (mul_nonneg (sub_nonneg.mpr hab) (le_max_right _ _))
    _ = _ := by ring

end RiemannResearch.Analysis.ZeroDPPTriangleVacancy
