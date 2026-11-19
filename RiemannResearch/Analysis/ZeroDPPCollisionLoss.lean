import RiemannResearch.Analysis.ZeroDPPWindowLattice
import RiemannResearch.Analysis.ActualZeroCollisionDensity

/-! A finite collision lower bound for the unmarked triangle-weighted loss from
thinning the occurrence labels of actual zeta zeros. -/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZeroDPPCollisionLoss
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

def normalizer (T : ℝ) := T * Real.log T / (2 * Real.pi)

def integratedTriangle (a b u : ℝ) : ℝ := ∫ r in a..b, max (r - |u|) 0

def keptPair (q : ℕ → ℝ) (T : ℝ) (i j : Copies T) : ℝ :=
  (limitingLaw q).real {x | x (liftCopy T i) = true ∧ x (liftCopy T j) = true}

open Classical in
def triangleLoss (q : ℕ → ℝ) (T a b : ℝ) : ℝ :=
  (∑ i : Copies T, ∑ j : Copies T, if i = j then 0 else
    integratedTriangle a b ((Real.log T / (2 * Real.pi)) * (copyOrdinate T i - copyOrdinate T j)) *
      (1 - keptPair q T i j)) / normalizer T

private theorem triangle_zero_lb {a b : ℝ} (hab : a ≤ b) :
    a * (b-a) ≤ integratedTriangle a b 0 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) hab
    (f := fun _ : ℝ => a) (g := fun r : ℝ => max (r - |(0:ℝ)|) 0)
    intervalIntegrable_const
    ((by fun_prop : Continuous (fun r : ℝ => max (r - |(0:ℝ)|) 0)).intervalIntegrable a b)
    (fun r hr => by simpa using hr.1.trans (le_max_left r 0))
  simpa [integratedTriangle, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

private theorem triangle_nonneg {a b : ℝ} (hab : a ≤ b) (u : ℝ) : 0 ≤ integratedTriangle a b u :=
  intervalIntegral.integral_nonneg hab (fun _ _ => le_max_right _ _)

/-- Every ordered pair of distinct occurrence labels at one ordinate is surely
lost, at its full triangle weight. Other pairs have nonnegative expected loss. -/
theorem zero_lag_weight_le_triangleLoss (q : ℕ → ℝ) {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b) :
    integratedTriangle a b 0 * ((occurrenceExcess (copyOrdinate T) : ℝ) / normalizer T) ≤
      triangleLoss q T a b := by
  classical
  have hn : 0 < normalizer T := by
    have ht := zero_lt_one.trans hT
    have hl := Real.log_pos hT
    unfold normalizer
    positivity
  unfold triangleLoss
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hn.le
  unfold occurrenceExcess
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases he : i = j
  · subst j; simp
  by_cases hg : copyOrdinate T i = copyOrdinate T j
  · have hzero : keptPair q T i j = 0 :=
      collision_pair_probability_zero q ((liftCopy T).injective.ne he) hg
    simp [he, hg, hzero]
  · have hprob : keptPair q T i j ≤ 1 := calc
      _ ≤ (limitingLaw q).real Set.univ := measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
      _ = 1 := by simp
    simp only [he, hg, and_false, if_false, mul_zero]
    exact mul_nonneg (triangle_nonneg hab _) (sub_nonneg.mpr hprob)

theorem collision_excess_le_triangleLoss (q : ℕ → ℝ) {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b) :
    a * (b-a) * ((occurrenceExcess (copyOrdinate T) : ℝ) / normalizer T) ≤
      triangleLoss q T a b := by
  have hpos := zero_lt_one.trans hT
  have hlog := Real.log_pos hT
  have hden : 0 < normalizer T := by unfold normalizer; positivity
  exact (mul_le_mul_of_nonneg_right (triangle_zero_lb hab)
    (div_nonneg (Nat.cast_nonneg _) hden.le)).trans
    (zero_lag_weight_le_triangleLoss q hT hab)

open Classical in
/-- Weighted summation over ordered pairs of distinct occurrence labels. -/
def offDiagonalTriangle (T a b : ℝ) (f : Copies T → Copies T → ℝ) : ℝ :=
  (∑ i : Copies T, ∑ j : Copies T, if i = j then 0 else
    integratedTriangle a b ((Real.log T / (2 * Real.pi)) * (copyOrdinate T i - copyOrdinate T j)) *
      f i j) / normalizer T

def labelVacancy (q : ℕ → ℝ) (T : ℝ) (i : Copies T) : ℝ :=
  1 - limitingKernel q (liftCopy T i) (liftCopy T i)

def triangleVacancyBudget (q : ℕ → ℝ) (T a b : ℝ) : ℝ :=
  offDiagonalTriangle T a b (fun i j => labelVacancy q T i + labelVacancy q T j)

private theorem offDiagonal_mono {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b)
    {f g : Copies T → Copies T → ℝ} (hfg : ∀ i j, i ≠ j → f i j ≤ g i j) :
    offDiagonalTriangle T a b f ≤ offDiagonalTriangle T a b g := by
  classical
  have hl := Real.log_pos hT
  have ht := zero_lt_one.trans hT
  have hnorm : 0 ≤ normalizer T := by unfold normalizer; positivity
  apply div_le_div_of_nonneg_right _ hnorm
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases he : i = j
  · simp [he]
  · simp only [if_neg he]
    exact mul_le_mul_of_nonneg_left (hfg _ _ he) (triangle_nonneg hab _)

private theorem offDiagonal_smul (T a b c : ℝ) (f : Copies T → Copies T → ℝ) :
    offDiagonalTriangle T a b (fun i j => c * f i j) = c * offDiagonalTriangle T a b f := by
  classical
  unfold offDiagonalTriangle
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

/-- The sum of the two marginal omission probabilities bounds the actual
pair omission from above and twice the actual omission from below. -/
theorem triangleLoss_budget_sandwich (q : ℕ → ℝ) {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b) :
    triangleLoss q T a b ≤ triangleVacancyBudget q T a b ∧
      triangleVacancyBudget q T a b ≤ 2 * triangleLoss q T a b := by
  let f := fun (i j : Copies T) => 1 - keptPair q T i j
  let K := limitingKernel q
  have hd := limitingLaw_isDPP q
  change offDiagonalTriangle T a b f ≤ _ ∧ _ ≤ 2 * offDiagonalTriangle T a b f
  constructor
  · apply offDiagonal_mono hT hab
    intro i j hij
    have htwo := hd.two_point ((liftCopy T).injective.ne hij)
    change keptPair q T i j = K _ _ * K _ _ - K _ _ * K _ _ at htwo
    change 1 - keptPair q T i j ≤ _
    rw [htwo]
    exact (hd.pairDefect_bounds ((liftCopy T).injective.ne hij)).2
  · rw [← offDiagonal_smul]
    apply offDiagonal_mono hT hab
    intro i j _
    have hi : keptPair q T i j ≤ K (liftCopy T i) (liftCopy T i) := calc
      _ ≤ (limitingLaw q).real {x | x (liftCopy T i) = true} :=
        measureReal_mono (fun _ hx => hx.1) (measure_ne_top _ _)
      _ = _ := hd.occupation _
    have hj : keptPair q T i j ≤ K (liftCopy T j) (liftCopy T j) := calc
      _ ≤ (limitingLaw q).real {x | x (liftCopy T j) = true} :=
        measureReal_mono (fun _ hx => hx.2) (measure_ne_top _ _)
      _ = _ := hd.occupation _
    change (1-K _ _)+(1-K _ _) ≤ 2*(1-keptPair q T i j)
    linarith

/-- For nonnegative triangle tests, controlling the marginal-vacancy budget
is equivalent to controlling the actual expected deletion loss. -/
theorem triangleLoss_tendsto_zero_iff_budget (q : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun T : ℝ => triangleLoss q T a b) atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => triangleVacancyBudget q T a b) atTop (𝓝 0) := by
  constructor
  · intro h
    have h2 : Tendsto (fun T : ℝ => 2 * triangleLoss q T a b) atTop (𝓝 0) := by
      simpa using h.const_mul (2 : ℝ)
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    obtain ⟨hl, hu⟩ := triangleLoss_budget_sandwich q hT hab
    have hp : 0 ≤ triangleVacancyBudget q T a b := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hu
  · intro h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    obtain ⟨hl, hu⟩ := triangleLoss_budget_sandwich q hT hab
    have hp : 0 ≤ triangleLoss q T a b := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hl

/-- Vanishing genuine omitted-pair loss on even one positive interval forces
normalized collision excess to vanish and hence density one of simple critical zeros. -/
theorem density_one_of_triangleLoss (q : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (h : Tendsto (fun T : ℝ => triangleLoss q T a b) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  have hcoef : 0 < a*(b-a) := mul_pos ha (sub_pos.mpr hab)
  have hex : Tendsto (fun T : ℝ => (occurrenceExcess (copyOrdinate T) : ℝ) / normalizer T)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun T : ℝ => triangleLoss q T a b / (a*(b-a)))
      atTop (𝓝 0) from ?_)
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
      have hn : 0 < normalizer T := by
        have htpos := zero_lt_one.trans ht
        have hl := Real.log_pos ht
        unfold normalizer
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hn.le),
        le_div_iff₀ hcoef, mul_comm]
      exact collision_excess_le_triangleLoss q ht hab.le
    · simpa using h.div_const (a*(b-a))
  apply density_one_of_collision_limit
  have total := tendsto_count_div_mainTerm.add hex
  simp only [add_zero] at total
  apply total.congr' (Eventually.of_forall fun T => ?_)
  have hc := congrArg (fun n : ℕ => (n : ℝ))
    (occurrenceCollision_eq_card_add_excess (copyOrdinate T))
  simp only [Nat.cast_add, card_copies] at hc
  change (Ncount 0 T : ℝ) / normalizer T + _ =
    (occurrenceCollision (copyOrdinate T) : ℝ) / normalizer T
  rw [← add_div, hc]

end RiemannResearch.Analysis.ZeroDPPCollisionLoss
