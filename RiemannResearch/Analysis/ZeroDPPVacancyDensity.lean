import RiemannResearch.Analysis.ZeroDPPTriangleVacancy
import RiemannResearch.Analysis.ZeroDPPCollisionLoss

/-! The integrated triangle loss for the prime and logarithmic projection laws
is equivalent to density one of simple critical zeros, given only the translated
cutoff count's normalized third-moment upper bound at the largest tested width. -/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZeroDPPVacancyDensity
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open ZeroDPPCorrelation OrdinateWindowVariance ZeroDPPCollisionLoss ZeroDPPTriangleVacancy
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

def BoundedTranslatedThirdMoment (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
    (∫ t : ℝ, (actualWindowCount T (b / (Real.log T / (2 * Real.pi))) t)^3) / T ≤ C

private theorem window_cube_integrable {ι : Type*} [Fintype ι] (x : ι → ℝ) (T h : ℝ) :
    Integrable (fun t => (windowCount Finset.univ x T h t)^3) := by
  let Z := windowCount Finset.univ x T h
  have hb (t : ℝ) : 0 ≤ Z t ∧ Z t ≤ (Fintype.card ι : ℝ) := by
    have hp (i : ι) : 0 ≤ windowPulse T h (x i) t ∧ windowPulse T h (x i) t ≤ 1 := by
      unfold windowPulse pulse Set.indicator
      split_ifs <;> norm_num
    refine ⟨Finset.sum_nonneg fun i _ => (hp i).1, ?_⟩
    exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hp i).2)).trans_eq (by simp)
  have hi := windowCount_integrable Finset.univ x T h
  have hi2 := (windowCount_sq_integrable Finset.univ x T h).const_mul (Fintype.card ι : ℝ)
  refine hi2.mono' (hi.aestronglyMeasurable.pow 3) (ae_of_all _ fun t => ?_)
  change ‖Z t ^ 3‖ ≤ (Fintype.card ι : ℝ) * (Z t)^2
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb t).1 _), pow_succ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb t).2 (sq_nonneg _)

private theorem rescale_weight {L : ℝ} (hL : 0 < L) (a b x y : ℝ) :
    integratedTriangle a b (L*(x-y)) = L*(∫ r in a..b, triangle (r/L) x y) := by
  unfold integratedTriangle
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  have he : r - |L*(x-y)| = L*(r/L-|x-y|) := by
    rw [abs_mul, abs_of_pos hL]
    field_simp
  change max (r - |L*(x-y)|) 0 = L * max (r/L - |x-y|) 0
  rw [he]
  rcases le_total (r/L-|x-y|) 0 with hh | hh
  · rw [max_eq_right hh, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hL.le hh), mul_zero]
  · rw [max_eq_left hh, max_eq_left (mul_nonneg hL.le hh)]

/-- The local third moment bounds the expected deletion loss by the square root
of the mean window vacancy. Finite copy diagonal terms carry zero deletion weight. -/
theorem eventually_triangleBudget_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (q : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h3 : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ, (actualWindowCount T (b / (Real.log T / (2 * Real.pi))) t)^3) / T ≤ C) :
    ∀ᶠ T : ℝ in atTop, triangleVacancyBudget q T a b ≤
      2 * (b-a) * Real.sqrt (C * meanWindowVacancy q T b) := by
  classical
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_supported_width b, h3] with T ht hfloor hthird
  let L := Real.log T / (2*Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos ht) (by positivity)
  have hT := zero_lt_one.trans ht
  let x := copyOrdinate T
  let v := labelVacancy q T
  let h := b/L
  have hs := hfloor b (ha.trans hab) le_rfl
  have hx (i : Copies T) : h ≤ x i ∧ x i ≤ T := ⟨hs.2 i, (mem_cutoff.mp i.1.2).2.2⟩
  have hv (i : Copies T) : 0 ≤ v i ∧ v i ≤ 1 := by
    have hb := (limitingLaw_isDPP q).diagonal_bounds (liftCopy T i)
    change 0 ≤ 1 - _ ∧ 1 - _ ≤ 1
    constructor <;> linarith [hb.1, hb.2]
  let o := fun (i j : Copies T) => if i = j then 0 else v i + v j
  have ho (i j : Copies T) : 0 ≤ o i j ∧ o i j ≤ v i + v j := by
    dsimp [o]; split_ifs <;> simp [add_nonneg (hv i).1 (hv j).1]
  let A := ∑ i, ∑ j, (∫ r in a..b, triangle (r/L) (x i) (x j)) * o i j
  have he : triangleVacancyBudget q T a b = A/T := by
    have hden : normalizer T = T * L := by dsimp [normalizer,L]; ring
    unfold triangleVacancyBudget offDiagonalTriangle
    rw [hden]
    have heq : (∑ i : Copies T, ∑ j : Copies T, if i = j then 0 else
        integratedTriangle a b (L*(x i-x j)) * (v i+v j)) = L * A := by
      dsimp only [A]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [rescale_weight hL]; dsimp only [o]; split_ifs <;> ring
    change _ / (T*L) = A/T
    rw [heq]; field_simp
  let J := ∫ t : ℝ, (windowCount Finset.univ x T h t)^3
  let V := ∑ i, v i
  have hJ : 0 ≤ J := by
    apply integral_nonneg; intro t
    apply pow_nonneg; apply Finset.sum_nonneg; intro i _
    unfold windowPulse pulse Set.indicator; split_ifs <;> norm_num
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => (hv i).1
  have hJV : 0 ≤ J*(h*V) := mul_nonneg hJ (mul_nonneg hs.1 hV)
  have hmean : meanWindowVacancy q T b = h*V/T := by
    unfold meanWindowVacancy
    rw [integral_windowVacancy _ _ _ hs.1 (fun i => (hx i).1)]
    change V*h/T = h*V/T
    ring
  have hroot : Real.sqrt (J*(h*V))/T = Real.sqrt ((J/T)*(h*V/T)) := by
    rw [show (J/T)*(h*V/T) = (J*(h*V))/T^2 by ring,
      Real.sqrt_div hJV, Real.sqrt_sq hT.le]
  have hle : A ≤ 2*(b-a)*Real.sqrt (J*(h*V)) :=
    interval_pair_loss_le v x ha hab hL hx hv o ho (window_cube_integrable x T h)
  rw [he,hmean]
  calc
    A/T ≤ (2*(b-a)*Real.sqrt (J*(h*V)))/T := div_le_div_of_nonneg_right hle hT.le
    _ = 2*(b-a)*Real.sqrt ((J/T)*(h*V/T)) := by rw [mul_div_assoc, hroot]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right hthird (div_nonneg (mul_nonneg hs.1 hV) hT.le)))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))

/-- Conditional on the published third-moment input, one positive interval detects
exactly density one of simple critical zeros for the logarithmic kernel. -/
theorem logarithmic_triangleLoss_tendsto_zero_iff {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (h3 : BoundedTranslatedThirdMoment b) :
    Tendsto (fun T : ℝ => triangleLoss (fun k => Real.log ((k:ℝ)+1)) T a b) atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  let q := fun k : ℕ => Real.log ((k:ℝ)+1)
  constructor
  · intro h; exact (density_one_of_triangleLoss q ha hab h).1
  · intro hd
    obtain ⟨C,hC,hb⟩ := h3
    have hv := (logarithmic_meanWindowVacancy_iff_simpleCritical_density (ha.trans hab)).2 hd
    have hc := hv.const_mul C
    rw [mul_zero] at hc
    have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hc
    have hu : Tendsto (fun T : ℝ => 2*(b-a)*Real.sqrt (C*meanWindowVacancy q T b)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hroot.const_mul (2*(b-a))
    apply (triangleLoss_tendsto_zero_iff_budget q hab.le).2
    refine squeeze_zero_norm' ?_ hu
    filter_upwards [eventually_gt_atTop (1:ℝ), eventually_triangleBudget_le ha.le hab.le q hC hb]
      with T ht hbound
    obtain ⟨hl,h2⟩ := triangleLoss_budget_sandwich q ht hab.le
    have hp : 0 ≤ triangleVacancyBudget q T a b := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hbound

theorem prime_triangleLoss_tendsto_zero_iff {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (h3 : BoundedTranslatedThirdMoment b) :
    Tendsto (fun T : ℝ => triangleLoss primeFrequencies T a b) atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  have he (T : ℝ) : triangleLoss primeFrequencies T a b =
      triangleLoss (fun k => Real.log ((k:ℝ)+1)) T a b := by
    simp only [triangleLoss, keptPair, primeFrequencies_limitingLaw]
  simpa only [he] using logarithmic_triangleLoss_tendsto_zero_iff ha hab h3

end RiemannResearch.Analysis.ZeroDPPVacancyDensity
