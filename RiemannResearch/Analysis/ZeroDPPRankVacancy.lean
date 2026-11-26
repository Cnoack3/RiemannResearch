import RiemannResearch.Analysis.ZeroDPPVacancyDensity
import Mathlib.Algebra.Order.Floor.Ring

/-! Expected DPP deletion loss from a uniformly exponential translated count tail.
The window split is deterministic and uses the marginal vacancy of each label.
See the index-truncation section of RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md. -/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZeroDPPRankVacancy
open OrdinateWindowVariance ZeroDPPTriangleVacancy
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open ZeroDPPCorrelation ZeroDPPCollisionLoss
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

def truncatedWindowSecondMoment (T b : ℝ) (J : ℕ) : ℝ :=
  let K := actualWindowCount T (b / (Real.log T / (2 * Real.pi)))
  (∫ t : ℝ, if (J : ℝ) < K t then (K t)^2 else 0) / T

/-- The height threshold is uniform in the rank cutoff. -/
def ExpTranslatedSquareTail (b : ℝ) : Prop :=
  ∃ A c : ℝ, 0 ≤ A ∧ 0 < c ∧ ∀ᶠ T : ℝ in atTop, ∀ J : ℕ,
    truncatedWindowSecondMoment T b J ≤ A * Real.exp (-c * (J : ℝ))

/-- At most J predecessors and J successors lie within index distance J. -/
theorem smallRankDegree_le (N i J : ℕ) :
    ((Finset.range N).filter (fun j =>
      (j < i ∧ i ≤ j+J) ∨ (i < j ∧ j ≤ i+J))).card ≤ 2*J := by
  classical
  have hs : (Finset.range N).filter (fun j =>
      (j < i ∧ i ≤ j+J) ∨ (i < j ∧ j ≤ i+J)) ⊆
      Finset.Ico (i-J) i ∪ Finset.Ioc i (i+J) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
    rcases hj.2 with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨by omega, h1⟩
    · exact Or.inr ⟨h1,h2⟩
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2*J := by rw [Nat.card_Ico, Nat.card_Ioc]; omega

theorem truncatedSquare_integrable {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (T h : ℝ) (J : ℕ) :
    Integrable (fun t => if (J : ℝ) < windowCount Finset.univ x T h t
      then (windowCount Finset.univ x T h t)^2 else 0) := by
  classical
  let K := windowCount Finset.univ x T h
  have hm : Measurable K := by
    unfold K windowCount
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.indicator measurableSet_Ioc
  exact (windowCount_sq_integrable Finset.univ x T h).indicator
    (measurableSet_lt measurable_const hm)

private theorem integrated_le {a b L : ℝ} (hab : a ≤ b) (hL : 0 < L) (x y : ℝ) :
    integratedTriangle a b (L*(x-y)) ≤ (b-a)*L*triangle (b/L) x y := by
  have h := intervalIntegral.integral_mono_on (μ := volume) hab
    (f := fun r : ℝ => max (r - |L*(x-y)|) 0)
    (g := fun _ : ℝ => max (b - |L*(x-y)|) 0)
    ((by fun_prop : Continuous (fun r : ℝ => max (r - |L*(x-y)|) 0)).intervalIntegrable a b)
    intervalIntegrable_const
    (fun r hr => max_le_max_right 0 (sub_le_sub_right hr.2 _))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  refine h.trans_eq ?_
  rw [abs_mul, abs_of_pos hL, triangle]
  have he : b - L*|x-y| = L*(b/L - |x-y|) := by field_simp [hL.ne']
  rw [he, mul_assoc]
  by_cases hp : 0 ≤ b/L - |x-y|
  · rw [max_eq_left hp, max_eq_left (mul_nonneg hL.le hp)]
  · rw [max_eq_right (le_of_not_ge hp), max_eq_right
      (mul_nonpos_of_nonneg_of_nonpos hL.le (le_of_not_ge hp))]
    simp

/-- Split the sum of triangle weights at a translated count cutoff. Tied but distinct
labels are included. The first term charges marginal vacancies and the second
charges the full local count on windows above the cutoff. -/
theorem eventually_triangleBudget_split (freq : ℕ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᶠ T : ℝ in atTop, ∀ J : ℕ, triangleVacancyBudget freq T a b ≤
      2*(b-a)*((J:ℝ)*meanWindowVacancy freq T b + truncatedWindowSecondMoment T b J) := by
  classical
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_supported_width b] with T ht hf J
  let L := Real.log T / (2*Real.pi)
  let h := b/L
  let x := copyOrdinate T
  let v := labelVacancy freq T
  let K := windowCount Finset.univ x T h
  let W := weightedWindow v x T h
  let E := fun t : ℝ => if (J:ℝ) < K t then (K t)^2 else 0
  let w := fun (i j : Copies T) => triangle h (x i) (x j)
  let B := (b-a)*L
  have hT := zero_lt_one.trans ht
  have hL : 0 < L := div_pos (Real.log_pos ht) (by positivity)
  have hB : 0 ≤ B := mul_nonneg (sub_nonneg.mpr hab) hL.le
  have hden : normalizer T = T*L := by dsimp [normalizer,L]; ring
  have hx (i : Copies T) : h ≤ x i ∧ x i ≤ T :=
    ⟨(hf b (ha.trans hab) le_rfl).2 i, (mem_cutoff.mp i.1.2).2.2⟩
  have hv (i : Copies T) : 0 ≤ v i ∧ v i ≤ 1 := by
    have hdiag := (limitingLaw_isDPP freq).diagonal_bounds (liftCopy T i)
    change 0 ≤ 1 - _ ∧ 1 - _ ≤ 1
    constructor <;> linarith [hdiag.1,hdiag.2]
  have hp (i : Copies T) (t : ℝ) : 0 ≤ windowPulse T h (x i) t := by
    unfold windowPulse pulse Set.indicator
    split_ifs <;> norm_num
  have hW (t : ℝ) : 0 ≤ W t := Finset.sum_nonneg fun i _ => mul_nonneg (hv i).1 (hp i t)
  have hWK (t : ℝ) : W t ≤ K t := Finset.sum_le_sum fun i _ =>
    mul_le_of_le_one_left (hp i t) (hv i).2
  have hWi : Integrable W := integrable_finsetSum _ fun i _ =>
    (windowPulse_integrable T h (x i)).const_mul (v i)
  have hKWi : Integrable (fun t => K t * W t) := by
    have hi := windowCount_integrable Finset.univ x T h
    refine (windowCount_sq_integrable Finset.univ x T h).mono'
      (hi.aestronglyMeasurable.mul hWi.aestronglyMeasurable) (ae_of_all _ fun t => ?_)
    have hk := (hW t).trans (hWK t)
    change ‖K t * W t‖ ≤ (K t)^2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (hW t)), sq]
    exact mul_le_mul_of_nonneg_left (hWK t) hk
  have hEi : Integrable E := truncatedSquare_integrable x T h J
  have hcut : (∫ t, K t * W t) ≤ (J:ℝ)*(∫ t, W t) + ∫ t, E t := by
    have hcut := PairVacancyMoment.integral_pair_error_le_square_tail volume
      (fun t => K t * W t) K W (1/2) J (by norm_num) (Nat.cast_nonneg J)
      hKWi hWi hEi hW hWK (fun t => by
        rw [abs_of_nonneg (mul_nonneg ((hW t).trans (hWK t)) (hW t))]
        norm_num)
    exact (le_abs_self _).trans (by simpa only [show 2*(1/2:ℝ) = 1 by norm_num,
      one_mul] using hcut)
  have hsw : (∑ i, ∑ j, v i * w i j) = ∑ i, ∑ j, v j * w i j := by
    rw [Finset.sum_comm]
    simp only [w, triangle, abs_sub_comm]
  have hsum :
      (∑ i : Copies T, ∑ j : Copies T, if i = j then 0 else
        integratedTriangle a b (L*(x i-x j))*(v i+v j)) ≤
      2*B*(∫ t, K t * W t) := by
    rw [show (∫ t, K t * W t) = ∑ i, ∑ j, v j * w i j from
      integral_count_mul_weightedWindow v x hx]
    calc
      _ ≤ ∑ i, ∑ j, B * (v i * w i j + v j * w i j) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have hw : 0 ≤ w i j := le_max_right _ _
        split_ifs with hij
        · exact mul_nonneg hB (add_nonneg (mul_nonneg (hv i).1 hw) (mul_nonneg (hv j).1 hw))
        · exact (mul_le_mul_of_nonneg_right (integrated_le hab hL (x i) (x j))
            (add_nonneg (hv i).1 (hv j).1)).trans_eq (by dsimp [B,w,h]; ring)
      _ = _ := by simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, hsw]; ring
  have hh := hsum.trans (mul_le_mul_of_nonneg_left hcut (mul_nonneg (by norm_num) hB))
  unfold triangleVacancyBudget offDiagonalTriangle
  rw [hden]
  change _ / (T*L) ≤ 2*(b-a)*((J:ℝ)*((∫ t, W t)/T) + (∫ t, E t)/T)
  apply (div_le_iff₀ (mul_pos hT hL)).2
  exact hh.trans_eq (by dsimp [B]; field_simp [hT.ne', hL.ne'])

/-- Exponential tails imply the improved vacancy rate for any projection law.
The zero-vacancy case is included. -/
theorem eventually_triangleLoss_logVacancy (freq : ℕ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (he : ExpTranslatedSquareTail b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      let d := cutoffVacancy freq T / normalizer T
      0 ≤ d → d ≤ 1 → triangleLoss freq T a b ≤ C*d*(1-Real.log d) := by
  obtain ⟨A,c,hA,hc,hTail⟩ := he
  have hb := ha.trans hab
  let C := 2*(b-a)*(b + b/c + A)
  refine ⟨C, mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))
    (add_nonneg (add_nonneg hb (div_nonneg hb hc.le)) hA), ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_supported_width b, hTail,
    eventually_triangleBudget_split freq ha hab] with T ht hf htTail hs
  let d := cutoffVacancy freq T / normalizer T
  change 0 ≤ d → d ≤ 1 → triangleLoss freq T a b ≤ C*d*(1-Real.log d)
  intro hd hu
  have hT := zero_lt_one.trans ht
  let L := Real.log T / (2*Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos ht) (by positivity)
  have hmean : meanWindowVacancy freq T b = b*d := by
    rw [meanWindowVacancy, integral_windowVacancy freq T _ (div_nonneg hb hL.le)
      ((hf b hb le_rfl).2)]
    have hn : normalizer T = T*L := by dsimp [normalizer,L]; ring
    dsimp only [d]; rw [hn]
    change _*(b/L)/T = b*(_/(T*L))
    field_simp [hL.ne', hT.ne'] <;> ring
  have hbnd (J : ℕ) : triangleLoss freq T a b ≤
      2*(b-a)*((J:ℝ)*(b*d)+A*Real.exp (-c*(J:ℝ))) := by
    have hbudget := (triangleLoss_budget_sandwich freq ht hab).1.trans (hs J)
    rw [hmean] at hbudget
    exact hbudget.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (htTail J))
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hab)))
  rcases hd.eq_or_lt with hz|hdp
  · have hlim := Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hc)).2
          (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hlim' : Tendsto (fun n : ℕ => 2*(b-a)*(A*Real.exp (-c*(n:ℝ)))) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (hlim.const_mul A).const_mul (2*(b-a))
    have hzero := ge_of_tendsto hlim' (Eventually.of_forall fun J => by
      simpa [← hz] using hbnd J)
    simpa [← hz] using hzero
  · have hlog : 0 ≤ -Real.log d := neg_nonneg.mpr (Real.log_nonpos hdp.le hu)
    let u := -Real.log d / c
    have hu0 : 0 ≤ u := div_nonneg hlog hc.le
    let J := ⌊u⌋₊ + 1
    have hju : u ≤ (J:ℝ) := by simpa [J] using (Nat.lt_floor_add_one u).le
    have hj1 : (J:ℝ) ≤ u+1 := by
      simp only [J, Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.floor_le hu0) le_rfl
    have hexp : Real.exp (-c*(J:ℝ)) ≤ d := by
      rw [← Real.exp_log hdp]
      apply Real.exp_le_exp.mpr
      have h := (div_le_iff₀ hc).mp hju
      linarith only [h]
    calc
      triangleLoss freq T a b ≤ _ := hbnd J
      _ ≤ 2*(b-a)*((u+1)*(b*d)+A*d) := by
        gcongr
      _ ≤ C*d*(1-Real.log d) := by
        have heq : C*d*(1-Real.log d) - 2*(b-a)*((u+1)*(b*d)+A*d) =
            2*(b-a)*d*(b/c+(b+A)*(-Real.log d)) := by dsimp [u,C]; ring
        apply sub_nonneg.mp
        rw [heq]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hab)) hd)
          (add_nonneg (div_nonneg hb hc.le) (mul_nonneg (add_nonneg hb hA) hlog))

end RiemannResearch.Analysis.ZeroDPPRankVacancy
