import RiemannResearch.Analysis.ZeroDPPProjectionBridge

/-! Direct dilation of nonnegative omitted-pair mass. A sparse upper estimate
for the full triangle moment at large widths removes the omission hypothesis
from the conditional prime-projection PCC criterion. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZeroDPPDilation
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryPositiveGap
open ZeroDPPCollisionLoss ZeroDPPProjectionBridge ProjectedDistinctSpacing
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

theorem integratedTriangle_dilate_le {a b s : ℝ} (hab : a ≤ b) (hs : 1 ≤ s) (u : ℝ) :
    s^2 * integratedTriangle a b u ≤ integratedTriangle (s*a) (s*b) u := by
  let f := fun r : ℝ => max (r-|u|) 0
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hscale (r : ℝ) : s*f r ≤ f (s*r) := by
    rcases le_total (r-|u|) 0 with hu | hu
    · simpa [f,max_eq_right hu] using (le_max_right (s*r-|u|) 0)
    · calc
        s*f r = s*(r-|u|) := by simp [f,max_eq_left hu]
        _ ≤ s*r-|u| := by nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg u)]
        _ ≤ f (s*r) := le_max_left _ _
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (f := fun r => s*f r) (g := fun r => f (s*r))
    ((continuous_const.mul hc).intervalIntegrable _ _)
    ((hc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    (fun r _ => hscale r)
  rw [intervalIntegral.integral_const_mul] at hm
  change s^2*(∫ r in a..b, f r) ≤ ∫ r in s*a..s*b, f r
  have e := intervalIntegral.smul_integral_comp_mul_left (a := a) (b := b) f s
  rw [smul_eq_mul] at e
  rw [← e, pow_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left hm (zero_le_one.trans hs)

private theorem omit_nonneg (q : ℕ → ℝ) (T : ℝ) (i j : Copies T) :
    0 ≤ 1-keptPair q T i j := by
  apply sub_nonneg.mpr
  calc
    _ ≤ (limitingLaw q).real univ :=
      measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := by simp

private theorem denom_nonneg {T : ℝ} (hT : 1 < T) : 0 ≤ normalizer T := by
  have ht := zero_lt_one.trans hT
  have hl := Real.log_pos hT
  unfold normalizer
  positivity

theorem triangleLoss_nonnegative (q : ℕ → ℝ) {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b) :
    0 ≤ triangleLoss q T a b := by
  classical
  apply div_nonneg _ (denom_nonneg hT)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (intervalIntegral.integral_nonneg hab (fun r _ => le_max_right _ _))
      (omit_nonneg q T i j)

/-- The probability of losing a pair is unchanged as the width varies.
The same statement holds for coincident occurrences carrying weight at zero. -/
theorem triangleLoss_dilate_le (q : ℕ → ℝ) {T a b s : ℝ}
    (hT : 1 < T) (hab : a ≤ b) (hs : 1 ≤ s) :
    s^2 * triangleLoss q T a b ≤ triangleLoss q T (s*a) (s*b) := by
  classical
  unfold triangleLoss
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (denom_nonneg hT)
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · simp
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (integratedTriangle_dilate_le hab hs _)
      (omit_nonneg q T i j)

/-- Quantifier order: choose a dilation for each tolerance and interval,
then go to large heights at that fixed dilation. -/
def SparseDilatedUpper : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → ∀ η : ℝ, 0 < η → ∃ n : ℕ, 1 ≤ n ∧
    ∀ᶠ T : ℝ in atTop,
      (∫ r in (n:ℝ)*(a:ℝ)..(n:ℝ)*(b:ℝ), unfoldedWindowEnergy T r) ≤
      (∫ r in (n:ℝ)*(a:ℝ)..(n:ℝ)*(b:ℝ), sineWindowEnergy r) + η*(n:ℝ)^2

/-- A one-sided error that is sublinear as the width grows. For any fixed
compact interval above the chosen width threshold, the height threshold
can depend on the whole interval. -/
def SublinearWidthUpper : Prop :=
  ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ c d : ℝ, R ≤ c → c ≤ d →
    ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc c d,
      unfoldedWindowEnergy T r ≤ sineWindowEnergy r + η*r

theorem sparseDilatedUpper_of_sublinearWidthUpper
    (h : SublinearWidthUpper) : SparseDilatedUpper := by
  intro a b ha hab η hη
  have ha' : 0 < (a:ℝ) := by exact_mod_cast ha
  have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
  have hb' := ha'.trans hab'
  let z := η/((b:ℝ)*((b:ℝ)-(a:ℝ)))
  have hz : 0 < z := div_pos hη (mul_pos hb' (sub_pos.mpr hab'))
  obtain ⟨R,hR⟩ := h z hz
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (R/(a:ℝ)))
  have hnr : 1 ≤ (n:ℝ) := ((le_max_left _ _).trans_lt hn).le
  have hnpos : 0 < (n:ℝ) := zero_lt_one.trans_le hnr
  have hstart : R ≤ (n:ℝ)*(a:ℝ) :=
    ((div_lt_iff₀ ha').1 ((le_max_right _ _).trans_lt hn)).le
  have hend := mul_le_mul_of_nonneg_left hab'.le hnpos.le
  refine ⟨n, by exact_mod_cast hnr, ?_⟩
  filter_upwards [hR _ _ hstart hend,eventually_gt_atTop (1:ℝ)] with T ht hT
  have hm := intervalIntegral.integral_mono_on (μ := volume) hend
    (f := unfoldedWindowEnergy T) (g := fun r => sineWindowEnergy r + z*((n:ℝ)*(b:ℝ)))
    (unfoldedWindowEnergy_mono T hT).intervalIntegrable
    ((continuous_sineWindowEnergy.add continuous_const).intervalIntegrable _ _)
    (fun r hr => (ht r hr).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr.2 hz.le)))
  rw [intervalIntegral.integral_add (continuous_sineWindowEnergy.intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at hm
  have he : ((n:ℝ)*(b:ℝ)-(n:ℝ)*(a:ℝ)) * (z*((n:ℝ)*(b:ℝ))) = η*(n:ℝ)^2 := by
    dsimp [z]
    field_simp [hb'.ne', (sub_pos.mpr hab').ne'] <;> ring
  simpa only [he] using hm

theorem triangleLoss_tendsto_of_projected_dilation (hu : SparseDilatedUpper)
    (hp : PrimeProjectedSineLimit) (a b : ℚ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun T : ℝ => triangleLoss primeFrequencies T a b) atTop (𝓝 0) := by
  have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab.le
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n,hn,hupper⟩ := hu a b ha hab (ε/2) (by positivity)
  have hnr : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hnr' : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hnr
  have hnq : 0 < (n:ℚ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let S := ∫ r in (n:ℝ)*(a:ℝ)..(n:ℝ)*(b:ℝ), sineWindowEnergy r
  have hmodel : Tendsto (fun T : ℝ => restoredPrimeMoment T ((n:ℝ)*(a:ℝ)) ((n:ℝ)*(b:ℝ)))
      atTop (𝓝 S) := by
    simpa [S] using hp ((n:ℚ)*a) ((n:ℚ)*b) (mul_pos hnq ha) (mul_lt_mul_of_pos_left hab hnq)
  have hmargin : 0 < (ε/2)*(n:ℝ)^2 := by positivity
  have hlo := hmodel.eventually (lt_mem_nhds (show S-(ε/2)*(n:ℝ)^2 < S by linarith))
  filter_upwards [hupper,hlo,eventually_gt_atTop (1:ℝ)] with T hU hP hT
  change S-(ε/2)*(n:ℝ)^2 < restoredPrimeMoment T _ _ at hP
  have hscaled := triangleLoss_dilate_le primeFrequencies hT hab' hnr
  rw [actual_integral_eq_restored_add_loss hT (mul_le_mul_of_nonneg_left hab' hnr'.le)] at hU
  change restoredPrimeMoment T _ _ + triangleLoss primeFrequencies T _ _ ≤ S+(ε/2)*(n:ℝ)^2 at hU
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (triangleLoss_nonnegative _ hT hab')]
  apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hnr')).1
  nlinarith only [hscaled,hU,hP]

/-- With the sparse full-energy upper bound, only the projected sine limit
remains as a spacing input. The vanishing omitted-pair loss is deduced. -/
theorem positiveGapPCC_of_projected_dilation (hu : SparseDilatedUpper)
    (hp : PrimeProjectedSineLimit) : PositiveGapPCC :=
  positiveGapPCC_of_prime_loss_and_restored (triangleLoss_tendsto_of_projected_dilation hu hp) hp

theorem positiveGapPCC_of_projected_sublinearUpper (hu : SublinearWidthUpper)
    (hp : PrimeProjectedSineLimit) : PositiveGapPCC :=
  positiveGapPCC_of_projected_dilation (sparseDilatedUpper_of_sublinearWidthUpper hu) hp

/--
info: 'RiemannResearch.Analysis.ZeroDPPDilation.positiveGapPCC_of_projected_dilation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_of_projected_dilation

/--
info: 'RiemannResearch.Analysis.ZeroDPPDilation.positiveGapPCC_of_projected_sublinearUpper'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_of_projected_sublinearUpper

end RiemannResearch.Analysis.ZeroDPPDilation
