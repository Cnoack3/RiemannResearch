import RiemannResearch.Analysis.ZeroDPPRankVacancy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Group.Measure

/-!
# From count exceedances to the truncated second moment

The analytic inputs are fixed-width count estimates at random starting heights.
The fourth moment follows on paper from Arias de Reyna and Rodgers, Corollary 35
(arXiv:2311.13441), by summing dyadic blocks. For the unconditional exponential
count tail see Rodgers, §2.2 (arXiv:1502.05658), and Simonič, Trudgian and
Turnage-Butterbaugh, Lemma 8 (arXiv:2010.10675). The cutoff and fixed-width
transfers of these published estimates are analytic hypotheses in this file.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis.MicroscopicCountTail

open ActualZeroOrdinate ActualZeroWindowVariance OrdinateWindowVariance ZeroDPPRankVacancy

/-- The fourth moment of the translated count at a fixed unfolded width. -/
def BoundedTranslatedFourthMoment (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
    (∫ t : ℝ, (actualWindowCount T (b / (Real.log T / (2 * Real.pi))) t)^4) / T ≤ C

/-- The normalized measure of the exceedance set. The single height threshold
works simultaneously for all integer count thresholds. -/
def ExpTranslatedCountTail (b : ℝ) : Prop :=
  ∃ A c : ℝ, 0 ≤ A ∧ 0 < c ∧ ∀ᶠ T : ℝ in atTop, ∀ J : ℕ,
    volume.real {t : ℝ | (J : ℝ) < actualWindowCount T
      (b / (Real.log T / (2 * Real.pi))) t} / T ≤ A * Real.exp (-c * (J : ℝ))

private theorem actual_count_measurable (T h : ℝ) : Measurable (actualWindowCount T h) := by
  unfold actualWindowCount windowCount
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator measurableSet_Ioc

private theorem actual_fourth_integrable (T h : ℝ) :
    Integrable (fun t : ℝ => (actualWindowCount T h t)^4) := by
  let K := actualWindowCount T h
  let B : ℝ := Fintype.card (Copies T)
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hb (t : ℝ) : 0 ≤ K t ∧ K t ≤ B := by
    have hp (i : Copies T) :
        0 ≤ windowPulse T h i.1.1.im t ∧ windowPulse T h i.1.1.im t ≤ 1 := by
      unfold windowPulse pulse Set.indicator
      split_ifs <;> norm_num
    refine ⟨Finset.sum_nonneg fun i _ => (hp i).1, ?_⟩
    exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hp i).2)).trans_eq (by simp [B])
  have hi : Integrable (fun t : ℝ => (K t)^2) := windowCount_sq_integrable _ _ _ _
  refine (hi.const_mul (B^2)).mono' ((actual_count_measurable T h).pow_const 4).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  change ‖K t ^ 4‖ ≤ B^2 * (K t)^2
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb t).1 _),
    show (K t)^4 = (K t)^2 * (K t)^2 by ring]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr (hb t).2) (add_nonneg hB (hb t).1)]

private theorem count_exceedance_ne_top (T h : ℝ) (J : ℕ) :
    volume {t : ℝ | (J:ℝ) < actualWindowCount T h t} ≠ ⊤ := by
  let K := actualWindowCount T h
  let S := {t : ℝ | (J:ℝ) < K t}
  have hsub : S ⊆ Ioc 0 T := by
    intro t ht
    by_contra hnot
    have hs := windowCount_mul_support (Finset.univ : Finset (Copies T))
      (fun i => i.1.1.im) T h t
    change K t * pulse 0 T t = K t at hs
    simp [pulse, Set.indicator_of_notMem hnot] at hs
    change (J : ℝ) < K t at ht
    linarith [Nat.cast_nonneg (α := ℝ) J]
  exact ne_of_lt ((measure_mono hsub).trans_lt (by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top))

/-- Weighted Young's inequality on the exceedance set. The normalized
Cauchy-Schwarz estimate follows by optimizing the positive parameter. -/
private theorem weighted_tail_le {T h : ℝ} (J : ℕ) (E : ℝ) :
    (2*E) * (∫ t : ℝ, if (J : ℝ) < actualWindowCount T h t then
        (actualWindowCount T h t)^2 else 0) ≤
    E^2 * (∫ t : ℝ, (actualWindowCount T h t)^4) +
      volume.real {t : ℝ | (J : ℝ) < actualWindowCount T h t} := by
  let K := actualWindowCount T h
  let S := {t : ℝ | (J : ℝ) < K t}
  have hm : MeasurableSet S := measurableSet_lt measurable_const (actual_count_measurable T h)
  have hvol : volume S ≠ ⊤ := count_exceedance_ne_top T h J
  have hi : Integrable (S.indicator (fun _ : ℝ => (1 : ℝ))) :=
    (integrable_indicator_iff hm).2 (integrableOn_const hvol)
  have hsq : Integrable (fun t : ℝ => (K t)^2) := windowCount_sq_integrable _ _ _ _
  have ht := hsq.indicator hm
  have hf := actual_fourth_integrable T h
  have H := integral_mono (ht.const_mul (2*E)) ((hf.const_mul (E^2)).add hi) (fun t => by
    change (2*E) * S.indicator (fun u => (K u)^2) t ≤
      E^2 * (K t)^4 + S.indicator (fun _ => (1 : ℝ)) t
    by_cases hs : t ∈ S
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      nlinarith [sq_nonneg (E * (K t)^2 - 1)]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
      simp only [mul_zero, add_zero]
      exact mul_nonneg (sq_nonneg _) (by positivity))
  change (∫ t : ℝ, (2*E) * S.indicator (fun u => (K u)^2) t) ≤
    ∫ t : ℝ, E^2 * (actualWindowCount T h t)^4 + S.indicator (fun _ => (1 : ℝ)) t at H
  rw [integral_const_mul, integral_add (hf.const_mul (E^2)) hi, integral_const_mul,
    integral_indicator_const (1 : ℝ) hm, smul_eq_mul, mul_one] at H
  simpa only [S, Set.indicator, Set.mem_setOf_eq, K] using H

/-- A raw exponential count tail and a bounded fourth moment imply the
exponential truncated-square bound, with half the original exponent. -/
theorem expTranslatedSquareTail_of_countTail {b : ℝ}
    (hfour : BoundedTranslatedFourthMoment b) (hexp : ExpTranslatedCountTail b) :
    ExpTranslatedSquareTail b := by
  obtain ⟨C, hC, h4⟩ := hfour
  obtain ⟨A, c, hA, hc, hp⟩ := hexp
  refine ⟨(C+A)/2, c/2, by positivity, by positivity, ?_⟩
  filter_upwards [h4, hp, eventually_gt_atTop (0 : ℝ)] with T h4T hpT hT
  intro J
  let h := b / (Real.log T / (2*Real.pi))
  let K := actualWindowCount T h
  let E := Real.exp (-(c/2) * (J : ℝ))
  have hE : 0 < E := Real.exp_pos _
  have heq : Real.exp (-c*(J : ℝ)) = E^2 := by
    dsimp [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hthin := hpT J
  rw [heq] at hthin
  have hmom := mul_le_mul_of_nonneg_left h4T (sq_nonneg E)
  have H := div_le_div_of_nonneg_right (weighted_tail_le (T := T) (h := h) J E) hT.le
  let V := truncatedWindowSecondMoment T b J
  change (2*E) * (∫ t : ℝ, if (J:ℝ) < K t then (K t)^2 else 0) / T ≤
    (E^2*(∫ t : ℝ, (K t)^4) + volume.real {t : ℝ | (J:ℝ) < K t}) / T at H
  rw [add_div, mul_div_assoc, mul_div_assoc] at H
  change 2*E*V ≤ E^2*((∫ t : ℝ, (K t)^4)/T) +
    volume.real {t : ℝ | (J:ℝ) < K t}/T at H
  have bound := H.trans (add_le_add hmom hthin)
  change V ≤ ((C+A)/2)*E
  apply (mul_le_mul_iff_right₀ (show 0 < 2*E by positivity)).mp
  nlinarith only [bound]

/-- Charge each count to its last nonempty integer level. This also holds for
real, nonnegative counts bounded by N. -/
private theorem fourth_le_levels (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hb : x ≤ N) :
    x^4 ≤ ∑ j ∈ Finset.range N, if (j:ℝ) < x then ((j:ℝ)+1)^4 else 0 := by
  induction N with
  | zero =>
    have hzero : x = 0 := le_antisymm (by simpa using hb) hx
    simp [hzero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : (n:ℝ) < x
    · rw [if_pos hn]
      have hsum : 0 ≤ ∑ j ∈ Finset.range n,
          if (j:ℝ) < x then ((j:ℝ)+1)^4 else 0 :=
        Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
      have hp := pow_le_pow_left₀ hx (show x ≤ (n:ℝ)+1 by simpa using hb) 4
      linarith only [hp, hsum]
    · simpa [hn] using ih (le_of_not_gt hn)

/-- Uniform exponential count exceedances supply the fourth translated moment.
The finite sum over levels is bounded by a convergent polynomial times
geometric series, independently of the number of occurrences through T. -/
theorem boundedTranslatedFourthMoment_of_countTail {b : ℝ} (hexp : ExpTranslatedCountTail b) :
    BoundedTranslatedFourthMoment b := by
  classical
  obtain ⟨A,c,hA,hc,hTail⟩ := hexp
  let f : ℕ → ℝ := fun j => ((j:ℝ)+1)^4 * (A*Real.exp (-c*(j:ℝ)))
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul 4 hc
  have hshift := (summable_nat_add_iff 1).mpr hbase
  have hfs : Summable f := by
    refine (hshift.mul_left (A * Real.exp c)).congr (fun n => ?_)
    dsimp [f]
    simp only [Nat.cast_add, Nat.cast_one]
    have he : Real.exp c * Real.exp (-c*((n:ℝ)+1)) = Real.exp (-c*(n:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = ((n:ℝ)+1)^4 * (A*(Real.exp c * Real.exp (-c*((n:ℝ)+1)))) := by ring
      _ = _ := by rw [he]
  have hf0 (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
  refine ⟨∑' j, f j, tsum_nonneg hf0, ?_⟩
  filter_upwards [hTail, eventually_gt_atTop (0:ℝ)] with T hbT hT
  let h := b / (Real.log T / (2*Real.pi))
  let K := actualWindowCount T h
  let N := Fintype.card (Copies T)
  let S := fun j : ℕ => {t : ℝ | (j:ℝ) < K t}
  let W := fun j : ℕ => (S j).indicator (fun _ : ℝ => ((j:ℝ)+1)^4)
  have hm (j : ℕ) : MeasurableSet (S j) :=
    measurableSet_lt measurable_const (actual_count_measurable T h)
  have hi (j : ℕ) : Integrable (W j) :=
    (integrable_indicator_iff (hm j)).2 (integrableOn_const (count_exceedance_ne_top T h j))
  have hk (t : ℝ) : 0 ≤ K t ∧ K t ≤ N := by
    have hp (i : Copies T) :
        0 ≤ windowPulse T h i.1.1.im t ∧ windowPulse T h i.1.1.im t ≤ 1 := by
      unfold windowPulse pulse Set.indicator
      split_ifs <;> norm_num
    refine ⟨Finset.sum_nonneg fun i _ => (hp i).1, ?_⟩
    exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hp i).2)).trans_eq (by simp [N])
  have H : (∫ t : ℝ, (K t)^4) ≤
      ∫ t : ℝ, ∑ j ∈ Finset.range N, W j t :=
    integral_mono (actual_fourth_integrable T h) (integrable_finsetSum _ (fun j _ => hi j))
      fun t => by simpa [W,S,Set.indicator] using fourth_le_levels N (K t) (hk t).1 (hk t).2
  rw [integral_finsetSum _ (fun j _ => hi j)] at H
  change (∫ t : ℝ, (K t)^4)/T ≤ _
  calc
    _ ≤ (∑ j ∈ Finset.range N, ∫ t : ℝ, W j t)/T := div_le_div_of_nonneg_right H hT.le
    _ = ∑ j ∈ Finset.range N, (∫ t : ℝ, W j t)/T := by rw [Finset.sum_div]
    _ ≤ ∑ j ∈ Finset.range N, f j := by
      apply Finset.sum_le_sum
      intro j _
      dsimp only [W]
      rw [integral_indicator_const _ (hm j), smul_eq_mul, mul_comm, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hbT j) (by positivity)
    _ ≤ _ := hfs.sum_le_tsum _ (fun j _ => hf0 j)

/-- A single uniform count exceedance estimate suffices for all rank cutoffs. -/
theorem expTranslatedSquareTail_of_exceedances {b : ℝ} (h : ExpTranslatedCountTail b) :
    ExpTranslatedSquareTail b :=
  expTranslatedSquareTail_of_countTail (boundedTranslatedFourthMoment_of_countTail h) h

/-- The clipped count is monotone in the physical width, at every origin. -/
theorem actualWindowCount_mono_width (T t : ℝ) {h k : ℝ} (hh : h ≤ k) :
    actualWindowCount T h t ≤ actualWindowCount T k t := by
  unfold actualWindowCount windowCount
  apply Finset.sum_le_sum
  intro i _
  let x := i.1.1.im
  change windowPulse T h x t ≤ windowPulse T k x t
  by_cases h₁ : t ∈ Ioc (max 0 (x-h)) (min T x)
  · have h₂ : t ∈ Ioc (max 0 (x-k)) (min T x) := by
      simp only [mem_Ioc, max_lt_iff, le_min_iff] at h₁ ⊢
      exact ⟨⟨h₁.1.1, by linarith only [hh, h₁.1.2]⟩, h₁.2⟩
    simp [windowPulse, pulse, Set.indicator, h₁, h₂]
  · unfold windowPulse pulse Set.indicator
    rw [if_neg h₁]
    split_ifs <;> norm_num

/-- Subdivision of the clipped window. Equal endpoints are assigned according
to the half-open pulse convention. Origins outside the observation window
are allowed on both sides of the inequality. -/
theorem actualWindowCount_double_le (T t : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    actualWindowCount T (h+h) t ≤ actualWindowCount T h t + actualWindowCount T h (t+h) := by
  unfold actualWindowCount windowCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  let x := i.1.1.im
  have hx : x ≤ T := (mem_cutoff.mp i.1.2).2.2
  have cover : t ∈ Ioc (max 0 (x-(h+h))) (min T x) →
      t ∈ Ioc (max 0 (x-h)) (min T x) ∨ t+h ∈ Ioc (max 0 (x-h)) (min T x) := by
    simp only [mem_Ioc, max_lt_iff, le_min_iff]
    rintro ⟨⟨ht,hu⟩, hT, hv⟩
    by_cases hp : x-h < t
    · exact Or.inl ⟨⟨ht, hp⟩, hT, hv⟩
    · exact Or.inr ⟨⟨by linarith only [ht,hh], by linarith only [hu]⟩,
        by linarith only [hx,le_of_not_gt hp], by linarith only [le_of_not_gt hp]⟩
  change windowPulse T (h+h) x t ≤ windowPulse T h x t + windowPulse T h x (t+h)
  unfold windowPulse pulse Set.indicator
  split_ifs <;> norm_num <;> tauto

theorem expTranslatedCountTail_mono {a b : ℝ} (hab : a ≤ b) (hb : ExpTranslatedCountTail b) :
    ExpTranslatedCountTail a := by
  obtain ⟨A,c,hA,hc,h⟩ := hb
  refine ⟨A,c,hA,hc,?_⟩
  filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with T hT ht
  intro J
  let L := Real.log T / (2*Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos ht) (by positivity)
  have hsub : {t : ℝ | (J : ℝ) < actualWindowCount T (a/L) t} ⊆
      {t : ℝ | (J : ℝ) < actualWindowCount T (b/L) t} := fun t hmem =>
    lt_of_lt_of_le hmem (actualWindowCount_mono_width T t (div_le_div_of_nonneg_right hab hL.le))
  exact (div_le_div_of_nonneg_right
    (measureReal_mono hsub (count_exceedance_ne_top T (b/L) J)) (zero_lt_one.trans ht).le).trans
    (hT J)

/-- Doubling the width of the translated count costs at most a factor two
in the exponential rate. All integer thresholds share one height cutoff. -/
theorem expTranslatedCountTail_double {b : ℝ} (hb : 0 ≤ b) (he : ExpTranslatedCountTail b) :
    ExpTranslatedCountTail (2*b) := by
  obtain ⟨A,c,hA,hc,htail⟩ := he
  refine ⟨2*A*Real.exp c,c/2,by positivity,by positivity,?_⟩
  filter_upwards [htail, eventually_gt_atTop (1 : ℝ)] with T hT ht
  intro J
  let h := b / (Real.log T / (2*Real.pi))
  let j := J/2
  let S := {t : ℝ | (j : ℝ) < actualWindowCount T h t}
  let U := {t : ℝ | (J : ℝ) < actualWindowCount T (h+h) t}
  let V := (fun t : ℝ => t+h) ⁻¹' S
  have hphys : 0 ≤ h := div_nonneg hb (div_nonneg (Real.log_pos ht).le (by positivity))
  have hjA : (2 : ℝ) * (j : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast (show 2*j ≤ J by dsimp [j]; omega)
  have hjB : (J : ℝ) ≤ 2*((j : ℝ)+1) := by
    exact_mod_cast (show J ≤ 2*(j+1) by dsimp [j]; omega)
  have hcover : U ⊆ S ∪ V := by
    intro t hmem
    rw [Set.mem_union]
    by_cases h₁ : t ∈ S
    · exact Or.inl h₁
    by_cases h₂ : t ∈ V
    · exact Or.inr h₂
    have hleft : actualWindowCount T h t ≤ (j : ℝ) := le_of_not_gt h₁
    have hright : actualWindowCount T h (t+h) ≤ (j : ℝ) := le_of_not_gt h₂
    change (J : ℝ) < actualWindowCount T (h+h) t at hmem
    exfalso
    linarith only [actualWindowCount_double_le T t hphys, hleft, hright, hmem, hjA]
  have hshift : volume V = volume S := measure_preimage_add_right volume h S
  have hS : volume S ≠ ⊤ := count_exceedance_ne_top T h j
  have hU : volume (S ∪ V) ≠ ⊤ := (measure_union_lt_top hS.lt_top (by rw [hshift]; exact hS.lt_top)).ne
  have hmass := (measureReal_mono (μ := volume) hcover hU).trans (measureReal_union_le S V)
  have hV : volume.real V = volume.real S := congrArg ENNReal.toReal hshift
  rw [hV] at hmass
  have hd : (2*b)/(Real.log T/(2*Real.pi)) = h+h := by dsimp [h]; ring
  rw [hd]
  change volume.real U/T ≤ _
  calc
    volume.real U / T ≤ (volume.real S + volume.real S) / T :=
      div_le_div_of_nonneg_right hmass (zero_lt_one.trans ht).le
    _ = 2*(volume.real S/T) := by ring
    _ ≤ 2*A*Real.exp (-c*(j:ℝ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hT j) (by norm_num)
    _ ≤ (2*A*Real.exp c)*Real.exp (-(c/2)*(J:ℝ)) := by
      rw [mul_assoc (2*A), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hA)
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hc.le (sub_nonneg.mpr hjB)]

/-- A single positive reference width suffices for every fixed unfolded width. -/
theorem expTranslatedCountTail_all_widths_iff {b : ℝ} (hb : 0 < b) :
    (∀ q : ℝ, 0 ≤ q → ExpTranslatedCountTail q) ↔ ExpTranslatedCountTail b := by
  refine ⟨fun h => h b hb.le, ?_⟩
  intro he q _
  have hpow (n : ℕ) : ExpTranslatedCountTail ((2 : ℝ)^n*b) := by
    induction n with
    | zero => simpa using he
    | succ n ih =>
      have h := expTranslatedCountTail_double (mul_nonneg (by positivity) hb.le) ih
      rw [pow_succ, show (2 : ℝ)^n*2*b = 2*((2 : ℝ)^n*b) by ring]
      exact h
  obtain ⟨n, hn⟩ := exists_nat_gt (q/b)
  have hbound (m : ℕ) : (m : ℝ)+1 ≤ (2 : ℝ)^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ, pow_succ]
      linarith only [ih, Nat.cast_nonneg (α := ℝ) m]
  apply expTranslatedCountTail_mono _ (hpow n)
  exact ((div_lt_iff₀ hb).mp hn).le.trans
    (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right zero_le_one).trans (hbound n)) hb.le)

end RiemannResearch.Analysis.MicroscopicCountTail
