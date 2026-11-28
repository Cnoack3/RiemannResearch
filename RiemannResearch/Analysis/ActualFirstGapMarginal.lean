import RiemannResearch.Analysis.ActualConsecutiveGapCriterion
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualCofinalOneSidedMassRH
import RiemannResearch.Analysis.MontgomeryPositiveGapDensity
import RiemannResearch.Analysis.SineGaussianMoment
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # The zero-gap atom in the first spacing marginal of actual zeta zeros

Arias de Reyna and Rodgers, Theorem 2(iv) and Section 5.2,
https://arxiv.org/abs/2311.13441, use weak convergence of finite blocks of
unfolded consecutive spacings. We count every occurrence in the project's
chronological list and omit its padded endpoint. The first marginal with
an atomless-at-zero limit implies density-one singleton ordinates.
A strict one-occurrence bound on cofinal cutoffs gives pointwise simplicity.
See also Goldston, Lee, Schettler and Suriajaya, Theorem 1,
https://doi.org/10.1112/mtk.70127.
-/

noncomputable section
open MeasureTheory Filter Set Zeta23
open scoped BigOperators Topology NNReal ENNReal ComplexConjugate
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate

private def tiedEdges (l : List ℝ) (d : ℝ) : ℕ :=
  ∑ i ∈ Finset.range (l.length - 1), if l.getD (i+1) d = l.getD i d then 1 else 0

private theorem tiedEdges_cons (x y : ℝ) (l : List ℝ) (d : ℝ) :
    tiedEdges (x::y::l) d = tiedEdges (y::l) d + (if y = x then 1 else 0) := by
  simp only [tiedEdges, List.length_cons, Nat.add_sub_cancel, Finset.sum_range_succ',
    List.getD_cons_succ, List.getD_cons_zero]

private theorem tiedEdges_add_card (l : List ℝ) (d : ℝ) (hs : l.SortedLE) :
    tiedEdges l d + l.toFinset.card = l.length := by
  induction l with
  | nil => simp [tiedEdges]
  | cons x l ih =>
    cases l with
    | nil => simp [tiedEdges]
    | cons y l =>
      have htail := (List.pairwise_cons.mp hs.pairwise).2
      have hxy : x ≤ y := (List.pairwise_cons.mp hs.pairwise).1 y (by simp)
      have ht := ih htail.sortedLE
      rw [tiedEdges_cons]
      by_cases h : y = x
      · subst y
        simpa [List.toFinset_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          congrArg (fun n : ℕ => n + 1) ht
      · have hx : x ∉ (y::l).toFinset := by
          rw [List.mem_toFinset]
          intro hm
          rcases List.mem_cons.mp hm with he | he
          · exact h he.symm
          · exact h (le_antisymm ((List.pairwise_cons.mp htail).1 x he) hxy)
        rw [if_neg h, Nat.add_zero, List.toFinset_cons, Finset.card_insert_of_notMem hx]
        simpa [Nat.add_assoc] using congrArg (fun n : ℕ => n + 1) ht

/-- Each block of equal heights has precisely one first occurrence. -/
theorem zeroInteriorGapCount_add_support (T : ℝ) :
    zeroInteriorGapCount T + (actualOrdinateSupport T).card = Ncount 0 T := by
  classical
  have hs : (chronologicalList T).toFinset = actualOrdinateSupport T := by
    ext t
    simp only [List.mem_toFinset, mem_chronologicalList, actualOrdinateSupport,
      OrdinateCollisionCertificate.ordinateSupport, Finset.mem_image, Finset.mem_univ, true_and]
  have he : tiedEdges (chronologicalList T) T = zeroInteriorGapCount T := by
    simp only [tiedEdges, chronologicalList_length, zeroInteriorGapCount, Finset.card_filter,
      cutoffGap, sub_eq_zero, cutoffOrdinate]
  simpa only [he, hs, chronologicalList_length] using
    tiedEdges_add_card (chronologicalList T) T (chronologicalList_sorted T)

/-- A block with m ≥ 2 occurrences has m ≤ 2(m−1). -/
theorem count_le_singletons_add_twice_zeroGaps (T : ℝ) :
    Ncount 0 T ≤ singletonOrdinateCount T + 2 * zeroInteriorGapCount T := by
  classical
  have hpos (τ : ℝ) (hτ : τ ∈ actualOrdinateSupport T) : 0 < actualOrdinateMultiplicity T τ := by
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hτ
    apply Finset.card_pos.mpr
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  have hrow (τ : ℝ) (hτ : τ ∈ actualOrdinateSupport T) :
      2 ≤ actualOrdinateMultiplicity T τ +
        (if actualOrdinateMultiplicity T τ = 1 then 1 else 0) := by
    have hp := hpos τ hτ
    split <;> omega
  have htwo : 2 * (actualOrdinateSupport T).card ≤ Ncount 0 T + singletonOrdinateCount T := by
    calc
      _ = ∑ _τ ∈ actualOrdinateSupport T, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ τ ∈ actualOrdinateSupport T,
          (actualOrdinateMultiplicity T τ +
            (if actualOrdinateMultiplicity T τ = 1 then 1 else 0)) :=
        Finset.sum_le_sum hrow
      _ = _ := by
        rw [Finset.sum_add_distrib, ← actualCount_eq_sum_ordinateMultiplicity, Finset.sum_boole]
        rfl
  have he := zeroInteriorGapCount_add_support T
  omega

theorem singletonOrdinateCount_le_simpleCriticalCount (T : ℝ) :
    singletonOrdinateCount T ≤ simpleCriticalCount T := by
  classical
  let S := (actualOrdinateSupport T).filter (fun τ => actualOrdinateMultiplicity T τ = 1)
  have hsub : S ⊆ (simpleCriticalCopies T).image (copyOrdinate T) := by
    intro τ hτ
    obtain ⟨hs, hm⟩ := Finset.mem_filter.mp hτ
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hs
    have hgood : c ∈ simpleCriticalCopies T := by
      by_contra hbad
      obtain ⟨d, hne, he⟩ := exceptional_has_companion T c hbad
      let A := Finset.univ.filter (fun x : Copies T => copyOrdinate T x = τ)
      have hcd : ({c, d} : Finset (Copies T)) ⊆ A := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm.trans hc⟩
      have htwo : 2 ≤ A.card := by simpa [hne] using Finset.card_le_card hcd
      change A.card = 1 at hm
      omega
    exact Finset.mem_image.mpr ⟨c, hgood, hc⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Forward spacing after applying the chosen unfolding to the two actual heights. -/
def unfoldedInteriorGap (u : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  u (cutoffOrdinate T (n+1)) - u (cutoffOrdinate T n)

/-- Interior spacings in a test set, excluding the final interval to the cutoff T. -/
def firstGapCount (u : ℝ → ℝ) (T : ℝ) (s : Set ℝ) : ℕ := by
  classical
  exact ((Finset.range (Ncount 0 T - 1)).filter (fun n => unfoldedInteriorGap u T n ∈ s)).card

/-- Weak first-gap empirical measure with the occurrence-count denominator. -/
def firstGapLaw (u : ℝ → ℝ) (T : ℝ) : FiniteMeasure ℝ :=
  ⟨(Ncount 0 T : ℝ≥0)⁻¹ • ∑ n ∈ Finset.range (Ncount 0 T - 1),
    Measure.dirac (unfoldedInteriorGap u T n), inferInstance⟩

theorem firstGapLaw_measureReal (u : ℝ → ℝ) (T : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ((firstGapLaw u T : Measure ℝ) s).toReal = (firstGapCount u T s : ℝ) / (Ncount 0 T : ℝ) := by
  classical
  have hsum : (∑ n ∈ Finset.range (Ncount 0 T - 1), (Measure.dirac (unfoldedInteriorGap u T n)) s)
      = (firstGapCount u T s : ℝ≥0∞) := by
    simp only [Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply, Finset.sum_boole,
      firstGapCount]
  simp only [firstGapLaw, FiniteMeasure.toMeasure_mk, Measure.smul_apply,
    Measure.finsetSum_apply, hsum]
  change (↑((Ncount 0 T : ℝ≥0)⁻¹) * (firstGapCount u T s : ℝ≥0∞)).toReal = _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast]
  simp [div_eq_mul_inv, mul_comm]

theorem zeroInteriorGapCount_le_firstGapCount (u : ℝ → ℝ) (T : ℝ) {s : Set ℝ}
    (hs : 0 ∈ s) : zeroInteriorGapCount T ≤ firstGapCount u T s := by
  classical
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hn, he⟩ := Finset.mem_filter.mp hn
  change cutoffOrdinate T (n+1) - cutoffOrdinate T n = 0 at he
  exact Finset.mem_filter.mpr ⟨hn, by simpa [unfoldedInteriorGap, sub_eq_zero.mp he] using hs⟩

/-- Portmanteau at the closed singleton {0} proves the density statement from the first
marginal of condition (iv). Every physical tie survives any unfolding. -/
theorem zeroGap_proportion_tendsto_of_firstGapLaw {u : ℝ → ℝ} {μ : FiniteMeasure ℝ}
    (hw : Tendsto (firstGapLaw u) atTop (𝓝 μ)) (h0 : (μ : Measure ℝ) {0} = 0) :
    Tendsto (fun T => (zeroInteriorGapCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  let a := fun T => (firstGapLaw u T : Measure ℝ) {0}
  have hup : limsup a atTop ≤ (0 : ℝ≥0∞) := by
    simpa only [a, h0] using
      FiniteMeasure.limsup_measure_closed_le_of_tendsto hw (isClosed_singleton (x := (0 : ℝ)))
  have ha : Tendsto a atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le (show 0 ≤ liminf a atTop from bot_le) hup
  have hr := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp ha
  simp only [Function.comp_def, a, ENNReal.toReal_zero,
    firstGapLaw_measureReal u _ (measurableSet_singleton (0 : ℝ))] at hr
  apply squeeze_zero' _ _ hr
  · filter_upwards with T; positivity
  · filter_upwards with T
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast zeroInteriorGapCount_le_firstGapCount u T (Set.mem_singleton (0 : ℝ))

/-- Density-one singleton heights and simple critical zeros from the same first marginal. -/
theorem singleton_and_simpleCritical_density_of_firstGapLaw {u : ℝ → ℝ} {μ : FiniteMeasure ℝ}
    (hw : Tendsto (firstGapLaw u) atTop (𝓝 μ)) (h0 : (μ : Measure ℝ) {0} = 0) :
    Tendsto (fun T => (singletonOrdinateCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun T => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  have hz := zeroGap_proportion_tendsto_of_firstGapLaw hw h0
  have hlo := (tendsto_const_nhds (x := (1 : ℝ))).sub (hz.const_mul 2)
  simp only [mul_zero, sub_zero] at hlo
  have hl : ∀ᶠ T : ℝ in atTop, 1 - 2 * ((zeroInteriorGapCount T : ℝ) / (Ncount 0 T : ℝ)) ≤
      (singletonOrdinateCount T : ℝ) / (Ncount 0 T : ℝ) := by
    filter_upwards [eventually_count_pos] with T hN
    have hn : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
    have hh : (Ncount 0 T : ℝ) ≤ singletonOrdinateCount T + 2 * (zeroInteriorGapCount T : ℝ) := by
      exact_mod_cast count_le_singletons_add_twice_zeroGaps T
    field_simp [hn]
    linarith only [hh]
  have hmid (T : ℝ) : (singletonOrdinateCount T : ℝ) / (Ncount 0 T : ℝ) ≤
      (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast singletonOrdinateCount_le_simpleCriticalCount T)
      (Nat.cast_nonneg _)
  have hu : ∀ᶠ T : ℝ in atTop, (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ) ≤ 1 := by
    filter_upwards [eventually_count_pos] with T hN
    have hn : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
    apply (div_le_iff₀ hn).mpr
    rw [one_mul]
    exact_mod_cast (simpleCriticalCount_le_criticalLineCount T).trans (criticalLineCount_le_count T)
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds hl
      (hu.mono fun T h => (hmid T).trans h),
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
      (hl.mono fun T h => h.trans (hmid T)) hu⟩

/-- Restoring the denominator gives the integer count, including at empty cutoffs. -/
theorem count_mul_firstGapLaw_measureReal (u : ℝ → ℝ) (T : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (Ncount 0 T : ℝ) * ((firstGapLaw u T : Measure ℝ) s).toReal = firstGapCount u T s := by
  rw [firstGapLaw_measureReal u T hs]
  by_cases hn : Ncount 0 T = 0
  · simp [firstGapCount, hn]
  · have hn' : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hn']

/-- A single exceptional zero contributes at least one first-gap atom at all later cutoffs. -/
theorem persistent_unit_firstGapMass {H T : ℝ} (hHT : H ≤ T) {ρ : ℂ} (hρ : ρ ∈ cutoff H)
    (hbad : ¬ (ρ.re = 1 / 2 ∧ zeroMult ρ = 1)) (u : ℝ → ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hzero : 0 ∈ s) :
    1 ≤ (Ncount 0 T : ℝ) * ((firstGapLaw u T : Measure ℝ) s).toReal := by
  rw [count_mul_firstGapLaw_measureReal u T hs]
  have hρT : ρ ∈ cutoff T := by
    obtain ⟨hz, hp, hh⟩ := mem_cutoff.mp hρ
    exact mem_cutoff.mpr ⟨hz, hp, hh.trans hHT⟩
  have ht : 0 < zeroInteriorGapCount T := Nat.pos_of_ne_zero
    (fun he => hbad ((zeroInteriorGapCount_eq_zero_iff T).mp he ρ hρT))
  have hunit : 1 ≤ firstGapCount u T s :=
    ht.trans_le (zeroInteriorGapCount_le_firstGapCount u T hzero)
  exact_mod_cast hunit

/-- Complex conjugation preserves analytic multiplicity and covers the negative ordinates. -/
private theorem simple_at_all_heights
    (h : ∀ H : ℝ, ∀ ρ ∈ cutoff H, zeroMult ρ = 1) (ρ : ℂ) (hz : IsNontrivialZero ρ) :
    zeroMult ρ = 1 := by
  rcases lt_trichotomy 0 ρ.im with hp | he | hn
  · exact h ρ.im ρ (mem_cutoff.mpr ⟨hz, hp, le_rfl⟩)
  · have heq : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [he.symm]
    exact False.elim (RiemannResearch.RH.riemannZeta_ofReal_ne_zero ρ.re hz.2.1 hz.2.2.ne
      ((congrArg riemannZeta heq).symm.trans hz.1))
  · have hc : IsNontrivialZero (conj ρ) := by
      refine ⟨?_, hz.2.1, hz.2.2⟩
      rw [_root_.riemannZeta_conj, hz.1, map_zero]
    have hp : 0 < (conj ρ).im := by simpa only [Complex.conj_im] using neg_pos.mpr hn
    have hs := h (conj ρ).im (conj ρ) (mem_cutoff.mpr ⟨hc, hp, le_rfl⟩)
    have hne : ρ ≠ 1 := by
      intro he
      have hlt := hz.2.2
      simp [he] at hlt
    simpa only [zeroMult, Zeta23.analyticOrderAt_zeta_conj hne] using hs

/-- Cofinal first-gap tests strictly below the mass of one occurrence imply RH and simplicity
at every nontrivial zero. The sets may shrink with the cutoff. -/
theorem rh_and_simplicity_of_cofinal_firstGapMass (u : ℝ → ℝ) (s : ℝ → Set ℝ)
    (hs : ∀ T, MeasurableSet (s T) ∧ 0 ∈ s T)
    (h : ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      (Ncount 0 T : ℝ) * ((firstGapLaw u T : Measure ℝ) (s T)).toReal < 1) :
    RiemannHypothesis ∧ (∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1) := by
  have hall (H : ℝ) (ρ : ℂ) (hρ : ρ ∈ cutoff H) : ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
    by_contra hbad
    obtain ⟨T, hT, hsmall⟩ := h H
    exact (not_lt_of_ge (persistent_unit_firstGapMass hT hρ hbad u (hs T).1 (hs T).2)) hsmall
  refine ⟨riemannHypothesis_iff_cofinalSmallOneSidedTotal.mpr ?_,
    simple_at_all_heights (fun H ρ hρ => (hall H ρ hρ).2)⟩
  intro ε hε B
  refine ⟨B, le_rfl, ?_⟩
  have hsum : realSum B (fun z => max (z.re - 1 / 2) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    simp [(hall B z hz).1]
  simpa only [oneSidedHeightMean, hsum, zero_div, mul_zero] using hε

/-- The global pointwise conclusion is equivalent to eliminating the integer tie count cofinally. -/
theorem rh_and_simple_iff_cofinal_zeroGapCount :
    (RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1) ↔
      ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ zeroInteriorGapCount T = 0 := by
  constructor
  · rintro ⟨hRH, hm⟩ H
    refine ⟨H, le_rfl, (zeroInteriorGapCount_eq_zero_iff H).mpr ?_⟩
    intro ρ hρ
    have hz := (mem_cutoff.mp hρ).1
    exact ⟨RH_implies_on_line hRH hz, hm ρ hz⟩
  · intro h
    apply rh_and_simplicity_of_cofinal_firstGapMass id (fun _ => {0})
      (fun _ => ⟨measurableSet_singleton _, Set.mem_singleton _⟩)
    intro H
    obtain ⟨T, hT, ha⟩ := h H
    refine ⟨T, hT, ?_⟩
    rw [count_mul_firstGapLaw_measureReal id T (measurableSet_singleton _)]
    have he : firstGapCount id T {0} = 0 := by
      classical
      unfold firstGapCount
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn hhit
      have hr := Finset.mem_range.mp hn
      have hp := (zeroInteriorGapCount_eq_zero_iff_pos T).mp ha n (by omega)
      exact hp.ne' (Set.mem_singleton_iff.mp hhit)
    simp [he]

/-- The sine Palm expected number of further points in (0,r] is at most π²r³/9. -/
theorem sineGapMass_le_cubic {r : ℝ} (hr : 0 ≤ r) :
    MontgomeryPositiveGap.sineGapMass r ≤ (Real.pi ^ 2 / 9) * r ^ 3 := by
  have h₁ : Continuous (fun t : ℝ => 1 - Real.sinc (Real.pi * t) ^ 2) := by fun_prop
  have h₂ : Continuous (fun t : ℝ => (Real.pi ^ 2 / 3) * t ^ 2) := by fun_prop
  calc
    _ ≤ ∫ t in (0 : ℝ)..r, (Real.pi ^ 2 / 3) * t ^ 2 := by
      apply intervalIntegral.integral_mono_on hr (h₁.intervalIntegrable _ _)
        (h₂.intervalIntegrable _ _)
      intro t _
      exact (GaussianGapTests.one_sub_sinc_sq_le (Real.pi * t)).trans_eq (by ring)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring

/-- A cofinal one-sided sine comparison with error o(1/N) settles the one-occurrence bound
when the limiting cubic budget is below one. The comparison is an analytic hypothesis. -/
theorem rh_and_simplicity_of_shrinking_sine_upper (u : ℝ → ℝ) {r err : ℝ → ℝ} {a : ℝ}
    (hr : ∀ T, 0 ≤ r T)
    (hscale : Tendsto (fun T => (Ncount 0 T : ℝ) * (r T) ^ 3) atTop (𝓝 a))
    (hbudget : (Real.pi ^ 2 / 9) * a < 1)
    (herror : Tendsto (fun T => (Ncount 0 T : ℝ) * err T) atTop (𝓝 0))
    (hcompare : ∃ᶠ T : ℝ in atTop, ((firstGapLaw u T : Measure ℝ) (Icc 0 (r T))).toReal ≤
      MontgomeryPositiveGap.sineGapMass (r T) + err T) :
    RiemannHypothesis ∧ (∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1) := by
  apply rh_and_simplicity_of_cofinal_firstGapMass u (fun T => Icc 0 (r T))
    (fun T => ⟨measurableSet_Icc, le_rfl, hr T⟩)
  have hsmall := (hscale.const_mul (Real.pi ^ 2 / 9)).add herror
  simp only [add_zero] at hsmall
  have hfreq : ∃ᶠ T : ℝ in atTop, (Ncount 0 T : ℝ) *
      ((firstGapLaw u T : Measure ℝ) (Icc 0 (r T))).toReal < 1 := by
    apply (hcompare.and_eventually (hsmall.eventually_lt_const hbudget)).mono
    rintro T ⟨hc, hb⟩
    calc
      _ ≤ (Ncount 0 T : ℝ) * ((Real.pi ^ 2 / 9) * (r T) ^ 3 + err T) :=
        mul_le_mul_of_nonneg_left (hc.trans (add_le_add (sineGapMass_le_cubic (hr T)) le_rfl))
          (Nat.cast_nonneg _)
      _ = (Real.pi ^ 2 / 9) * ((Ncount 0 T : ℝ) * (r T) ^ 3) + (Ncount 0 T : ℝ) * err T := by ring
      _ < 1 := hb
  exact frequently_atTop.mp hfreq

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.singleton_and_simpleCritical_density_of_firstGapLaw'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms singleton_and_simpleCritical_density_of_firstGapLaw

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.rh_and_simplicity_of_cofinal_firstGapMass'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_and_simplicity_of_cofinal_firstGapMass

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.rh_and_simplicity_of_shrinking_sine_upper'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_and_simplicity_of_shrinking_sine_upper

end RiemannResearch.Analysis.ActualZeroOrdinate
