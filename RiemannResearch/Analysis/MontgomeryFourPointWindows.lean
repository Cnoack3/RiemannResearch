import RiemannResearch.Analysis.FourPointFactorialComparison
import RiemannResearch.Analysis.MontgomeryWindowCountLaw
import RiemannResearch.Analysis.ZeroDPPWindowLattice
import Mathlib.Probability.ConditionalProbability

/-! # Fourth factorial tests of actual zeta zero windows

The two tests count four different occurrence labels, either all in a long
interval or divided between two disjoint intervals. A comparison law with
the sine pair mean then supplies positive-gap PCC. The fourth correlations
of the actual ordinates are arithmetic hypotheses.
-/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroWindowVariance ActualZeroOrdinate OrdinateWindowVariance
open ZeroDPPCorrelation FourPointComparison MicroscopicCountTail

/-- Uniform sampling in (0,T] for T≥1. -/
def fourTestHeightLaw (T : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (max T 1))⁻¹ • volume.restrict (Ioc 0 (max T 1))

instance (T : ℝ) : IsProbabilityMeasure (fourTestHeightLaw T) := by
  constructor
  have hp : 0 < max T 1 := zero_lt_one.trans_le (le_max_right _ _)
  simpa [fourTestHeightLaw, Real.volume_Ioc, -ENNReal.ofReal_max] using
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top

private theorem height_expectation {T : ℝ} (hT : 1 < T) (g : ℝ → ℝ)
    (hg : ∀ u, u ∉ Ioc 0 T → g u = 0) :
    (∫ u, g u ∂fourTestHeightLaw T) = (∫ u, g u)/T := by
  rw [fourTestHeightLaw,max_eq_left hT.le,integral_smul_measure,
    ← integral_indicator measurableSet_Ioc]
  have hi : (Ioc 0 T).indicator g = g := by
    funext u
    by_cases hu : u ∈ Ioc 0 T
    · exact indicator_of_mem hu _
    · rw [indicator_of_notMem hu,hg u hu]
  rw [hi,ENNReal.toReal_inv,ENNReal.toReal_ofReal (zero_lt_one.trans hT).le]
  simp [div_eq_inv_mul]

def unfoldedLocalCount (T q u : ℝ) : ℕ :=
  translatedWindowCard T (q / (Real.log T/(2*Real.pi))) u

/-- The next H=n+12 unfolded units following the local q-window. -/
def extraWindowCount (T q : ℝ) (n : ℕ) (u : ℝ) : ℕ :=
  unfoldedLocalCount T (q+((n:ℝ)+12)) u - unfoldedLocalCount T q u

/-- Ordered pairs of distinct occurrence labels in the local q-window. -/
def localOrderedPairs (T q u : ℝ) : ℝ := countTwo 1 (unfoldedLocalCount T q u)

private theorem local_cast (T q u : ℝ) : (unfoldedLocalCount T q u : ℝ) =
    actualWindowCount T (q / (Real.log T/(2*Real.pi))) u :=
  (actualWindowCount_eq_card _ _ _).symm

private theorem local_measurable (T q : ℝ) : Measurable (unfoldedLocalCount T q) := by
  apply measurable_to_countable'
  intro m
  have h : (unfoldedLocalCount T q) ⁻¹' {m} =
      (actualWindowCount T (q / (Real.log T/(2*Real.pi)))) ⁻¹' {(m:ℝ)} := by
    ext u
    simp only [mem_preimage,mem_singleton_iff,← local_cast,Nat.cast_inj]
  rw [h]
  exact (actual_count_measurable _ _) (measurableSet_singleton _)

private theorem local_le (T q u : ℝ) : unfoldedLocalCount T q u ≤ Fintype.card (Copies T) := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq Finset.card_univ

private theorem local_outside (T q u : ℝ) (hu : u ∉ Ioc 0 T) : unfoldedLocalCount T q u = 0 := by
  have h := windowCount_mul_support (Finset.univ : Finset (Copies T))
    (fun c => c.1.1.im) T (q / (Real.log T/(2*Real.pi))) u
  rw [show pulse 0 T u = 0 from indicator_of_notMem hu _,mul_zero] at h
  exact_mod_cast ((local_cast T q u).trans h.symm : (unfoldedLocalCount T q u : ℝ) = 0)

private theorem integrable_count_function {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y) (N : ℕ)
    (hx : ∀ x, X x ≤ N) (hy : ∀ x, Y x ≤ N) (g : ℕ → ℕ → ℝ) :
    Integrable (fun x => g (X x) (Y x)) μ := by
  let F (j : Fin (N+1) × Fin (N+1)) : ℝ := ‖g j.1.val j.2.val‖
  obtain ⟨B,hB⟩ := (finite_range F).bddAbove
  have hm : Measurable (fun x => g (X x) (Y x)) :=
    (measurable_of_countable (f := fun p : ℕ × ℕ => g p.1 p.2)).comp (hX.prodMk hY)
  apply Integrable.of_bound hm.aestronglyMeasurable B
  exact ae_of_all _ fun x =>
    hB ⟨(⟨X x,Nat.lt_succ_of_le (hx x)⟩,⟨Y x,Nat.lt_succ_of_le (hy x)⟩),rfl⟩

private theorem actual_test_integrability (T q : ℝ) (n : ℕ) :
    CountTestIntegrability (fourTestHeightLaw T) (localOrderedPairs T q)
      (extraWindowCount T q n) (inverseLength n) := by
  let X := unfoldedLocalCount T q
  let M := extraWindowCount T q n
  have hM : Measurable M :=
    (measurable_of_countable (f := fun p : ℕ × ℕ => p.1-p.2)).comp
      ((local_measurable T _).prodMk (local_measurable T q))
  have hi (g : ℕ → ℕ → ℝ) :
      Integrable (fun u => g (X u) (M u)) (fourTestHeightLaw T) :=
    integrable_count_function (local_measurable T q) hM _ (local_le T q)
      (fun u => (Nat.sub_le _ _).trans (local_le T _ u)) g
  exact ⟨hi (fun x _ => countTwo 1 x),hi (fun x _ => (countTwo 1 x)^2),
    hi (fun x y => countTwo 1 x*countTwo (inverseLength n) y),
    hi (fun _ y => countFour (inverseLength n) y),hi (fun _ y => countOne (inverseLength n) y)⟩

private theorem local_mean_eq {q : ℝ} (hq : 0 ≤ q) :
    ∀ᶠ T : ℝ in atTop, (∫ u, (unfoldedLocalCount T q u : ℝ) ∂fourTestHeightLaw T) =
      unfoldedWindowMean T q := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_supported_width q] with T hT hw
  obtain ⟨hpos,hfloor⟩ := hw q hq le_rfl
  rw [height_expectation hT _ (fun u hu => by rw [local_outside T q u hu]; simp)]
  simp_rw [local_cast]
  rw [integral_actualWindowCount _ _ hpos hfloor]
  rfl

private theorem extra_mean (q : ℝ) (hq : 0 ≤ q) (n : ℕ) :
    Tendsto (fun T => ∫ u, countOne (inverseLength n) (extraWindowCount T q n u)
      ∂fourTestHeightLaw T) atTop (𝓝 1) := by
  let H := (n:ℝ)+12
  have hH : 0 < H := by dsimp [H]; positivity
  have hlim := ((unfoldedWindowMean_tendsto (q+H)).sub
    (unfoldedWindowMean_tendsto q)).const_mul (inverseLength n)
  rw [show inverseLength n*((q+H)-q) = 1 by
    unfold inverseLength; rw [add_sub_cancel_left]; exact one_div_mul_cancel hH.ne'] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),local_mean_eq hq,
    local_mean_eq (add_nonneg hq hH.le)] with T hT hqT hHT
  have hscale : 0 ≤ Real.log T / (2*Real.pi) := div_nonneg (Real.log_pos hT).le (by positivity)
  have hmono (u : ℝ) : unfoldedLocalCount T q u ≤ unfoldedLocalCount T (q+H) u := by
    exact_mod_cast (show (unfoldedLocalCount T q u : ℝ) ≤ (unfoldedLocalCount T (q+H) u : ℝ) by
      rw [local_cast,local_cast]
      exact actualWindowCount_mono_width T u
        (div_le_div_of_nonneg_right (by linarith) hscale))
  have hi (r : ℝ) : Integrable (fun u => (unfoldedLocalCount T r u : ℝ)) (fourTestHeightLaw T) :=
    integrable_count_function (local_measurable T r) (local_measurable T r) _
      (local_le T r) (local_le T r) (fun x _ => (x:ℝ))
  change inverseLength n * (unfoldedWindowMean T (q+H)-unfoldedWindowMean T q) =
    ∫ u, inverseLength n * ((unfoldedLocalCount T (q+H) u - unfoldedLocalCount T q u : ℕ) : ℝ)
      ∂fourTestHeightLaw T
  simp_rw [Nat.cast_sub (hmono _)]
  rw [integral_const_mul]
  rw [integral_sub (hi _) (hi _),hqT,hHT]

private theorem actual_local_square_bound {q : ℝ} (h : BoundedTranslatedFourthMoment q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      (∫ u, (localOrderedPairs T q u)^2 ∂fourTestHeightLaw T) ≤ C := by
  obtain ⟨C,hC,hb⟩ := h
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with T h4 hT
  have hpow : Integrable (fun u => (unfoldedLocalCount T q u:ℝ)^4) (fourTestHeightLaw T) :=
    integrable_count_function (local_measurable T q) (local_measurable T q) _
      (local_le T q) (local_le T q) (fun x _ => (x:ℝ)^4)
  calc
    _ ≤ ∫ u, (unfoldedLocalCount T q u : ℝ)^4 ∂fourTestHeightLaw T := by
      apply integral_mono (actual_test_integrability T q 0).localSquare hpow
      intro u
      have hNat (m : ℕ) : (countTwo 1 m)^2 ≤ (m:ℝ)^4 := by
        cases m with
        | zero => norm_num [countTwo,countOne]
        | succ m =>
          apply sub_nonneg.mp
          simp only [countTwo,countOne,one_mul,Nat.cast_succ]
          ring_nf
          positivity
      exact hNat (unfoldedLocalCount T q u)
    _ = (∫ u : ℝ, (actualWindowCount T (q/(Real.log T/(2*Real.pi))) u)^4)/T := by
      rw [height_expectation hT _ (fun u hu => by rw [local_outside T q u hu]; norm_num)]
      simp_rw [local_cast]
    _ ≤ C := h4

/-- A bounded local four-label statistic suffices. Full fourth-order
correlation convergence gives this bound by testing the box [0,q)⁴. -/
def BoundedLocalFourthFactorial (q : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
    (∫ u, countFour 1 (unfoldedLocalCount T q u) ∂fourTestHeightLaw T) ≤ C

private theorem integrable_local_four (T q : ℝ) :
    Integrable (fun u => countFour 1 (unfoldedLocalCount T q u)) (fourTestHeightLaw T) :=
  integrable_count_function (local_measurable T q) (local_measurable T q) _
    (local_le T q) (local_le T q) (fun x _ => countFour 1 x)

theorem boundedLocalFourthFactorial_of_fujii {q : ℝ} (h : BoundedTranslatedFourthMoment q) :
    BoundedLocalFourthFactorial q := by
  obtain ⟨C,hC,hb⟩ := actual_local_square_bound h
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with T hT
  exact (integral_mono (integrable_local_four T q) (actual_test_integrability T q 0).localSquare
    (fun u => (local_factorial_comparison (unfoldedLocalCount T q u)).1)).trans hT

private theorem local_pair_bound_of_four {q : ℝ} (h : BoundedLocalFourthFactorial q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      (∫ u, (localOrderedPairs T q u)^2 ∂fourTestHeightLaw T) ≤ C := by
  obtain ⟨C,hC,hb⟩ := h
  refine ⟨36+6*C,by positivity,?_⟩
  filter_upwards [hb] with T hT
  have h₁ : Integrable (fun _ : ℝ => (36:ℝ)) (fourTestHeightLaw T) := integrable_const _
  have h₂ : Integrable (fun u => 6*countFour 1 (unfoldedLocalCount T q u)) (fourTestHeightLaw T) :=
    (integrable_local_four T q).const_mul _
  have hbound := integral_mono (actual_test_integrability T q 0).localSquare (h₁.add h₂)
    (fun u => (local_factorial_comparison (unfoldedLocalCount T q u)).2)
  change (∫ u, (localOrderedPairs T q u)^2 ∂fourTestHeightLaw T) ≤
    ∫ u, 36+6*countFour 1 (unfoldedLocalCount T q u) ∂fourTestHeightLaw T at hbound
  rw [integral_add h₁ h₂,integral_const_mul] at hbound
  simpa only [integral_const,probReal_univ,one_smul] using
    (hbound.trans (add_le_add_right (mul_le_mul_of_nonneg_left hT (by norm_num : (0:ℝ) ≤ 6)) _))

private theorem eventually_window_energy_eq_local_pairs {q : ℝ} (hq : 0 ≤ q) :
    ∀ᶠ T : ℝ in atTop, unfoldedWindowEnergy T q = unfoldedWindowMean T q +
      ∫ u, localOrderedPairs T q u ∂fourTestHeightLaw T := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_window_energy_eq_count_square q,
    local_mean_eq hq] with T hT h2 h1
  let K := actualWindowCount T ((q:ℝ)/(Real.log T/(2*Real.pi)))
  have hi₁ : Integrable K := windowCount_integrable _ _ _ _
  have hi₂ : Integrable (fun u => K u^2) := windowCount_sq_integrable _ _ _ _
  have hp : (∫ u, localOrderedPairs T q u ∂fourTestHeightLaw T) =
      ((∫ u, K u^2)-(∫ u, K u))/T := by
    rw [height_expectation hT _ (fun u hu => by
      simp [localOrderedPairs,local_outside T q u hu,countTwo,countOne])]
    rw [← integral_sub hi₂ hi₁]
    congr 1
    apply integral_congr_ae
    filter_upwards with u
    simp only [localOrderedPairs,countTwo,countOne,one_mul,local_cast,K]
    ring
  rw [height_expectation hT _ (fun u hu => by rw [local_outside T q u hu]; simp)] at h1
  simp_rw [local_cast] at h1
  rw [h2,← h1,hp]
  dsimp only [K]
  ring

/-- Sufficient fourth-order tests for actual positive-gap PCC. The inputs
hpure and hmixed are precisely expectations of four distinct labels in a
single interval or in two disjoint intervals. All pair data on the target
side belong to the comparison process. The local fourth-factorial
bound also follows from the fixed-width Fujii estimate. -/
structure FourPointWindowTests {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ)
    (X : ℚ → Ξ → ℕ) (N : ℚ → ℕ → Ξ → ℕ) : Prop where
  localFourthBound : ∀ q : ℚ, 0 < q → BoundedLocalFourthFactorial q
  referenceIntegrable : ∀ q : ℚ, 0 < q → ∀ n, CountTestIntegrability ν
    (fun x => countTwo 1 (X q x)) (N q n) (inverseLength n)
  referenceIntensity : ∀ q : ℚ, 0 < q → ∀ n,
    (∫ x, countOne (inverseLength n) (N q n x) ∂ν) = 1
  referenceFourthUpper : ∀ q : ℚ, 0 < q → ∀ n, (∫ x, countFour (inverseLength n) (N q n x) ∂ν) ≤ 1
  referencePair : ∀ q : ℚ, 0 < q →
    (∫ x, countTwo 1 (X q x) ∂ν) = sineWindowEnergy q - (q:ℝ)
  pureFour : ∀ q : ℚ, 0 < q → ∀ n, Tendsto
    (fun T => ∫ u, countFour (inverseLength n) (extraWindowCount T q n u) ∂fourTestHeightLaw T)
    atTop (𝓝 (∫ x, countFour (inverseLength n) (N q n x) ∂ν))
  mixedFour : ∀ q : ℚ, 0 < q → ∀ n, Tendsto
    (fun T => ∫ u, localOrderedPairs T q u*countTwo (inverseLength n) (extraWindowCount T q n u)
      ∂fourTestHeightLaw T)
    atTop (𝓝 (∫ x, countTwo 1 (X q x)*countTwo (inverseLength n) (N q n x) ∂ν))

theorem sineWindowMoment_of_four_point_windows
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {X : ℚ → Ξ → ℕ} {N : ℚ → ℕ → Ξ → ℕ} (h : FourPointWindowTests ν X N) : SineWindowMoment := by
  obtain ⟨hlocal,hint,hintensity,hGram,hsine,hpure,hmixed⟩ := h
  apply sineWindowMoment_of_rational
  intro q hq
  have hq' : 0 ≤ (q:ℝ) := by exact_mod_cast hq.le
  have h := pair_expectation_of_four_point_comparison fourTestHeightLaw ν
    (fun T => localOrderedPairs T q) (fun n T => extraWindowCount T q n)
    (fun x => countTwo 1 (X q x)) (N q)
    (fun n T => actual_test_integrability T q n) (hint q hq)
    (local_pair_bound_of_four (hlocal q hq)) (extra_mean q hq')
    (hintensity q hq) (hpure q hq) (hGram q hq) (hmixed q hq)
  rw [hsine q hq] at h
  have hsum := (unfoldedWindowMean_tendsto (q:ℝ)).add h
  rw [show (q:ℝ)+(sineWindowEnergy q-(q:ℝ)) = sineWindowEnergy q by ring] at hsum
  exact hsum.congr' ((eventually_window_energy_eq_local_pairs hq').mono fun _ hT => hT.symm)

theorem positiveGapPCC_of_four_point_windows
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {X : ℚ → Ξ → ℕ} {N : ℚ → ℕ → Ξ → ℕ} (h : FourPointWindowTests ν X N) : PositiveGapPCC :=
  positiveGapPCC_of_sineWindowMoment (sineWindowMoment_of_four_point_windows h)

theorem simple_critical_density_of_four_point_windows
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {X : ℚ → Ξ → ℕ} {N : ℚ → ℕ → Ξ → ℕ} (h : FourPointWindowTests ν X N) :
    Tendsto (fun T : ℝ => (ActualZeroCollisionCertificate.simpleCriticalCount T : ℝ) /
      (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  (ActualZeroCollisionCertificate.density_one_of_collision_limit
    (collision_limit_of_sineWindowMoment (sineWindowMoment_of_four_point_windows h))).1

end RiemannResearch.Analysis.MontgomeryPositiveGap
