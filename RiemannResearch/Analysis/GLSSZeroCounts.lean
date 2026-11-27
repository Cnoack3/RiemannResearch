import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.MontgomeryArgumentWindowVariance
import RiemannResearch.Analysis.MontgomeryFourPointWindows
import RiemannResearch.Analysis.MontgomeryGapIntegratedCriterion
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # GLSS counts of all, simple, and simple critical zeros

Goldston, Lee, Schettler and Suriajaya, *Pair correlation conjecture for the
zeros of the Riemann zeta-function I*, §§5, 7–8, https://arxiv.org/abs/2503.15449.
The finite comparison and the horizontal multiplicity implication are their
Theorem 2 argument. For the ordinary positive-gap formulation, the published
analytic input is the upper bound from Proposition 2 (Fujii). The four-point
window formulation supplies the diagonal through its own second-moment limit.
-/

noncomputable section
open Filter Asymptotics MeasureTheory Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroCollisionCertificate
open ActualZeroOrdinate

/-- Simple zeros in the positive cutoff, counted at all real parts. -/
def simpleZeroCount (T : ℝ) : ℕ := by
  classical
  exact ((cutoff T).filter (fun ρ => zeroMult ρ = 1)).card

/-- Forgetting the copy index is a bijection on analytically simple zeros. -/
theorem simpleZeroCount_eq_card_copies (T : ℝ) :
    simpleZeroCount T =
      (Finset.univ.filter (fun c : Copies T => zeroMult c.1.1 = 1)).card := by
  classical
  symm
  apply Finset.card_bij (fun (c : Copies T) _ => c.1.1)
  · intro c hc
    exact Finset.mem_filter.mpr ⟨c.1.2, (Finset.mem_filter.mp hc).2⟩
  · rintro ⟨a,i⟩ ha ⟨b,j⟩ hb hab
    have hab' : a = b := Subtype.ext hab
    subst b
    have hm : zeroMult a.1 = 1 := (Finset.mem_filter.mp ha).2
    have hi := i.isLt
    have hj := j.isLt
    have hij : i = j := Fin.ext (by omega)
    cases hij
    rfl
  · intro ρ hρ
    obtain ⟨hcut, hm⟩ := Finset.mem_filter.mp hρ
    let c : Copies T := ⟨⟨ρ,hcut⟩, ⟨0, multiplicity_pos hcut⟩⟩
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩

/-- A singleton horizontal fibre forces its unique zero to be simple and critical. -/
theorem simple_critical_of_singleton_ordinate {T : ℝ} (c : Copies T)
    (h : actualOrdinateMultiplicity T (copyOrdinate T c) = 1) :
    c.1.1.re = 1 / 2 ∧ zeroMult c.1.1 = 1 := by
  classical
  apply (show c ∈ simpleCriticalCopies T → _ from fun hc => (Finset.mem_filter.mp hc).2)
  by_contra hc
  obtain ⟨d, hcd, ht⟩ := exceptional_has_companion T c hc
  let F := Finset.univ.filter (fun x : Copies T => copyOrdinate T x = copyOrdinate T c)
  have hF : F.card = 1 := h
  have hsub : ({c,d} : Finset (Copies T)) ⊆ F := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · obtain rfl := Finset.mem_singleton.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.symm⟩
  have hle := Finset.card_le_card hsub
  simpa [hcd, hF] using hle

/-- The signed finite-height inequalities, including heights with no zeros.
The square sums the entire horizontal fibre, with all analytic copies. -/
theorem glss_finite_count_chain (T : ℝ) :
    (2 : ℤ) * Ncount 0 T -
      (∑ τ ∈ actualOrdinateSupport T, (actualOrdinateMultiplicity T τ : ℤ)^2)
      ≤ (simpleCriticalCount T : ℤ) ∧
    simpleCriticalCount T ≤ simpleZeroCount T ∧ simpleZeroCount T ≤ Ncount 0 T := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := twice_count_le_simpleCriticalCount_add_collision T
    rw [actualCollision_eq_sum_multiplicity_sq] at h
    apply sub_le_iff_le_add.mpr
    exact_mod_cast h
  · rw [simpleZeroCount_eq_card_copies]
    apply Finset.card_le_card
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2.2⟩
  · rw [simpleZeroCount_eq_card_copies, ← card_copies, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)

/-- Horizontal multiplicity, simple critical zeros and all simple zeros,
each compared to the actual occurrence count by asymptotic equivalence. -/
structure GLSSCountAsymptotics : Prop where
  horizontal : (fun T : ℝ => ∑ τ ∈ actualOrdinateSupport T,
      (actualOrdinateMultiplicity T τ : ℝ)^2) ~[atTop] (fun T => (Ncount 0 T : ℝ))
  simpleCritical : (fun T : ℝ => (simpleCriticalCount T : ℝ)) ~[atTop]
      (fun T => (Ncount 0 T : ℝ))
  simple : (fun T : ℝ => (simpleZeroCount T : ℝ)) ~[atTop] (fun T => (Ncount 0 T : ℝ))

/-- GLSS Theorem 2 with the actual count in every denominator. -/
theorem glss_counts_of_horizontal_multiplicity
    (hm : (fun T : ℝ => ∑ τ ∈ actualOrdinateSupport T,
      (actualOrdinateMultiplicity T τ : ℝ)^2) ~[atTop] (fun T => (Ncount 0 T : ℝ))) :
    GLSSCountAsymptotics := by
  let D := fun T : ℝ => T * Real.log T / (2 * Real.pi)
  have hN : (fun T : ℝ => (Ncount 0 T : ℝ)) ~[atTop] D :=
    isEquivalent_of_tendsto_one tendsto_count_div_mainTerm
  have hd : ∀ᶠ T : ℝ in atTop, D T ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).ne'
  have hC : Tendsto (fun T : ℝ => (actualCollision T : ℝ) / D T) atTop (𝓝 1) := by
    have hlim := (isEquivalent_iff_tendsto_one hd).mp (hm.trans hN)
    change Tendsto (fun T : ℝ => (∑ τ ∈ actualOrdinateSupport T,
      (actualOrdinateMultiplicity T τ : ℝ)^2) / D T) atTop (𝓝 1) at hlim
    simpa only [actualCollision_eq_sum_multiplicity_sq, Nat.cast_sum,
      Nat.cast_pow] using hlim
  have hcrit := (density_one_of_collision_limit hC).1
  refine ⟨hm, isEquivalent_of_tendsto_one hcrit, isEquivalent_of_tendsto_one ?_⟩
  change Tendsto (fun T : ℝ => (simpleZeroCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcrit tendsto_const_nhds
  · filter_upwards with T
    exact div_le_div_of_nonneg_right (by exact_mod_cast (glss_finite_count_chain T).2.1)
      (Nat.cast_nonneg _)
  · filter_upwards [eventually_count_pos] with T hT
    have hT' : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hT
    apply (div_le_iff₀ hT').2
    rw [one_mul]
    exact_mod_cast (glss_finite_count_chain T).2.2

/-- info: 'RiemannResearch.Analysis.ActualZeroCollisionCertificate.glss_finite_count_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glss_finite_count_chain

end RiemannResearch.Analysis.ActualZeroCollisionCertificate

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroCollisionCertificate ActualZeroOrdinate

private theorem glss_counts_of_collision_mainTerm
    (h : Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1)) : GLSSCountAsymptotics := by
  apply glss_counts_of_horizontal_multiplicity
  have hN := isEquivalent_of_tendsto_one (u := fun T : ℝ => (Ncount 0 T : ℝ))
    (v := fun T : ℝ => T * Real.log T / (2 * Real.pi)) tendsto_count_div_mainTerm
  have hC := isEquivalent_of_tendsto_one (u := fun T : ℝ => (actualCollision T : ℝ))
    (v := fun T : ℝ => T * Real.log T / (2 * Real.pi)) h
  simpa only [actualCollision_eq_sum_multiplicity_sq, Nat.cast_sum, Nat.cast_pow] using
    hC.trans hN.symm

/-- The fixed-width logarithmic upper bound for the actual bare argument
increment used in GLSS Proposition 2, with L = log T / (2π). -/
def FujiiArgumentIncrementUpper : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ᶠ T : ℝ in atTop,
    pureArgumentWidthMoment T R ≤ C * Real.log (R + 2)

/-- The uniform second-moment estimate in equation (5.6) implies the
fixed-width upper bound in the normalization used by the actual zero count.
Here the moment in the premise is multiplied by T, as in the paper. -/
theorem fujiiArgumentIncrementUpper_of_prop_two
    (h : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop, ∀ U : ℝ, 0 < U → U ≤ 1 →
      let L := Real.log T / (2 * Real.pi)
      |(∫ t in (0 : ℝ)..T, (ActualZeroDiscrepancy.discrepancy (t+U) -
          ActualZeroDiscrepancy.discrepancy t)^2) -
        T * Real.log (2+U*L) / Real.pi^2| ≤ A*T*Real.sqrt (Real.log (2+U*L))) :
    FujiiArgumentIncrementUpper := by
  obtain ⟨A, hA, hprop⟩ := h
  refine ⟨1 / Real.pi^2 + A, by positivity, ?_⟩
  intro R hR
  have hlog : 1 ≤ Real.log (R+2) :=
    (Real.le_log_iff_exp_le (by linarith)).2 (Real.exp_one_lt_three.le.trans (by linarith))
  have hsqrt : Real.sqrt (Real.log (R+2)) ≤ Real.log (R+2) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hlog)
  filter_upwards [hprop, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (R * (2 * Real.pi))] with T hTprop hT hl
  let L := Real.log T / (2 * Real.pi)
  have hTpos := zero_lt_one.trans hT
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hRL : R ≤ L := (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2 hl
  have hb := hTprop (R / L) (div_pos (zero_lt_one.trans_le hR) hL)
    ((div_le_one hL).2 hRL)
  change |(∫ t in (0 : ℝ)..T, (ActualZeroDiscrepancy.discrepancy (t + R/L) -
    ActualZeroDiscrepancy.discrepancy t)^2) - T * Real.log (2+(R/L)*L) / Real.pi^2| ≤
      A*T*Real.sqrt (Real.log (2+(R/L)*L)) at hb
  rw [div_mul_cancel₀ R hL.ne', add_comm 2 R] at hb
  change (∫ t in (0 : ℝ)..T, (ActualZeroDiscrepancy.discrepancy (t + R/L) -
    ActualZeroDiscrepancy.discrepancy t)^2) / T ≤ _
  apply (div_le_iff₀ hTpos).2
  have hb' := (abs_le.mp hb).2
  have hbudget := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hA hTpos.le)
  calc
    _ ≤ A*T*Real.sqrt (Real.log (R+2)) + T*Real.log (R+2)/Real.pi^2 :=
      sub_le_iff_le_add.mp hb'
    _ ≤ A*T*Real.log (R+2) + T*Real.log (R+2)/Real.pi^2 := by linarith only [hbudget]
    _ = _ := by ring

/-- The cutoff and smooth-count differences vanish at each fixed width, so
Fujii's bare-argument estimate supplies the required one-sided window bound. -/
theorem shortWindowUpper_of_fujiiArgumentIncrement (hf : FujiiArgumentIncrementUpper) :
    ShortWindowSecondMomentUpper := by
  obtain ⟨C, hC, hb⟩ := hf
  intro ε hε
  have hlog : ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → ∀ᶠ T : ℝ in atTop,
      ActualZeroWindowVariance.actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi)))
        ≤ R^2 + K * Real.log (R+2) := by
    refine ⟨C+1, by linarith, ?_⟩
    intro R hR
    have hpos : 0 < Real.log (R+2) := Real.log_pos (by linarith)
    have he := (unfoldedWindowEnergy_sub_sq_sub_pureArgument_tendsto
      (zero_le_one.trans hR)).eventually (gt_mem_nhds hpos)
    filter_upwards [he, hb R hR] with T he hbound
    change unfoldedWindowEnergy T R ≤ _
    linarith
  obtain ⟨R,hR,h⟩ := cofinalShortWindowSecondMomentUpper_of_logarithmicUpper hlog ε hε 1
  exact ⟨R, hR, h⟩

/-- The classical GLSS deduction from strict positive gaps and Fujii's
published unconditional analytic estimate. -/
theorem glss_counts_of_positiveGapPCC (hp : PositiveGapPCC) (hf : FujiiArgumentIncrementUpper) :
    GLSSCountAsymptotics :=
  glss_counts_of_collision_mainTerm
    (collision_limit_of_positiveGapPCC hp (shortWindowUpper_of_fujiiArgumentIncrement hf))

/-- The four-point route supplies the horizontal diagonal directly. -/
theorem glss_counts_of_four_point_windows
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {X : ℚ → Ξ → ℕ} {N : ℚ → ℕ → Ξ → ℕ} (h : FourPointWindowTests ν X N) :
    PositiveGapPCC ∧ GLSSCountAsymptotics := by
  have h₂ := sineWindowMoment_of_four_point_windows h
  exact ⟨positiveGapPCC_of_sineWindowMoment h₂,
    glss_counts_of_collision_mainTerm (collision_limit_of_sineWindowMoment h₂)⟩

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.glss_counts_of_positiveGapPCC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glss_counts_of_positiveGapPCC

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.glss_counts_of_four_point_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glss_counts_of_four_point_windows

end RiemannResearch.Analysis.MontgomeryPositiveGap
