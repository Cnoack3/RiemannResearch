import RiemannResearch.Analysis.ActualFixedFrequencyLandau
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroFixedStripConcentration
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoExactHeadClosure
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.RH.ParetoWeights
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Completeness of actual-ordinate cosine probes in the legal Pareto space

The sampling index retains every positive-height zeta zero with its analytic
multiplicity. The physical probe at height t is n ↦ cos(t log n) on the
positive integers with weights 1/(n(n+1)). A count-normalized finite
combination recovers each coordinate indicator in Hilbert norm. Applying the
legal projection gives a total family in its range. The unprojected defect
at the first site gives an equivalent criterion for RH.

The analytic input is the actual fixed-frequency Hlawka limit. For its history
see Ford and Zaharescu, https://arxiv.org/abs/math/0405459, Section 1. The
coordinate recovery uses the cosine product formula and dominated convergence.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open RiemannResearch.Analysis.ActualZeroOrdinate
open RiemannResearch.Analysis.ZeroOrdinate (phase)
open CoefficientStabilization

private def siteFrequency (n : ℕ) : ℝ := Real.log ((n + 1 : ℕ) : ℝ)

private theorem siteFrequency_strictMono : StrictMono siteFrequency := by
  intro i j hij
  apply Real.log_lt_log (by positivity)
  exact_mod_cast Nat.add_lt_add_right hij 1

private theorem siteFrequency_zero_iff (n : ℕ) : siteFrequency n = 0 ↔ n = 0 := by
  have h0 : siteFrequency 0 = 0 := by simp [siteFrequency]
  rw [← h0]
  exact siteFrequency_strictMono.injective.eq_iff

private theorem siteFrequency_nonneg (n : ℕ) : 0 ≤ siteFrequency n := by
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- Its physical value at the positive integer k is cos(t log k). -/
def cosineRow (t : ℝ) : ThresholdHilbert :=
  sequenceHilbert (fun k => Real.cos (Real.log k * t))
    (weighted_summable_of_bounded (C := 1) (fun k => by
      rw [abs_pow]
      calc
        _ ≤ (1 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (Real.abs_cos_le_one _) _
        _ = 1 := by norm_num))

private theorem cosineRow_apply (t : ℝ) (i : ℕ) :
    cosineRow t i = Real.sqrt (paretoWeight i) * Real.cos (siteFrequency i * t) := rfl

/-- The full family of actual positive ordinate occurrences. -/
def actualRow (c : PositiveCopies) : ThresholdHilbert := cosineRow c.1.1.im

private def cosineMean (T u : ℝ) : ℝ :=
  (∑ c : Copies T, Real.cos (u * c.1.1.im)) / (Ncount 0 T : ℝ)

private theorem cosineMean_eq (T u : ℝ) :
    cosineMean T u = (ordinateSum T u / (Ncount 0 T : ℂ)).re := by
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, ordinateSum, sum_eq_copies, Complex.re_sum]
  simp only [cosineMean, phase, Complex.exp_ofReal_mul_I_re]

private theorem cosineMean_abs_le_one (T u : ℝ) : |cosineMean T u| ≤ 1 := by
  rw [cosineMean_eq]
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_div, Complex.norm_natCast]
  by_cases h : Ncount 0 T = 0
  · simp [h]
  · apply (div_le_iff₀ (show (0 : ℝ) < Ncount 0 T by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    simpa only [one_mul] using norm_ordinateSum_le_count T u

private theorem cosineMean_tendsto (hs : FixedStripConcentration) (u : ℝ) :
    Tendsto (fun T => cosineMean T u) atTop (𝓝 (if u = 0 then 1 else 0)) := by
  simp only [cosineMean_eq]
  by_cases hu : u = 0
  · subst u
    simp only [ordinateSum_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_count_pos] with T hN
    have hn : (Ncount 0 T : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [hn]
  · rw [if_neg hu]
    have h : Tendsto (fun T : ℝ => ordinateSum T u / (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
      rcases lt_or_gt_of_ne hu with hn | hp
      · simpa [ordinateSum_neg] using
          (tendsto_ordinate_div_count_of_pos (neg_pos.mpr hn) hs).star
      · exact tendsto_ordinate_div_count_of_pos hp hs
    exact Complex.continuous_re.continuousAt.tendsto.comp h

private def cosineMatrix (T : ℝ) (q i : ℕ) : ℝ :=
  (∑ c : Copies T, Real.cos (siteFrequency q * c.1.1.im) *
    Real.cos (siteFrequency i * c.1.1.im)) / (Ncount 0 T : ℝ)

private theorem cosineMatrix_eq (T : ℝ) (q i : ℕ) :
    cosineMatrix T q i =
      (cosineMean T (siteFrequency q - siteFrequency i) +
       cosineMean T (siteFrequency q + siteFrequency i)) / 2 := by
  have hs : (∑ c : Copies T, Real.cos (siteFrequency q * c.1.1.im) *
      Real.cos (siteFrequency i * c.1.1.im)) =
      ((∑ c : Copies T, Real.cos ((siteFrequency q - siteFrequency i) * c.1.1.im)) +
       (∑ c : Copies T, Real.cos ((siteFrequency q + siteFrequency i) * c.1.1.im))) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  rw [cosineMatrix, hs, cosineMean, cosineMean]
  ring

/-- The zero-frequency physical site has full energy. Every positive logarithm
has cosine energy one half. -/
def diagonalMass (q : ℕ) : ℝ := if q = 0 then 1 else 1 / 2

private theorem cosineMatrix_tendsto (hs : FixedStripConcentration) (q i : ℕ) :
    Tendsto (fun T => cosineMatrix T q i) atTop (𝓝 (if i = q then diagonalMass q else 0)) := by
  have hd : siteFrequency q - siteFrequency i = 0 ↔ i = q :=
    sub_eq_zero.trans (siteFrequency_strictMono.injective.eq_iff.trans eq_comm)
  have ha : siteFrequency q + siteFrequency i = 0 ↔ q = 0 ∧ i = 0 := by
    constructor
    · intro h
      constructor
      · apply (siteFrequency_zero_iff q).mp
        linarith [siteFrequency_nonneg q, siteFrequency_nonneg i]
      · apply (siteFrequency_zero_iff i).mp
        linarith [siteFrequency_nonneg q, siteFrequency_nonneg i]
    · rintro ⟨rfl, rfl⟩
      simp [siteFrequency]
  have ht := ((cosineMean_tendsto hs (siteFrequency q - siteFrequency i)).add
    (cosineMean_tendsto hs (siteFrequency q + siteFrequency i))).div_const 2
  simp only [hd, ha] at ht
  by_cases hi : i = q
  · subst i
    by_cases hq : q = 0 <;> simpa [cosineMatrix_eq, diagonalMass, hq] using ht
  · have hz : ¬ (q = 0 ∧ i = 0) := fun h => hi (h.2.trans h.1.symm)
    simpa [cosineMatrix_eq, hi, hz] using ht

private theorem cosineMatrix_abs_le_one (T : ℝ) (q i : ℕ) : |cosineMatrix T q i| ≤ 1 := by
  rw [cosineMatrix_eq]
  have h₁ := abs_le.mp (cosineMean_abs_le_one T (siteFrequency q - siteFrequency i))
  have h₂ := abs_le.mp (cosineMean_abs_le_one T (siteFrequency q + siteFrequency i))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A finite linear combination of the original ordinate rows, with all copies
retained in the count and in the sum. -/
def recovery (T : ℝ) (q : ℕ) : ThresholdHilbert :=
  (Ncount 0 T : ℝ)⁻¹ • ∑ c : Copies T,
    Real.cos (siteFrequency q * c.1.1.im) • cosineRow c.1.1.im

private theorem recovery_apply (T : ℝ) (q i : ℕ) :
    recovery T q i = Real.sqrt (paretoWeight i) * cosineMatrix T q i := by
  simp only [recovery, cosineMatrix, lp.coeFn_smul, lp.coeFn_sum,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, cosineRow_apply, div_eq_mul_inv,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- At the first recovered site, Selberg density at exponent two bounds the
difference from the count-normalized Landau trace at each integer logarithm
through log T. Both traces use the same zero occurrences. -/
theorem first_recovery_landau_error_of_selberg_two {T C : ℝ} (hT : 1 < T)
    (hN : 0 < Ncount 0 T) (hC : 0 ≤ C) (hD : SelbergDensityBound T C 2)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℝ) ≤ T) :
    |hilbertGibbsPhysical (recovery T 0) i -
      (landauSum T (Real.log ((i + 1 : ℕ) : ℝ)) / (Ncount 0 T : ℂ)).re| ≤
      (T / (Ncount 0 T : ℝ)) * (2 * C * (Real.log ((i + 1 : ℕ) : ℝ)) ^ 2 /
        (3 * Real.log T)) := by
  let u := siteFrequency i
  have ht : 0 < T := lt_trans zero_lt_one hT
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb : |u| ≤ (1 / 2 : ℝ) * (2 * Real.log T) := by
    rw [abs_of_nonneg (siteFrequency_nonneg i)]
    have hl : u ≤ Real.log T := Real.log_le_log (by positivity) hi
    linarith
  have hm : cosineMatrix T 0 i = cosineMean T u := by
    simp [u, cosineMatrix, cosineMean, siteFrequency]
  have hp : hilbertGibbsPhysical (recovery T 0) i =
      (ordinateSum T u / (Ncount 0 T : ℂ)).re := by
    rw [hilbertGibbsPhysical, recovery_apply, hm, cosineMean_eq]
    field_simp [(Real.sqrt_pos.mpr (paretoWeight_pos i)).ne']
  have h := normalized_ordinate_landau_error_of_selbergDensity_band T u C 2 (1 / 2)
    hT hC (by norm_num) (by norm_num) (by norm_num) hb hD
  change |hilbertGibbsPhysical (recovery T 0) i - (landauSum T u / (Ncount 0 T : ℂ)).re| ≤ _
  rw [hp, ← Complex.sub_re, ← sub_div]
  apply (Complex.abs_re_le_norm _).trans
  calc
    ‖(ordinateSum T u - landauSum T u) / (Ncount 0 T : ℂ)‖ =
        (T / (Ncount 0 T : ℝ)) * ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ := by
      rw [norm_div, norm_div, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht]
      field_simp [hn, ht.ne']
    _ ≤ _ := (mul_le_mul_of_nonneg_left h (div_nonneg ht.le (Nat.cast_nonneg _))).trans_eq
      (by change _ = (T / (Ncount 0 T : ℝ)) * (2 * C * u ^ 2 / (3 * Real.log T)); ring)

/-- Strong recovery of each physical singleton. Selberg density at slope two
supplies fixed-strip concentration, and the project's displacement-moment
theorem supplies it unconditionally as well. -/
theorem recovery_tendsto_of_fixedStrip (hs : FixedStripConcentration) (q : ℕ) :
    Tendsto (fun T => recovery T q) atTop (𝓝 (diagonalMass q • paretoPointHilbert q)) := by
  let v := diagonalMass q • paretoPointHilbert q
  let d (i : ℕ) : ℝ := if i = q then diagonalMass q else 0
  have hv (i : ℕ) : v i = Real.sqrt (paretoWeight i) * d i := by
    change diagonalMass q * (Real.sqrt (paretoWeight i) * (if i + 1 = q + 1 then 1 else 0)) = _
    by_cases h : i = q <;> simp [d, h, mul_comm]
  have hi (i : ℕ) : Tendsto (fun T => recovery T q i) atTop (𝓝 (v i)) := by
    simpa only [hv, recovery_apply, d] using
      (cosineMatrix_tendsto hs q i).const_mul (Real.sqrt (paretoWeight i))
  have hd (i : ℕ) : |d i| ≤ 1 := by
    by_cases h : i = q
    · rw [show d i = diagonalMass q by simp [d, h]]
      by_cases hz : q = 0 <;> norm_num [diagonalMass, hz]
    · simp [d, h]
  have hbound (T : ℝ) (i : ℕ) :
      ‖(recovery T q i - v i)^2‖ ≤ 4 * paretoWeight i := by
    have hab : |cosineMatrix T q i - d i| ≤ 2 :=
      (abs_sub _ _).trans (by linarith [cosineMatrix_abs_le_one T q i, hd i])
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hab 2
    rw [sq_abs] at hsq
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), recovery_apply, hv,
      ← mul_sub, mul_pow, Real.sq_sqrt (paretoWeight_pos i).le]
    nlinarith only [mul_le_mul_of_nonneg_left hsq (paretoWeight_pos i).le]
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun (T : ℝ) i => (recovery T q i - v i)^2) (g := fun _ : ℕ => (0 : ℝ))
    (paretoWeight_hasSum.summable.mul_left 4)
    (fun i => by simpa using ((hi i).sub_const (v i)).pow 2)
    (Eventually.of_forall hbound)
  have hn : Tendsto (fun T => ‖recovery T q - v‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hilbert_norm_sq, lp.coeFn_sub, Pi.sub_apply, tsum_zero] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hn

private theorem actual_concentration : FixedStripConcentration := by
  apply fixedStrip_of_relativeEnergy_tendsto_zero
  change Tendsto (fun T : ℝ => horizontalEnergy T / (Ncount 0 T : ℝ)) atTop (𝓝 0)
  simpa only [show 1+1 = (2 : ℕ) by decide, displacementMoment_two] using
    tendsto_displacementMoment 1

private theorem recovery_mem (T : ℝ) (q : ℕ) :
    recovery T q ∈ Submodule.span ℝ (Set.range actualRow) := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro c _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hz := (mem_cutoff_iff_zeta.mp c.1.property)
  exact ⟨⟨⟨c.1.1, hz.1, hz.2.1⟩, c.2⟩, rfl⟩

/-- The real cosine rows of the actual ordinates span the ambient Pareto
Hilbert space after closure. -/
theorem actualRow_span_dense :
    (Submodule.span ℝ (Set.range actualRow)).topologicalClosure = ⊤ := by
  let W := (Submodule.span ℝ (Set.range actualRow)).topologicalClosure
  have hW : IsClosed (W : Set ThresholdHilbert) := Submodule.isClosed_topologicalClosure _
  have hpoint (q : ℕ) : paretoPointHilbert q ∈ W := by
    have hm := hW.mem_of_tendsto (recovery_tendsto_of_fixedStrip actual_concentration q)
      (Eventually.of_forall (fun T => (Submodule.span ℝ (Set.range actualRow)).le_topologicalClosure
        (recovery_mem T q)))
    have hd : diagonalMass q ≠ 0 := by by_cases h : q = 0 <;> norm_num [diagonalMass, h]
    simpa [smul_smul, hd] using W.smul_mem (diagonalMass q)⁻¹ hm
  have hspan : Submodule.span ℝ (Set.range paretoPointHilbert) ≤ W :=
    Submodule.span_le.mpr (by rintro x ⟨q, rfl⟩; exact hpoint q)
  have htop := (Submodule.span ℝ (Set.range paretoPointHilbert)).topologicalClosure_minimal hspan hW
  rw [paretoPoint_span_dense] at htop
  exact top_unique htop

/-- Orthogonally projecting the same occurrence-indexed family into the
actual closed legal space gives a total family in that space. -/
theorem projected_actualRow_span :
    (Submodule.span ℝ
      (Set.range (fun c => closedSpace.starProjection (actualRow c)))).topologicalClosure =
        closedSpace := by
  let S := Submodule.span ℝ (Set.range actualRow)
  let A := Submodule.span ℝ (Set.range (fun c => closedSpace.starProjection (actualRow c)))
  let W := A.topologicalClosure
  have hW : IsClosed (W : Set ThresholdHilbert) := A.isClosed_topologicalClosure
  have hV : IsClosed (closedSpace : Set ThresholdHilbert) := Submodule.isClosed_topologicalClosure _
  apply le_antisymm
  · apply A.topologicalClosure_minimal _ hV
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    exact closedSpace.starProjection_apply_mem _
  · have hs : S ≤ W.comap closedSpace.starProjection.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨c, rfl⟩
      exact A.le_topologicalClosure (Submodule.subset_span ⟨c, rfl⟩)
    have hc : IsClosed
        ((W.comap closedSpace.starProjection.toLinearMap : Submodule ℝ ThresholdHilbert) :
          Set ThresholdHilbert) := hW.preimage closedSpace.starProjection.continuous
    have ht := S.topologicalClosure_minimal hs hc
    change (Submodule.span ℝ (Set.range actualRow)).topologicalClosure ≤ _ at ht
    rw [actualRow_span_dense] at ht
    intro x hx
    have hm : closedSpace.starProjection x ∈ W :=
      ht (show x ∈ (⊤ : Submodule ℝ ThresholdHilbert) from by trivial)
    simpa only [Submodule.starProjection_eq_self_iff.mpr hx] using hm

/-- RH is equivalent to vanishing of the unprojected first-site recovery's
legal projection error. The finite averages use precisely the same ordinates. -/
theorem rh_iff_first_recovery_defect :
    RiemannHypothesis ↔ Tendsto
      (fun T => recovery T 0 - closedSpace.starProjection (recovery T 0)) atTop (𝓝 0) := by
  have hr : Tendsto (fun T => recovery T 0) atTop (𝓝 (paretoPointHilbert 0)) := by
    simpa [diagonalMass] using recovery_tendsto_of_fixedStrip actual_concentration 0
  have hd := hr.sub (closedSpace.starProjection.continuous.continuousAt.tendsto.comp hr)
  have hRH : RiemannHypothesis ↔ paretoPointHilbert 0 ∈ closedSpace :=
    (PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.trans
      BaezDuarte.naturalApproximation_iff_one_mem).trans firstPoint_mem_iff_one_mem.symm
  rw [hRH]
  constructor
  · intro hm
    simpa only [Function.comp_def, Submodule.starProjection_eq_self_iff.mpr hm, sub_self] using hd
  · intro h
    have he := tendsto_nhds_unique hd h
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.projected_actualRow_span' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms projected_actualRow_span

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_first_recovery_defect' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_first_recovery_defect

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.first_recovery_landau_error_of_selberg_two' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms first_recovery_landau_error_of_selberg_two

end RiemannResearch.RH.Pareto.OrdinateCosine
