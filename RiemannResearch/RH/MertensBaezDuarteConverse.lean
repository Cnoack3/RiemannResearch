import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.MertensEndpointPairing
import RiemannResearch.RH.MertensUnconditionalStretched
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The squarefree reverse from Báez-Duarte's explicit approximants

Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the
Riemann hypothesis*, Rend. Lincei Mat. Appl. 14 (2003), 5–11, Theorem 2,
formula (3.1), proves on RH that the global L² error of these approximants
tends to zero. Its arXiv version math/0205003 numbers this Proposition 3.1.
`BaezDuarteMobiusApproximation` states just the resulting squared-error
limit. Both literature inputs appear explicitly in the final theorem.
-/

noncomputable section
open Filter
open scoped Topology ENNReal BigOperators

namespace RiemannResearch.RH.Pareto.BaezDuarte

/-- The signed coefficient in the finite natural-dilation approximant. -/
def baezDuarteCoefficient (c : ℝ) (N m : ℕ) : ℝ :=
  -(ArithmeticFunction.moebius m : ℝ) *
    Real.exp (-c * Real.log (m : ℝ) / Real.log (Real.log (N : ℝ)))

/-- The global squared-error convergence supplied by Theorem 2 under RH. -/
def BaezDuarteMobiusApproximation : Prop :=
  RiemannHypothesis → ∃ c : ℝ, 0 < c ∧
    Tendsto (fun N : ℕ => naturalError (Finset.Icc 1 N) (baezDuarteCoefficient c N))
      atTop (𝓝 0)

/-- Centering the finite natural-dilation approximant preserves its squarefree support. -/
theorem baezDuarteSum_mem_squarefreeSpan (c : ℝ) (N : ℕ) :
    finiteResidueSum (Finset.Icc 1 N) (baezDuarteCoefficient c N) ∈ squarefreeCRTSpan := by
  classical
  unfold finiteResidueSum
  apply squarefreeCRTSpan.sum_mem
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  by_cases hsf : Squarefree d
  · apply squarefreeCRTSpan.smul_mem
    by_cases h1 : d = 1
    · subst d
      have hz : residueVector 1 = 0 := by
        apply hilbertSequence_injective
        rw [residueVector, dif_pos (by omega : 0 < 1), normalizedResidueHilbert_sequence]
        change ArithmeticCumulative.residueFraction 1 = hilbertSequenceLinear 0
        rw [map_zero]
        funext k
        simp [ArithmeticCumulative.residueFraction, Nat.mod_one]
      rw [hz]
      exact squarefreeCRTSpan.zero_mem
    · rw [squarefreeCRTSpan_eq_span, residueVector, dif_pos hdpos]
      exact Submodule.subset_span ⟨⟨d, by omega, hsf⟩, rfl⟩
  · have hz : baezDuarteCoefficient c N d = 0 := by
      simp [baezDuarteCoefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    rw [hz, zero_smul]
    exact squarefreeCRTSpan.zero_mem

/-- Vanishing global error for the explicit finite sums puts one in the legal Pareto closure. -/
theorem squarefreeClosure_of_baezDuarteMobiusApproximation
    (hBD : BaezDuarteMobiusApproximation) (hRH : RiemannHypothesis) :
    hilbertOne ∈ squarefreeCRTSpan.topologicalClosure := by
  obtain ⟨c, _, hc⟩ := hBD hRH
  change hilbertOne ∈ _root_.closure (squarefreeCRTSpan : Set ThresholdHilbert)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let u := ε ^ 2 / 4
  have hu : 0 < u := by dsimp [u]; positivity
  have he := (tendsto_order.1 hc).2 (ENNReal.ofReal u) (ENNReal.ofReal_pos.mpr hu)
  obtain ⟨N, hN⟩ := he.exists
  let s := Finset.Icc 1 N
  let a := baezDuarteCoefficient c N
  have hs (d : ℕ) (hd : d ∈ s) : 0 < d := (Finset.mem_Icc.mp hd).1
  have hsmall : centeredError s a < ENNReal.ofReal (ε ^ 2) := calc
    centeredError s a ≤ 2 * naturalError s a := centeredError_le_two_naturalError s a hs
    _ ≤ 2 * ENNReal.ofReal u := mul_le_mul_of_nonneg_left hN.le (by positivity)
    _ = ENNReal.ofReal (2 * u) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ < ENNReal.ofReal (ε ^ 2) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).mpr
      dsimp [u]
      nlinarith [sq_pos_of_pos hε]
  rw [centeredError_eq_hilbert_norm_sq s a hs] at hsmall
  have hsq : ‖hilbertOne - finiteResidueSum s a‖ ^ 2 < ε ^ 2 := by
    by_contra! hbad
    exact (not_le_of_gt hsmall) (ENNReal.ofReal_le_ofReal hbad)
  refine ⟨finiteResidueSum s a, baezDuarteSum_mem_squarefreeSpan c N, ?_⟩
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (hilbertOne - finiteResidueSum s a)]

end RiemannResearch.RH.Pareto.BaezDuarte

namespace RiemannResearch.RH.QMertensFirstMoment
open Pareto.BaezDuarte ZetaTwoProbability ZetaTwoHilbert
open QSquarefreeDisplacementRigidity RiemannResearch.Analysis

/-- The external approximation result supplies the reverse RH-to-residual implication. -/
theorem residual_zero_of_baezDuarte_and_riemannHypothesis
    (hBD : BaezDuarteMobiusApproximation) (hRH : RiemannHypothesis) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  have hmem : qOne ∈ ZetaTwoOptimizerStage.closure := by
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr
      (squarefreeClosure_of_baezDuarteMobiusApproximation hBD hRH)
  exact sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr hmem).symm

/-- Assuming the two published analytic inputs, RH is equivalent to the pure
absolute first moment at every fixed strictly interior Lee–Leong rate. -/
theorem riemannHypothesis_iff_leeLeong_displacement_moment
    (hLL : LeeLeongMertensEstimate) (hBD : BaezDuarteMobiusApproximation)
    (c : ℝ) (hc : 0 < c) (hca : c < leeLeongRate) :
    RiemannHypothesis ↔ Summable (fun n : ℕ => positiveQWeight n *
      ((n : ℝ) * Real.exp (-c * vkProfile (n : ℝ))) * |qSequence displacement n|) := by
  constructor
  · intro hRH
    exact (residual_zero_iff_leeLeong_displacement_moment hLL c hc hca).mp
      (residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH)
  · exact riemannHypothesis_of_leeLeong_displacement_moment hLL c hc hca

/-- Under the two published analytic inputs the absolute endpoint moment
is equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_iff_leeLeong_endpoint_displacement_moment
    (hLL : LeeLeongMertensEstimate) (hBD : BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-leeLeongRate * vkProfile (n : ℝ) - Real.sqrt (vkProfile (n : ℝ)) / 8)) *
        |qSequence displacement n|) :=
  ⟨fun hRH => (residual_zero_iff_leeLeong_endpoint_displacement_moment hLL).mp
      (residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH),
    riemannHypothesis_of_leeLeong_endpoint_displacement_moment hLL⟩

/-- On RH, the displacement vanishes and its logarithm divided by any
divergent profile tends to zero. -/
private theorem log_displacement_div_tendsto_of_riemannHypothesis
    (hBD : BaezDuarteMobiusApproximation) (hRH : RiemannHypothesis)
    (φ : ℕ → ℝ) (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) / φ n)
      atTop (𝓝 0) := by
  have hd := displacement_eq_zero_of_residual_eq_zero
    (residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH)
  have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
    cases n <;> simp [qSequence]
  rw [hd]
  simpa only [hz, abs_zero, add_zero] using hφ.const_div_atTop (Real.log 2)

/-- With the two external analytic inputs, the published VK-scale
little-o criterion is an equivalence with RH. -/
theorem riemannHypothesis_iff_leeLeong_log_displacement
    (hLL : LeeLeongMertensEstimate) (hBD : BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      vkProfile (n : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro hRH
    exact log_displacement_div_tendsto_of_riemannHypothesis hBD hRH _
      (vkProfile_tendsto_atTop.comp tendsto_natCast_atTop_atTop)
  · intro hgrowth
    apply QSquarefreeMertensProfileCriterion.riemannHypothesis_of_vk_log_displacement leeLeongRate
    · unfold leeLeongRate
      positivity
    · simpa only [one_mul] using mertens_vk_of_leeLeong hLL
    · exact hgrowth

/-- At the unconditional Mertens scale only the Báez-Duarte approximation
result is required to obtain an equivalence with RH. -/
theorem riemannHypothesis_iff_stretched_log_displacement
    (hBD : BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      logProductPower (1 / 11) (6 + Real.log (n : ℝ))) atTop (𝓝 0) := by
  constructor
  · intro hRH
    have hL : Tendsto (fun n : ℕ => 6 + Real.log (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop 6 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact log_displacement_div_tendsto_of_riemannHypothesis hBD hRH _
      ((tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp hL)
  · exact QSquarefreeStretchedDisplacement.riemannHypothesis_of_stretched_log_displacement

end RiemannResearch.RH.QMertensFirstMoment
