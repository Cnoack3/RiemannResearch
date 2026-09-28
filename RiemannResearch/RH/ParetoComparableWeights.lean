import RiemannResearch.RH.BaezDuarteNaturalApproximation

/-!
# Comparable discrete weights preserve the Pareto approximation criterion

Source: B. Bagchi, `On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis`, arXiv:math/0607733, Theorem 1 and
the following paragraph, for the statement that two-sided comparable weights
preserve the criterion. The proofs below use the repository's actual residue
vectors and complete infinite physical errors.

Index n represents the positive physical coordinate n+1. The approximation
equivalence is unconditional. Its RH converse retains precisely the external
analytic implication RH -> BaezDuarte.NaturalApproximation; its normalization
transfer is already proved in the imported module.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ComparableWeights
open CoefficientStabilization BaezDuarte

/-- Complete physical squared energy, with the zero coordinate omitted. -/
def weightedEnergy (w : ℕ → ℝ) (f : ThresholdHilbert) : ℝ :=
  ∑' n, w n * (hilbertSequence f (n + 1)) ^ 2

theorem pareto_energy_summable (f : ThresholdHilbert) :
    Summable (fun n => paretoWeight n * (hilbertSequence f (n + 1)) ^ 2) := by
  simpa only [positiveWeight_succ] using
    (summable_nat_add_iff 1).mpr (hilbertSequence_square_summable f)

theorem weightedEnergy_pareto (f : ThresholdHilbert) :
    weightedEnergy paretoWeight f = ‖f‖ ^ 2 := by
  rw [weightedEnergy, hilbert_norm_sq]
  apply tsum_congr
  intro n
  simpa only [positiveWeight_succ] using hilbertSequence_weighted_square f n

theorem weightedEnergy_summable (w : ℕ → ℝ) (C : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hupper : ∀ n, w n ≤ C * paretoWeight n)
    (f : ThresholdHilbert) :
    Summable (fun n => w n * (hilbertSequence f (n + 1)) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (sq_nonneg _))
    (fun n => ?_) ((pareto_energy_summable f).mul_left C)
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (hupper n) (sq_nonneg (hilbertSequence f (n+1)))

theorem weightedEnergy_le (w : ℕ → ℝ) (C : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hupper : ∀ n, w n ≤ C * paretoWeight n)
    (f : ThresholdHilbert) : weightedEnergy w f ≤ C * ‖f‖ ^ 2 := by
  have hp := pareto_energy_summable f
  calc
    weightedEnergy w f ≤ ∑' n, C * (paretoWeight n *
        (hilbertSequence f (n + 1)) ^ 2) := by
      apply Summable.tsum_le_tsum _ (weightedEnergy_summable w C hw hupper f)
        (hp.mul_left C)
      intro n
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hupper n) (sq_nonneg _)
    _ = C * weightedEnergy paretoWeight f := (hp.hasSum.mul_left C).tsum_eq
    _ = C * ‖f‖ ^ 2 := by rw [weightedEnergy_pareto]

theorem weightedEnergy_ge (w : ℕ → ℝ) (c C : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hlower : ∀ n, c * paretoWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * paretoWeight n) (f : ThresholdHilbert) :
    c * ‖f‖ ^ 2 ≤ weightedEnergy w f := by
  have hp := pareto_energy_summable f
  calc
    c * ‖f‖ ^ 2 = c * weightedEnergy paretoWeight f := by rw [weightedEnergy_pareto]
    _ = ∑' n, c * (paretoWeight n * (hilbertSequence f (n + 1)) ^ 2) :=
      (hp.hasSum.mul_left c).tsum_eq.symm
    _ ≤ weightedEnergy w f := by
      apply Summable.tsum_le_tsum _ (hp.mul_left c)
        (weightedEnergy_summable w C hw hupper f)
      intro n
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hlower n) (sq_nonneg _)

/-- All finite real combinations of the actual residue generators remain
available; conductor 1 is harmless because its generator is zero. -/
def WeightedApproximation (w : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℕ, ∃ a : ℕ → ℝ,
    (∀ d ∈ s, 0 < d) ∧
      weightedEnergy w (hilbertOne - finiteResidueSum s a) < ε

/-- Explicit scalar formula for the full weighted error of a legal sum. -/
theorem weightedEnergy_error_eq (w : ℕ → ℝ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    weightedEnergy w (hilbertOne - finiteResidueSum s a) =
      ∑' n, w n * (1 - ∑ d ∈ s,
        a d * ((((n + 1) % d : ℕ) : ℝ) / (d : ℝ))) ^ 2 := by
  apply tsum_congr
  intro n
  have hsub := congrFun
    (hilbertSequenceLinear.map_sub hilbertOne (finiteResidueSum s a)) (n + 1)
  change hilbertSequence (hilbertOne - finiteResidueSum s a) (n + 1) =
    hilbertSequence hilbertOne (n + 1) -
      hilbertSequence (finiteResidueSum s a) (n + 1) at hsub
  rw [hsub, finiteResidueSum_sequence s a hs, hilbertOne_sequence]
  simp [zeroAnchor]

theorem weightedApproximation_pareto_iff_one_mem :
    WeightedApproximation paretoWeight ↔ hilbertOne ∈ closedSpace := by
  rw [← centeredApproximation_iff_one_mem]
  constructor
  · intro h ε hε
    obtain ⟨s, a, hs, he⟩ := h ε hε
    rw [weightedEnergy_pareto] at he
    refine ⟨s, a, hs, ?_⟩
    rw [centeredError_eq_hilbert_norm_sq s a hs]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr he
  · intro h ε hε
    obtain ⟨s, a, hs, he⟩ := h ε hε
    refine ⟨s, a, hs, ?_⟩
    rw [centeredError_eq_hilbert_norm_sq s a hs] at he
    rw [weightedEnergy_pareto]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp he

/-- Uniform comparison of weights preserves arbitrary-small legal errors. -/
theorem weightedApproximation_iff_pareto (w : ℕ → ℝ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ n, c * paretoWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * paretoWeight n) :
    WeightedApproximation w ↔ WeightedApproximation paretoWeight := by
  have hw (n : ℕ) : 0 ≤ w n :=
    (mul_nonneg hc.le (paretoWeight_pos n).le).trans (hlower n)
  constructor
  · intro h ε hε
    obtain ⟨s, a, hs, he⟩ := h (c * ε) (mul_pos hc hε)
    refine ⟨s, a, hs, ?_⟩
    rw [weightedEnergy_pareto]
    have hb := weightedEnergy_ge w c C hw hlower hupper
      (hilbertOne - finiteResidueSum s a)
    exact (mul_lt_mul_iff_right₀ hc).mp (hb.trans_lt he)
  · intro h ε hε
    obtain ⟨s, a, hs, he⟩ := h (ε / C) (div_pos hε hC)
    refine ⟨s, a, hs, ?_⟩
    rw [weightedEnergy_pareto] at he
    calc
      weightedEnergy w (hilbertOne - finiteResidueSum s a) ≤
          C * ‖hilbertOne - finiteResidueSum s a‖ ^ 2 :=
        weightedEnergy_le w C hw hupper _
      _ < C * (ε / C) := mul_lt_mul_of_pos_left he hC
      _ = ε := by field_simp [ne_of_gt hC]

theorem weightedApproximation_iff_one_mem (w : ℕ → ℝ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ n, c * paretoWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * paretoWeight n) :
    WeightedApproximation w ↔ hilbertOne ∈ closedSpace :=
  (weightedApproximation_iff_pareto w c C hc hC hlower hupper).trans
    weightedApproximation_pareto_iff_one_mem

/-- The approximation-to-RH direction uses the proved Mellin obstruction,
with no external density hypothesis. -/
theorem riemannHypothesis_of_weightedApproximation (w : ℕ → ℝ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ n, c * paretoWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * paretoWeight n)
    (ha : WeightedApproximation w) : RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn)
  exact closedSpace_le_legalClosure
    ((weightedApproximation_iff_one_mem w c C hc hC hlower hupper).mp ha)

/-- Conditional research reduction. The only external analytic input is the
published RH-to-natural-approximation theorem, stated explicitly. -/
theorem weightedApproximation_iff_RH (w : ℕ → ℝ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ n, c * paretoWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * paretoWeight n)
    (hBaezDuarte : RiemannHypothesis → NaturalApproximation) :
    WeightedApproximation w ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_weightedApproximation w c C hc hC hlower hupper
  · intro hRH
    apply (weightedApproximation_iff_one_mem w c C hc hC hlower hupper).mpr
    exact one_mem_of_riemannHypothesis hBaezDuarte hRH

/-- Quantitative preservation of the full Mellin zero obstruction. -/
theorem weightedError_lower_of_zeta (w : ℕ → ℝ) (c C : ℝ)
    (hc : 0 ≤ c) (hw : ∀ n, 0 ≤ w n)
    (hlower : ∀ n, c * paretoWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * paretoWeight n)
    (s : Finset ℕ) (a : ℕ → ℝ) (hs : ∀ d ∈ s, 0 < d)
    (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    c * ((2 * ρ.re - 1) / ‖ρ‖ ^ 2) ≤
      weightedEnergy w (hilbertOne - finiteResidueSum s a) := by
  have hf : finiteResidueSum s a ∈ closedSpace :=
    (Submodule.le_topologicalClosure _)
      (finiteResidueSum_mem_span s a hs)
  have hb := legalClosure_distance_sq_lower_bound_of_zeta
    {n : ℕ | 0 < n} (fun _ hn => hn) ρ hρ hρ1 hz
      (closedSpace_le_legalClosure hf)
  exact (mul_le_mul_of_nonneg_left hb hc).trans
    (weightedEnergy_ge w c C hw hlower hupper _)

/-- The shifted inverse-square weights mentioned in Bagchi's criterion. -/
def inverseSquareWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2

theorem paretoWeight_le_inverseSquareWeight (n : ℕ) :
    paretoWeight n ≤ inverseSquareWeight n := by
  unfold paretoWeight inverseSquareWeight
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [show (0 : ℝ) ≤ n by positivity]

theorem inverseSquareWeight_le_twice_paretoWeight (n : ℕ) :
    inverseSquareWeight n ≤ 2 * paretoWeight n := by
  unfold paretoWeight inverseSquareWeight
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [show (0 : ℝ) ≤ n by positivity]

/-- The coefficient criterion depends on two-sided order of weights, not
on the exact Pareto(1) normalization. -/
theorem inverseSquare_comparable_approximation_iff_one_mem
    (w : ℕ → ℝ) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ n, c * inverseSquareWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * inverseSquareWeight n) :
    WeightedApproximation w ↔ hilbertOne ∈ closedSpace := by
  apply weightedApproximation_iff_one_mem w c (2 * C) hc (by positivity)
  · intro n
    exact (mul_le_mul_of_nonneg_left
      (paretoWeight_le_inverseSquareWeight n) hc.le).trans (hlower n)
  · intro n
    calc
      w n ≤ C * inverseSquareWeight n := hupper n
      _ ≤ C * (2 * paretoWeight n) :=
        mul_le_mul_of_nonneg_left (inverseSquareWeight_le_twice_paretoWeight n) hC.le
      _ = (2 * C) * paretoWeight n := by ring

theorem inverseSquare_comparable_approximation_iff_RH
    (w : ℕ → ℝ) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ n, c * inverseSquareWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * inverseSquareWeight n)
    (hBaezDuarte : RiemannHypothesis → NaturalApproximation) :
    WeightedApproximation w ↔ RiemannHypothesis := by
  rw [inverseSquare_comparable_approximation_iff_one_mem w c C hc hC hlower hupper]
  constructor
  · intro h
    exact riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
      (fun _ hn => hn) (closedSpace_le_legalClosure h)
  · exact one_mem_of_riemannHypothesis hBaezDuarte

/-- Uniformly comparable weights have exactly the same finite-energy domain,
for every raw physical sequence, before choosing a Hilbert realization. -/
theorem weighted_square_summable_iff_pareto
    (w : ℕ → ℝ) (c C : ℝ) (hc : 0 < c)
    (hlower : ∀ n, c * paretoWeight n ≤ w n)
    (hupper : ∀ n, w n ≤ C * paretoWeight n)
    (f : ℕ → ℝ) :
    Summable (fun n => w n * (f n) ^ 2) ↔
      Summable (fun n => paretoWeight n * (f n) ^ 2) := by
  have hp (n : ℕ) : 0 ≤ paretoWeight n * (f n) ^ 2 :=
    mul_nonneg (paretoWeight_pos n).le (sq_nonneg _)
  have hw (n : ℕ) : 0 ≤ w n :=
    (mul_nonneg hc.le (paretoWeight_pos n).le).trans (hlower n)
  constructor
  · intro h
    have hs : Summable (fun n => c * (paretoWeight n * (f n) ^ 2)) := by
      apply Summable.of_nonneg_of_le (fun n => mul_nonneg hc.le (hp n))
        (fun n => ?_) h
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hlower n) (sq_nonneg (f n))
    have hcancel := hs.mul_left c⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] using hcancel
  · intro h
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (sq_nonneg _))
      (fun n => ?_) (h.mul_left C)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hupper n) (sq_nonneg (f n))


end RiemannResearch.RH.Pareto.ComparableWeights
