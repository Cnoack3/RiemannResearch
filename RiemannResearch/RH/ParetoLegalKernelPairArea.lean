import RiemannResearch.NumberTheory.DivisorRankPairBudget
import RiemannResearch.Analysis.MontgomeryLatticeSineComparison
import RiemannResearch.RH.ParetoResidueAtomTests
import Mathlib.LinearAlgebra.Dimension.Constructions
import RiemannResearch.Probability.ContinuousProjectionPairMass

/-! # Physical all-pairs obstruction for the full-divisor Mellin system

The finite legal dimension is bounded by the number of positive divisors.
Even counting every labeled pair in a configuration of that size gives a
vanishing fraction at the physical PCC normalization whenever the conductor
period grows at most polynomially in the height. This applies to the running
LCM family, including the exact height choice T = lcm(1,...,M).
-/

noncomputable section

open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.NumberTheory.DivisorRankPairBudget

/-- The number of modes in the actual divisor trial space is bounded by the
number of divisors of its period. -/
theorem divisorTrial_finrank_le_card (L : ℕ) :
    Module.finrank ℝ (trialSpace L) ≤ L.divisors.card := by
  classical
  let g := fun d : L.divisors => normalizedResidueHilbert d.val (Nat.pos_of_mem_divisors d.property)
  change Module.finrank ℝ (Submodule.span ℝ (Set.range g)) ≤ _
  calc
    _ ≤ (Set.range g).toFinset.card := finrank_span_le_card _
    _ ≤ L.divisors.card := by
      simpa only [Set.toFinset_range, Finset.univ_eq_attach] using
        (Finset.card_image_le (s := L.divisors.attach) (f := g)).trans_eq Finset.card_attach

/-- Any subset of the labeled pairs in the full-divisor LCM sample has
vanishing physical mass, uniformly over the choice of gap mask and sample. -/
theorem lcm_divisorTrial_selected_pairs_tendsto_zero (T : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) (k : ℕ) (hk : k ≠ 0)
    (hscale : ∀ᶠ M in atTop, (Nat.lcmUpto M : ℝ) ≤ (T M)^k)
    (S : ∀ M, Finset (Fin (Module.finrank ℝ (trialSpace (Nat.lcmUpto M))) ×
      Fin (Module.finrank ℝ (trialSpace (Nat.lcmUpto M))))) :
    Tendsto (fun M => ((S M).card : ℝ) / (T M * Real.log (T M) / (2 * Real.pi)))
      atTop (𝓝 0) :=
  selected_pairs_tendsto_zero (L := Nat.lcmUpto) S
    (fun M => divisorTrial_finrank_le_card (Nat.lcmUpto M)) hT k hk
    (hscale.mono fun M h => ⟨Nat.lcmUpto_ne_zero M, h⟩)

/-- At every fixed positive width the complete legal sample cannot supply the
physical sine pair law: even an arbitrary choice of labeled pairs has limiting
mass zero, whereas the sine gap mass is strictly positive. -/
theorem lcm_divisorTrial_not_sine_gap_mass (T : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) (k : ℕ) (hk : k ≠ 0)
    (hscale : ∀ᶠ M in atTop, (Nat.lcmUpto M : ℝ) ≤ (T M)^k)
    (S : ∀ M, Finset (Fin (Module.finrank ℝ (trialSpace (Nat.lcmUpto M))) ×
      Fin (Module.finrank ℝ (trialSpace (Nat.lcmUpto M))))) {q : ℝ} (hq : 0 < q) :
    ¬ Tendsto (fun M => ((S M).card : ℝ) / (T M * Real.log (T M) / (2 * Real.pi))) atTop
      (𝓝 (RiemannResearch.Analysis.MontgomeryPositiveGap.sineGapMass q)) := by
  intro hs
  have he := tendsto_nhds_unique (lcm_divisorTrial_selected_pairs_tendsto_zero T hT k hk hscale S) hs
  exact (RiemannResearch.Analysis.MontgomeryLatticeSine.sineGapMass_strictly_pos hq).ne he

/-- Matching the period exactly to the physical height is a concrete cofinal
case of the preceding obstruction. -/
theorem lcm_period_height_selected_pairs_tendsto_zero
    (S : ∀ M, Finset (Fin (Module.finrank ℝ (trialSpace (Nat.lcmUpto M))) ×
      Fin (Module.finrank ℝ (trialSpace (Nat.lcmUpto M))))) :
    Tendsto (fun M => ((S M).card : ℝ) /
      ((Nat.lcmUpto M : ℝ) * Real.log (Nat.lcmUpto M : ℝ) / (2 * Real.pi))) atTop (𝓝 0) := by
  have hnat : Tendsto Nat.lcmUpto atTop atTop :=
    tendsto_atTop_mono (fun M => by have := lcmResidueIndex_succ M; omega) lcmResidueIndex_tendsto
  exact lcm_divisorTrial_selected_pairs_tendsto_zero _ (tendsto_natCast_atTop_atTop.comp hnat)
    1 (by decide) (Filter.Eventually.of_forall fun _ => by simp) S

open MeasureTheory ProbabilityTheory.ContinuousProjectionDPP
open scoped ComplexConjugate

/-- The integrated second factorial density of any orthonormal Mellin features
of the legal dimension vanishes on the physical PCC scale, even when integrated
over the whole frequency plane. -/
theorem lcm_divisorTrial_total_pair_det_tendsto_zero {μ : Measure ℝ} [SigmaFinite μ]
    (ψ : ∀ M, Fin (Module.finrank ℝ (trialSpace (Nat.lcmUpto M))) → ℝ → ℂ)
    (hψ : ∀ M i, MemLp (ψ M i) 2 μ)
    (ho : ∀ M i j, (∫ t, conj (ψ M i t) * ψ M j t ∂μ) = if i = j then 1 else 0)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (k : ℕ) (hk : k ≠ 0)
    (hscale : ∀ᶠ M in atTop, (Nat.lcmUpto M : ℝ) ≤ (T M)^k) :
    Tendsto (fun M => (∫ x, ∫ y,
      Matrix.det !![kernel (ψ M) x x, kernel (ψ M) x y; kernel (ψ M) y x, kernel (ψ M) y y]
      ∂μ ∂μ).re / (T M * Real.log (T M) / (2 * Real.pi))) atTop (𝓝 0) := by
  apply normalized_pair_mass_tendsto_zero (L := Nat.lcmUpto) hT k hk
    (hscale.mono fun M h => ⟨Nat.lcmUpto_ne_zero M, h⟩)
  apply Filter.Eventually.of_forall
  intro M
  rw [total_pair_det_integral (ψ M) (hψ M) (ho M)]
  let r := Module.finrank ℝ (trialSpace (Nat.lcmUpto M))
  change 0 ≤ ((r : ℂ) * ((r : ℂ) - 1)).re ∧
    ((r : ℂ) * ((r : ℂ) - 1)).re ≤ ((Nat.lcmUpto M).divisors.card : ℝ)^2
  simp only [Complex.mul_re, Complex.sub_re, Complex.natCast_re, Complex.one_re,
    Complex.natCast_im, zero_mul, sub_zero]
  have hr : (r : ℝ) ≤ ((Nat.lcmUpto M).divisors.card : ℝ) := by
    exact_mod_cast divisorTrial_finrank_le_card (Nat.lcmUpto M)
  constructor
  · cases r with
    | zero => norm_num
    | succ n => simp; positivity
  · nlinarith only [sq_le_sq₀ (Nat.cast_nonneg r) (Nat.cast_nonneg _) |>.2 hr, Nat.cast_nonneg (α := ℝ) r]

end RiemannResearch.RH.Pareto.ResidueMellin
