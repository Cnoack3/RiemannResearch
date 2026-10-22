import RiemannResearch.RH.CanonicalMobiusFullEnergy
/-!
# Exact-head coefficient convergence does not control the full Pareto error

Source: user-provided coefficient-limit question, 2026-09-22.
The existing theorem `riemannHypothesis_of_coefficients_tendsto_mobius`
concerns the actual full-norm orthogonal projections. Here we prove that
coefficient convergence is automatic for arbitrary growing exact heads and
construct a finite legal family with those limits but divergent full error.

The perturbation is
v_N = (N+2) g_(N+2) - (N+1) g_(N+1).
It vanishes through N and has value N+1 at N+1. Adding the explicitly
scaled perturbation to the canonical Möbius witness sets that next value
to (N+1)^2, forcing full squared error at least N^2.
No PNT or RH assumption enters these counterexample theorems.
-/

open Filter
open scoped BigOperators Topology
noncomputable section

namespace RiemannResearch.RH.Pareto
open CoefficientStabilization ArithmeticCumulative

/-- A finite exact head fixes all Möbius coefficients within that head. -/
theorem coefficientCLM_eq_mobius_of_exact_head (f : ThresholdHilbert) (N m : ℕ)
    (hm : 1 < m) (hmN : m ≤ N)
    (hhead : ∀ j, 0 < j → j ≤ N → hilbertSequence f j = 1) :
    coefficientCLM m f = -(ArithmeticFunction.moebius m : ℝ) := by
  have he (j : ℕ) (hj : j ≤ N) : hilbertSequence f j = hilbertSequence hilbertOne j := by
    by_cases hj0 : j = 0
    · simp [hj0]
    · rw [hhead j (by omega) hj, hilbertOne_sequence]
      simp [zeroAnchor, hj0]
  change -(mobiusDifferenceCLM m f) = _
  congr 1
  rw [← mobius_coordinate_one m (by omega)]
  simp only [mobiusDifferenceCLM_apply, mobiusDifference]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hj).1
  rw [he j (hjm.trans hmN), he (j - 1) (by omega)]

/-- Our original constructed family already has the coefficient limits unconditionally. -/
theorem canonicalMobiusHilbert_coefficients_tendsto (m : ℕ) (hm : 1 < m) :
    Tendsto (fun N => coefficientCLM m (canonicalMobiusHilbert N)) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop m] with N hN
  exact (coefficientCLM_eq_mobius_of_exact_head _ N m hm hN
    (canonicalMobiusHilbert_exact N)).symm

namespace CoefficientConvergenceCounterexample

/-- Two legal atoms whose linear head contributions cancel exactly. -/
def repair (N : ℕ) : ThresholdHilbert :=
  ((N + 2 : ℕ) : ℝ) • normalizedResidueHilbert (N + 2) (by omega) -
    ((N + 1 : ℕ) : ℝ) • normalizedResidueHilbert (N + 1) (by omega)

theorem repair_sequence (N j : ℕ) :
    hilbertSequence (repair N) j =
      ((N + 2 : ℕ) : ℝ) * residueFraction (N + 2) j -
      ((N + 1 : ℕ) : ℝ) * residueFraction (N + 1) j := by
  change hilbertSequenceLinear (repair N) j = _
  unfold repair
  simp only [map_sub, map_smul]
  change ((N + 2 : ℕ) : ℝ) * hilbertSequence (normalizedResidueHilbert (N+2) _) j -
    ((N + 1 : ℕ) : ℝ) * hilbertSequence (normalizedResidueHilbert (N+1) _) j = _
  rw [normalizedResidueHilbert_sequence, normalizedResidueHilbert_sequence]

theorem repair_head (N j : ℕ) (hj : j ≤ N) :
    hilbertSequence (repair N) j = 0 := by
  rw [repair_sequence]
  simp only [residueFraction, Nat.mod_eq_of_lt (by omega : j < N+2),
    Nat.mod_eq_of_lt (by omega : j < N+1)]
  field_simp
  ring

theorem repair_next (N : ℕ) :
    hilbertSequence (repair N) (N+1) = ((N+1 : ℕ) : ℝ) := by
  rw [repair_sequence]
  simp only [residueFraction, Nat.mod_eq_of_lt (by omega : N+1 < N+2), Nat.mod_self]
  field_simp
  ring

/-- A finite legal exact-head witness with an explicitly prescribed large next value. -/
def escapingFamily (N : ℕ) : ThresholdHilbert :=
  canonicalMobiusHilbert N +
    ((((N+1 : ℕ) : ℝ)^2 - canonicalMobiusHead N (N+1)) / ((N+1 : ℕ) : ℝ)) • repair N

theorem escapingFamily_sequence (N j : ℕ) :
    hilbertSequence (escapingFamily N) j =
      canonicalMobiusHead N j +
        ((((N+1 : ℕ) : ℝ)^2 - canonicalMobiusHead N (N+1)) / ((N+1 : ℕ) : ℝ)) *
          hilbertSequence (repair N) j := by
  change hilbertSequenceLinear (escapingFamily N) j = _
  unfold escapingFamily
  simp only [map_add, map_smul]
  change hilbertSequence (canonicalMobiusHilbert N) j + _ = _
  rw [canonicalMobiusHilbert_sequence]
  rfl

theorem escapingFamily_exact (N j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    hilbertSequence (escapingFamily N) j = 1 := by
  rw [escapingFamily_sequence, repair_head N j hjN,
    canonicalMobiusHead_exact N j hj hjN]
  ring

theorem escapingFamily_next (N : ℕ) :
    hilbertSequence (escapingFamily N) (N+1) = ((N+1 : ℕ) : ℝ)^2 := by
  rw [escapingFamily_sequence, repair_next]
  have hn : ((N+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem escapingFamily_coefficient (N m : ℕ) (hm : 1 < m) (hmN : m ≤ N) :
    coefficientCLM m (escapingFamily N) = -(ArithmeticFunction.moebius m : ℝ) :=
  coefficientCLM_eq_mobius_of_exact_head _ N m hm hmN (escapingFamily_exact N)

theorem escapingFamily_coefficients_tendsto (m : ℕ) (hm : 1 < m) :
    Tendsto (fun N => coefficientCLM m (escapingFamily N)) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop m] with N hN
  exact (escapingFamily_coefficient N m hm hN).symm

/-- A single moving coordinate bounds the complete infinite Pareto error below. -/
theorem escapingFamily_error_lower (N : ℕ) :
    (N : ℝ)^2 ≤ ‖hilbertOne - escapingFamily N‖^2 := by
  have hcoord : hilbertSequence (hilbertOne - escapingFamily N) (N+1) =
      1 - ((N+1 : ℕ) : ℝ)^2 := by
    change hilbertSequenceLinear (hilbertOne - escapingFamily N) (N+1) = _
    rw [map_sub]
    change hilbertSequence hilbertOne (N+1) - hilbertSequence (escapingFamily N) (N+1) = _
    rw [escapingFamily_next, hilbertOne_sequence]
    simp [zeroAnchor]
  have hterm := (hilbertSequence_square_summable (hilbertOne - escapingFamily N)).le_tsum
    (N+1) (fun j _ => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
  rw [← hilbert_norm_weighted_sq, hcoord] at hterm
  calc
    _ ≤ positiveWeight (N+1) * (1 - ((N+1 : ℕ) : ℝ)^2)^2 := by
      simp only [positiveWeight]
      push_cast
      field_simp
      nlinarith [sq_nonneg (N : ℝ)]
    _ ≤ _ := hterm

theorem escapingFamily_error_tendsto_atTop :
    Tendsto (fun N => ‖hilbertOne - escapingFamily N‖^2) atTop atTop := by
  refine tendsto_atTop.2 fun B => ?_
  have hlarge : ∀ᶠ N : ℕ in atTop, max B 1 ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [hlarge] with N hN
  have hB : B ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have h1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
  nlinarith [escapingFamily_error_lower N]

theorem escapingFamily_mem_finiteSpace (N : ℕ) :
    escapingFamily N ∈ finiteSpace (N+1) := by
  have hu : canonicalMobiusHilbert N ∈ finiteSpace (N+1) :=
    (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id (Nat.le_succ N))
      (canonicalMobiusHilbert_mem_finiteSpace N)
  have hv : repair N ∈ finiteSpace (N+1) := by
    unfold repair
    apply (finiteSpace (N+1)).sub_mem
    · apply (finiteSpace (N+1)).smul_mem
      exact normalizedResidueHilbert_mem_finiteSpace (N+1) (N+2) (by omega) (by omega)
    · apply (finiteSpace (N+1)).smul_mem
      exact normalizedResidueHilbert_mem_finiteSpace (N+1) (N+1) (by omega) (by omega)
  unfold escapingFamily
  exact (finiteSpace (N+1)).add_mem hu ((finiteSpace (N+1)).smul_mem _ hv)

/-- Exact heads and all fixed Möbius coefficient limits coexist with divergent full error. -/
theorem exists_exact_head_coefficient_limits_with_divergent_error :
    ∃ F : ℕ → ThresholdHilbert,
      (∀ N, F N ∈ finiteSpace (N+1)) ∧
      (∀ N j, 0 < j → j ≤ N → hilbertSequence (F N) j = 1) ∧
      (∀ m, 1 < m → Tendsto (fun N => coefficientCLM m (F N)) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ∧
      Tendsto (fun N => ‖hilbertOne - F N‖^2) atTop atTop :=
  ⟨escapingFamily, escapingFamily_mem_finiteSpace, escapingFamily_exact,
    escapingFamily_coefficients_tendsto, escapingFamily_error_tendsto_atTop⟩

end CoefficientConvergenceCounterexample
end RiemannResearch.RH.Pareto
