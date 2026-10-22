import RiemannResearch.RH.ParetoGibbsHilbert
import RiemannResearch.RH.ParetoGibbsPositive

/-!
# Positivity and exact norm rigidity of the actual Hilbert Gibbs operator

All statements concern the complete weighted Hilbert space.  In particular,
vectorwise strict norm loss is not confused with a uniform spectral gap.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The normalized Hankel series converges to each coordinate of the actual operator. -/
theorem hilbertGibbs_matrix_hasSum (f : ThresholdHilbert) (n : ℕ) :
    HasSum (fun m => normalizedGibbsHankel n m * f m) (hilbertGibbs f n) := by
  have he (m : ℕ) : (Real.sqrt (paretoWeight n) / paretoWeight n) *
      (geometricKernel n m * hilbertGibbsPhysical f m) =
        normalizedGibbsHankel n m * f m := by
    calc
      _ = (Real.sqrt (paretoWeight n) * (geometricKernel n m / paretoWeight n) /
          Real.sqrt (paretoWeight m)) * f m := by
        unfold hilbertGibbsPhysical
        ring
      _ = _ := by rw [normalizedGibbsHankel_conjugation]
  have h := (gibbs_row_summable (hilbertGibbsPhysical_abs_summable f) n).hasSum.mul_left
    (Real.sqrt (paretoWeight n) / paretoWeight n)
  simp only [he] at h
  convert h using 1
  all_goals first
    | rfl
    | (change Real.sqrt (paretoWeight n) *
        ((∑' m, geometricKernel n m * hilbertGibbsPhysical f m) / paretoWeight n) = _
       ring)

/-- Complete matrix action, on arbitrary l2 vectors rather than only finite sections. -/
theorem hilbertGibbs_matrix_tsum (f : ThresholdHilbert) (n : ℕ) :
    hilbertGibbs f n = ∑' m, normalizedGibbsHankel n m * f m :=
  (hilbertGibbs_matrix_hasSum f n).tsum_eq.symm

theorem hilbertGibbs_norm_sq (f : ThresholdHilbert) :
    ‖hilbertGibbs f‖ ^ 2 =
      ∑' n, paretoWeight n * gibbsAction (hilbertGibbsPhysical f) n ^ 2 := by
  rw [hilbert_norm_sq]
  apply tsum_congr
  intro n
  simp only [hilbertGibbs_apply, mul_pow, Real.sq_sqrt (paretoWeight_pos n).le]

theorem hilbertGibbsPhysical_norm_sq (f : ThresholdHilbert) :
    (∑' n, paretoWeight n * hilbertGibbsPhysical f n ^ 2) = ‖f‖ ^ 2 := by
  simp only [hilbertGibbsPhysical_square, hilbert_norm_sq]

/-- Positivity of the actual bounded operator, derived from the full beta Gram form. -/
theorem hilbertGibbs_inner_nonneg (f : ThresholdHilbert) :
    0 ≤ inner ℝ f (hilbertGibbs f) := by
  rw [hilbertGibbs_inner_physical, hilbertGibbs_physical]
  exact gibbsAction_pairing_nonneg (hilbertGibbsPhysical_square_summable f)

/-- Equality in the norm contraction forces an actual fixed vector. -/
theorem hilbertGibbs_norm_eq_iff_fixed (f : ThresholdHilbert) :
    ‖hilbertGibbs f‖ = ‖f‖ ↔ hilbertGibbs f = f := by
  constructor
  · intro heq
    have hsq : (∑' n, paretoWeight n * gibbsAction (hilbertGibbsPhysical f) n ^ 2) =
        ∑' n, paretoWeight n * hilbertGibbsPhysical f n ^ 2 := by
      rw [← hilbertGibbs_norm_sq, hilbertGibbsPhysical_norm_sq, heq]
    have hc := (gibbsAction_square_eq_iff_constant
      (hilbertGibbsPhysical_square_summable f)).mp hsq
    have hp := (gibbsAction_fixed_iff_constant
      (hilbertGibbsPhysical_square_summable f)).mpr hc
    apply hilbertSequence_injective
    funext k
    cases k with
    | zero => simp
    | succ n =>
        change hilbertGibbsPhysical (hilbertGibbs f) n = hilbertGibbsPhysical f n
        rw [hilbertGibbs_physical, hp]
  · intro heq
    rw [heq]

theorem hilbertGibbs_norm_eq_iff_constant (f : ThresholdHilbert) :
    ‖hilbertGibbs f‖ = ‖f‖ ↔ ∃ c : ℝ, f = c • hilbertOne := by
  rw [hilbertGibbs_norm_eq_iff_fixed, hilbertGibbs_fixed_iff]

/-- The square has the same fixed space; in particular there is no -1 eigenvector. -/
theorem hilbertGibbs_sq_fixed_iff (f : ThresholdHilbert) :
    hilbertGibbs (hilbertGibbs f) = f ↔ hilbertGibbs f = f := by
  constructor
  · intro hsq
    have h1 := hilbertGibbs_norm_le f
    have h2 := hilbertGibbs_norm_le (hilbertGibbs f)
    rw [hsq] at h2
    exact (hilbertGibbs_norm_eq_iff_fixed f).mp (le_antisymm h1 h2)
  · intro hfix
    simp only [hfix]

theorem hilbertGibbs_norm_lt_of_nonconstant (f : ThresholdHilbert)
    (hf : ¬ ∃ c : ℝ, f = c • hilbertOne) : ‖hilbertGibbs f‖ < ‖f‖ :=
  lt_of_le_of_ne (hilbertGibbs_norm_le f)
    (fun heq => hf ((hilbertGibbs_norm_eq_iff_constant f).mp heq))

end
end RiemannResearch.RH.Pareto
