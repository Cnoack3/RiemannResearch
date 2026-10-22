import RiemannResearch.Probability.DeterminantalConfiguration
import RiemannResearch.RH.IntegerDPPCardinality
import RiemannResearch.RH.IntegerDPPArithmeticExclusion

/-!
# Exact arithmetic factorization of full DPP configurations

Source: the user-provided residue DPP and independent-lift argument. The
normalized kernel depends only on residue features. Every finite correlation,
and every full N-point configuration probability, therefore factors into a
residue determinant and the product of its exact Pareto weights. This proves
joint lift-weight factorization without assuming a conditional lift law.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP

/-- The counting kernel with both square-root Pareto factors removed. -/
def normalizedIntegerKernel (n i j : ℕ) : ℝ :=
  integerKernel n i j / Real.sqrt (paretoWeight i) / Real.sqrt (paretoWeight j)

theorem normalizedIntegerKernel_symmetric (n i j : ℕ) :
    normalizedIntegerKernel n i j = normalizedIntegerKernel n j i := by
  have hs : integerKernel n i j = integerKernel n j i := real_inner_comm _ _
  unfold normalizedIntegerKernel
  rw [hs]
  ring

theorem normalizedIntegerKernel_residue_congr_right (n i j k : ℕ)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2)) :
    normalizedIntegerKernel n k i = normalizedIntegerKernel n k j := by
  have hi : Real.sqrt (paretoWeight i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos i))
  have hj : Real.sqrt (paretoWeight j) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos j))
  have hd : integerKernel n k i / Real.sqrt (paretoWeight i) =
      integerKernel n k j / Real.sqrt (paretoWeight j) := by
    apply (div_eq_div_iff hi hj).mpr
    simpa only [mul_comm] using integerKernel_weighted_residue_congr n i j k hres
  calc
    _ = (integerKernel n k i / Real.sqrt (paretoWeight i)) /
        Real.sqrt (paretoWeight k) := by unfold normalizedIntegerKernel; ring
    _ = (integerKernel n k j / Real.sqrt (paretoWeight j)) /
        Real.sqrt (paretoWeight k) := by rw [hd]
    _ = _ := by unfold normalizedIntegerKernel; ring

theorem normalizedIntegerKernel_residue_congr (n i i' j j' : ℕ)
    (hi : ∀ d : Fin n, (i + 1) % (d.val + 2) = (i' + 1) % (d.val + 2))
    (hj : ∀ d : Fin n, (j + 1) % (d.val + 2) = (j' + 1) % (d.val + 2)) :
    normalizedIntegerKernel n i j = normalizedIntegerKernel n i' j' := by
  calc
    _ = normalizedIntegerKernel n j i := normalizedIntegerKernel_symmetric n i j
    _ = normalizedIntegerKernel n j i' := normalizedIntegerKernel_residue_congr_right n i i' j hi
    _ = normalizedIntegerKernel n i' j := normalizedIntegerKernel_symmetric n j i'
    _ = _ := normalizedIntegerKernel_residue_congr_right n j j' i' hj

/-- The determinant of the arithmetic counting kernel factors into the product
of Pareto weights and a determinant depending only on the residue features. -/
theorem integerKernel_principal_det_weight_factorization (n m : ℕ) (e : Fin m → ℕ) :
    Matrix.det (Matrix.of (fun i j => integerKernel n (e i) (e j))) =
      (∏ i, paretoWeight (e i)) *
        Matrix.det (Matrix.of (fun i j => normalizedIntegerKernel n (e i) (e j))) := by
  let a : Fin m → ℝ := fun i => Real.sqrt (paretoWeight (e i))
  let B : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of (fun i j => normalizedIntegerKernel n (e i) (e j))
  have hm : Matrix.of (fun i j => integerKernel n (e i) (e j)) =
      Matrix.diagonal a * B * Matrix.diagonal a := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, B,
      normalizedIntegerKernel, a]
    have hi : Real.sqrt (paretoWeight (e i)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos (e i)))
    have hj : Real.sqrt (paretoWeight (e j)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos (e j)))
    field_simp
  have hp : (∏ i, a i) * (∏ i, a i) = ∏ i, paretoWeight (e i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.mul_self_sqrt (paretoWeight_pos (e i)).le
  rw [hm]
  simp only [Matrix.det_mul, Matrix.det_diagonal]
  calc
    _ = ((∏ i, a i) * (∏ i, a i)) * B.det := by ring
    _ = _ := by rw [hp]

/-- Residue-preserving substitutions change every finite correlation exactly
by the product of their Pareto-weight ratios. -/
theorem integerKernel_principal_det_residue_substitution (n m : ℕ)
    (e f : Fin m → ℕ)
    (hres : ∀ i, ∀ d : Fin n,
      (e i + 1) % (d.val + 2) = (f i + 1) % (d.val + 2)) :
    (∏ i, paretoWeight (f i)) *
        Matrix.det (Matrix.of (fun i j => integerKernel n (e i) (e j))) =
      (∏ i, paretoWeight (e i)) *
        Matrix.det (Matrix.of (fun i j => integerKernel n (f i) (f j))) := by
  have he : Matrix.of (fun i j => normalizedIntegerKernel n (e i) (e j)) =
      Matrix.of (fun i j => normalizedIntegerKernel n (f i) (f j)) := by
    ext i j
    exact normalizedIntegerKernel_residue_congr n (e i) (f i) (e j) (f j)
      (hres i) (hres j)
  rw [integerKernel_principal_det_weight_factorization,
    integerKernel_principal_det_weight_factorization, he]
  ring

/-- The actual N-point probability, using the checked cardinality theorem. -/
theorem integerLaw_full_configuration (n : ℕ) (e : Fin n ↪ ℕ) :
    (integerLaw n).real {x | {i | x i = true} = Set.range e} =
      Matrix.det (Matrix.of (fun i j => integerKernel n (e i) (e j))) :=
  (integerLaw_isDPP n).full_configuration_of_setCount n (integerLaw_cardinality n) e

theorem integerLaw_full_configuration_weight_factorization (n : ℕ) (e : Fin n ↪ ℕ) :
    (integerLaw n).real {x | {i | x i = true} = Set.range e} =
      (∏ i, paretoWeight (e i)) *
        Matrix.det (Matrix.of (fun i j => normalizedIntegerKernel n (e i) (e j))) := by
  rw [integerLaw_full_configuration, integerKernel_principal_det_weight_factorization]

/-- Joint factorization for all N occupied lifts, not just one-site marginals. -/
theorem integerLaw_full_configuration_residue_substitution (n : ℕ)
    (e f : Fin n ↪ ℕ)
    (hres : ∀ i, ∀ d : Fin n,
      (e i + 1) % (d.val + 2) = (f i + 1) % (d.val + 2)) :
    (∏ i, paretoWeight (f i)) *
        (integerLaw n).real {x | {j | x j = true} = Set.range e} =
      (∏ i, paretoWeight (e i)) *
        (integerLaw n).real {x | {j | x j = true} = Set.range f} := by
  rw [integerLaw_full_configuration, integerLaw_full_configuration]
  exact integerKernel_principal_det_residue_substitution n n e f hres

/-- The normalized full-configuration mass is identical for every choice of
integer lifts of the same labelled residue classes. -/
theorem integerLaw_full_configuration_per_weight_residue_congr (n : ℕ)
    (e f : Fin n ↪ ℕ)
    (hres : ∀ i, ∀ d : Fin n,
      (e i + 1) % (d.val + 2) = (f i + 1) % (d.val + 2)) :
    (integerLaw n).real {x | {j | x j = true} = Set.range e} /
        (∏ i, paretoWeight (e i)) =
      (integerLaw n).real {x | {j | x j = true} = Set.range f} /
        (∏ i, paretoWeight (f i)) := by
  have he : (∏ i, paretoWeight (e i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => ne_of_gt (paretoWeight_pos (e i)))
  have hf : (∏ i, paretoWeight (f i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => ne_of_gt (paretoWeight_pos (f i)))
  apply (div_eq_div_iff he hf).mpr
  simpa only [mul_comm] using integerLaw_full_configuration_residue_substitution n e f hres

/-- Common-conductor versions have no per-generator residue hypothesis left. -/
theorem integerLaw_full_configuration_common_conductor (n L : ℕ)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (e f : Fin n ↪ ℕ)
    (hmod : ∀ i, (e i + 1) % L = (f i + 1) % L) :
    (integerLaw n).real {x | {j | x j = true} = Set.range e} /
        (∏ i, paretoWeight (e i)) =
      (integerLaw n).real {x | {j | x j = true} = Set.range f} /
        (∏ i, paretoWeight (f i)) := by
  apply integerLaw_full_configuration_per_weight_residue_congr n e f
  intro i d
  have hh := congrArg (fun k : ℕ => k % (d.val + 2)) (hmod i)
  simpa only [Nat.mod_mod_of_dvd (e i + 1) (hL d),
    Nat.mod_mod_of_dvd (f i + 1) (hL d)] using hh

end RiemannResearch.RH.Pareto.IntegerDPP
