import RiemannResearch.Probability.ConditionalIIDWeightedEnergy
import RiemannResearch.Analysis.CesaroWeightedContraction
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The actual H domain and the exact convex combination of weighted errors

Source: user-provided conditional-iid manuscript, Sections 3 and 6.
The countable marginal measure converts weighted square summability to genuine
`MemLp` on the constructed probability space. In particular, all physical
`ThresholdHilbert` vectors satisfy the moment hypotheses; no boundedness or
unproved probabilistic input is added.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID
open RH.ArithmeticCumulative RH.Pareto Analysis.Cesaro

/-- Weighted summability is sufficient for the actual coordinate second moment. -/
theorem coordinate_memLp_two_of_weighted_square_summable (F : ℕ → ℝ)
    (hF : Summable (fun n => weight n * F n ^ 2)) (i : ℕ) :
    MemLp (fun ω => F (coordinate i ω)) 2 probability := by
  let μ : Measure ℕ := Measure.map (coordinate i) probability
  have hi : ∀ n : ℕ, IntegrableOn (fun m => F m ^ 2) ({n} : Set ℕ) μ := by
    intro n
    simpa only [Finset.coe_singleton] using
      (IntegrableOn.finset (μ := μ) (f := fun m => F m ^ 2) (s := {n}))
  have he (n : ℕ) : (∫ m in ({n} : Set ℕ), ‖F m ^ 2‖ ∂μ) =
      weight n * F n ^ 2 := by
    calc
      _ = μ.real {n} • ‖F n ^ 2‖ := by
        simpa only [Finset.coe_singleton, Finset.sum_singleton] using
          (setIntegral_finset ({n} : Finset ℕ)
            (IntegrableOn.finset (μ := μ) (f := fun m => ‖F m ^ 2‖) (s := {n})))
      _ = _ := by
        rw [smul_eq_mul, show μ.real {n} = weight n from coordinate_real_singleton i n,
          Real.norm_of_nonneg (sq_nonneg _)]
  have hs : Summable (fun n : ℕ => ∫ m in ({n} : Set ℕ), ‖F m ^ 2‖ ∂μ) := by
    simpa only [he] using hF
  have hglobal : Integrable (fun n => F n ^ 2) μ := by
    have h := integrableOn_iUnion_of_summable_integral_norm hi hs
    have hu : (⋃ n : ℕ, ({n} : Set ℕ)) = Set.univ := by ext n; simp
    rw [hu] at h
    simpa only [integrableOn_univ] using h
  have hm : MemLp F 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_of_countable F).stronglyMeasurable.aestronglyMeasurable).2 hglobal
  exact hm.comp_measurePreserving
    ⟨coordinate_measurable i, rfl⟩

/-- Every vector of the actual weighted Hilbert space meets the global L² hypotheses. -/
theorem hilbertSequence_coordinate_memLp_two (f : ThresholdHilbert) (i : ℕ) :
    MemLp (fun ω => hilbertSequence f (coordinate i ω)) 2 probability := by
  apply coordinate_memLp_two_of_weighted_square_summable
  exact hilbertSequence_square_summable f

/-- The marginal moment is exactly the physical H norm. -/
theorem hilbertSequence_coordinate_square_integral (f : ThresholdHilbert) (i : ℕ) :
    (∫ ω, hilbertSequence f (coordinate i ω) ^ 2 ∂probability) = ‖f‖ ^ 2 := by
  rw [coordinate_integral i (fun n => hilbertSequence f n ^ 2)
    (hilbertSequence_coordinate_memLp_two f i).integrable_sq]
  exact (hilbert_norm_weighted_sq f).symm

/-- The complete convex combination of the full and smoothed weighted squared errors. -/
theorem average_error_weighted_convex_combination (F : ℕ → ℝ) (r : ℕ)
    (hr : 0 < r) (c : ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    (∫ ω : Omega, (c - pathAverage F r ω.2) ^ 2 ∂probability) =
      (1 / (r : ℝ)) * (∑' n : ℕ, weight n * (c - F n) ^ 2) +
      (1 - 1 / (r : ℝ)) *
        (∑' k : ℕ, mixtureWeight (k + 1) * (c - cesaro F (k + 1)) ^ 2) := by
  have h1 := average_error_weighted F 1 (by omega) c hF
  simp only [pathAverage_apply, Finset.sum_range_one, Nat.cast_one, inv_one,
    one_mul, div_one] at h1
  rw [coordinate_integral 0 (fun n => (c - F n) ^ 2)
    ((memLp_const c).sub hF).integrable_sq] at h1
  rw [average_error_weighted F r hr c hF]
  rw [h1]
  ring

/-- The manuscript's full formula holds for every actual H vector. -/
theorem hilbertSequence_average_error_convex_combination (f : ThresholdHilbert)
    (r : ℕ) (hr : 0 < r) (c : ℝ) :
    (∫ ω : Omega, (c - pathAverage (hilbertSequence f) r ω.2) ^ 2 ∂probability) =
      (1 / (r : ℝ)) * (∑' n : ℕ, weight n * (c - hilbertSequence f n) ^ 2) +
      (1 - 1 / (r : ℝ)) * (∑' k : ℕ, mixtureWeight (k + 1) *
        (c - cesaro (hilbertSequence f) (k + 1)) ^ 2) :=
  average_error_weighted_convex_combination (hilbertSequence f) r hr c
    (hilbertSequence_coordinate_memLp_two f 0)

/-- At target zero the two weighted energies are the two genuine Hilbert norms. -/
theorem hilbertSequence_average_square_norm_identity (f : ThresholdHilbert)
    (r : ℕ) (hr : 0 < r) :
    (∫ ω : Omega, pathAverage (hilbertSequence f) r ω.2 ^ 2 ∂probability) =
      (1 / (r : ℝ)) * ‖f‖ ^ 2 +
      (1 - 1 / (r : ℝ)) * ‖cesaroOperator f‖ ^ 2 := by
  have h := hilbertSequence_average_error_convex_combination f r hr 0
  simp only [zero_sub, neg_sq] at h
  have hfull : (∑' n : ℕ, weight n * hilbertSequence f n ^ 2) = ‖f‖ ^ 2 :=
    (hilbert_norm_weighted_sq f).symm
  rw [hfull, ← hilbertCesaro_norm_sq f] at h
  exact h

end RiemannResearch.Probability.ConditionalIID
