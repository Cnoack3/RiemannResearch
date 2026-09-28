import RiemannResearch.Probability.ContinuousProjectionCompression

/-!
# Generating function of actual continuous projection window counts

Source: Hough--Krishnapur--Peres--Virág, Probability Surveys 3 (2006),
Theorem 7. The proof below supplies the continuous-law bridge: weighted
Andréief applied to the actual finite determinant density. No discrete-site
DPP assumption, infinite DPP, or unproved correlation provider is used.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate Classical

namespace ProbabilityTheory.ContinuousProjectionDPP

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ] {n : ℕ}

/-- Number of labels in a measurable window; labels are a.s. distinct under the law. -/
def windowCount (I : Set X) (x : Fin n → X) : ℕ :=
  (Finset.univ.filter (fun i => x i ∈ I)).card

theorem windowCount_le (I : Set X) (x : Fin n → X) : windowCount I x ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n)

theorem measurable_windowCount {I : Set X} (hI : MeasurableSet I) :
    Measurable (windowCount (n := n) I) := by
  have he : windowCount (n := n) I =
      fun x => ∑ i : Fin n, if x i ∈ I then (1 : ℕ) else 0 := by
    funext x
    simp only [windowCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hI.preimage (measurable_pi_apply i))
    measurable_const measurable_const

theorem prod_windowWeight (I : Set X) (x : Fin n → X) (z : ℂ) :
    (∏ i, if x i ∈ I then z else 1) = z ^ windowCount I x := by
  simp [windowCount, ← Finset.prod_filter]

/-- Complex-valued PGF equals the determinant of the actual integrated compression. -/
theorem windowCount_generating_det (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (ψ i t) * ψ j t ∂μ) = if i = j then 1 else 0)
    {I : Set X} (hI : MeasurableSet I) (z : ℂ) :
    (∫ x, z ^ windowCount I x ∂law μ ψ) =
      (1 + (z - 1) • windowCompression μ ψ I).det := by
  let w : X → ℂ := fun t => if t ∈ I then z else 1
  have he (i j : Fin n) :
      (fun t => w t * (conj (ψ i t) * ψ j t)) =
      fun t => conj (ψ i t) * ψ j t +
        (z - 1) * I.indicator (fun t => conj (ψ i t) * ψ j t) t := by
    funext t
    by_cases ht : t ∈ I <;> simp [w, ht] <;> ring
  have hc (i j : Fin n) :
      Integrable (fun t => w t * (conj (ψ i t) * ψ j t)) μ := by
    rw [he]
    exact (integrable_cross_of_memLp ψ hψ i j).add
      (((integrable_cross_of_memLp ψ hψ i j).indicator hI).const_mul _)
  have hmat : ((fun i j => ∫ t, w t * (conj (ψ i t) * ψ j t) ∂μ) : Matrix (Fin n) (Fin n) ℂ) =
      ((1 : Matrix (Fin n) (Fin n) ℂ) + (z - 1) • windowCompression μ ψ I) := by
    ext i j
    rw [he, integral_add (integrable_cross_of_memLp ψ hψ i j)
      (((integrable_cross_of_memLp ψ hψ i j).indicator hI).const_mul _),
      integral_const_mul, integral_indicator hI, ho]
    simp [windowCompression, Matrix.one_apply]
  have hw := integral_weighted_squaredDet ψ w hc
  rw [hmat] at hw
  rw [law, integral_withDensity_eq_integral_toReal_smul₀
    (integrable_density (integrable_squaredDet ψ hψ)).aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (density_nonneg ψ _), Complex.real_smul]
  have heprod : (fun x : Fin n → X => (density ψ x : ℂ) * z ^ windowCount I x) =
      fun x => ((∏ j, w (x j)) * (squaredDet ψ x : ℂ)) / (n.factorial : ℂ) := by
    funext x
    rw [show (∏ j, w (x j)) = z ^ windowCount I x from prod_windowWeight I x z]
    simp only [density, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  rw [heprod, integral_div, hw]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast n.factorial_ne_zero)

/-- Exact Bernoulli-product PGF of the continuous count, with no count-law premise. -/
theorem windowCount_generating_spectral (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (ψ i t) * ψ j t ∂μ) = if i = j then 1 else 0)
    {I : Set X} (hI : MeasurableSet I) (z : ℝ) :
    (∫ x, z ^ windowCount I x ∂law μ ψ) =
      ∏ i, (1 - (windowCompression_isHermitian μ ψ I).eigenvalues i +
        z * (windowCompression_isHermitian μ ψ I).eigenvalues i) := by
  have h := windowCount_generating_det ψ hψ ho hI (z : ℂ)
  rw [(windowCompression_isHermitian μ ψ I).det_one_add_smul_eq_prod_complex] at h
  have he : (∫ x, ((z : ℂ) ^ windowCount I x) ∂law μ ψ) =
      ((∫ x, z ^ windowCount I x ∂law μ ψ : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_pow]
    exact integral_complex_ofReal
  rw [he] at h
  apply Complex.ofReal_injective
  rw [h, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  ring

end ProbabilityTheory.ContinuousProjectionDPP
