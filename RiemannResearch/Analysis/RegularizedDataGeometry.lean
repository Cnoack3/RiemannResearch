import RiemannResearch.Analysis.FiniteRegularizedConstraints
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact data geometry of finite quadratic regularization

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The augmented Hilbert projection gives a signed normal pairing and an exact
orthogonal split for simultaneous changes of the physical and observation
targets. Arbitrary dependent observation rows are allowed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.RegularizedDataGeometry
open FiniteHilbertGram FiniteRegularizedConstraints
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem target_sub (f g : H) (t s : κ → ℝ) (ρ : ℝ) :
    target (f - g) (t - s) ρ = target f t ρ - target g s ρ := by
  apply augmented_ext
  · rfl
  · intro j
    change ρ * (t j - s j) = ρ * t j - ρ * s j
    ring

/-- The optimizer is linear in both complete data vectors. -/
theorem coefficients_sub_data {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f g : H) (t s : κ → ℝ) (ρ : ℝ) :
    coefficients hv B (f - g) (t - s) ρ =
      coefficients hv B f t ρ - coefficients hv B g s ρ := by
  unfold coefficients inverseCoeff
  rw [target_sub]
  have he : cross (rows v B ρ) (target f t ρ - target g s ρ) =
      cross (rows v B ρ) (target f t ρ) - cross (rows v B ρ) (target g s ρ) := by
    funext i
    exact inner_sub_right _ _ _
  rw [he, map_sub]

/-- Signed normal pairing against every coefficient direction. -/
theorem normal_pairing {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (c : ι → ℝ) :
    inner ℝ (f - Fintype.linearCombination ℝ v (coefficients hv B f t ρ))
      (Fintype.linearCombination ℝ v c) =
      ρ ^ 2 * ∑ j, (observe B (coefficients hv B f t ρ) j - t j) * observe B c j := by
  have h := residual_orthogonal (rows_independent hv B ρ) (target f t ρ) c
  change inner ℝ (target f t ρ - Fintype.linearCombination ℝ (rows v B ρ)
    (coefficients hv B f t ρ)) (Fintype.linearCombination ℝ (rows v B ρ) c) = 0 at h
  rw [synthesis_rows, synthesis_rows, target, pair_sub, pair_inner] at h
  have he : (∑ j, (ρ * t j - ρ * observe B (coefficients hv B f t ρ) j) *
      (ρ * observe B c j)) =
      -(ρ ^ 2 * ∑ j, (observe B (coefficients hv B f t ρ) j - t j) * observe B c j) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change inner ℝ (f - Fintype.linearCombination ℝ v (coefficients hv B f t ρ))
    (Fintype.linearCombination ℝ v c) + _ = 0 at h
  simp only [Pi.sub_apply] at h
  rw [he] at h
  linarith

/-- The complete data energy splits into response energy and full residual energy. -/
theorem data_energy_split {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    ‖f‖ ^ 2 + ρ ^ 2 * ∑ j, (t j) ^ 2 =
      ‖Fintype.linearCombination ℝ v (coefficients hv B f t ρ)‖ ^ 2 +
      ρ ^ 2 * observationEnergy B (coefficients hv B f t ρ) +
      objective v B f t ρ (coefficients hv B f t ρ) := by
  have h := residual_completion (rows_independent hv B ρ) (target f t ρ) 0
  change ‖target f t ρ - Fintype.linearCombination ℝ (rows v B ρ) 0‖ ^ 2 =
    ‖target f t ρ - Fintype.linearCombination ℝ (rows v B ρ)
      (coefficients hv B f t ρ)‖ ^ 2 +
    ‖Fintype.linearCombination ℝ (rows v B ρ) (0 - coefficients hv B f t ρ)‖ ^ 2 at h
  simp only [map_zero, sub_zero, zero_sub, map_neg, norm_neg] at h
  rw [← objective_eq_augmented, synthesis_rows_norm_sq, target, pair_norm_sq] at h
  simp only [mul_pow, ← Finset.mul_sum] at h
  linarith

/-- Exact joint sensitivity. The remainder is the full optimum for the data difference. -/
theorem data_difference_exact {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f g : H) (t s : κ → ℝ) (ρ : ℝ) :
    ‖f - g‖ ^ 2 + ρ ^ 2 * ∑ j, (t j - s j) ^ 2 =
      ‖Fintype.linearCombination ℝ v
        (coefficients hv B f t ρ - coefficients hv B g s ρ)‖ ^ 2 +
      ρ ^ 2 * observationEnergy B
        (coefficients hv B f t ρ - coefficients hv B g s ρ) +
      objective v B (f - g) (t - s) ρ
        (coefficients hv B f t ρ - coefficients hv B g s ρ) := by
  simpa only [coefficients_sub_data, Pi.sub_apply] using
    data_energy_split hv B (f - g) (t - s) ρ

theorem data_difference_bound {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f g : H) (t s : κ → ℝ) (ρ : ℝ) :
    ‖Fintype.linearCombination ℝ v
      (coefficients hv B f t ρ - coefficients hv B g s ρ)‖ ^ 2 +
      ρ ^ 2 * observationEnergy B
        (coefficients hv B f t ρ - coefficients hv B g s ρ) ≤
      ‖f - g‖ ^ 2 + ρ ^ 2 * ∑ j, (t j - s j) ^ 2 := by
  have h := data_difference_exact hv B f g t s ρ
  have hp := mul_nonneg (sq_nonneg ρ) (mismatchEnergy_nonneg B (t - s)
    (coefficients hv B f t ρ - coefficients hv B g s ρ))
  unfold objective at h
  nlinarith [sq_nonneg ‖(f - g) - Fintype.linearCombination ℝ v
    (coefficients hv B f t ρ - coefficients hv B g s ρ)‖]

/-- Exact preservation of prescribed target data has no hidden projection loss. -/
theorem data_difference_bound_eq_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f g : H) (t s : κ → ℝ) (ρ : ℝ) :
    ‖Fintype.linearCombination ℝ v
      (coefficients hv B f t ρ - coefficients hv B g s ρ)‖ ^ 2 +
      ρ ^ 2 * observationEnergy B
        (coefficients hv B f t ρ - coefficients hv B g s ρ) =
      ‖f - g‖ ^ 2 + ρ ^ 2 * ∑ j, (t j - s j) ^ 2 ↔
    objective v B (f - g) (t - s) ρ
      (coefficients hv B f t ρ - coefficients hv B g s ρ) = 0 := by
  have h := data_difference_exact hv B f g t s ρ
  constructor <;> intro he <;> linarith

end RiemannResearch.Analysis.RegularizedDataGeometry
