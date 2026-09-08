import RiemannResearch.LinearAlgebra.WeightedFiniteProjection
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact finite weighted quotient calculus

Source: user-provided `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 10, equations `eq:conditional-matrix`, `eq:crt-exact-error` and the
compatible finite quotient construction. This module constructs the averaging
map from its actual finite fiber weights, proves its right inverse and tower
law, and obtains exact weighted orthogonality and error decomposition.
No independence of CRT coordinates, uniform weights, or RH input is assumed.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.WeightedFiniteQuotient

noncomputable section

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq κ] [DecidableEq τ]

/-- The actual pushforward weight, with every point of the fiber retained. -/
def pushforward (q : ι → κ) (z : ι → ℝ) (b : κ) : ℝ :=
  ∑ i, if q i = b then z i else 0

/-- Exact weighted conditional averaging along a finite quotient. -/
def average (q : ι → κ) (w x : ι → ℝ) (b : κ) : ℝ :=
  pushforward q (fun i => w i * x i) b / pushforward q w b

/-- Matrix entries of the exact conditional map. -/
def averageMatrix (q : ι → κ) (w : ι → ℝ) : Matrix κ ι ℝ :=
  fun b i => (if q i = b then w i else 0) / pushforward q w b

/-- Repetition of coarse data under quotient reduction. -/
def repeatMatrix (q : ι → κ) : Matrix ι κ ℝ :=
  fun i b => if q i = b then 1 else 0

theorem pushforward_pairing (q : ι → κ) (z : ι → ℝ) (g : κ → ℝ) :
    (∑ b, pushforward q z b * g b) = ∑ i, z i * g (q i) := by
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

theorem pushforward_total (q : ι → κ) (z : ι → ℝ) :
    (∑ b, pushforward q z b) = ∑ i, z i := by
  simpa using pushforward_pairing q z (fun _ => 1)

theorem pushforward_mul_pullback (q : ι → κ) (w : ι → ℝ)
    (g : κ → ℝ) (b : κ) :
    pushforward q (fun i => w i * g (q i)) b = pushforward q w b * g b := by
  unfold pushforward
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i = b <;> simp [h]

theorem pushforward_comp (q : ι → κ) (r : κ → τ) (z : ι → ℝ) :
    pushforward r (pushforward q z) = pushforward (r ∘ q) z := by
  funext c
  calc
    pushforward r (pushforward q z) c =
        ∑ b, pushforward q z b * (if r b = c then 1 else 0) := by
      simp [pushforward, mul_ite]
    _ = ∑ i, z i * (if r (q i) = c then 1 else 0) :=
      pushforward_pairing q z (fun b => if r b = c then 1 else 0)
    _ = pushforward (r ∘ q) z c := by simp [pushforward, mul_ite]

theorem average_mass (q : ι → κ) (w x : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) (b : κ) :
    pushforward q w b * average q w x b =
      pushforward q (fun i => w i * x i) b := by
  unfold average
  field_simp [hW b]

theorem average_pullback (q : ι → κ) (w : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) (g : κ → ℝ) :
    average q w (g ∘ q) = g := by
  funext b
  unfold average
  rw [show (fun i => w i * (g ∘ q) i) = (fun i => w i * g (q i)) from rfl,
    pushforward_mul_pullback]
  field_simp [hW b]

theorem average_preserves_sum (q : ι → κ) (w x : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    (∑ b, pushforward q w b * average q w x b) = ∑ i, w i * x i := by
  simp_rw [average_mass q w x hW]
  exact pushforward_total q (fun i => w i * x i)

/-- Successive weighted averaging equals averaging along the composed quotient.
The denominator is the actual composed pushforward, not a Haar substitute. -/
theorem average_tower (q : ι → κ) (r : κ → τ) (w x : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    average r (pushforward q w) (average q w x) = average (r ∘ q) w x := by
  have hm : (fun b => pushforward q w b * average q w x b) =
      pushforward q (fun i => w i * x i) := by
    funext b
    exact average_mass q w x hW b
  funext c
  change pushforward r (fun b => pushforward q w b * average q w x b) c /
      pushforward r (pushforward q w) c =
    pushforward (r ∘ q) (fun i => w i * x i) c / pushforward (r ∘ q) w c
  rw [hm, pushforward_comp, pushforward_comp]

theorem averageMatrix_apply (q : ι → κ) (w x : ι → ℝ) :
    Matrix.mulVec (averageMatrix q w) x = average q w x := by
  funext b
  simp only [Matrix.mulVec, dotProduct, averageMatrix, average, pushforward,
    div_mul_eq_mul_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i = b <;> simp [h, div_mul_eq_mul_div]

theorem repeatMatrix_apply (q : ι → κ) (g : κ → ℝ) :
    Matrix.mulVec (repeatMatrix q) g = g ∘ q := by
  funext i
  simp [Matrix.mulVec, dotProduct, repeatMatrix]

theorem averaging_after_repetition (q : ι → κ) (w : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) (g : κ → ℝ) :
    Matrix.mulVec (averageMatrix q w) (Matrix.mulVec (repeatMatrix q) g) = g := by
  rw [repeatMatrix_apply, averageMatrix_apply, average_pullback q w hW]

/-- The weighted adjoint relation, with the true quotient masses. -/
theorem weighted_adjoint (q : ι → κ) (w x : ι → ℝ) (g : κ → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    (∑ i, w i * x i * g (q i)) =
      ∑ b, pushforward q w b * average q w x b * g b := by
  simp_rw [average_mass q w x hW]
  exact (pushforward_pairing q (fun i => w i * x i) g).symm

theorem pullback_energy (q : ι → κ) (w : ι → ℝ) (g : κ → ℝ) :
    (∑ i, w i * g (q i) ^ 2) = ∑ b, pushforward q w b * g b ^ 2 := by
  exact (pushforward_pairing q w (fun b => g b ^ 2)).symm

/-- The actual residual is orthogonal to every coarse test vector. -/
theorem residual_orthogonal (q : ι → κ) (w x : ι → ℝ) (g : κ → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    (∑ i, w i * (x i - average q w x (q i)) * g (q i)) = 0 := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [weighted_adjoint q w x g hW]
  have h := pushforward_pairing q w (fun b => average q w x b * g b)
  simp only [mul_assoc] at h ⊢
  rw [h]
  exact sub_self _

/-- Exact fine error = unresolved fiber error + coarse error. -/
theorem error_decomposition (q : ι → κ) (w x : ι → ℝ) (g : κ → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    (∑ i, w i * (x i - g (q i)) ^ 2) =
      (∑ i, w i * (x i - average q w x (q i)) ^ 2) +
      ∑ b, pushforward q w b * (average q w x b - g b) ^ 2 := by
  have h := RiemannResearch.RH.CombinedAudited.weighted_pythagorean
    (Finset.univ : Finset ι) w
    (fun i => x i - average q w x (q i))
    (fun i => average q w x (q i) - g (q i))
    (residual_orthogonal q w x (fun b => average q w x b - g b) hW)
  simp only [sub_add_sub_cancel] at h
  rw [pullback_energy q w (fun b => average q w x b - g b)] at h
  exact h

end
end RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
