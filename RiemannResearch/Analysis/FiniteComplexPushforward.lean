import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite complex pushforward preserves full pairings and quadratic forms. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteComplexPushforward
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Finite pushforward; for an embedding, this is extension by zero. -/
def pushforward (e : ι → κ) (c : ι → ℂ) (j : κ) : ℂ :=
  by
    classical
    exact ∑ i, if e i = j then c i else 0

theorem sum_pushforward_mul (e : ι → κ) (c : ι → ℂ) (f : κ → ℂ) :
    (∑ j, pushforward e c j * f j) = ∑ i, c i * f (e i) := by
  classical
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  simp

theorem sum_conj_pushforward_mul (e : ι → κ) (c : ι → ℂ) (f : κ → ℂ) :
    (∑ j, starRingEnd ℂ (pushforward e c j) * f j) =
      ∑ i, starRingEnd ℂ (c i) * f (e i) := by
  classical
  simp only [pushforward, map_sum, apply_ite, map_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  simp

theorem quadratic_pushforward (e : ι → κ) (c : ι → ℂ) (G : κ → κ → ℂ) :
    (∑ j, ∑ k, starRingEnd ℂ (pushforward e c j) *
      pushforward e c k * G j k) =
    ∑ i, ∑ l, starRingEnd ℂ (c i) * c l * G (e i) (e l) := by
  classical
  calc
    _ = ∑ j, starRingEnd ℂ (pushforward e c j) *
        (∑ k, pushforward e c k * G j k) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ j, starRingEnd ℂ (pushforward e c j) *
        (∑ l, c l * G j (e l)) := by
      simp_rw [sum_pushforward_mul]
    _ = ∑ i, starRingEnd ℂ (c i) * (∑ l, c l * G (e i) (e l)) :=
      sum_conj_pushforward_mul e c _
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end RiemannResearch.Analysis.FiniteComplexPushforward
