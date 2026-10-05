/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.EuclideanOperatorCoordinates
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Euclidean Hilbert--Schmidt certificates

Row Cauchy--Schwarz gives entry-square operator bounds and scalar-envelope
assembly. Concrete consumer: the actual Landau residual in
`LandauHilbertSchmidtResidual.lean`. Proof: independent finite assembly.
-/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix

namespace ContinuousLinearMap

/-- Finite Hilbert--Schmidt entry certificate in the actual Euclidean norm. -/
theorem norm_toEuclideanCLM_le_of_sum_sq_le {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hM : (∑ n, ∑ m, ‖M n m‖ ^ 2) ≤ R ^ 2) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  have hc (n : Fin d) :
      ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) n‖ ^ 2 ≤
        (∑ m : Fin d, ‖M n m‖ ^ 2) * ‖x‖ ^ 2 := by
    have htri :
        ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) n‖ ≤
          ∑ m : Fin d, ‖M n m‖ * ‖x m‖ := by
      change ‖∑ m : Fin d, M n m * x m‖ ≤ _
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun m => M n m * x m)
    have hsum0 : 0 ≤ ∑ m : Fin d, ‖M n m‖ * ‖x m‖ := by positivity
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun m : Fin d => ‖M n m‖) (fun m => ‖x m‖)
    calc
      _ ≤ (∑ m : Fin d, ‖M n m‖ * ‖x m‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hsum0).2 htri
      _ ≤ _ := by simpa only [← EuclideanSpace.norm_sq_eq] using hcs
  have hs : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x‖ ^ 2 ≤
      (R * ‖x‖) ^ 2 := by
    calc
      _ = ∑ n : Fin d,
          ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) n‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ n : Fin d, (∑ m : Fin d, ‖M n m‖ ^ 2) * ‖x‖ ^ 2 :=
        Finset.sum_le_sum (fun n _ => hc n)
      _ = (∑ n, ∑ m, ‖M n m‖ ^ 2) * ‖x‖ ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ R ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hM (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hs

theorem norm_le_of_euclideanEntry_sum_sq_le {d : ℕ}
    (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (R : ℝ) (hR : 0 ≤ R)
    (hA : (∑ n, ∑ m, ‖euclideanEntry A n m‖ ^ 2) ≤ R ^ 2) :
    ‖A‖ ≤ R := by
  have ha : A = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
      (Matrix.of fun n m => euclideanEntry A n m) := by
    apply euclideanEntry_ext
    intro n m
    exact (euclideanEntry_toEuclideanCLM _ n m).symm
  rw [ha]
  exact norm_toEuclideanCLM_le_of_sum_sq_le _ R hR hA

/-- Entrywise scalar domination can be assembled with an HS certificate. -/
theorem norm_toEuclideanCLM_le_scaled_envelope {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (E : Fin d → Fin d → ℝ)
    (K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hE : ∀ n m, 0 ≤ E n m)
    (hM : ∀ n m, ‖M n m‖ ≤ K * E n m)
    (hsq : (∑ n, ∑ m, E n m ^ 2) ≤ R ^ 2) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M‖ ≤ K * R := by
  apply norm_toEuclideanCLM_le_of_sum_sq_le M (K * R) (mul_nonneg hK hR)
  calc
    _ ≤ ∑ n : Fin d, ∑ m : Fin d, (K * E n m) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (hE n m))).2 (hM n m)
    _ = K ^ 2 * (∑ n, ∑ m, E n m ^ 2) := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ K ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

end ContinuousLinearMap
