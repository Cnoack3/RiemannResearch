/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Probability.Independence.Basic

/-! Lossless infinite prime-exponent matrices with independent random rows. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RiemannResearch.Probability.PrimeExponentMatrix

/-- Columns are all natural numbers; the nonprime columns vanish automatically. -/
def row (n : ℕ) : ℕ → ℕ := n.factorization

def matrix {ι : Type*} (N : ι → ℕ) : ι → ℕ → ℕ := fun i => row (N i)

theorem row_finite_support (n : ℕ) : (Function.support (row n)).Finite :=
  n.factorization.finite_support

/-- Unique factorization reconstructs every nonzero integer exactly. -/
theorem reconstruct (n : ℕ) (hn : n ≠ 0) :
    (n.factorization.prod fun p e => p ^ e) = n := Nat.factorization_prod_pow_eq_self hn

theorem row_injective_nonzero {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (h : row n = row m) : n = m := by
  have he : n.factorization = m.factorization := Finsupp.ext (congrFun h)
  have hp := congrArg (fun f : ℕ →₀ ℕ => f.prod (fun p e => p ^ e)) he
  simpa only [reconstruct n hn, reconstruct m hm] using hp

theorem row_nonzero {n : ℕ} (hn : 2 ≤ n) : row n ≠ 0 := by
  intro h
  have he : n.factorization = 0 := Finsupp.ext (congrFun h)
  have hp := reconstruct n (by omega)
  rw [he] at hp
  simp only [Finsupp.prod_zero_index] at hp
  omega

/-- The whole matrix is a lossless encoding when none of the integers is zero. -/
theorem matrix_injective {ι : Type*} {N M : ι → ℕ}
    (hN : ∀ i, N i ≠ 0) (hM : ∀ i, M i ≠ 0) (h : matrix N = matrix M) : N = M := by
  funext i
  exact row_injective_nonzero (hN i) (hM i) (congrFun h i)

/-- Multiplication of integers is addition of their exponent rows. -/
theorem row_mul (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    row (n * m) = row n + row m := by
  funext p
  simp only [row, Nat.factorization_mul hn hm, Finsupp.coe_add, Pi.add_apply]

theorem row_measurable : Measurable row := measurable_of_countable _

theorem matrix_coordinate_measurable {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ → Ω → ℕ) (hN : ∀ i, Measurable (N i)) (i p : ℕ) :
    Measurable (fun ω => row (N i ω) p) :=
  (measurable_pi_apply p).comp (row_measurable.comp (hN i))

/-- Independence of sampled integers gives actual independence of the full row vectors. -/
theorem independent_rows {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ι → Ω → ℕ) (hN : iIndepFun N μ) :
    iIndepFun (fun i ω => row (N i ω)) μ :=
  hN.comp (fun _ => row) (fun _ => row_measurable)

/-- All infinitely many rows are simultaneously finite and nonzero almost surely. -/
theorem ae_valid_rows {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ → Ω → ℕ) (hN : ∀ i, ∀ᵐ ω ∂μ, 2 ≤ N i ω) :
    ∀ᵐ ω ∂μ, ∀ i, (Function.support (row (N i ω))).Finite ∧ row (N i ω) ≠ 0 := by
  have h := ae_all_iff.mpr hN
  filter_upwards [h] with ω hω
  intro i
  exact ⟨row_finite_support _, row_nonzero (hω i)⟩

end RiemannResearch.Probability.PrimeExponentMatrix
