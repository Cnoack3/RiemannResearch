import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-! Exact signed finite incidence energy.
Source: user-provided Prime_Phases_Agenda_Proof_Attempts.tex, prime-only budget. -/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.SignedIncidence

/-- A finite weighted square energy, with every signed cross term retained. -/
def energy (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, w m * (f m) ^ 2

/-- A finite incidence Gram entry. -/
def kernel (S : Finset ℕ) (w : ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  ∑ m ∈ S, w m * A m p * A m q

/-- The background row, including the finite endpoint. -/
def row (S : Finset ℕ) (w b : ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    (p : ℕ) : ℝ :=
  ∑ m ∈ S, w m * A m p * b m

/-- A complete finite square identity; no positivity or absolute values are used. -/
theorem square_expansion (P : Finset ℕ) (c : ℕ → ℝ)
    (A : ℕ → ℕ → ℝ) (b : ℝ) (m : ℕ) :
    ((∑ p ∈ P, c p * A m p) - b) ^ 2 =
      b ^ 2 + (∑ p ∈ P, ∑ q ∈ P, c p * c q * A m p * A m q)
        - 2 * ∑ p ∈ P, c p * A m p * b := by
  have hquad : (∑ p ∈ P, c p * A m p) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, c p * c q * A m p * A m q := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hlin : (∑ p ∈ P, c p * A m p) * b =
      ∑ p ∈ P, c p * A m p * b := by
    rw [Finset.sum_mul]
  have hlin2 : 2 * (∑ p ∈ P, c p * A m p) * b =
      2 * ∑ p ∈ P, c p * A m p * b := by
    calc
      _ = 2 * ((∑ p ∈ P, c p * A m p) * b) := by ring
      _ = _ := by rw [hlin]
  rw [sub_sq, hquad, hlin2]
  ring

/-- The finite signed budget, including its complete double Gram sum. -/
theorem energy_expansion (S P : Finset ℕ) (w b c : ℕ → ℝ)
    (A : ℕ → ℕ → ℝ) :
    energy S w (fun m => (∑ p ∈ P, c p * A m p) - b m) =
      energy S w b + (∑ p ∈ P, ∑ q ∈ P, c p * c q * kernel S w A p q)
        - 2 * ∑ p ∈ P, c p * row S w b A p := by
  have hpoint (m : ℕ) :
      w m * ((∑ p ∈ P, c p * A m p) - b m) ^ 2 =
        w m * (b m) ^ 2 +
          (∑ p ∈ P, ∑ q ∈ P, c p * c q * (w m * A m p * A m q)) -
          2 * ∑ p ∈ P, c p * (w m * A m p * b m) := by
    rw [square_expansion]
    simp only [mul_sub, mul_add, Finset.mul_sum]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      ring
    · apply Finset.sum_congr rfl
      intro p hp
      ring
  have hquad :
      (∑ m ∈ S, ∑ p ∈ P, ∑ q ∈ P,
        c p * c q * (w m * A m p * A m q)) =
      ∑ p ∈ P, ∑ q ∈ P, c p * c q * kernel S w A p q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_comm]
    simp only [kernel, Finset.mul_sum]
  have hlin :
      (∑ m ∈ S, ∑ p ∈ P, c p * (w m * A m p * b m)) =
      ∑ p ∈ P, c p * row S w b A p := by
    rw [Finset.sum_comm]
    simp only [row, Finset.mul_sum]
  unfold energy
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hquad, hlin]

/-- Signed cross energy over distinct conductors, counting both orientations. -/
def cross (P : Finset ℕ) (c : ℕ → ℝ) (K : ℕ → ℕ → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ P, ∑ q ∈ P.erase p, c p * c q * K p q

/-- Separating the diagonal keeps every distinct-conductor interaction. -/
theorem full_gram_eq_diagonal_add_cross (P : Finset ℕ) (c : ℕ → ℝ)
    (K : ℕ → ℕ → ℝ) :
    (∑ p ∈ P, ∑ q ∈ P, c p * c q * K p q) =
      (∑ p ∈ P, (c p) ^ 2 * K p p) + 2 * cross P c K := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (∑ q ∈ P, c p * c q * K p q) =
      (c p) ^ 2 * K p p + (∑ q ∈ P.erase p, c p * c q * K p q) := by
    rw [← Finset.sum_erase_add P (fun q => c p * c q * K p q) hp]
    ring
  calc
    (∑ p ∈ P, ∑ q ∈ P, c p * c q * K p q) =
        ∑ p ∈ P, ((c p) ^ 2 * K p p +
          (∑ q ∈ P.erase p, c p * c q * K p q)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hpoint p hp
    _ = _ := by rw [Finset.sum_add_distrib]; unfold cross; ring

end RiemannResearch.Analysis.SignedIncidence
