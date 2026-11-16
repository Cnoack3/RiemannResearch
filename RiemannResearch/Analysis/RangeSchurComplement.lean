import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Schur positivity with a range solution

Source: user-provided `v_prime_side_factorization_A_F_audited.pdf`,
Theorem 11.6. The square-completion argument is classical.
This version does not require an inverse or a uniform positive lower bound
for the auxiliary operator: a solution of `D (S x) = C x` suffices.
The RH consumer is the proposed auxiliary-sector Weil factorization.
-/

namespace RiemannResearch.Analysis.RangeSchurComplement

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

def blockEnergy (B : H → H) (C : H → K) (D : K →ₗ[ℝ] K)
    (x : H) (y : K) : ℝ :=
  inner ℝ x (B x) + 2 * inner ℝ (C x) y + inner ℝ y (D y)

def reducedEnergy (B : H → H) (C S : H → K) (x : H) : ℝ :=
  inner ℝ x (B x) - inner ℝ (C x) (S x)

theorem complete_square (B : H → H) (C S : H → K) (D : K →ₗ[ℝ] K)
    (hD : ∀ u v, inner ℝ u (D v) = inner ℝ (D u) v)
    (hS : ∀ x, D (S x) = C x) (x : H) (y : K) :
    blockEnergy B C D x y =
      reducedEnergy B C S x + inner ℝ (y + S x) (D (y + S x)) := by
  simp only [blockEnergy, reducedEnergy, map_add, inner_add_left, inner_add_right, hS]
  rw [hD (S x) y, hS]
  rw [real_inner_comm y (C x), real_inner_comm (S x) (C x)]
  ring

theorem minimizing_value (B : H → H) (C S : H → K) (D : K →ₗ[ℝ] K)
    (hD : ∀ u v, inner ℝ u (D v) = inner ℝ (D u) v)
    (hS : ∀ x, D (S x) = C x) (x : H) :
    blockEnergy B C D x (-S x) = reducedEnergy B C S x := by
  rw [complete_square B C S D hD hS]
  simp

theorem reduced_le_block (B : H → H) (C S : H → K) (D : K →ₗ[ℝ] K)
    (hD : ∀ u v, inner ℝ u (D v) = inner ℝ (D u) v)
    (hS : ∀ x, D (S x) = C x)
    (hpos : ∀ y, 0 ≤ inner ℝ y (D y)) (x : H) (y : K) :
    reducedEnergy B C S x ≤ blockEnergy B C D x y := by
  rw [complete_square B C S D hD hS]
  exact le_add_of_nonneg_right (hpos _)

/-- A positive auxiliary block cannot conceal a negative Schur direction.
This remains true for singular auxiliary operators with a range solution. -/
theorem block_nonneg_iff (B : H → H) (C S : H → K) (D : K →ₗ[ℝ] K)
    (hD : ∀ u v, inner ℝ u (D v) = inner ℝ (D u) v)
    (hS : ∀ x, D (S x) = C x)
    (hpos : ∀ y, 0 ≤ inner ℝ y (D y)) :
    (∀ x y, 0 ≤ blockEnergy B C D x y) ↔
      ∀ x, 0 ≤ reducedEnergy B C S x := by
  constructor
  · intro h x
    have hx := h x (-S x)
    rwa [minimizing_value B C S D hD hS x] at hx
  · intro h x y
    exact (h x).trans (reduced_le_block B C S D hD hS hpos x y)

end RiemannResearch.Analysis.RangeSchurComplement
