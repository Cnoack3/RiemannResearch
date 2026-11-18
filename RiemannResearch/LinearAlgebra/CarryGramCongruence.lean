import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.NoncommRing

/-!
# Changing from residue atoms to CRT carries

Source: C. Noack, *Q CRT Carry Gram and Schur Matrices with Zeta Trace
Identities*, October 2026. The columns consist of the original prime atoms
and their prescribed linear combinations minus the composite atoms. This
coefficient calculation works over any field, with any finite block sizes.
-/

noncomputable section
open scoped Matrix
namespace RiemannResearch.LinearAlgebra.CarryGramCongruence
variable {ι κ K : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Field K]

def change (U : Matrix ι κ K) : Matrix (ι ⊕ κ) (ι ⊕ κ) K :=
  Matrix.fromBlocks 1 U 0 (-1)

theorem change_mul_self (U : Matrix ι κ K) : change U * change U = 1 := by
  rw [change, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem det_congr (U : Matrix ι κ K) (G : Matrix (ι ⊕ κ) (ι ⊕ κ) K) :
    ((change U)ᵀ * G * change U).det = G.det := by
  have hdet := congrArg Matrix.det (change_mul_self U)
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc
    _ = G.det * ((change U).det * (change U).det) := by ac_rfl
    _ = _ := by rw [hdet, mul_one]

/-- The transformed inverse is explicit, so the capacity equality retains its target vector. -/
theorem inv_congr (U : Matrix ι κ K) (G : Matrix (ι ⊕ κ) (ι ⊕ κ) K) (hg : IsUnit G.det) :
    ((change U)ᵀ * G * change U)⁻¹ = change U * G⁻¹ * (change U)ᵀ := by
  let T := change U
  have hT : T * T = 1 := change_mul_self U
  have ht : Tᵀ * Tᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using (congrArg Matrix.transpose hT)
  change (Tᵀ * G * T)⁻¹ = T * G⁻¹ * Tᵀ
  apply Matrix.inv_eq_right_inv
  calc
    _ = Tᵀ * G * (T * T) * G⁻¹ * Tᵀ := by simp only [Matrix.mul_assoc]
    _ = Tᵀ * (G * G⁻¹) * Tᵀ := by rw [hT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hg, Matrix.mul_one, ht]

theorem target_energy_invariant (U : Matrix ι κ K) (G : Matrix (ι ⊕ κ) (ι ⊕ κ) K)
    (hg : IsUnit G.det) (b : Matrix (ι ⊕ κ) Unit K) :
    (((change U)ᵀ * b)ᵀ * ((change U)ᵀ * G * change U)⁻¹ * ((change U)ᵀ * b)) =
      bᵀ * G⁻¹ * b := by
  let T := change U
  have hT : T * T = 1 := change_mul_self U
  have ht : Tᵀ * Tᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using (congrArg Matrix.transpose hT)
  rw [inv_congr U G hg, Matrix.transpose_mul, Matrix.transpose_transpose]
  change bᵀ * T * (T * G⁻¹ * Tᵀ) * (Tᵀ * b) = _
  calc
    _ = bᵀ * (T * T) * G⁻¹ * (Tᵀ * Tᵀ) * b := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, ht, Matrix.mul_one, Matrix.mul_one]

end RiemannResearch.LinearAlgebra.CarryGramCongruence
