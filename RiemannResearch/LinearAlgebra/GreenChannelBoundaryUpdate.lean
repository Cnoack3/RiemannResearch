import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
/-!
# Exact Green channel updates and boundary migration

Source: user-provided argument in
`RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`, section 6, and
`window_growth_agent.md`, sections 2--3. These support the statements and
block-elimination strategy. All identities below are proved for actual finite
matrices. The Schur update is established by multiplication; Woodbury includes
a right-inverse certificate and a proof of determinant nonsingularity.

The inverse hypotheses are ordinary finite-dimensional nonsingularity
conditions. No signed Weil positivity or arithmetic comparison is assumed or
concluded. The symmetric specialization displays both the screened coefficient
and the residualized channel. The final rational example verifies that total
energy can fall from 1 to 2/3 while the boundary term rises from 0 to 1/6.
-/

namespace RiemannResearch.LinearAlgebra.GreenChannelBoundary

open Matrix
section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
/-- Exact right-inverse certificate for the finite Woodbury update. -/
theorem woodbury_solve (A Ai : Matrix m m ℝ) (U : Matrix m n ℝ) (V : Matrix n m ℝ)
 (L Li K : Matrix n n ℝ) (hA : A * Ai = 1) (hL : L * Li = 1)
 (hK : (Li + V * Ai * U) * K = 1) :
 (A + U * L * V) * (Ai - Ai * U * K * V * Ai) = 1 := by
 have hk : K + L * V * Ai * U * K = L := by
   have hh := congrArg (fun X => L * X) hK
   simpa only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hL, one_mul, mul_one] using hh
 have hh := congrArg (fun X => U * X * V * Ai) hk
 have he : U * K * V * Ai + U * L * V * Ai * U * K * V * Ai = U * L * V * Ai := by
   simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using hh
 simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc, ← Matrix.mul_assoc A Ai, hA, one_mul]
 simp only [Matrix.mul_assoc] at he
 rw [he]
 abel
end


section
variable {m n b : Type*} [Fintype m] [Fintype n] [Fintype b]
 [DecidableEq m] [DecidableEq n] [DecidableEq b]

omit [Fintype b] [DecidableEq m] [DecidableEq b] in
/-- The updated cross block uses the residualized channel. -/
theorem screened_cross (Ai : Matrix m m ℝ) (U : Matrix m n ℝ) (V : Matrix n m ℝ)
 (D : Matrix b m ℝ) (W : Matrix b n ℝ)
 (L Li K : Matrix n n ℝ) (hL : L * Li = 1)
 (hK : (Li + V * Ai * U) * K = 1) :
 (D + W * L * V) * (Ai - Ai * U * K * V * Ai) =
 D * Ai + (W - D * Ai * U) * K * V * Ai := by
 have hk : K + L * V * Ai * U * K = L := by
   have hh := congrArg (fun X => L * X) hK
   simpa only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hL, one_mul, mul_one] using hh
 have hh := congrArg (fun X => W * X * V * Ai) hk
 simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] at hh
 simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
 rw [← hh]
 abel

omit [Fintype b] [DecidableEq m] [DecidableEq b] in
/-- Block elimination of the update with both inverse relations retained. -/
theorem screened_schur (Ai : Matrix m m ℝ) (U : Matrix m n ℝ) (V : Matrix n m ℝ)
 (D : Matrix b m ℝ) (B : Matrix m b ℝ) (C : Matrix b b ℝ)
 (W : Matrix b n ℝ) (Z : Matrix n b ℝ)
 (L Li K : Matrix n n ℝ) (hL : L * Li = 1) (hL' : Li * L = 1)
 (hK : (Li + V * Ai * U) * K = 1) (hK' : K * (Li + V * Ai * U) = 1) :
 C + W * L * Z -
   (D + W * L * V) * (Ai - Ai * U * K * V * Ai) * (B + U * L * Z) =
 (C - D * Ai * B) + (W - D * Ai * U) * K * (Z - V * Ai * B) := by
 rw [screened_cross Ai U V D W L Li K hL hK]
 have hk : K + K * V * Ai * U * L = L := by
   have hh := congrArg (fun X => X * L) hK'
   simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hL', one_mul, mul_one] using hh
 have hh := congrArg (fun X => (W - D * Ai * U) * X * Z) hk
 simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] at hh ⊢
 rw [(sub_eq_iff_eq_add.mp hh.symm)]
 abel

/-- The certificate determines the actual nonsingular matrix inverse. -/
theorem woodbury_inverse (A : Matrix m m ℝ) (U : Matrix m n ℝ)
 (V : Matrix n m ℝ) (L : Matrix n n ℝ)
 (hA : IsUnit A.det) (hL : IsUnit L.det)
 (hK : IsUnit (L⁻¹ + V * A⁻¹ * U).det) :
 (A + U * L * V)⁻¹ =
 A⁻¹ - A⁻¹ * U * (L⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
 apply Matrix.inv_eq_right_inv
 exact woodbury_solve A A⁻¹ U V L L⁻¹ _ (Matrix.mul_nonsing_inv A hA)
   (Matrix.mul_nonsing_inv L hL) (Matrix.mul_nonsing_inv _ hK)

end
section
variable {m b : Type*} [Fintype m] [Fintype b] [DecidableEq m] [DecidableEq b]
/-- Exact interior/boundary decomposition of the actual inverse energy. -/
theorem gluing (A : Matrix m m ℝ) (B : Matrix m b ℝ) (C : Matrix b b ℝ)
 [Invertible A] [Invertible (C - Bᵀ * ⅟A * B)]
 (hAs : (⅟A)ᵀ = ⅟A) (x : m → ℝ) (y : b → ℝ) :
 let η := y - (Bᵀ * ⅟A) *ᵥ x
 (Sum.elim x y) ⬝ᵥ (fromBlocks A B Bᵀ C)⁻¹ *ᵥ (Sum.elim x y) =
 x ⬝ᵥ (⅟A) *ᵥ x + η ⬝ᵥ (⅟(C - Bᵀ * ⅟A * B)) *ᵥ η := by
 let := Matrix.fromBlocks₁₁Invertible A B Bᵀ C
 have hd (v : b → ℝ) : x ⬝ᵥ (⅟A * B) *ᵥ v = ((Bᵀ * ⅟A) *ᵥ x) ⬝ᵥ v := by
   simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hAs, dotProduct_comm] using
     (Matrix.dotProduct_transpose_mulVec (Bᵀ * ⅟A) x v)
 have hs (z : m → ℝ) (w : b → ℝ) :
   Sum.elim x y ⬝ᵥ Sum.elim z w = x ⬝ᵥ z + y ⬝ᵥ w := by
   simp [dotProduct, Fintype.sum_sum_type]
 dsimp
 rw [← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq, Matrix.fromBlocks_mulVec, hs]
 simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.add_mulVec, Matrix.neg_mulVec,
   Matrix.mulVec_sub, dotProduct_add, dotProduct_neg, dotProduct_sub, sub_dotProduct]
 simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
 rw [show ⅟A *ᵥ (B *ᵥ ((⅟(C - Bᵀ * ⅟A * B)) *ᵥ (Bᵀ *ᵥ ((⅟A) *ᵥ x)))) =
    (⅟A * B) *ᵥ ((⅟(C - Bᵀ * ⅟A * B)) *ᵥ ((Bᵀ * ⅟A) *ᵥ x)) by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]]
 rw [show ⅟A *ᵥ (B *ᵥ ((⅟(C - Bᵀ * ⅟A * B)) *ᵥ y)) =
    (⅟A * B) *ᵥ ((⅟(C - Bᵀ * ⅟A * B)) *ᵥ y) by rw [Matrix.mulVec_mulVec]]
 rw [hd, hd]
 simp only [← Matrix.mulVec_mulVec]
 ring
end

section
variable {m n b : Type*} [Fintype m] [Fintype n] [Fintype b]
 [DecidableEq m] [DecidableEq n] [DecidableEq b]
omit [Fintype b] [DecidableEq b] in
/-- General rectangular-channel update of the actual Schur complement. -/
theorem schur_update_inverse (A : Matrix m m ℝ) (U : Matrix m n ℝ) (V : Matrix n m ℝ)
 (D : Matrix b m ℝ) (B : Matrix m b ℝ) (C : Matrix b b ℝ)
 (W : Matrix b n ℝ) (Z : Matrix n b ℝ) (L : Matrix n n ℝ)
 (hA : IsUnit A.det) (hL : IsUnit L.det)
 (hK : IsUnit (L⁻¹ + V * A⁻¹ * U).det) :
 C + W * L * Z -
   (D + W * L * V) * (A + U * L * V)⁻¹ * (B + U * L * Z) =
 (C - D * A⁻¹ * B) + (W - D * A⁻¹ * U) *
   (L⁻¹ + V * A⁻¹ * U)⁻¹ * (Z - V * A⁻¹ * B) := by
 rw [woodbury_inverse A U V L hA hL hK]
 exact screened_schur A⁻¹ U V D B C W Z L L⁻¹ _
   (Matrix.mul_nonsing_inv L hL) (Matrix.nonsing_inv_mul L hL)
   (Matrix.mul_nonsing_inv _ hK) (Matrix.nonsing_inv_mul _ hK)

omit [Fintype b] [DecidableEq b] in
/-- The boundary signal migrates by the screened interior correlation. -/
theorem innovation_update (A : Matrix m m ℝ) (U : Matrix m n ℝ)
 (V : Matrix n m ℝ) (D : Matrix b m ℝ) (W : Matrix b n ℝ)
 (L : Matrix n n ℝ) (x : m → ℝ) (y : b → ℝ)
 (hA : IsUnit A.det) (hL : IsUnit L.det)
 (hK : IsUnit (L⁻¹ + V * A⁻¹ * U).det) :
 y - ((D + W * L * V) * (A + U * L * V)⁻¹) *ᵥ x =
 (y - (D * A⁻¹) *ᵥ x) -
 ((W - D * A⁻¹ * U) * (L⁻¹ + V * A⁻¹ * U)⁻¹) *ᵥ ((V * A⁻¹) *ᵥ x) := by
 rw [woodbury_inverse A U V L hA hL hK,
   screened_cross A⁻¹ U V D W L L⁻¹ _
    (Matrix.mul_nonsing_inv L hL) (Matrix.mul_nonsing_inv _ hK)]
 simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
 abel

/-- Exact matrix expression for the change in inverse energy. -/
theorem inverse_energy_drop (A : Matrix m m ℝ) (U : Matrix m n ℝ)
 (V : Matrix n m ℝ) (L : Matrix n n ℝ) (x : m → ℝ)
 (hA : IsUnit A.det) (hL : IsUnit L.det)
 (hK : IsUnit (L⁻¹ + V * A⁻¹ * U).det) :
 x ⬝ᵥ A⁻¹ *ᵥ x - x ⬝ᵥ (A + U * L * V)⁻¹ *ᵥ x =
 x ⬝ᵥ (A⁻¹ * U * (L⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹) *ᵥ x := by
 rw [woodbury_inverse A U V L hA hL hK, Matrix.sub_mulVec, dotProduct_sub]
 ring
end

section
variable {m b : Type*} [Fintype m] [Fintype b] [DecidableEq m] [DecidableEq b]
/-- The boundary-energy change is the interior improvement minus the total
improvement, deduced from the two actual inverse block energies. -/
theorem boundary_migration
 (A A' : Matrix m m ℝ) (B B' : Matrix m b ℝ) (C C' : Matrix b b ℝ)
 [Invertible A] [Invertible A']
 [Invertible (C - Bᵀ * ⅟A * B)] [Invertible (C' - B'ᵀ * ⅟A' * B')]
 (hAs : (⅟A)ᵀ = ⅟A) (hAs' : (⅟A')ᵀ = ⅟A')
 (x : m → ℝ) (y : b → ℝ) :
 let d := Sum.elim x y
 let eta := y - (Bᵀ * ⅟A) *ᵥ x
 let eta' := y - (B'ᵀ * ⅟A') *ᵥ x
 eta' ⬝ᵥ (⅟(C' - B'ᵀ * ⅟A' * B')) *ᵥ eta' -
   eta ⬝ᵥ (⅟(C - Bᵀ * ⅟A * B)) *ᵥ eta =
 (x ⬝ᵥ (⅟A) *ᵥ x - x ⬝ᵥ (⅟A') *ᵥ x) -
   (d ⬝ᵥ (fromBlocks A B Bᵀ C)⁻¹ *ᵥ d -
    d ⬝ᵥ (fromBlocks A' B' B'ᵀ C')⁻¹ *ᵥ d) := by
 have h := gluing A B C hAs x y
 have h' := gluing A' B' C' hAs' x y
 dsimp at h h' ⊢
 rw [h,h']
 ring
end

section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
/-- The constructed Woodbury solution proves actual nonsingularity. -/
theorem update_nonsingular (A : Matrix m m ℝ) (U : Matrix m n ℝ)
 (V : Matrix n m ℝ) (L : Matrix n n ℝ)
 (hA : IsUnit A.det) (hL : IsUnit L.det)
 (hK : IsUnit (L⁻¹ + V * A⁻¹ * U).det) :
 IsUnit (A + U * L * V).det := by
 apply isUnit_iff_ne_zero.mpr
 intro hz
 have h := congrArg Matrix.det (woodbury_solve A A⁻¹ U V L L⁻¹
   (L⁻¹ + V * A⁻¹ * U)⁻¹ (Matrix.mul_nonsing_inv A hA)
   (Matrix.mul_nonsing_inv L hL) (Matrix.mul_nonsing_inv _ hK))
 rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at h
 norm_num at h
end

section
variable {m n b : Type*} [Fintype m] [Fintype n] [Fintype b]
 [DecidableEq m] [DecidableEq n] [DecidableEq b]
/-- Symmetric channel form of the screened Schur identity, with the actual
updated off-diagonal block and the transposed residualized channel. -/
theorem symmetric_schur_update (A : Matrix m m ℝ) (B : Matrix m b ℝ)
 (C : Matrix b b ℝ) (U : Matrix m n ℝ) (W : Matrix b n ℝ)
 (L : Matrix n n ℝ) (hAs : (A⁻¹)ᵀ = A⁻¹) (hLs : Lᵀ = L)
 (hA : IsUnit A.det) (hL : IsUnit L.det)
 (hK : IsUnit (L⁻¹ + Uᵀ * A⁻¹ * U).det) :
 C + W * L * Wᵀ -
   (B + U * L * Wᵀ)ᵀ * (A + U * L * Uᵀ)⁻¹ * (B + U * L * Wᵀ) =
 (C - Bᵀ * A⁻¹ * B) + (W - Bᵀ * A⁻¹ * U) *
   (L⁻¹ + Uᵀ * A⁻¹ * U)⁻¹ * (W - Bᵀ * A⁻¹ * U)ᵀ := by
 simpa only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
   Matrix.transpose_transpose, hAs, hLs, Matrix.mul_assoc] using
   schur_update_inverse A U Uᵀ Bᵀ B C W Wᵀ L hA hL hK
end

section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
/-- In symmetric coordinates the exact inverse-energy drop is the screened
quadratic energy of the channel correlation. -/
theorem symmetric_inverse_energy_drop (A : Matrix m m ℝ) (U : Matrix m n ℝ)
 (L : Matrix n n ℝ) (x : m → ℝ) (hAs : (A⁻¹)ᵀ = A⁻¹)
 (hA : IsUnit A.det) (hL : IsUnit L.det)
 (hK : IsUnit (L⁻¹ + Uᵀ * A⁻¹ * U).det) :
 let alpha := (Uᵀ * A⁻¹) *ᵥ x
 x ⬝ᵥ A⁻¹ *ᵥ x - x ⬝ᵥ (A + U * L * Uᵀ)⁻¹ *ᵥ x =
 alpha ⬝ᵥ (L⁻¹ + Uᵀ * A⁻¹ * U)⁻¹ *ᵥ alpha := by
 have hd (v : n → ℝ) : x ⬝ᵥ (A⁻¹ * U) *ᵥ v = ((Uᵀ * A⁻¹) *ᵥ x) ⬝ᵥ v := by
   simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hAs, dotProduct_comm] using
     (Matrix.dotProduct_transpose_mulVec (Uᵀ * A⁻¹) x v)
 dsimp
 rw [inverse_energy_drop A U Uᵀ L x hA hL hK]
 let K := (L⁻¹ + Uᵀ * A⁻¹ * U)⁻¹
 change x ⬝ᵥ (A⁻¹ * U * K * Uᵀ * A⁻¹) *ᵥ x = _
 rw [show A⁻¹ * U * K * Uᵀ * A⁻¹ = (A⁻¹ * U) * K * (Uᵀ * A⁻¹) by
   simp only [Matrix.mul_assoc]]
 rw [← Matrix.mulVec_mulVec x ((A⁻¹ * U) * K) (Uᵀ * A⁻¹),
   ← Matrix.mulVec_mulVec ((Uᵀ * A⁻¹) *ᵥ x) (A⁻¹ * U) K, hd]
end

namespace MigrationExample
def original : Matrix (Fin 2) (Fin 2) ℚ := 1
def channel : Matrix (Fin 2) (Fin 1) ℚ := fun _ _ => 1
def updated : Matrix (Fin 2) (Fin 2) ℚ := original + channel * channelᵀ
def signal : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0
noncomputable def total (G : Matrix (Fin 2) (Fin 2) ℚ) : ℚ := signal ⬝ᵥ G⁻¹ *ᵥ signal
def boundary (G : Matrix (Fin 2) (Fin 2) ℚ) : ℚ :=
 (signal 1 - G 1 0 / G 0 0 * signal 0)^2 / (G 1 1 - G 1 0 / G 0 0 * G 0 1)
theorem updated_entries : updated = (fun i j => if i = j then 2 else 1) := by
 ext i j
 fin_cases i <;> fin_cases j <;> norm_num [updated, original, channel, Matrix.mul_apply]
theorem updated_inverse : updated⁻¹ = (fun i j => if i = j then (2:ℚ)/3 else -1/3) := by
 apply Matrix.inv_eq_right_inv
 ext i j
 change (∑ k : Fin 2, updated i k * (if k = j then (2:ℚ)/3 else -1/3)) = _
 rw [Fin.sum_univ_two, updated_entries]
 fin_cases i <;> fin_cases j <;> norm_num
theorem exact_migration :
 total original = 1 ∧ total updated = 2/3 ∧ boundary original = 0 ∧ boundary updated = 1/6 := by
 unfold total
 rw [updated_inverse]
 norm_num [boundary, signal, original, updated_entries,
   Matrix.mulVec, dotProduct, Fin.sum_univ_two]
end MigrationExample

end RiemannResearch.LinearAlgebra.GreenChannelBoundary
