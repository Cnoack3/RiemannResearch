import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixInverse
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FieldSimp

/-!
# Relative comparison of finite inverse Gram quadratic forms

Source: user-provided trigamma/DPP argument, 21 September 2026.
The proof uses the variational completion of an actual positive matrix inverse.
It retains all mixed terms and has no condition-number hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
variable {ι : Type*} [Fintype ι]

def gramQuadratic (G : Matrix ι ι ℝ) (c : ι → ℝ) : ℝ :=
  dotProduct c (G.mulVec c)

def inverseQuadratic (G : Matrix ι ι ℝ) (hG : G.PosDef) (b : ι → ℝ) : ℝ :=
  dotProduct ((gramEquiv G hG).symm b) b

theorem gramQuadratic_nonneg (G : Matrix ι ι ℝ) (hG : G.PosDef) (c : ι → ℝ) :
    0 ≤ gramQuadratic G c := by
  by_cases hc : c = 0
  · simp [gramQuadratic, hc, dotProduct]
  · exact le_of_lt (by simpa only [gramQuadratic, star_trivial] using
      (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hc)

theorem inverseQuadratic_eq_energy (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (b : ι → ℝ) :
    inverseQuadratic G hG b = gramQuadratic G ((gramEquiv G hG).symm b) := by
  have he : G.mulVec ((gramEquiv G hG).symm b) = b :=
    (gramEquiv G hG).apply_symm_apply b
  simp only [inverseQuadratic, gramQuadratic, he]

theorem inverseQuadratic_nonneg (G : Matrix ι ι ℝ) (hG : G.PosDef) (b : ι → ℝ) :
    0 ≤ inverseQuadratic G hG b := by
  rw [inverseQuadratic_eq_energy]
  exact gramQuadratic_nonneg G hG _

theorem quadratic_objective_le_inverse (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (b c : ι → ℝ) :
    2 * dotProduct c b - gramQuadratic G c ≤ inverseQuadratic G hG b := by
  let x := (gramEquiv G hG).symm b
  have hx : G.mulVec x = b := (gramEquiv G hG).apply_symm_apply b
  have hn := gramQuadratic_nonneg G hG (x - c)
  have hlin : G.mulVec (x - c) = G.mulVec x - G.mulVec c :=
    (matrixMap G).map_sub x c
  have hexpand : gramQuadratic G (x - c) =
      dotProduct x (G.mulVec x) - dotProduct x (G.mulVec c) -
        dotProduct c (G.mulVec x) + gramQuadratic G c := by
    unfold gramQuadratic
    rw [hlin]
    simp only [dotProduct, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hs := posDef_pairing_comm G hG x c
  rw [hx] at hs
  rw [hexpand, hx, hs] at hn
  change 2 * dotProduct c b - gramQuadratic G c ≤ dotProduct x b
  linarith

theorem gramQuadratic_smul (G : Matrix ι ι ℝ) (c : ι → ℝ) (t : ℝ) :
    gramQuadratic G (t • c) = t^2 * gramQuadratic G c := by
  unfold gramQuadratic
  rw [show G.mulVec (t • c) = t • G.mulVec c from (matrixMap G).map_smul t c]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Inversion reverses quadratic-form order. -/
theorem inverseQuadratic_antitone (G H : Matrix ι ι ℝ)
    (hG : G.PosDef) (hH : H.PosDef)
    (hE : ∀ c, gramQuadratic G c ≤ gramQuadratic H c) (b : ι → ℝ) :
    inverseQuadratic H hH b ≤ inverseQuadratic G hG b := by
  have h := quadratic_objective_le_inverse G hG b ((gramEquiv H hH).symm b)
  have he := hE ((gramEquiv H hH).symm b)
  rw [← inverseQuadratic_eq_energy] at he
  change 2 * inverseQuadratic H hH b - _ ≤ _ at h
  linarith

/-- A uniform multiplicative energy comparison survives inversion. -/
theorem inverseQuadratic_relative (G H : Matrix ι ι ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (a : ℝ) (ha : 0 ≤ a)
    (hLower : ∀ c, a * gramQuadratic G c ≤ gramQuadratic H c)
    (hUpper : ∀ c, gramQuadratic H c ≤ gramQuadratic G c) (b : ι → ℝ) :
    a * inverseQuadratic H hH b ≤ inverseQuadratic G hG b ∧
      inverseQuadratic G hG b ≤ inverseQuadratic H hH b := by
  refine ⟨?_, inverseQuadratic_antitone H G hH hG hUpper b⟩
  let x := (gramEquiv H hH).symm b
  have h := quadratic_objective_le_inverse G hG b (a • x)
  have hpair : dotProduct (a • x) b = a * inverseQuadratic H hH b := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rfl
  rw [hpair, gramQuadratic_smul] at h
  have he := mul_le_mul_of_nonneg_left (hLower x) ha
  have hn : gramQuadratic H x = inverseQuadratic H hH b :=
    (inverseQuadratic_eq_energy H hH b).symm
  rw [hn] at he
  nlinarith

theorem inverseQuadratic_eq_matrix_inverse [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (b : ι → ℝ) :
    inverseQuadratic G hG b = dotProduct b (G⁻¹.mulVec b) := by
  rw [inverseQuadratic, gramEquiv_symm_eq_inv_mulVec, dot_comm]

end RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
