import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact constrained minimum for a positive finite matrix

Source: `ArithmeticVariationalProof.md`, Section 6. The actual inverse maps
are constructed from positive definiteness and surjectivity, rather than
being supplied as hypotheses. This is the matrix form of the previously
formalized finite Hilbert constraint theorem and has the concrete
conditional-residue matrices as its consumer.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def matrixMap (A : Matrix κ ι ℝ) : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) where
  toFun := A.mulVec
  map_add' u v := by
    funext i
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' r u := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem dot_comm (x y : ι → ℝ) : dotProduct x y = dotProduct y x := by
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem dot_transpose (A : Matrix κ ι ℝ) (x : κ → ℝ) (y : ι → ℝ) :
    dotProduct x (A.mulVec y) = dotProduct (A.transpose.mulVec x) y := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dot_self_pos (x : ι → ℝ) (hx : x ≠ 0) : 0 < dotProduct x x := by
  classical
  have hnonneg : 0 ≤ dotProduct x x := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  by_contra hpos
  have hz : dotProduct x x = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
  have he : ∀ i, x i * x i = 0 := by
    intro i
    have hterm : x i * x i ≤ dotProduct x x :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    rw [hz] at hterm
    exact le_antisymm hterm (mul_self_nonneg _)
  apply hx
  funext i
  exact mul_self_eq_zero.mp (he i)

theorem transpose_mulVec_injective_of_surjective (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec) : Function.Injective A.transpose.mulVec := by
  intro x y hxy
  have hz : A.transpose.mulVec (x - y) = 0 := by
    change matrixMap A.transpose (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  obtain ⟨c, hc⟩ := hA (x - y)
  have hdot : dotProduct (x - y) (x - y) = 0 := by
    calc
      _ = dotProduct (x - y) (A.mulVec c) :=
        congrArg (fun z => dotProduct (x - y) z) hc.symm
      _ = dotProduct (A.transpose.mulVec (x - y)) c := dot_transpose A (x - y) c
      _ = 0 := by rw [hz]; simp [dotProduct]
  have he : x - y = 0 := by
    by_contra hne
    have hp := dot_self_pos (x - y) hne
    rw [hdot] at hp
    exact lt_irrefl _ hp
  exact sub_eq_zero.mp he

theorem posDef_mulVec_injective (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    Function.Injective G.mulVec := by
  intro x y hxy
  have hz : G.mulVec (x - y) = 0 := by
    change matrixMap G (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  apply sub_eq_zero.mp
  by_contra hne
  have hp : 0 < dotProduct (x - y) (G.mulVec (x - y)) := by
    simpa only [star_trivial] using (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hne
  rw [hz] at hp
  simp [dotProduct] at hp

def gramEquiv (G : Matrix ι ι ℝ) (hG : G.PosDef) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofInjectiveEndo (matrixMap G) (posDef_mulVec_injective G hG)

def compressedMap (G : Matrix ι ι ℝ) (hG : G.PosDef) (A : Matrix κ ι ℝ) :
    (κ → ℝ) →ₗ[ℝ] (κ → ℝ) :=
  (matrixMap A).comp ((gramEquiv G hG).symm.toLinearMap.comp (matrixMap A.transpose))

/-- This is the actual positive quadratic form `xᵀ A G⁻¹ Aᵀ x`. -/
theorem compressedMap_positive (G : Matrix ι ι ℝ) (hG : G.PosDef) (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec) (x : κ → ℝ) (hx : x ≠ 0) :
    0 < dotProduct x (compressedMap G hG A x) := by
  let y := (gramEquiv G hG).symm (A.transpose.mulVec x)
  have hGy : G.mulVec y = A.transpose.mulVec x := (gramEquiv G hG).apply_symm_apply _
  have hy : y ≠ 0 := by
    intro hy0
    have hx0 : A.transpose.mulVec x = A.transpose.mulVec 0 := by
      rw [← hGy, hy0]
      simp [Matrix.mulVec, dotProduct]
    exact hx (transpose_mulVec_injective_of_surjective A hA hx0)
  have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hy
  have he : dotProduct x (compressedMap G hG A x) = dotProduct y (G.mulVec y) := by
    change dotProduct x (A.mulVec y) = _
    rw [dot_transpose, ← hGy, dot_comm]
  rw [he]
  simpa only [star_trivial] using hp

theorem compressedMap_injective (G : Matrix ι ι ℝ) (hG : G.PosDef) (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec) : Function.Injective (compressedMap G hG A) := by
  intro x y hxy
  have hz : compressedMap G hG A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have he : x - y = 0 := by
    by_contra hne
    have hp := compressedMap_positive G hG A hA (x - y) hne
    rw [hz] at hp
    simp [dotProduct] at hp
  exact sub_eq_zero.mp he

def compressedEquiv (G : Matrix ι ι ℝ) (hG : G.PosDef) (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec) : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ) :=
  LinearEquiv.ofInjectiveEndo (compressedMap G hG A) (compressedMap_injective G hG A hA)

def multiplier (G : Matrix ι ι ℝ) (hG : G.PosDef) (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec) (b : κ → ℝ) : κ → ℝ :=
  (compressedEquiv G hG A hA).symm b

def minimumCoefficients (G : Matrix ι ι ℝ) (hG : G.PosDef) (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec) (b : κ → ℝ) : ι → ℝ :=
  (gramEquiv G hG).symm (A.transpose.mulVec (multiplier G hG A hA b))

theorem minimumCoefficients_constraint (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) :
    A.mulVec (minimumCoefficients G hG A hA b) = b :=
  (compressedEquiv G hG A hA).apply_symm_apply b

theorem minimumCoefficients_normal (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) :
    G.mulVec (minimumCoefficients G hG A hA b) =
      A.transpose.mulVec (multiplier G hG A hA b) :=
  (gramEquiv G hG).apply_symm_apply _

theorem minimumCoefficients_energy (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) :
    dotProduct (minimumCoefficients G hG A hA b)
      (G.mulVec (minimumCoefficients G hG A hA b)) =
      dotProduct b (multiplier G hG A hA b) := by
  rw [minimumCoefficients_normal, dot_comm, ← dot_transpose,
    minimumCoefficients_constraint, dot_comm]

theorem posDef_pairing_comm (G : Matrix ι ι ℝ) (hG : G.PosDef) (x y : ι → ℝ) :
    dotProduct x (G.mulVec y) = dotProduct y (G.mulVec x) := by
  have ht : G.transpose = G := by
    have hH := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).1
    change G.conjTranspose = G at hH
    ext i j
    have h := congrFun (congrFun hH i) j
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using h
  rw [dot_transpose, ht, dot_comm]

/-- Exact constrained completion with all signed mixed terms preserved. -/
theorem minimumCoefficients_completion (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ)
    (c : ι → ℝ) (hc : A.mulVec c = b) :
    dotProduct c (G.mulVec c) =
      dotProduct b (multiplier G hG A hA b) +
        dotProduct (c - minimumCoefficients G hG A hA b)
          (G.mulVec (c - minimumCoefficients G hG A hA b)) := by
  let v := minimumCoefficients G hG A hA b
  have hcross : dotProduct c (G.mulVec v) = dotProduct v (G.mulVec v) := by
    calc
      _ = dotProduct c (A.transpose.mulVec (multiplier G hG A hA b)) :=
        congrArg (fun z => dotProduct c z) (minimumCoefficients_normal G hG A hA b)
      _ = dotProduct (multiplier G hG A hA b) (A.mulVec c) := by
        exact (dot_comm c (A.transpose.mulVec (multiplier G hG A hA b))).trans
          (dot_transpose A (multiplier G hG A hA b) c).symm
      _ = dotProduct b (multiplier G hG A hA b) :=
        (congrArg (fun z => dotProduct (multiplier G hG A hA b) z) hc).trans
          (dot_comm (multiplier G hG A hA b) b)
      _ = dotProduct v (G.mulVec v) := (minimumCoefficients_energy G hG A hA b).symm
  have hsym := posDef_pairing_comm G hG c v
  have hlin : G.mulVec (c - v) = G.mulVec c - G.mulVec v := (matrixMap G).map_sub c v
  have hexpand : dotProduct (c - v) (G.mulVec (c - v)) =
      dotProduct c (G.mulVec c) - dotProduct c (G.mulVec v) -
        dotProduct v (G.mulVec c) + dotProduct v (G.mulVec v) := by
    rw [hlin]
    simp only [dotProduct, Pi.sub_apply, sub_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have he := minimumCoefficients_energy G hG A hA b
  change dotProduct v (G.mulVec v) = _ at he
  change dotProduct c (G.mulVec c) = _ + dotProduct (c - v) (G.mulVec (c - v))
  linarith

/-- Exact attained minimum: `bᵀ (A G⁻¹ Aᵀ)⁻¹ b`. -/
theorem inverseCompressed_isLeast (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) :
    IsLeast {E : ℝ | ∃ c : ι → ℝ, A.mulVec c = b ∧ dotProduct c (G.mulVec c) = E}
      (dotProduct b (multiplier G hG A hA b)) := by
  constructor
  · exact ⟨minimumCoefficients G hG A hA b, minimumCoefficients_constraint G hG A hA b,
      minimumCoefficients_energy G hG A hA b⟩
  · rintro E ⟨c, hc, rfl⟩
    rw [minimumCoefficients_completion G hG A hA b c hc]
    apply le_add_of_nonneg_right
    by_cases hz : c - minimumCoefficients G hG A hA b = 0
    · simp [hz, dotProduct]
    · have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hz
      exact le_of_lt (by simpa only [star_trivial] using hp)

theorem minimumCoefficients_unique (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ)
    (c : ι → ℝ) (hc : A.mulVec c = b)
    (he : dotProduct c (G.mulVec c) = dotProduct b (multiplier G hG A hA b)) :
    c = minimumCoefficients G hG A hA b := by
  by_contra hne
  have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 (sub_ne_zero.mpr hne)
  simp only [star_trivial] at hp
  have h := minimumCoefficients_completion G hG A hA b c hc
  linarith

theorem inverseCompressed_value_pos (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) (hb : b ≠ 0) :
    0 < dotProduct b (multiplier G hG A hA b) := by
  have hc : minimumCoefficients G hG A hA b ≠ 0 := by
    intro hz
    have h := minimumCoefficients_constraint G hG A hA b
    rw [hz] at h
    have hb0 : b = 0 := by simpa [Matrix.mulVec, dotProduct] using h.symm
    exact hb hb0
  have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hc
  simp only [star_trivial] at hp
  rw [minimumCoefficients_energy] at hp
  exact hp

end RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
