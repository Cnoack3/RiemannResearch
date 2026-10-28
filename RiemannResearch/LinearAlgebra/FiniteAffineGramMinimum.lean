/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixInverse
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Minimum energy on a finite affine correction space

Source: the user's minimum-energy exact-head research agenda, Section 10,
28 October 2026. This is finite-dimensional real Gram algebra.

The correction columns are independent and span the constraint kernel.
The head rows need not be independent. The exact signed Schur term and
positive quadratic remainder are retained. Empty correction index types
are permitted. No stage-uniform energy estimate is assumed or proved.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.FiniteAffineGramMinimum
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def energy (G : Matrix ι ι ℝ) (c : ι → ℝ) : ℝ := dotProduct c (G.mulVec c)
def correctionGram (G : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) : Matrix κ κ ℝ :=
  B.transpose * G * B
def correctionSource (G : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (c0 : ι → ℝ) : κ → ℝ := B.transpose.mulVec (G.mulVec c0)
theorem energy_nonneg (G : Matrix ι ι ℝ) (hG : G.PosDef) (c : ι → ℝ) :
    0 ≤ energy G c := by
  by_cases hc : c = 0
  · simp [energy, hc, dotProduct]
  · have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hc
    exact le_of_lt (by simpa only [star_trivial, energy] using h)

theorem energy_eq_zero_iff (G : Matrix ι ι ℝ) (hG : G.PosDef) (c : ι → ℝ) :
    energy G c = 0 ↔ c = 0 := by
  constructor
  · intro he
    by_contra hc
    have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hc
    have hp' : 0 < energy G c := by simpa only [star_trivial, energy] using hp
    linarith
  · rintro rfl
    simp [energy, dotProduct]

theorem quadratic_add (G : Matrix ι ι ℝ) (hG : G.PosDef) (x y : ι → ℝ) :
    energy G (x + y) = energy G x + 2 * dotProduct x (G.mulVec y) + energy G y := by
  have hlin : G.mulVec (x + y) = G.mulVec x + G.mulVec y :=
    (matrixMap G).map_add x y
  have hs := posDef_pairing_comm G hG x y
  unfold energy
  rw [hlin]
  simp only [dotProduct, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib] at *
  linarith

theorem pullback_dot (B : Matrix ι κ ℝ) (x : κ → ℝ) (y : ι → ℝ) :
    dotProduct (B.mulVec x) y = dotProduct x (B.transpose.mulVec y) := by
  calc
    _ = dotProduct y (B.mulVec x) := dot_comm _ _
    _ = dotProduct (B.transpose.mulVec y) x := dot_transpose B y x
    _ = _ := dot_comm _ _

theorem correction_energy (G : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (z : κ → ℝ) :
    energy G (B.mulVec z) = energy (correctionGram G B) z := by
  unfold energy
  rw [pullback_dot]
  simp only [correctionGram, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem correctionGram_posDef (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec) :
    (correctionGram G B).PosDef := by
  have hp : (B.conjTranspose * G * B).PosDef :=
    hG.conjTranspose_mul_mul_same hB
  have ht : B.conjTranspose = B.transpose := by ext i j; rfl
  simpa only [ht, correctionGram] using hp


theorem normal_energy (G : Matrix ι ι ℝ) (A : Matrix κ ι ℝ)
    (K : Matrix κ κ ℝ) (e : κ → ℝ) (cStar : ι → ℝ)
    (hfeas : A.mulVec cStar = e)
    (hnormal : G.mulVec cStar = A.transpose.mulVec (K.mulVec e)) :
    energy G cStar = dotProduct e (K.mulVec e) := by
  unfold energy
  rw [hnormal, dot_comm, ← dot_transpose, hfeas, dot_comm]

/-- A feasible normal-equation solution has the full quadratic remainder. -/
theorem normal_completion (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ) (e : κ → ℝ)
    (cStar : ι → ℝ) (hfeas : A.mulVec cStar = e)
    (hnormal : G.mulVec cStar = A.transpose.mulVec (K.mulVec e))
    (c : ι → ℝ) (hc : A.mulVec c = e) :
    energy G c = dotProduct e (K.mulVec e) + energy G (c - cStar) := by
  have he := normal_energy G A K e cStar hfeas hnormal
  have hcross : dotProduct c (G.mulVec cStar) = energy G cStar := by
    calc
      _ = dotProduct c (A.transpose.mulVec (K.mulVec e)) :=
        congrArg (fun z => dotProduct c z) hnormal
      _ = dotProduct (K.mulVec e) (A.mulVec c) :=
        (dot_comm _ _).trans (dot_transpose A (K.mulVec e) c).symm
      _ = dotProduct e (K.mulVec e) := by rw [hc, dot_comm]
      _ = energy G cStar := he.symm
  have hsym := posDef_pairing_comm G hG c cStar
  have hlin : G.mulVec (c - cStar) = G.mulVec c - G.mulVec cStar :=
    (matrixMap G).map_sub c cStar
  have hd : energy G (c - cStar) = energy G c -
      dotProduct c (G.mulVec cStar) - dotProduct cStar (G.mulVec c) +
        energy G cStar := by
    unfold energy
    rw [hlin]
    simp only [dotProduct, Pi.sub_apply, sub_mul, mul_sub,
      Finset.sum_sub_distrib]
    ring
  linarith

theorem normal_isLeast (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ) (e : κ → ℝ)
    (cStar : ι → ℝ) (hfeas : A.mulVec cStar = e)
    (hnormal : G.mulVec cStar = A.transpose.mulVec (K.mulVec e)) :
    IsLeast {E : ℝ | ∃ c : ι → ℝ, A.mulVec c = e ∧ energy G c = E}
      (dotProduct e (K.mulVec e)) := by
  constructor
  · exact ⟨cStar, hfeas, normal_energy G A K e cStar hfeas hnormal⟩
  · rintro E ⟨c, hc, rfl⟩
    rw [normal_completion G hG A K e cStar hfeas hnormal c hc]
    exact le_add_of_nonneg_right (energy_nonneg G hG _)

theorem normal_unique (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ) (e : κ → ℝ)
    (cStar : ι → ℝ) (hfeas : A.mulVec cStar = e)
    (hnormal : G.mulVec cStar = A.transpose.mulVec (K.mulVec e))
    (c : ι → ℝ) (hc : A.mulVec c = e)
    (he : energy G c = dotProduct e (K.mulVec e)) : c = cStar := by
  have ht := normal_completion G hG A K e cStar hfeas hnormal c hc
  have hz : energy G (c - cStar) = 0 := by linarith
  exact sub_eq_zero.mp ((energy_eq_zero_iff G hG _).mp hz)

variable [DecidableEq κ]

def correctionCoeff (G : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (c0 : ι → ℝ) : κ → ℝ :=
  (correctionGram G B)⁻¹.mulVec (correctionSource G B c0)
def corrected (G : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (c0 : ι → ℝ) : ι → ℝ := c0 - B.mulVec (correctionCoeff G B c0)

theorem correctionCoeff_normal (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec) (c0 : ι → ℝ) :
    (correctionGram G B).mulVec (correctionCoeff G B c0) =
      correctionSource G B c0 := by
  unfold correctionCoeff
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (correctionGram G B)
    ((Matrix.isUnit_iff_isUnit_det _).mp (correctionGram_posDef G hG B hB).isUnit),
    Matrix.one_mulVec]

/-- Exact signed completion on the entire affine correction space. -/
theorem correction_completion (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec)
    (c0 : ι → ℝ) (z : κ → ℝ) :
    energy G (c0 + B.mulVec z) =
      energy G c0 - dotProduct (correctionSource G B c0) (correctionCoeff G B c0) +
        energy (correctionGram G B) (z + correctionCoeff G B c0) := by
  let S := correctionGram G B
  let b := correctionSource G B c0
  let u := correctionCoeff G B c0
  have hS : S.PosDef := correctionGram_posDef G hG B hB
  have hn : S.mulVec u = b := correctionCoeff_normal G hG B hB c0
  have hc : dotProduct c0 (G.mulVec (B.mulVec z)) = dotProduct z b := by
    calc
      _ = dotProduct (B.mulVec z) (G.mulVec c0) := posDef_pairing_comm G hG _ _
      _ = _ := pullback_dot B z (G.mulVec c0)
  have ha : energy G (c0 + B.mulVec z) =
      energy G c0 + 2 * dotProduct z b + energy S z := by
    rw [quadratic_add G hG, hc, correction_energy]
  have he := quadratic_add S hS z u
  have hu : energy S u = dotProduct b u := by
    unfold energy
    rw [hn, dot_comm]
  rw [hn, hu] at he
  change energy G (c0 + B.mulVec z) = energy G c0 - dotProduct b u + energy S (z + u)
  linarith

theorem corrected_energy (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec) (c0 : ι → ℝ) :
    energy G (corrected G B c0) =
      energy G c0 - dotProduct (correctionSource G B c0) (correctionCoeff G B c0) := by
  let u := correctionCoeff G B c0
  have he := correction_completion G hG B hB c0 (-u)
  have hbneg : B.mulVec (-u) = -B.mulVec u := (matrixMap B).map_neg u
  have hz : energy (correctionGram G B) (0 : κ → ℝ) = 0 := by
    simp [energy, dotProduct]
  change energy G (c0 + B.mulVec (-u)) =
    energy G c0 - dotProduct (correctionSource G B c0) u +
      energy (correctionGram G B) (-u + u) at he
  rw [hbneg, ← sub_eq_add_neg, neg_add_cancel, hz, add_zero] at he
  exact he

theorem corrected_minimizes (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec)
    (c0 : ι → ℝ) (z : κ → ℝ) :
    energy G (corrected G B c0) ≤ energy G (c0 + B.mulVec z) := by
  rw [corrected_energy G hG B hB c0, correction_completion G hG B hB]
  exact le_add_of_nonneg_right
    (energy_nonneg _ (correctionGram_posDef G hG B hB) _)

theorem correction_minimizer_unique (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec)
    (c0 : ι → ℝ) (z : κ → ℝ)
    (he : energy G (c0 + B.mulVec z) = energy G (corrected G B c0)) :
    z = -correctionCoeff G B c0 := by
  rw [correction_completion G hG B hB, corrected_energy G hG B hB] at he
  have hz : energy (correctionGram G B) (z + correctionCoeff G B c0) = 0 := by
    linarith
  have hv := (energy_eq_zero_iff _ (correctionGram_posDef G hG B hB) _).mp hz
  have h := congrArg (fun t : κ → ℝ => t - correctionCoeff G B c0) hv
  simpa only [add_sub_cancel_right, zero_sub] using h

variable {ν : Type*}

theorem corrected_constraint (G : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (A : Matrix ν ι ℝ)
    (hker : LinearMap.range (matrixMap B) = LinearMap.ker (matrixMap A))
    (c0 : ι → ℝ) (e : ν → ℝ) (hc0 : A.mulVec c0 = e) :
    A.mulVec (corrected G B c0) = e := by
  have hm : B.mulVec (correctionCoeff G B c0) ∈ LinearMap.range (matrixMap B) :=
    ⟨correctionCoeff G B c0, rfl⟩
  rw [hker] at hm
  change A.mulVec (B.mulVec (correctionCoeff G B c0)) = 0 at hm
  change matrixMap A (c0 - B.mulVec (correctionCoeff G B c0)) = e
  rw [map_sub]
  change A.mulVec c0 - A.mulVec (B.mulVec (correctionCoeff G B c0)) = e
  rw [hc0, hm, sub_zero]

/-- The literal inverse-Gram value is attained under arbitrary feasible
linear constraints; no row-rank assumption is needed. -/
theorem feasible_isLeast (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec)
    (A : Matrix ν ι ℝ)
    (hker : LinearMap.range (matrixMap B) = LinearMap.ker (matrixMap A))
    (c0 : ι → ℝ) (e : ν → ℝ) (hc0 : A.mulVec c0 = e) :
    IsLeast {E : ℝ | ∃ c : ι → ℝ, A.mulVec c = e ∧ energy G c = E}
      (energy G c0 - dotProduct (correctionSource G B c0) (correctionCoeff G B c0)) := by
  constructor
  · exact ⟨corrected G B c0, corrected_constraint G B A hker c0 e hc0,
      corrected_energy G hG B hB c0⟩
  · rintro E ⟨c, hc, rfl⟩
    have hz : matrixMap A (c - c0) = 0 := by
      rw [map_sub]
      change A.mulVec c - A.mulVec c0 = 0
      rw [hc, hc0, sub_self]
    have hm : c - c0 ∈ LinearMap.ker (matrixMap A) := hz
    rw [← hker] at hm
    obtain ⟨z, hz⟩ := hm
    change B.mulVec z = c - c0 at hz
    have he : c = c0 + B.mulVec z := by rw [hz]; abel
    rw [← corrected_energy G hG B hB c0, he]
    exact corrected_minimizes G hG B hB c0 z

theorem feasible_unique (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (B : Matrix ι κ ℝ) (hB : Function.Injective B.mulVec)
    (A : Matrix ν ι ℝ)
    (hker : LinearMap.range (matrixMap B) = LinearMap.ker (matrixMap A))
    (c0 c : ι → ℝ) (e : ν → ℝ) (hc0 : A.mulVec c0 = e)
    (hc : A.mulVec c = e)
    (he : energy G c = energy G (corrected G B c0)) :
    c = corrected G B c0 := by
  have hz : matrixMap A (c - c0) = 0 := by
    rw [map_sub]
    change A.mulVec c - A.mulVec c0 = 0
    rw [hc, hc0, sub_self]
  have hm : c - c0 ∈ LinearMap.ker (matrixMap A) := hz
  rw [← hker] at hm
  obtain ⟨z, hz⟩ := hm
  change B.mulVec z = c - c0 at hz
  have hr : c = c0 + B.mulVec z := by rw [hz]; abel
  have hzmin : z = -correctionCoeff G B c0 :=
    correction_minimizer_unique G hG B hB c0 z (by rw [← hr]; exact he)
  rw [hr, hzmin]
  have hn : B.mulVec (-correctionCoeff G B c0) =
      -B.mulVec (correctionCoeff G B c0) := (matrixMap B).map_neg _
  rw [hn]
  rfl

end RiemannResearch.LinearAlgebra.FiniteAffineGramMinimum
