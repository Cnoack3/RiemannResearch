/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FiniteAffineGramMinimum

/-!
# Minimum energy from Penrose identities

Source: the user's minimum-energy exact-head research agenda, Section 10,
28 October 2026. For C = A G⁻¹ Aᵀ, only C K C = C and symmetry of C K
are needed. These are two defining identities of the Moore-Penrose inverse.

This proves the displayed inverse formula, feasibility, exact remainder,
attainment, and uniqueness for any K with those identities. It does not
define or construct a canonical Moore-Penrose inverse. The separate
correction-space theorem constructs the attained minimum using an ordinary
positive-definite inverse and does not require a pseudoinverse provider.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.FinitePenroseMinimum
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
open RiemannResearch.LinearAlgebra.FiniteAffineGramMinimum
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

def compressed (G : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) : Matrix κ κ ℝ :=
  A * G⁻¹ * A.transpose

def coefficients (G : Matrix ι ι ℝ) (A : Matrix κ ι ℝ)
    (K : Matrix κ κ ℝ) (e : κ → ℝ) : ι → ℝ :=
  G⁻¹.mulVec (A.transpose.mulVec (K.mulVec e))

theorem coefficients_feasible (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ)
    (hCKC : compressed G A * K * compressed G A = compressed G A)
    (hCKsym : (compressed G A * K).transpose = compressed G A * K)
    (c0 : ι → ℝ) :
    A.mulVec (coefficients G A K (A.mulVec c0)) = A.mulVec c0 := by
  let C := compressed G A
  let D := C * K
  change D * C = C at hCKC
  change D.transpose = D at hCKsym
  let e := A.mulVec c0
  let x := coefficients G A K e
  let r := e - D.mulVec e
  have hDpair (u v : κ → ℝ) :
      dotProduct (D.mulVec u) v = dotProduct u (D.mulVec v) := by
    calc
      _ = dotProduct v (D.mulVec u) := dot_comm _ _
      _ = dotProduct (D.transpose.mulVec v) u := dot_transpose D v u
      _ = dotProduct (D.mulVec v) u := by rw [hCKsym]
      _ = _ := dot_comm _ _
  have hquad : dotProduct r (C.mulVec r) = 0 := by
    have hp := hDpair e (C.mulVec r)
    have hDCr : D.mulVec (C.mulVec r) = C.mulVec r := by
      rw [Matrix.mulVec_mulVec, hCKC]
    rw [hDCr] at hp
    change dotProduct (e - D.mulVec e) (C.mulVec r) = 0
    calc
      _ = dotProduct e (C.mulVec r) - dotProduct (D.mulVec e) (C.mulVec r) := by
        simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hp.symm
  have hAt : A.transpose.mulVec r = 0 := by
    by_contra hn
    have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hG.inv).2 hn
    simp only [star_trivial] at hp
    have he : dotProduct r (C.mulVec r) =
        dotProduct (A.transpose.mulVec r) (G⁻¹.mulVec (A.transpose.mulVec r)) := by
      dsimp only [C, compressed]
      simp only [← Matrix.mulVec_mulVec]
      exact dot_transpose A r _
    rw [he] at hquad
    linarith
  have hDe : D.mulVec e = A.mulVec x := by
    dsimp only [D, C, compressed, x, coefficients]
    simp only [← Matrix.mulVec_mulVec]
  have hr : r = A.mulVec (c0 - x) := by
    change e - D.mulVec e = _
    rw [hDe]
    exact ((matrixMap A).map_sub c0 x).symm
  have hrr : dotProduct r r = 0 := by
    calc
      _ = dotProduct r (A.mulVec (c0 - x)) := congrArg (dotProduct r) hr
      _ = dotProduct (A.transpose.mulVec r) (c0 - x) := dot_transpose A r _
      _ = 0 := by rw [hAt]; simp [dotProduct]
  have hr0 : r = 0 := by
    by_contra hn
    have hp := dot_self_pos r hn
    rw [hrr] at hp
    exact lt_irrefl _ hp
  have hfix : D.mulVec e = e := (sub_eq_zero.mp hr0).symm
  rw [hDe] at hfix
  exact hfix

theorem coefficients_normal (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ) (e : κ → ℝ) :
    G.mulVec (coefficients G A K e) = A.transpose.mulVec (K.mulVec e) := by
  unfold coefficients
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G
    ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit), Matrix.one_mulVec]

theorem penrose_identity_minimum (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ)
    (hCKC : compressed G A * K * compressed G A = compressed G A)
    (hCKsym : (compressed G A * K).transpose = compressed G A * K)
    (c0 : ι → ℝ) (e : κ → ℝ) (hc0 : A.mulVec c0 = e) :
    A.mulVec (coefficients G A K e) = e ∧
    energy G (coefficients G A K e) = dotProduct e (K.mulVec e) ∧
    IsLeast {E : ℝ | ∃ c : ι → ℝ, A.mulVec c = e ∧ energy G c = E}
      (dotProduct e (K.mulVec e)) := by
  have hf : A.mulVec (coefficients G A K e) = e := by
    simpa only [hc0] using coefficients_feasible G hG A K hCKC hCKsym c0
  have hn := coefficients_normal G hG A K e
  exact ⟨hf, normal_energy G A K e _ hf hn, normal_isLeast G hG A K e _ hf hn⟩

theorem penrose_identity_completion (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ)
    (hCKC : compressed G A * K * compressed G A = compressed G A)
    (hCKsym : (compressed G A * K).transpose = compressed G A * K)
    (c0 : ι → ℝ) (e : κ → ℝ) (hc0 : A.mulVec c0 = e)
    (c : ι → ℝ) (hc : A.mulVec c = e) :
    energy G c = dotProduct e (K.mulVec e) +
      energy G (c - coefficients G A K e) := by
  have hf := (penrose_identity_minimum G hG A K hCKC hCKsym c0 e hc0).1
  exact normal_completion G hG A K e _ hf (coefficients_normal G hG A K e) c hc

theorem penrose_identity_unique (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (K : Matrix κ κ ℝ)
    (hCKC : compressed G A * K * compressed G A = compressed G A)
    (hCKsym : (compressed G A * K).transpose = compressed G A * K)
    (c0 : ι → ℝ) (e : κ → ℝ) (hc0 : A.mulVec c0 = e)
    (c : ι → ℝ) (hc : A.mulVec c = e)
    (he : energy G c = dotProduct e (K.mulVec e)) :
    c = coefficients G A K e := by
  have hf := (penrose_identity_minimum G hG A K hCKC hCKsym c0 e hc0).1
  exact normal_unique G hG A K e _ hf (coefficients_normal G hG A K e) c hc he

end RiemannResearch.LinearAlgebra.FinitePenroseMinimum
