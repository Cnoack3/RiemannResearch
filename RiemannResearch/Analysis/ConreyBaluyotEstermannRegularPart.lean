/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermann
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
/-!
# Exact singular-part separation for Estermann functions

For every unit numerator h modulo K, the complete continued function is
K^(1-u-v) zeta(u) zeta(v) plus a finite Hurwitz remainder. The remainder is
entire along every common complex shift. Thus differences between unit twists
have no singularities, including when the two shifted poles collide.

Source: the finite Hurwitz identity in S. A. C. Baluyot, *On the Zeros of
Riemann's Zeta-function* (2017), equation (3.1.7), pp. 95–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the starting identity. The separation is derived here
by exact character orthogonality, retaining the entire finite remainder.
-/

open Complex Set Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The exact finite remainder after removing the common zeta-product term. -/
def estermannRegularPart {K : ℕ} [NeZero K] (h : ZMod K) (u v : ℂ) : ℂ :=
  (K : ℂ) ^ (-u-v) *
    ∑ a : ZMod K, ∑ b : ZMod K, ZMod.stdAddChar (h*a*b) *
      ((HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u - riemannZeta u) *
       (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle b) v - riemannZeta v))

private theorem sum_character_unit_row {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) (a : ZMod K) :
    (∑ b : ZMod K, ZMod.stdAddChar ((h : ZMod K)*a*b)) =
      if a = 0 then (K : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, ZMod.card]
  · have hha : (h : ZMod K) * a ≠ 0 := by
      intro he
      apply ha
      calc
        a = (↑h⁻¹ : ZMod K) * ((h : ZMod K) * a) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = 0 := by rw [he, mul_zero]
    simpa [ha, AddChar.mulShift, mul_comm, mul_left_comm, mul_assoc] using
      (AddChar.sum_eq_zero_of_ne_one ((ZMod.isPrimitive_stdAddChar K) hha))

/-- Exact separation, including the pointwise continued values at the poles. -/
theorem estermann_eq_zeta_product_add_regular {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) (u v : ℂ) :
    estermann (h : ZMod K) u v =
      (K : ℂ) ^ (1-u-v) * riemannZeta u * riemannZeta v +
        estermannRegularPart (h : ZMod K) u v := by
  classical
  let D (a : ZMod K) (z : ℂ) :=
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) z - riemannZeta z
  let χ (a b : ZMod K) := ZMod.stdAddChar ((h : ZMod K)*a*b)
  have hD (z : ℂ) : D 0 z = 0 := by simp [D, HurwitzZeta.hurwitzZeta_zero]
  have hrow (a : ZMod K) : (∑ b, χ a b) = if a = 0 then (K : ℂ) else 0 :=
    sum_character_unit_row h a
  have hcol (b : ZMod K) : (∑ a, χ a b) = if b = 0 then (K : ℂ) else 0 := by
    simpa only [χ, mul_right_comm (h : ZMod K)] using hrow b
  have hcross₁ : (∑ a, ∑ b, χ a b * (D a u * riemannZeta v)) = 0 := by
    simp only [← Finset.sum_mul, hrow]
    simp [ite_mul, hD]
  have hcross₂ : (∑ a, ∑ b, χ a b * (riemannZeta u * D b v)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol]
    simp [ite_mul, hD]
  have hconstant : (∑ a, ∑ b, χ a b * (riemannZeta u * riemannZeta v)) =
      (K : ℂ) * (riemannZeta u * riemannZeta v) := by
    simp only [← Finset.sum_mul, hrow]
    simp
  have hsum :
      (∑ a : ZMod K, ∑ b : ZMod K, χ a b *
        (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u *
         HurwitzZeta.hurwitzZeta (ZMod.toAddCircle b) v)) =
      (K : ℂ) * (riemannZeta u * riemannZeta v) +
        ∑ a : ZMod K, ∑ b : ZMod K, χ a b * (D a u * D b v) := by
    have he (a b : ZMod K) :
        χ a b * (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle b) v) =
        χ a b * (riemannZeta u * riemannZeta v) +
        χ a b * (D a u * riemannZeta v) +
        χ a b * (riemannZeta u * D b v) +
        χ a b * (D a u * D b v) := by dsimp [D]; ring
    simp_rw [he, Finset.sum_add_distrib, hcross₁, hcross₂, hconstant]
    ring
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hp : (K : ℂ) ^ (1-u-v) = (K : ℂ) ^ (-u-v) * K := by
    rw [show (1-u-v : ℂ) = (-u-v)+1 by ring, Complex.cpow_add _ _ hK, cpow_one]
  rw [estermann_eq_sum_hurwitzZeta, hsum, hp]
  dsimp [estermannRegularPart, χ, D]
  ring

/-- The remainder is entire along every common shift, without exclusions on alpha or beta. -/
theorem analyticAt_estermannRegularPart_shifted {K : ℕ} [NeZero K]
    (h : ZMod K) (α β z : ℂ) :
    AnalyticAt ℂ (fun s => estermannRegularPart h (s+α) (s+β)) z := by
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  apply Differentiable.analyticAt
  intro w
  unfold estermannRegularPart
  apply DifferentiableAt.mul
  · simp only [Complex.cpow_def_of_ne_zero hK]
    fun_prop
  · apply DifferentiableAt.fun_sum
    intro a _
    apply DifferentiableAt.fun_sum
    intro b _
    have hc : DifferentiableAt ℂ (fun _ : ℂ => ZMod.stdAddChar (h*a*b)) w := by
      fun_prop
    have hd (a : ZMod K) (δ : ℂ) : DifferentiableAt ℂ
        (fun s : ℂ => HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) (s+δ) -
          riemannZeta (s+δ)) w := by
      have hd := HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta
        (ZMod.toAddCircle a) 0
      simpa only [HurwitzZeta.hurwitzZeta_zero, Function.comp_def, id_eq] using
        (hd (w+δ)).comp w (differentiableAt_id.add_const δ)
    exact hc.mul ((hd a α).mul (hd b β))

/-- The singular part is independent of the unit numerator, for all complex shifts. -/
theorem analyticAt_estermann_sub_estermann_shifted {K : ℕ} [NeZero K]
    (h k : (ZMod K)ˣ) (α β z : ℂ) :
    AnalyticAt ℂ (fun s => estermann (h : ZMod K) (s+α) (s+β) -
      estermann (k : ZMod K) (s+α) (s+β)) z := by
  have he : (fun s => estermann (h : ZMod K) (s+α) (s+β) -
      estermann (k : ZMod K) (s+α) (s+β)) =
      (fun s => estermannRegularPart (h : ZMod K) (s+α) (s+β) -
        estermannRegularPart (k : ZMod K) (s+α) (s+β)) := by
    funext s
    rw [estermann_eq_zeta_product_add_regular h, estermann_eq_zeta_product_add_regular k]
    ring
  rw [he]
  exact (analyticAt_estermannRegularPart_shifted (h : ZMod K) α β z).sub
    (analyticAt_estermannRegularPart_shifted (k : ZMod K) α β z)
end RiemannResearch.Analysis.ConreyBaluyot
