import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Dyadic adjoint-defect algebra for the fixed signed RH criterion

Source: user-provided fixed-Gram continuation, Section 7, for the general
adjoint-square identity. The weighted-pair and scalar leakage completions are
deductions developed in the continuation of 6 October 2026.
Bagchi's Pareto-space criterion supplies the application setting:
https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf .

This module proves a real Hilbert-space four-vector identity, the exact
weighted pair defect, and scalar energy implications. The scalar energy
premises remain explicit. It does not construct the actual infinite adjoint,
closed legal-span compression, coefficient limits, or the open cofinal
arithmetic provider. Their paper derivation is recorded in
RH/FixedGramAdjointContinuation20261006.md. These support lemmas must not be
reported as a formal proof of RH or as a verified actual-provider theorem.
-/

set_option autoImplicit false
namespace RiemannResearch.Analysis.DyadicAdjointDefect
theorem completed_square (e h d : ℝ) :
    (4+e) * (23*e^2 + (24*h-13*e)^2 + 144*e*(e-h-d)^2) -
      e * (23*e*(4+e)+(11*e-24*d)^2) =
    4 * (6*(4+e)*h-e*(13+6*e)+6*e*d)^2 := by ring
theorem nonlinear_lower_bound {e h d J : ℝ} (he : 0 < e)
    (hJ : 23*e^2 + (24*h-13*e)^2 + 144*e*(e-h-d)^2 ≤ 24*e*J) :
    23*e*(4+e)+(11*e-24*d)^2 ≤ 24*(4+e)*J := by
  have hp : 0 ≤ 4+e := by linarith
  have hh := mul_le_mul_of_nonneg_left hJ hp
  have hid := completed_square e h d
  have hs := sq_nonneg (6*(4+e)*h-e*(13+6*e)+6*e*d)
  have hb : e * (23*e*(4+e)+(11*e-24*d)^2) ≤ e * (24*(4+e)*J) := by
    nlinarith [hh, hid, hs]
  by_contra hbad
  have hpos := mul_pos he (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith [hpos]
theorem limiting_lower_bound {e h J : ℝ} (he : 0 < e)
    (hJ : 23*e^2 + (24*h-13*e)^2 + 144*e*(e-h)^2 ≤ 24*e*J) :
    e*(23+36*e) ≤ 6*(4+e)*J := by
  have hh := nonlinear_lower_bound (d := 0) he (by simpa using hJ)
  nlinarith [hh]

theorem leakage_completed_square (e z : ℝ) :
    (4-2*e-e^2) *
      (23*e^2*(1-e)+(1-e)*(12*z-11*e)^2+
        36*e*(1-e)*z^2+36*e*(z-e)^2) -
      4*e^2*(1-e)*(23+19*e-27*e^2) =
    4*(3*(4-2*e-e^2)*z-e*(11-8*e))^2 := by ring

theorem leakage_lower_bound {e z J : ℝ} (he : 0 < e) (he1 : e < 1)
    (hJ : 23*e^2*(1-e)+(1-e)*(12*z-11*e)^2+
      36*e*(1-e)*z^2+36*e*(z-e)^2 ≤ 24*e*(1-e)*J) :
    e*(23+19*e-27*e^2) ≤ 6*(4-2*e-e^2)*J := by
  have hd : 0 < 4-2*e-e^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hJ (le_of_lt hd)
  have hid := leakage_completed_square e z
  have hs := sq_nonneg (3*(4-2*e-e^2)*z-e*(11-8*e))
  have hb : (4*e^2*(1-e))*(23+19*e-27*e^2) ≤
      (4*e*(1-e))*(6*(4-2*e-e^2)*J) := by
    nlinarith [hh,hid,hs]
  have hc : 0 < 4*e*(1-e) := by positivity
  by_contra hbad
  have hpos := mul_pos hc (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith [hpos]

theorem weighted_pair_defect (m x y : ℝ) (hm : 0 < m) :
    x^2 / (2*(2*m)*(2*m+1)) + y^2 / (2*(2*m+1)*(2*m+2)) -
      (((m+1)*x+m*y)/(2*(2*m+1)))^2 / (m*(m+1)) =
    (x-y)^2 / (4*(2*m+1)^2) := by
  have h1 : m+1 ≠ 0 := by positivity
  have h2 : 2*m+1 ≠ 0 := by positivity
  have h3 : 2*m+2 ≠ 0 := by positivity
  field_simp
  ring

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem adjoint_square_identity (x u w z : E)
    (hx : inner ℝ x u = inner ℝ x w)
    (hz : inner ℝ x z = inner ℝ u w) :
    inner ℝ x ((14:ℝ) • x - (26:ℝ) • u + (12:ℝ) • z) =
      6*‖u+w-(13/12:ℝ) • x‖^2+(167/24:ℝ)*‖x‖^2 -
        6*‖u‖^2-6*‖w‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  have hu : inner ℝ u x = inner ℝ x u := by exact real_inner_comm _ _
  have hw : inner ℝ w x = inner ℝ x u := by
    calc
      inner ℝ w x = inner ℝ x w := by exact real_inner_comm _ _
      _ = inner ℝ x u := hx.symm
  have huw : inner ℝ w u = inner ℝ u w := by exact real_inner_comm _ _
  simp only [hu, hw, huw, hx, hz]
  ring
end Hilbert

theorem finite_leakage_completed_square (e z d : ℝ) :
    (4-2*e-e^2) *
      (23*e^2*(1-e)+(1-e)*(12*z+24*d-11*e)^2+
        36*e*(1-e)*z^2+36*e*(z-e+4*d)^2) -
      4*e*(1-e)*(e*(23+19*e-27*e^2)-12*e*(12-5*e)*d+288*d^2) =
    4*(3*(4-2*e-e^2)*z-e*(11-8*e)+12*(2-e)*d)^2 := by ring

theorem finite_leakage_lower_bound {e z d J : ℝ} (he : 0 < e) (he1 : e < 1)
    (hJ : 23*e^2*(1-e)+(1-e)*(12*z+24*d-11*e)^2+
      36*e*(1-e)*z^2+36*e*(z-e+4*d)^2 ≤ 24*e*(1-e)*J) :
    e*(23+19*e-27*e^2)-12*e*(12-5*e)*d+288*d^2 ≤
      6*(4-2*e-e^2)*J := by
  have hd : 0 < 4-2*e-e^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hJ (le_of_lt hd)
  have hid := finite_leakage_completed_square e z d
  have hs := sq_nonneg (3*(4-2*e-e^2)*z-e*(11-8*e)+12*(2-e)*d)
  have hb : (4*e*(1-e))*(e*(23+19*e-27*e^2)-12*e*(12-5*e)*d+288*d^2) ≤
      (4*e*(1-e))*(6*(4-2*e-e^2)*J) := by
    nlinarith [hh,hid,hs]
  have hc : 0 < 4*e*(1-e) := by positivity
  by_contra hbad
  have hpos := mul_pos hc (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith [hpos]

theorem zero_of_compensated_upper {e J : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hJ : e*(23+19*e-27*e^2) ≤ 6*(4-2*e-e^2)*J)
    (hc : 24*J ≤ 23*e) : e = 0 := by
  by_contra hne
  have hp : 0 < e := by rcases he.eq_or_lt with h | h; exact False.elim (hne h.symm); exact h
  have hd : 0 < 4-2*e-e^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hc (le_of_lt hd)
  have hpositive := mul_pos (sq_pos_of_ne_zero hne) (show 0 < 122-85*e by linarith)
  nlinarith [hh,hJ,hpositive]

end RiemannResearch.Analysis.DyadicAdjointDefect
