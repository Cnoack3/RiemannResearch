import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# All-degree prime-local formal logarithm and exponential

Source: V_vector_space_RH.pdf, Section 1. The derivative argument follows
Mathlib/RingTheory/PowerSeries/Log.lean (Ralf Stephan, Apache 2.0), adapted to
the pinned mathlib version. All coefficients and inverse identities are formal;
no convergence or zero-ordinate assertion is assumed.

The prime-indexed equivalence replaces the previous degree-three truncation.
Reconstruction as a globally multiplicative arithmetic function is separate.
-/
noncomputable section
namespace RiemannResearch.NumberTheory.PrimePowerFormalCoordinates
open PowerSeries
variable {A : Type*} [CommRing A] [Algebra ℚ A]
omit [Algebra ℚ A] in
theorem constantCoeff_subst_zero {h : PowerSeries A} (hh : constantCoeff h = 0)
    (f : PowerSeries A) : constantCoeff (f.subst h) = constantCoeff f := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh
  have hz := constantCoeff_subst_eq_zero hh (f - C (constantCoeff f)) (by simp)
  change constantCoeff ((f - C (constantCoeff f)).subst h) = 0 at hz
  rw [subst_sub hs, subst_C, map_sub] at hz
  simpa only [PowerSeries.constantCoeff_eq, MvPowerSeries.constantCoeff_C] using sub_eq_zero.mp hz

theorem deriv_log_mul : d⁄dX A (PowerSeries.log A) * (1 + X) = 1 := by
  rw [deriv_log]
  ext n
  cases n with
  | zero => simp
  | succ n => simp [mul_add, pow_succ]

variable [IsAddTorsionFree A]
omit [Algebra ℚ A] in
theorem eq_of_derivative_mul {g : PowerSeries A}
    (hderiv : d⁄dX A g * (1 + X) = g) :
    g = constantCoeff g • (1 + X) := by
  let : Invertible (1 + X : PowerSeries A) :=
    (isUnit_iff_constantCoeff.mpr (by simp)).invertible
  have hcu : constantCoeff (⅟(1 + X) : PowerSeries A) = 1 := by
    have h := congrArg (constantCoeff (R := A)) (mul_invOf_self (1 + X : PowerSeries A))
    rw [map_mul] at h
    simpa using h
  have hg : g * ⅟(1 + X) = d⁄dX A g := by
    conv_lhs => rw [← hderiv]
    rw [mul_assoc, mul_invOf_self, mul_one]
  have key : g * ⅟(1 + X) = C (constantCoeff g) := by
    refine derivative.ext ?_ ?_
    · simp only [Derivation.leibniz, derivative_invOf, map_add, derivative_one, derivative_X,
        zero_add, derivative_C, mul_one, smul_eq_mul, ← hg]
      ring
    · simp [hcu]
  rw [smul_eq_C_mul, ← key, mul_assoc, invOf_mul_self, mul_one]

theorem subst_exp_log : (PowerSeries.exp A).subst (PowerSeries.log A) = 1 + X := by
  have hd : d⁄dX A ((PowerSeries.exp A).subst (PowerSeries.log A)) * (1 + X) =
      (PowerSeries.exp A).subst (PowerSeries.log A) := by
    rw [derivative_subst HasSubst.log, derivative_exp, mul_assoc, deriv_log_mul, mul_one]
  have hc : constantCoeff ((PowerSeries.exp A).subst (PowerSeries.log A)) = 1 := by
    rw [constantCoeff_subst_zero constantCoeff_log, constantCoeff_exp]
  simpa [hc] using eq_of_derivative_mul hd

theorem subst_log_exp_sub_one :
    (PowerSeries.log A).subst (PowerSeries.exp A - 1) = X := by
  apply derivative.ext
  · rw [derivative_subst HasSubst.exp_sub_one, map_sub, derivative_exp,
      derivative_one, sub_zero, derivative_X]
    have hd := congrArg (fun f : PowerSeries A => f.subst (PowerSeries.exp A - 1))
      (deriv_log_mul (A := A))
    rw [subst_mul HasSubst.exp_sub_one, subst_add HasSubst.exp_sub_one,
      subst_X HasSubst.exp_sub_one] at hd
    simpa [← coe_substAlgHom HasSubst.exp_sub_one] using hd
  · rw [constantCoeff_subst_zero (by simp [constantCoeff_exp]),
      constantCoeff_log, constantCoeff_X]
def expOf (h : PowerSeries A) : PowerSeries A := (PowerSeries.exp A).subst h
omit [IsAddTorsionFree A] in
theorem constantCoeff_expOf {h : PowerSeries A} (hh : constantCoeff h = 0) :
    constantCoeff (expOf h) = 1 := by
  rw [expOf, constantCoeff_subst_zero hh, constantCoeff_exp]
theorem logOf_expOf {h : PowerSeries A} (hh : constantCoeff h = 0) :
    PowerSeries.logOf (expOf h) = h := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh
  have he : expOf h - 1 = (PowerSeries.exp A - 1).subst h := by
    rw [subst_sub hs]
    simp [expOf, ← coe_substAlgHom hs]
  rw [PowerSeries.logOf_eq, he,
    ← subst_comp_subst_apply HasSubst.exp_sub_one hs,
    subst_log_exp_sub_one, subst_X hs]
theorem expOf_logOf {f : PowerSeries A} (hf : constantCoeff f = 1) :
    expOf (PowerSeries.logOf f) = f := by
  have hs : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp [hf])
  rw [expOf, PowerSeries.logOf_eq,
    ← subst_comp_subst_apply HasSubst.log hs, subst_exp_log,
    subst_add hs, subst_X hs]
  simp [← coe_substAlgHom hs]
def expLogEquiv :
    {h : PowerSeries A // constantCoeff h = 0} ≃
      {f : PowerSeries A // constantCoeff f = 1} where
  toFun h := ⟨expOf h, constantCoeff_expOf h.property⟩
  invFun f := ⟨PowerSeries.logOf f, PowerSeries.constantCoeff_logOf f.property⟩
  left_inv h := Subtype.ext (logOf_expOf h.property)
  right_inv f := Subtype.ext (expOf_logOf f.property)
def primeFamilyEquiv :
    (Nat.Primes → {h : PowerSeries A // constantCoeff h = 0}) ≃
      (Nat.Primes → {f : PowerSeries A // constantCoeff f = 1}) :=
  Equiv.piCongrRight (fun _ => expLogEquiv)
end RiemannResearch.NumberTheory.PrimePowerFormalCoordinates





namespace RiemannResearch.NumberTheory.PrimePowerFormalCoordinates
open PowerSeries
def eta : PowerSeries ℂ := mk (fun n => if n = 0 then 0 else 1 / (n : ℂ))
theorem eta_constantCoeff : constantCoeff eta = 0 := by
  simp [eta, ← coeff_zero_eq_constantCoeff_apply]
theorem derivative_eta : d⁄dX ℂ eta = mk 1 := by
  ext n
  simp [eta, coeff_derivative, Nat.cast_add, Nat.cast_one]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n)
theorem expOf_eta : expOf eta = mk 1 := by
  have hs : HasSubst eta := HasSubst.of_constantCoeff_zero' eta_constantCoeff
  have hd : d⁄dX ℂ (expOf eta) = expOf eta * mk 1 := by
    rw [expOf, derivative_subst hs, derivative_exp, derivative_eta]
  have hz : expOf eta * (1 - X) = 1 := by
    apply derivative.ext
    · calc
        d⁄dX ℂ (expOf eta * (1 - X)) =
            expOf eta * ((mk 1 : PowerSeries ℂ) * (1 - X)) - expOf eta := by
          rw [Derivation.leibniz, hd, map_sub, derivative_one, derivative_X]
          simp only [smul_eq_mul]
          ring
        _ = d⁄dX ℂ (1 : PowerSeries ℂ) := by
          rw [mk_one_mul_one_sub_eq_one]
          simp
    · simp [constantCoeff_expOf eta_constantCoeff]
  calc
    expOf eta = expOf eta * ((1 - X) * (mk 1 : PowerSeries ℂ)) := by
      rw [mul_comm (1 - X), mk_one_mul_one_sub_eq_one]
      simp
    _ = (expOf eta * (1 - X)) * mk 1 := (mul_assoc _ _ _).symm
    _ = mk 1 := by rw [hz, one_mul]
end RiemannResearch.NumberTheory.PrimePowerFormalCoordinates
