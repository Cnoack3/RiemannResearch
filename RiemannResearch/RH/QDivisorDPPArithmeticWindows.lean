import RiemannResearch.RH.QDivisorDPPWindows
import RiemannResearch.RH.QDivisorDPP
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisibilityResidueCoefficients
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# Divisor signatures and exact arithmetic exclusion

Source: direct calculation from the user-provided Q divisor-wavelet kernel.
Equal signatures give
proportional feature rows and zero two-point occupation, without a limit.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert

theorem divisorWavelet_coordinate (r i : ℕ) :
    divisorWavelet r i = Real.sqrt (qWeight i) * qDivisorWavelet r (i + 1) := by
  have h := qSequence_divisorWavelet_succ r i
  rw [qSequence_succ] at h
  have hs : Real.sqrt (qWeight i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos i))
  simpa only [mul_comm] using (div_eq_iff hs).mp h

theorem normalizedDivisorWavelet_coordinate (r : ℕ+) (i : ℕ) :
    normalizedDivisorWavelet r i =
      Real.sqrt (qWeight i) * (Real.sqrt (qJordanTwo (r : ℕ)))⁻¹ *
        qDivisorWavelet (r : ℕ) (i + 1) := by
  change (Real.sqrt (qJordanTwo (r : ℕ)))⁻¹ * divisorWavelet (r : ℕ) i = _
  rw [divisorWavelet_coordinate]
  ring

end RiemannResearch.RH.QDivisorHilbert

namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoHilbert QDivisorHilbert

/-- The physical inverse-square factors are retained in counting coordinates. -/
theorem basisKernel_arithmetic_sum (N i j : ℕ) :
    basisKernel N i j = Real.sqrt (qWeight i) * Real.sqrt (qWeight j) *
      ∑ r : Fin N,
        qDivisorWavelet (basisIndex r : ℕ) (i + 1) *
          qDivisorWavelet (basisIndex r : ℕ) (j + 1) /
            qJordanTwo (basisIndex r : ℕ) := by
  rw [basisKernel_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [normalizedDivisorWavelet_coordinate, normalizedDivisorWavelet_coordinate]
  have hs : (Real.sqrt (qJordanTwo (basisIndex r : ℕ))) ^ 2 =
      qJordanTwo (basisIndex r : ℕ) :=
    Real.sq_sqrt (qJordanTwo_pos _ (basisIndex r).pos).le
  have hi : (Real.sqrt (qJordanTwo (basisIndex r : ℕ)))⁻¹ *
      (Real.sqrt (qJordanTwo (basisIndex r : ℕ)))⁻¹ =
        (qJordanTwo (basisIndex r : ℕ))⁻¹ := by
    rw [← mul_inv, ← pow_two, hs]
  simp only [div_eq_mul_inv]
  calc
    _ = Real.sqrt (qWeight i) * Real.sqrt (qWeight j) *
        (qDivisorWavelet (basisIndex r : ℕ) (i + 1) *
          qDivisorWavelet (basisIndex r : ℕ) (j + 1)) *
        ((Real.sqrt (qJordanTwo (basisIndex r : ℕ)))⁻¹ *
          (Real.sqrt (qJordanTwo (basisIndex r : ℕ)))⁻¹) := by ring
    _ = _ := by rw [hi]; ring

/-- The full finite divisibility signature, not only prime indicators. -/
def sameDivisorSignature (N n m : ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → d ≤ N → (d ∣ n ↔ d ∣ m)

theorem qDivisorWavelet_eq_of_same_signature {N n m r : ℕ}
    (h : sameDivisorSignature N n m) (hr : 0 < r) (hrN : r ≤ N) :
    qDivisorWavelet r n = qDivisorWavelet r m := by
  unfold qDivisorWavelet qScaledDivisibilitySum
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdN : d ≤ N :=
    (Nat.le_of_dvd hr (Nat.dvd_of_mem_divisors hd)).trans hrN
  simp only [h d hdpos hdN]

/-- Arithmetic collisions force exact exclusion even when N is large. -/
theorem basisLaw_two_point_eq_zero_of_same_signature (N i j : ℕ)
    (hij : i ≠ j) (h : sameDivisorSignature N (i + 1) (j + 1)) :
    (basisLaw N).real {x | x i = true ∧ x j = true} = 0 := by
  have he (r : Fin N) : qDivisorWavelet (basisIndex r : ℕ) (i + 1) =
      qDivisorWavelet (basisIndex r : ℕ) (j + 1) :=
    qDivisorWavelet_eq_of_same_signature h (basisIndex r).pos
      (by change (r : ℕ) + 1 ≤ N; exact Nat.succ_le_of_lt r.isLt)
  rw [basisLaw_two_point N i j hij]
  simp only [basisKernel_arithmetic_sum, he]
  ring

end RiemannResearch.RH.QDivisorDPP
