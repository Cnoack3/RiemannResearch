import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QDivisibilityResidueCoefficients
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp

/-!
# Totality of the arithmetic divisor wavelets in the actual Q Hilbert space

Source: user-provided inverse-Gram argument. The change from divisibility
indicators to Möbius wavelets is finite and triangular, with diagonal `r²`.
Thus its dense-span statement follows from actual divisibility density,
without making any assumption about residue approximation or RH.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert QDivisibilityDensity

/-- Actual Hilbert vector for the finite arithmetic Möbius wavelet. -/
def divisorWavelet (r : ℕ) : QHilbert :=
  ∑ k ∈ r.divisors,
    ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) • qDivisor k

/-- The Hilbert coordinates agree at every positive physical integer. -/
theorem qSequence_divisorWavelet (r : ℕ) (n : ℕ+) :
    qSequence (divisorWavelet r) (n : ℕ) = qDivisorWavelet r (n : ℕ) := by
  change qSequenceLinear (divisorWavelet r) (n : ℕ) = _
  unfold divisorWavelet
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  change (∑ k ∈ r.divisors,
    ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) *
      qSequence (qDivisor k) (n : ℕ)) = _
  simp only [qSequence_qDivisor]
  simp [positiveDivisor, ne_of_gt n.pos, qDivisorWavelet, qScaledDivisibilitySum]

/-- Successor-coordinate spelling, convenient for inverse-power series. -/
theorem qSequence_divisorWavelet_succ (r n : ℕ) :
    qSequence (divisorWavelet r) (n + 1) = qDivisorWavelet r (n + 1) := by
  exact qSequence_divisorWavelet r (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)

/-- The exact triangular relation retains all proper-divisor terms. -/
theorem divisorWavelet_triangular (r : ℕ) (hr : 0 < r) :
    (∑ k ∈ r.divisors.erase r,
      ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) • qDivisor k) +
      (r : ℝ) ^ 2 • qDivisor r = divisorWavelet r := by
  have hrmem : r ∈ r.divisors := by
    simp [Nat.mem_divisors, ne_of_gt hr]
  have he := Finset.sum_erase_add r.divisors
    (fun k => ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) • qDivisor k)
    hrmem
  simpa [Nat.div_self hr, divisorWavelet] using he

/-- Exact finite inversion at the level of spans; every positive divisor
indicator lies in the span of wavelets, by strong induction on its divisor. -/
theorem qDivisor_mem_wavelet_span (r : ℕ) (hr : 0 < r) :
    qDivisor r ∈ Submodule.span ℝ
      (Set.range (fun n : ℕ+ => divisorWavelet (n : ℕ))) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    let W := Submodule.span ℝ (Set.range (fun n : ℕ+ => divisorWavelet (n : ℕ)))
    have hW : divisorWavelet r ∈ W :=
      Submodule.subset_span ⟨(⟨r, hr⟩ : ℕ+), rfl⟩
    have hsmall :
        (∑ k ∈ r.divisors.erase r,
          ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) • qDivisor k) ∈ W := by
      apply W.sum_mem
      intro k hk
      have hkdiv : k ∈ r.divisors := (Finset.mem_erase.mp hk).2
      have hkne : k ≠ r := (Finset.mem_erase.mp hk).1
      have hkpos : 0 < k := Nat.pos_of_mem_divisors hkdiv
      have hkle : k ≤ r := Nat.le_of_dvd hr (Nat.dvd_of_mem_divisors hkdiv)
      exact W.smul_mem _ (ih k (lt_of_le_of_ne hkle hkne) hkpos)
    have hscaled : (r : ℝ) ^ 2 • qDivisor r ∈ W := by
      have he := divisorWavelet_triangular r hr
      have he' : (r : ℝ) ^ 2 • qDivisor r = divisorWavelet r -
          (∑ k ∈ r.divisors.erase r,
            ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) • qDivisor k) := by
        exact eq_sub_of_add_eq' he
      rw [he']
      exact W.sub_mem hW hsmall
    have hr0 : (r : ℝ) ^ 2 ≠ 0 := by positivity
    have hinv := W.smul_mem (((r : ℝ) ^ 2)⁻¹) hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hr0, one_smul] using hinv

/-- The Möbius and divisibility dictionaries have exactly the same algebraic span. -/
theorem divisorWavelet_span_eq :
    Submodule.span ℝ (Set.range (fun n : ℕ+ => divisorWavelet (n : ℕ))) =
      Submodule.span ℝ (Set.range (fun n : ℕ+ => qDivisor (n : ℕ))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨r, rfl⟩
    unfold divisorWavelet
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(⟨k, Nat.pos_of_mem_divisors hk⟩ : ℕ+), rfl⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨r, rfl⟩
    exact qDivisor_mem_wavelet_span (r : ℕ) r.pos

/-- Unconditional dense span of all arithmetic Möbius wavelets. -/
theorem divisorWavelet_span_dense :
    (Submodule.span ℝ (Set.range (fun n : ℕ+ => divisorWavelet (n : ℕ)))).topologicalClosure =
      ⊤ := by
  rw [divisorWavelet_span_eq]
  exact qDivisor_span_dense

end RiemannResearch.RH.QDivisorHilbert
