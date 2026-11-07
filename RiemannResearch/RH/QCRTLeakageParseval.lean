import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisorWaveletFactorization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete arithmetic Parseval leakage of CRT collocation

Source: user-provided CRT collocation handoff, Section 5. The existing actual
Q divisor Hilbert basis is used, including all prime-power depths. Every
infinite series below is the full Hilbert norm; no cutoff of physical N occurs.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTLeakageParseval
open ZetaTwoHilbert QDivisibilityDensity QDivisorHilbert QCRTFiniteCollocation

theorem wavelet_mem_cell (L : ℕ) (hL : 0 < L) (r : ℕ) (hrL : r ∣ L) :
    divisorWavelet r ∈ cellSpace L := by
  rw [cellSpace, ← divisorWavelet_cutoff_span_eq L hL]
  exact Submodule.subset_span ⟨r, Nat.mem_divisors.mpr ⟨hrL, ne_of_gt hL⟩, rfl⟩

/-- Exact finite Möbius inversion in the physical Hilbert space. -/
theorem sum_divisorWavelet (L : ℕ) :
    (∑ d ∈ L.divisors, divisorWavelet d) = (L : ℝ)^2 • qDivisor L := by
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    change qSequenceLinear (∑ d ∈ L.divisors, divisorWavelet d) (n+1) =
      qSequenceLinear ((L : ℝ)^2 • qDivisor L) (n+1)
    rw [map_sum, map_smul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ d ∈ L.divisors, qSequence (divisorWavelet d) (n+1)) =
      (L : ℝ)^2 * qSequence (qDivisor L) (n+1)
    simp only [qSequence_divisorWavelet_succ, qSequence_qDivisor]
    simp_rw [← divisorWaveletAF_apply]
    rw [sum_divisorWaveletAF]
    simp [scaledDivisorAF, positiveDivisor]

theorem divisor_wavelet_inner (L : ℕ) (hL : 0 < L) (r : ℕ+) :
    inner ℝ (qDivisor L) (divisorWavelet r) =
      if (r : ℕ) ∣ L then qJordanTwo r / (L : ℝ)^2 else 0 := by
  have he := congrArg (fun f : QHilbert => inner ℝ f (divisorWavelet r))
    (sum_divisorWavelet L)
  rw [sum_inner, real_inner_smul_left] at he
  have hsum : (∑ d ∈ L.divisors, inner ℝ (divisorWavelet d) (divisorWavelet r)) =
      if (r : ℕ) ∣ L then qJordanTwo r else 0 := by
    calc
      _ = ∑ d ∈ L.divisors, if d = (r : ℕ) then qJordanTwo r else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdp := Nat.pos_of_mem_divisors hd
        by_cases hdr : d = (r : ℕ)
        · subst d
          simpa only [if_pos rfl] using divisorWavelet_inner r r
        · let dd : ℕ+ := ⟨d, hdp⟩
          have hne : dd ≠ r := fun h => hdr (congrArg Subtype.val h)
          have hi := divisorWavelet_inner dd r
          simp only [if_neg hne] at hi
          change inner ℝ (divisorWavelet d) (divisorWavelet r) = 0 at hi
          simpa only [if_neg hdr] using hi
      _ = _ := by simp [Nat.mem_divisors, ne_of_gt hL]
  rw [hsum] at he
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  by_cases hr : (r : ℕ) ∣ L
  · simp only [hr, if_true] at he ⊢
    apply (eq_div_iff (pow_ne_zero 2 hL0)).mpr
    nlinarith
  · simp only [hr, if_false] at he ⊢
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero 2 hL0)

/-- All prescribed low coordinates, with the Jordan normalization explicit. -/
theorem canonical_low_wavelet (L : ℕ) (hL : 2 ≤ L) (r : ℕ+)
    (hrL : (r : ℕ) ∣ L) :
    inner ℝ (canonical L hL : QHilbert) (divisorWavelet r) =
      (if r = 1 then (1 : ℝ) else 0) - qJordanTwo r / (L : ℝ)^2 := by
  rw [inner_eq_of_divisor_tests L _ _ (canonical_match L hL) _
      (wavelet_mem_cell L (by omega) r hrL),
    target, inner_sub_left, qOne_divisorWavelet_inner,
    divisor_wavelet_inner L (by omega) r, if_pos hrL]

theorem target_wavelet_outside (L : ℕ) (hL : 0 < L) (r : ℕ+)
    (hrL : ¬ (r : ℕ) ∣ L) : inner ℝ (target L) (divisorWavelet r) = 0 := by
  have hr1 : r ≠ 1 := by intro h; apply hrL; simp [h]
  rw [target, inner_sub_left, qOne_divisorWavelet_inner,
    divisor_wavelet_inner L hL r, if_neg hrL, if_neg hr1, sub_self]

/-- Complete leakage consists exactly of modes whose conductor does not divide L.
This includes both new primes and excessive powers of previously present primes. -/
theorem canonical_leakage_parseval (L : ℕ) (hL : 2 ≤ L) :
    (∑' r : ℕ+, if (r : ℕ) ∣ L then 0 else
      (inner ℝ (canonical L hL : QHilbert) (divisorWavelet r))^2 / qJordanTwo r) =
      leakage L hL := by
  have hp := divisorWavelet_parseval_norm ((canonical L hL : QHilbert) - target L)
  calc
    _ = ∑' r : ℕ+, (inner ℝ ((canonical L hL : QHilbert) - target L)
        (divisorWavelet r))^2 / qJordanTwo r := by
      apply tsum_congr
      intro r
      by_cases hr : (r : ℕ) ∣ L
      · have hi := inner_eq_of_divisor_tests L _ _ (canonical_match L hL) _
          (wavelet_mem_cell L (by omega) r hr)
        simp only [hr, if_true, inner_sub_left, hi, sub_self, zero_pow
          (by decide : 2 ≠ 0), zero_div]
      · rw [if_neg hr, inner_sub_left, target_wavelet_outside L (by omega) r hr,
          sub_zero]
    _ = _ := hp

end RiemannResearch.RH.QCRTLeakageParseval
