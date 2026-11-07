/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.NumberTheory.DivisorIncidence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual gcd-cell sampling in the complete Q Hilbert space

Source: the user's CRT collocation handoff, 6 November 2026, Section 7.
The finite sampler is obtained from the existing divisor-incidence Möbius
inverse. No boundedness hypothesis on the input sequence is necessary:
only finitely many of its values occur in the gcd sampler.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QGcdSampling
open ZetaTwoHilbert QDivisibilityDensity QCRTFiniteCollocation
open RiemannResearch.NumberTheory.DivisorIncidence

/-- The actual Q vector of one positive gcd cell. -/
def gcdCell (L d : ℕ) : QHilbert :=
  ∑ j ∈ L.divisors,
    (if d ∣ j then (ArithmeticFunction.moebius (j/d) : ℝ) else 0) • qDivisor j

theorem gcdCell_mem_cell (L : ℕ) (hL : 0 < L) (d : ℕ) :
    gcdCell L d ∈ cellSpace L := by
  apply (cellSpace L).sum_mem
  intro j hj
  apply (cellSpace L).smul_mem
  exact divisor_mem_cell L j hL (Nat.dvd_of_mem_divisors hj)

theorem qSequence_gcdCell (L : ℕ) (hL : 0 < L) (d : ℕ) (hd : d ∣ L)
    (n : ℕ) (hn : 0 < n) :
    qSequence (gcdCell L d) n = if Nat.gcd n L = d then 1 else 0 := by
  have hdmem : d ∈ L.divisors := Nat.mem_divisors.mpr ⟨hd, ne_of_gt hL⟩
  have hgmem : Nat.gcd n L ∈ L.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n L, ne_of_gt hL⟩
  have hcoords : qSequence (gcdCell L d) n =
      ∑ j ∈ L.divisors,
        (if d ∣ j then (ArithmeticFunction.moebius (j/d) : ℝ) else 0) *
          positiveDivisor j n := by
    change qSequenceLinear (∑ j ∈ L.divisors,
      (if d ∣ j then (ArithmeticFunction.moebius (j/d) : ℝ) else 0) • qDivisor j) n = _
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    change (∑ j ∈ L.divisors,
      (if d ∣ j then (ArithmeticFunction.moebius (j/d) : ℝ) else 0) *
        qSequence (qDivisor j) n) = _
    simp only [qSequence_qDivisor]
  rw [hcoords]
  calc
    _ = ∑ j ∈ L.divisors,
        (if d ∣ j then (ArithmeticFunction.moebius (j/d) : ℝ) else 0) *
          (if j ∣ Nat.gcd n L then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjL : j ∣ L := Nat.dvd_of_mem_divisors hj
      simp [positiveDivisor, ne_of_gt hn, Nat.dvd_gcd_iff, hjL]
    _ = if d = Nat.gcd n L then 1 else 0 :=
      moebius_left_inverse L d (Nat.gcd n L) hdmem hgmem
    _ = _ := by
      by_cases hdg : d = Nat.gcd n L
      · simp only [hdg]
      · simp only [if_neg hdg, if_neg (Ne.symm hdg)]

/-- Evaluation of a real sequence at the gcd with L, anchored at zero. -/
def sample (L : ℕ) (b : ℕ → ℝ) : QHilbert :=
  ∑ d ∈ L.divisors, b d • gcdCell L d

theorem sample_mem_cell (L : ℕ) (hL : 0 < L) (b : ℕ → ℝ) :
    sample L b ∈ cellSpace L := by
  apply (cellSpace L).sum_mem
  intro d hd
  exact (cellSpace L).smul_mem _ (gcdCell_mem_cell L hL d)

theorem qSequence_sample (L : ℕ) (hL : 0 < L) (b : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    qSequence (sample L b) n = b (Nat.gcd n L) := by
  have hgmem : Nat.gcd n L ∈ L.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n L, ne_of_gt hL⟩
  have hcoords : qSequence (sample L b) n =
      ∑ d ∈ L.divisors, b d * qSequence (gcdCell L d) n := by
    change qSequenceLinear (∑ d ∈ L.divisors, b d • gcdCell L d) n = _
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hcoords]
  calc
    _ = ∑ d ∈ L.divisors, b d * (if Nat.gcd n L = d then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [qSequence_gcdCell L hL d (Nat.dvd_of_mem_divisors hd) n hn]
    _ = b (Nat.gcd n L) := by
      rw [Finset.sum_eq_single (Nat.gcd n L)]
      · simp
      · intro d hd hne
        rw [if_neg (Ne.symm hne), mul_zero]
      · exact fun h => (h hgmem).elim

/-- Orthogonal leakage has an actually convergent, zero real sampled pairing. -/
theorem real_sample_pairing_hasSum (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : conditionalProjection L f = 0) (b : ℕ → ℝ) :
    HasSum (fun n : ℕ => qWeight n * b (Nat.gcd (n+1) L) * qSequence f (n+1)) 0 := by
  let g := sample L b
  have hfull := qSequence_product_summable f g
  have hsum : Summable (fun n : ℕ =>
      qWeight n * qSequence f (n+1) * qSequence g (n+1)) := by
    simpa only [qWeight] using (summable_nat_add_iff 1).mpr hfull
  have hinner : inner ℝ f g = ∑' n : ℕ,
      qWeight n * qSequence f (n+1) * qSequence g (n+1) := by
    rw [qInner_weighted, hfull.tsum_eq_zero_add]
    simp only [qSequence_zero, mul_zero, zero_add, qWeight]
  have hzero : inner ℝ f g = 0 := by
    rw [← conditional_inner L f g (sample_mem_cell L hL b), hf]
    simp
  have hp := hsum.hasSum
  rw [← hinner, hzero] at hp
  convert hp using 1
  funext n
  change qWeight n * b (Nat.gcd (n+1) L) * qSequence f (n+1) =
    qWeight n * qSequence f (n+1) * qSequence (sample L b) (n+1)
  rw [qSequence_sample L hL b (n+1) (Nat.succ_pos n)]
  ring

/-- The complete sampled complex pairing converges to zero; this supplies both
cancellation and summability for the Mellin-gcd witness subtraction. -/
theorem complex_sample_pairing_hasSum (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : conditionalProjection L f = 0) (b : ℕ → ℂ) :
    HasSum (fun n : ℕ => (qWeight n : ℂ) * b (Nat.gcd (n+1) L) *
      (qSequence f (n+1) : ℂ)) 0 := by
  have hr := real_sample_pairing_hasSum L hL f hf (fun n => (b n).re)
  have hi := real_sample_pairing_hasSum L hL f hf (fun n => (b n).im)
  have hp := (Complex.ofRealCLM.hasSum hr).add
    ((Complex.ofRealCLM.hasSum hi).mul_right Complex.I)
  convert hp using 1
  · funext n
    change (qWeight n : ℂ) * b (Nat.gcd (n+1) L) * (qSequence f (n+1) : ℂ) =
      ((qWeight n * (b (Nat.gcd (n+1) L)).re * qSequence f (n+1) : ℝ) : ℂ) +
        ((qWeight n * (b (Nat.gcd (n+1) L)).im * qSequence f (n+1) : ℝ) : ℂ) *
          Complex.I
    calc
      _ = (qWeight n : ℂ) *
          (((b (Nat.gcd (n+1) L)).re : ℂ) +
            ((b (Nat.gcd (n+1) L)).im : ℂ) * Complex.I) *
              (qSequence f (n+1) : ℂ) := by rw [Complex.re_add_im]
      _ = _ := by push_cast; ring
  · simp

/-- Exact cancellation of every complex gcd-cell sampler against leakage. -/
theorem complex_sample_pairing_zero (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : conditionalProjection L f = 0) (b : ℕ → ℂ) :
    (∑' n : ℕ, (qWeight n : ℂ) * b (Nat.gcd (n+1) L) *
      (qSequence f (n+1) : ℂ)) = 0 :=
  (complex_sample_pairing_hasSum L hL f hf b).tsum_eq

end RiemannResearch.RH.QGcdSampling
