/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResampling
import RiemannResearch.RH.PrimeResamplingCore
import RiemannResearch.RH.PrimeResamplingGeometric
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The complete geometric formula for actual prime resampling

Source: the user's prime-coordinate research agenda. Pairing orthogonal
projection with actual arithmetic fiber indicators identifies it with the
complete geometric conditional average. Every infinite sum is proved
summable for every QHilbert input.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert PrimeResampling

/-- A multiplication-invariant sequence is constant along every prime-power fiber. -/
theorem qSequence_mul_pow_of_mem (p : ℕ) (f : QHilbert) (hf : f ∈ primeInvariant p)
    (n k : ℕ) : qSequence f (n * p ^ k) = qSequence f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show n * p ^ (k + 1) = p * (n * p ^ k) by rw [pow_succ]; ring]
      exact (hf (n * p ^ k)).trans ih

theorem qSequence_replaceValuation_of_mem (p : ℕ) (f : QHilbert)
    (hf : f ∈ primeInvariant p) (n k : ℕ) :
    qSequence f (replaceValuation p n k) = qSequence f n := by
  have h1 := qSequence_mul_pow_of_mem p f hf (primeCore p n) k
  have h2 := qSequence_mul_pow_of_mem p f hf (primeCore p n) (n.factorization p)
  rw [primeCore_mul_primePower] at h2
  exact h1.trans h2.symm

def fiberIndicator (p n m : ℕ) : ℝ :=
  if primeCore p m = primeCore p n then 1 else 0

theorem fiberIndicator_abs_le_one (p n m : ℕ) : |fiberIndicator p n m| ≤ 1 := by
  unfold fiberIndicator
  split_ifs <;> norm_num

def fiberVector (p n : ℕ) : QHilbert :=
  encodeQ (fiberIndicator p n)
    (boundedQ_square_summable _ 1 (by norm_num) (fiberIndicator_abs_le_one p n))

theorem qSequence_fiberVector (p n : ℕ) (hn : n ≠ 0) :
    qSequence (fiberVector p n) = fiberIndicator p n := by
  apply qSequence_encodeQ
  have hcore := primeCore_ne_zero p n hn
  change (if primeCore p 0 = primeCore p n then (1 : ℝ) else 0) = 0
  have hz : primeCore p 0 = 0 := by simp [primeCore]
  rw [hz, if_neg (Ne.symm hcore)]

theorem fiberVector_mem (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    fiberVector p n ∈ primeInvariant p := by
  intro m
  rw [qSequence_fiberVector p n hn]
  by_cases hm : m = 0
  · simp [hm]
  · unfold fiberIndicator
    rw [primeCore_mul_prime p m hp hm]

/-- The complete inner product with one arithmetic fiber. -/
theorem inner_fiberVector (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) (f : QHilbert) :
    inner ℝ (fiberVector p n) f =
      ∑' k : ℕ, positiveQWeight (replaceValuation p n k) *
        qSequence f (replaceValuation p n k) := by
  rw [qInner_weighted, qSequence_fiberVector p n hn]
  calc
    _ = ∑' m : ℕ, if primeCore p m = primeCore p n then
        positiveQWeight m * qSequence f m else 0 := by
      apply tsum_congr
      intro m
      unfold fiberIndicator
      split_ifs <;> simp_all
    _ = _ := tsum_primeFiber p n hp hn (fun m => positiveQWeight m * qSequence f m)

/-- On a valuation-independent input, the fiber pairing is its full fiber mass
multiplied by its physical value. -/
theorem inner_fiberVector_of_mem (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (f : QHilbert) (hf : f ∈ primeInvariant p) :
    inner ℝ (fiberVector p n) f = primeFiberMass p n * qSequence f n := by
  rw [inner_fiberVector p n hp hn]
  simp_rw [qSequence_replaceValuation_of_mem p f hf]
  rw [tsum_mul_right, primeFiberMass_tsum p n hp]

/-- The actual geometric average is absolutely convergent for every Hilbert input. -/
theorem geometricAverage_summable (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (f : QHilbert) :
    Summable (fun k : ℕ => geometricMass p k *
      qSequence f (replaceValuation p n k)) := by
  have hmass := (primeFiberMass_pos p n hp hn).ne'
  have hsub := summable_replaceValuation p n hp hn
    (fun m => positiveQWeight m * qSequence (fiberVector p n) m * qSequence f m)
    (qSequence_product_summable (fiberVector p n) f)
  apply (hsub.div_const (primeFiberMass p n)).congr
  intro k
  rw [qSequence_fiberVector p n hn]
  simp only [fiberIndicator, primeCore_replaceValuation p n k hp hn, if_true, mul_one]
  rw [positiveQWeight_eq_fiberMass_mul_geometricMass p n k hp]
  field_simp [hmass]

/-- Exact complete-countable prime resampling, with no finite replacement cutoff. -/
theorem qSequence_C (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) (f : QHilbert) :
    qSequence (C p f) n = ∑' k : ℕ, geometricMass p k *
      qSequence f (replaceValuation p n k) := by
  have hmass := (primeFiberMass_pos p n hp hn).ne'
  apply mul_left_cancel₀ hmass
  calc
    primeFiberMass p n * qSequence (C p f) n = inner ℝ (fiberVector p n) (C p f) :=
      (inner_fiberVector_of_mem p n hp hn (C p f) (C_mem p f)).symm
    _ = inner ℝ (fiberVector p n) f := by
      rw [← C_selfAdjoint p (fiberVector p n) f,
        (C_eq_self_iff p (fiberVector p n)).mpr (fiberVector_mem p n hp hn)]
    _ = ∑' k : ℕ, positiveQWeight (replaceValuation p n k) *
        qSequence f (replaceValuation p n k) := inner_fiberVector p n hp hn f
    _ = _ := by
      simp_rw [positiveQWeight_eq_fiberMass_mul_geometricMass p n _ hp, mul_assoc]
      rw [tsum_mul_left]

end RiemannResearch.RH.QPrimeResampling
