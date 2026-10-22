/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Squarefree lattice packets and physical head preservation

Source: user-provided infinite-CRT continuation, 16 October 2026, and the
user's convolution log/exp proposal. The two-prime coefficient a*b+k is
the squarefree moment/cumulant formula: see T. Sinclair, *Finite free
convolution via reproducing kernels and squarefree algebras*, arXiv:2606.10870v2,
Section 4, for that algebraic terminology and formula. The physical legal
packet and compensated-direction arguments below are developed here.

These results concern the actual complete Q Hilbert space. They do not
identify nilpotent multiplication with unrestricted floor-operator
composition and do not assume a tail bound or prove RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeLatticePackets
open ZetaTwoHilbert ZetaTwoProbability QFloorDilation ArithmeticCumulative

/-- A finite divisor dictionary; the divisor-one atom is zero. -/
def divisorStage (L : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ {f | ∃ d : ℕ, d ∣ L ∧ f = qResidue d}

theorem divisorStage_mono {L K : ℕ} (hLK : L ∣ K) :
    divisorStage L ≤ divisorStage K := by
  apply Submodule.span_mono
  rintro f ⟨d, hd, rfl⟩
  exact ⟨d, dvd_trans hd hLK, rfl⟩

theorem divisorStage_le_squarefreeSpan (L : ℕ) (hL : 0 < L)
    (hsf : Squarefree L) : divisorStage L ≤ qSquarefreeCRTSpan := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, rfl⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hL
  by_cases hd1 : d = 1
  · rw [hd1, qResidue_one]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span
      ⟨⟨d, by omega, hsf.squarefree_of_dvd hd⟩, rfl⟩

/-- Coprime arithmetic is needed only when asserting that the new period
is squarefree. The exact finite divisor-span map holds for every m>0. -/
theorem floorDilation_mem_divisorStage (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (f : QHilbert) (hf : f ∈ divisorStage L) :
    floorDilation m hm f ∈ divisorStage (m * L) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨d, hd, rfl⟩ := hf
      rw [floorDilation_qResidue m d hm (Nat.pos_of_dvd_of_pos hd hL)]
      exact (divisorStage (m * L)).sub_mem
        (Submodule.subset_span ⟨m * d, Nat.mul_dvd_mul_left m hd, rfl⟩)
        ((divisorStage (m * L)).smul_mem _
          (Submodule.subset_span ⟨m, dvd_mul_right m L, rfl⟩))
  | zero => simpa only [map_zero] using (divisorStage (m * L)).zero_mem
  | add f g hf hg ihf ihg =>
      rw [map_add]
      exact (divisorStage (m * L)).add_mem ihf ihg
  | smul a f hf ih =>
      rw [map_smul]
      exact (divisorStage (m * L)).smul_mem a ih

theorem floorDilation_mem_squarefreeSpan (L m : ℕ) (hL : 0 < L) (hm : 0 < m)
    (hsf : Squarefree L) (hmsf : Squarefree m) (hcop : m.Coprime L)
    (f : QHilbert) (hf : f ∈ divisorStage L) :
    floorDilation m hm f ∈ qSquarefreeCRTSpan := by
  apply divisorStage_le_squarefreeSpan (m * L) (Nat.mul_pos hm hL)
    (Nat.squarefree_mul_iff.mpr ⟨hcop, hmsf, hsf⟩)
  exact floorDilation_mem_divisorStage L m hL hm f hf

/-- A literal legal direction with zero reciprocal slope. -/
def compensatedResidue (d p : ℕ) : QHilbert :=
  qResidue d - ((p : ℝ) / (d : ℝ)) • qResidue p

theorem compensatedResidue_sequence (d p n : ℕ) :
    qSequence (compensatedResidue d p) n =
      residueFraction d n - ((p : ℝ) / (d : ℝ)) * residueFraction p n := by
  change qSequenceLinear (qResidue d - ((p : ℝ) / (d : ℝ)) • qResidue p) n = _
  rw [map_sub, map_smul]
  change qSequence (qResidue d) n - ((p : ℝ) / (d : ℝ)) *
    qSequence (qResidue p) n = _
  simp only [qSequence_qResidue]

theorem compensatedResidue_head (d p n : ℕ) (hd : 0 < d) (hp : 0 < p)
    (hnd : n < d) (hnp : n < p) :
    qSequence (compensatedResidue d p) n = 0 := by
  rw [compensatedResidue_sequence]
  simp only [residueFraction, Nat.mod_eq_of_lt hnd, Nat.mod_eq_of_lt hnp]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  field_simp [hdR, hpR]
  ring

theorem compensatedResidue_mem_squarefreeSpan (d p : ℕ)
    (hd : 2 ≤ d) (hp : 2 ≤ p) (hdsf : Squarefree d) (hpsf : Squarefree p) :
    compensatedResidue d p ∈ qSquarefreeCRTSpan := by
  exact qSquarefreeCRTSpan.sub_mem
    (Submodule.subset_span ⟨⟨d, hd, hdsf⟩, rfl⟩)
    (qSquarefreeCRTSpan.smul_mem _ (Submodule.subset_span ⟨⟨p, hp, hpsf⟩, rfl⟩))

/-- All finite zero-slope combinations are synthesized by the compensated
directions. No restriction on coefficient signs or support size is made. -/
theorem zeroSlope_eq_compensated_sum {ι : Type*} (s : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (p : ℕ)
    (hzero : (∑ i ∈ s, c i / (d i : ℝ)) = 0) :
    (∑ i ∈ s, c i • qResidue (d i)) =
      ∑ i ∈ s, c i • compensatedResidue (d i) p := by
  have hc : (∑ i ∈ s, c i * ((p : ℝ) / (d i : ℝ))) = 0 := by
    calc
      _ = (p : ℝ) * ∑ i ∈ s, c i / (d i : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hzero, mul_zero]
  simp only [compensatedResidue, smul_sub, smul_smul, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, hc, zero_smul, sub_zero]

/-- The two-prime squarefree exponential has coefficients 1,a,b,a*b+k.
The composite cumulant k is independent of the two singleton cumulants. -/
def twoPrimePacket (f : QHilbert) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (a b k : ℝ) : QHilbert :=
  f + a • floorDilation p hp f + b • floorDilation q hq f +
    (a * b + k) • floorDilation (p * q) (Nat.mul_pos hp hq) f

theorem twoPrimePacket_factorization (f : QHilbert) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (a b k : ℝ) :
    twoPrimePacket f p q hp hq a b k =
      (f + b • floorDilation q hq f) +
        a • floorDilation p hp (f + b • floorDilation q hq f) +
          k • floorDilation (p * q) (Nat.mul_pos hp hq) f := by
  have hcomp := congrArg (fun T : QHilbert →L[ℝ] QHilbert => T f)
    (floorDilation_comp p q hp hq)
  simp only [ContinuousLinearMap.comp_apply] at hcomp
  rw [map_add, map_smul, smul_add, smul_smul, hcomp]
  simp only [twoPrimePacket, add_smul]
  abel

theorem twoPrimePacket_mem_divisorStage (L p q : ℕ) (hL : 0 < L)
    (hp : 0 < p) (hq : 0 < q) (f : QHilbert) (hf : f ∈ divisorStage L)
    (a b k : ℝ) : twoPrimePacket f p q hp hq a b k ∈ divisorStage (p * q * L) := by
  have hbase : f ∈ divisorStage (p * q * L) :=
    divisorStage_mono (show L ∣ p * q * L from ⟨p * q, by ring⟩) hf
  have hpf : floorDilation p hp f ∈ divisorStage (p * q * L) :=
    divisorStage_mono (show p * L ∣ p * q * L from ⟨q, by ring⟩)
      (floorDilation_mem_divisorStage L p hL hp f hf)
  have hqf : floorDilation q hq f ∈ divisorStage (p * q * L) :=
    divisorStage_mono (show q * L ∣ p * q * L from ⟨p, by ring⟩)
      (floorDilation_mem_divisorStage L q hL hq f hf)
  have hpqf := floorDilation_mem_divisorStage L (p * q) hL (Nat.mul_pos hp hq) f hf
  exact (divisorStage (p * q * L)).add_mem
    ((divisorStage (p * q * L)).add_mem
      ((divisorStage (p * q * L)).add_mem hbase
        ((divisorStage (p * q * L)).smul_mem a hpf))
      ((divisorStage (p * q * L)).smul_mem b hqf))
    ((divisorStage (p * q * L)).smul_mem _ hpqf)

theorem twoPrimePacket_mem_squarefreeSpan (L p q : ℕ) (hL : 0 < L)
    (hp : 0 < p) (hq : 0 < q) (hsf : Squarefree (p * q * L))
    (f : QHilbert) (hf : f ∈ divisorStage L) (a b k : ℝ) :
    twoPrimePacket f p q hp hq a b k ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan _ (Nat.mul_pos (Nat.mul_pos hp hq) hL) hsf
    (twoPrimePacket_mem_divisorStage L p q hL hp hq f hf a b k)

/-- Every physical site below both fresh primes is exactly unchanged. -/
theorem twoPrimePacket_head (f : QHilbert) (p q n : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hnp : n < p) (hnq : n < q) (a b k : ℝ) :
    qSequence (twoPrimePacket f p q hp hq a b k) n = qSequence f n := by
  have hnpq : n < p * q := lt_of_lt_of_le hnp (Nat.le_mul_of_pos_right p hq)
  have hzero := qSequence_zero f
  change qSequenceLinear (_ + _ + _ + _) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence f n + a * qSequence (floorDilation p hp f) n +
    b * qSequence (floorDilation q hq f) n +
      (a * b + k) * qSequence (floorDilation (p * q) (Nat.mul_pos hp hq) f) n = _
  simp only [floorDilation_sequence, Nat.div_eq_of_lt hnp,
    Nat.div_eq_of_lt hnq, Nat.div_eq_of_lt hnpq, hzero, mul_zero, add_zero]

/-- Complete signed Q energy. Every mixed inner product is retained. -/
theorem twoPrimePacket_error_exact (t f : QHilbert) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (a b k : ℝ) :
    ‖t - twoPrimePacket f p q hp hq a b k‖ ^ 2 = ‖t - f‖ ^ 2 -
      2 * (a * inner ℝ (t - f) (floorDilation p hp f) +
        b * inner ℝ (t - f) (floorDilation q hq f) +
        (a * b + k) * inner ℝ (t - f) (floorDilation (p * q) (Nat.mul_pos hp hq) f)) +
      a ^ 2 * ‖floorDilation p hp f‖ ^ 2 + b ^ 2 * ‖floorDilation q hq f‖ ^ 2 +
      (a * b + k) ^ 2 * ‖floorDilation (p * q) (Nat.mul_pos hp hq) f‖ ^ 2 +
      2 * a * b * inner ℝ (floorDilation p hp f) (floorDilation q hq f) +
      2 * a * (a * b + k) * inner ℝ (floorDilation p hp f)
        (floorDilation (p * q) (Nat.mul_pos hp hq) f) +
      2 * b * (a * b + k) * inner ℝ (floorDilation q hq f)
        (floorDilation (p * q) (Nat.mul_pos hp hq) f) := by
  let u := floorDilation p hp f
  let v := floorDilation q hq f
  let w := floorDilation (p * q) (Nat.mul_pos hp hq) f
  have he : t - twoPrimePacket f p q hp hq a b k =
      (t - f) - (a • u + b • v + (a * b + k) • w) := by
    unfold twoPrimePacket
    dsimp [u, v, w]
    abel
  rw [he, norm_sub_sq_real]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, sq_abs,
    mul_pow, real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right]
  change _ = ‖t - f‖ ^ 2 - _ + a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 +
    (a * b + k) ^ 2 * ‖w‖ ^ 2 + 2 * a * b * inner ℝ u v +
    2 * a * (a * b + k) * inner ℝ u w + 2 * b * (a * b + k) * inner ℝ v w
  ring

/-- Optimizing the composite cumulant removes exactly one squared full-Q
correlation. The last square is the exact excess for every other value. -/
theorem twoPrimePacket_cumulant_completion (t f : QHilbert) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (a b k : ℝ)
    (hw : floorDilation (p * q) (Nat.mul_pos hp hq) f ≠ 0) :
    let w := floorDilation (p * q) (Nat.mul_pos hp hq) f
    let r := t - twoPrimePacket f p q hp hq a b 0
    ‖t - twoPrimePacket f p q hp hq a b k‖ ^ 2 =
      ‖r‖ ^ 2 - (inner ℝ r w) ^ 2 / ‖w‖ ^ 2 +
        ‖w‖ ^ 2 * (k - inner ℝ r w / ‖w‖ ^ 2) ^ 2 := by
  dsimp only
  let w := floorDilation (p * q) (Nat.mul_pos hp hq) f
  let r := t - twoPrimePacket f p q hp hq a b 0
  have he : t - twoPrimePacket f p q hp hq a b k = r - k • w := by
    dsimp [r, w, twoPrimePacket]
    rw [add_zero, add_smul]
    abel
  change ‖t - twoPrimePacket f p q hp hq a b k‖ ^ 2 =
    ‖r‖ ^ 2 - (inner ℝ r w) ^ 2 / ‖w‖ ^ 2 +
      ‖w‖ ^ 2 * (k - inner ℝ r w / ‖w‖ ^ 2) ^ 2
  rw [he, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  field_simp [hnorm]
  ring

end RiemannResearch.RH.QSquarefreeLatticePackets
