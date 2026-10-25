/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalKernelScreening
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.QSquarefreeKernelLocalization
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Effective complete prime-square screening

Source: the user's arithmetic-kernel screening handoff, 25 October 2026,
and its continuation. Odd-prime-square radical rows annihilate both the
actual legal stage and the constant target. Their supports, including
after applying B, are disjoint. Weighted Bessel gives the complete
screening-gain tail bound 4*||k||^2/P^4. Finite cutoff screening therefore
differs from complete prime-square screening by at most 4*zeta(2) whenever
the cutoff P satisfies n^2 <= P^4.

All sums and physical Hilbert norms here are complete. The exact Schur
subtraction and every screening square are retained. No uniform bound
for the surviving error-weighted energy, and no unconditional RH theorem,
is asserted.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSquareKernelScreening
open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoProbability
open QShiftedReciprocal QSquarefreeCorrectionKernel QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.OrthogonalKernelScreening
open RiemannResearch.LinearAlgebra
open Filter


def primeSquareSupport (p : ℕ) : Finset ℕ := {p ^ 2, p ^ 2 - 1, p, p - 1}

private theorem support_disjoint_of_mod_two {p q : ℕ}
    (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : p ≠ q)
    (hpq2 : p ≠ q ^ 2) (hp2q : p ^ 2 ≠ q) :
    Disjoint (primeSquareSupport p) (primeSquareSupport q) := by
  have hp2 : p ^ 2 % 2 = 1 := by simp [pow_two, Nat.mul_mod, hp]
  have hq2 : q ^ 2 % 2 = 1 := by simp [pow_two, Nat.mul_mod, hq]
  have hp2q2 : p ^ 2 ≠ q ^ 2 := by
    intro he
    rcases lt_or_gt_of_ne hpq with hlt | hgt <;> nlinarith
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [primeSquareSupport, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with h1 | h1 | h1 | h1 <;>
    rcases hy with h2 | h2 | h2 | h2 <;> omega

private theorem prime_ne_square {p q : ℕ} (hq : Nat.Prime q)
    (hp : 2 ≤ p) : q ≠ p ^ 2 := by
  intro he
  have hdiv : p ∣ q := ⟨p, by simpa [pow_two] using he⟩
  rcases (Nat.dvd_prime hq).mp hdiv with h | h
  · omega
  · nlinarith

private theorem prime_mod_two {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) : p % 2 = 1 := by
  have hlt : p % 2 < 2 := Nat.mod_lt p (by decide)
  have hn : p % 2 ≠ 0 := by
    intro he
    have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero he
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · omega
    · exact hp2 h.symm
  omega

theorem primeSquareSupport_disjoint {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    Disjoint (primeSquareSupport p) (primeSquareSupport q) := by
  apply support_disjoint_of_mod_two (prime_mod_two hp hp2) (prime_mod_two hq hq2) hpq
  · exact prime_ne_square hp hq.two_le
  · exact Ne.symm (prime_ne_square hq hp.two_le)

def primeSquareVector (p : ℕ) : QHilbert :=
  evaluation (p ^ 2) - evaluation (p ^ 2 - 1) - evaluation p + evaluation (p - 1)

theorem inner_primeSquareVector (f : QHilbert) (p : ℕ) :
    inner ℝ f (primeSquareVector p) =
      qSequence f (p ^ 2) - qSequence f (p ^ 2 - 1) -
        qSequence f p + qSequence f (p - 1) := by
  simp only [primeSquareVector, inner_add_right, inner_sub_right, inner_evaluation]

theorem primeSquareVector_inner_residue (p d : ℕ) (hp : 0 < p)
    (hd : Squarefree d) : inner ℝ (primeSquareVector p) (qResidue d) = 0 := by
  rw [real_inner_comm, inner_primeSquareVector, qSequence_qResidue]
  have he := hd.dvd_pow_iff_dvd (y := p) (by decide : 2 ≠ 0)
  have h1 := Pareto.residue_difference d (p ^ 2) (pow_pos hp _)
  have h2 := Pareto.residue_difference d p hp
  have hh : Pareto.residue d (p ^ 2) - Pareto.residue d (p ^ 2 - 1) =
      Pareto.residue d p - Pareto.residue d (p - 1) := by
    simp only [h1, h2, he]
  change ((p ^ 2 % d : ℕ) : ℝ) - (((p ^ 2 - 1) % d : ℕ) : ℝ) =
    ((p % d : ℕ) : ℝ) - (((p - 1) % d : ℕ) : ℝ) at hh
  change ((p ^ 2 % d : ℕ) : ℝ) / d - (((p ^ 2 - 1) % d : ℕ) : ℝ) / d -
    ((p % d : ℕ) : ℝ) / d + (((p - 1) % d : ℕ) : ℝ) / d = 0
  rw [← sub_div, hh]
  ring

theorem primeSquareVector_inner_stage (N p : ℕ) (hp : 0 < p)
    {f : QHilbert} (hf : f ∈ stage N) : inner ℝ (primeSquareVector p) f = 0 := by
  have hs : Submodule.span ℝ (Set.range squarefreeAtom) ≤
      (innerSL ℝ (primeSquareVector p)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ (primeSquareVector p) (squarefreeAtom i) = 0
    by_cases hi : Squarefree (i + 2)
    · simp only [squarefreeAtom, if_pos hi]
      exact primeSquareVector_inner_residue p (i + 2) hp hi
    · simp [squarefreeAtom, hi]
  exact hs (walkSpan_le squarefreeAtom id N hf)

theorem primeSquareVector_inner_one (p : ℕ) (hp : 2 ≤ p) :
    inner ℝ (primeSquareVector p) qOne = 0 := by
  rw [real_inner_comm, inner_primeSquareVector, qSequence_qOne]
  have hp2 : 1 < p ^ 2 := by nlinarith
  simp [qOneSequence, show p ^ 2 - 1 ≠ 0 by omega,
    show p ≠ 0 by omega, show p - 1 ≠ 0 by omega]

theorem residual_inner_primeSquareVector (N p : ℕ) (hp : 2 ≤ p) :
    inner ℝ (residual N) (primeSquareVector p) = 0 := by
  rw [real_inner_comm, ZetaTwoOptimizerStage.residual, inner_sub_right,
    primeSquareVector_inner_one p hp,
    optimizer, primeSquareVector_inner_stage N p (by omega)
      ((stage N).starProjection_apply_mem qOne), sub_self]

theorem evaluation_inner (m n : ℕ) :
    inner ℝ (evaluation m) (evaluation n) =
      if m = n then zetaTwo * (m : ℝ) ^ 2 else 0 := by
  cases m with
  | zero => simp [evaluation]
  | succ m =>
    cases n with
    | zero => simp [evaluation]
    | succ n =>
      rw [inner_evaluation, qSequence_succ]
      by_cases h : m = n
      · subst n
        simp only [evaluation, lp.single_apply, Pi.single_eq_same]
        rw [div_div, ← pow_two, Real.sq_sqrt (qWeight_pos m).le]
        simp [qWeight, positiveQWeight]
      · simp [evaluation, lp.single_apply, h, Ne.symm h]

theorem primeSquareVector_norm_sq (p : ℕ) (hp : 3 ≤ p) :
    ‖primeSquareVector p‖ ^ 2 = zetaTwo * (2 * (p : ℝ) ^ 4 - 2 * p + 2) := by
  have hsep : p + 1 < p ^ 2 := by nlinarith
  rw [← real_inner_self_eq_norm_sq]
  simp only [primeSquareVector, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right, evaluation_inner]
  simp only [ite_true, if_neg (show p ^ 2 ≠ p ^ 2 - 1 by omega),
    if_neg (show p ^ 2 ≠ p by omega), if_neg (show p ^ 2 ≠ p - 1 by omega),
    if_neg (show p ^ 2 - 1 ≠ p ^ 2 by omega), if_neg (show p ^ 2 - 1 ≠ p by omega),
    if_neg (show p ^ 2 - 1 ≠ p - 1 by omega), if_neg (show p ≠ p ^ 2 by omega),
    if_neg (show p ≠ p ^ 2 - 1 by omega), if_neg (show p ≠ p - 1 by omega),
    if_neg (show p - 1 ≠ p ^ 2 by omega), if_neg (show p - 1 ≠ p ^ 2 - 1 by omega),
    if_neg (show p - 1 ≠ p by omega)]
  push_cast [Nat.cast_sub (show 1 ≤ p ^ 2 by omega), Nat.cast_sub (show 1 ≤ p by omega)]
  ring

theorem evaluation_apply_zero (m i : ℕ) (h : i + 1 ≠ m) : evaluation m i = 0 := by
  cases m with
  | zero => rfl
  | succ m => simp [evaluation, lp.single_apply, show i ≠ m by omega]

theorem primeSquareVector_apply_zero (p i : ℕ)
    (hi : i + 1 ∉ primeSquareSupport p) : primeSquareVector p i = 0 := by
  have h1 : i + 1 ≠ p ^ 2 := by intro h; apply hi; simp [primeSquareSupport, h]
  have h2 : i + 1 ≠ p ^ 2 - 1 := by intro h; apply hi; simp [primeSquareSupport, h]
  have h3 : i + 1 ≠ p := by intro h; apply hi; simp [primeSquareSupport, h]
  have h4 : i + 1 ≠ p - 1 := by intro h; apply hi; simp [primeSquareSupport, h]
  change evaluation (p ^ 2) i - evaluation (p ^ 2 - 1) i - evaluation p i +
    evaluation (p - 1) i = 0
  rw [evaluation_apply_zero _ _ h1, evaluation_apply_zero _ _ h2,
    evaluation_apply_zero _ _ h3, evaluation_apply_zero _ _ h4]
  ring

private theorem inner_zero_disjoint (f g : QHilbert) (s t : Finset ℕ)
    (hf : ∀ i, i + 1 ∉ s → f i = 0) (hg : ∀ i, i + 1 ∉ t → g i = 0)
    (h : Disjoint s t) : inner ℝ f g = 0 := by
  rw [lp.inner_eq_tsum]
  trans ∑' _ : ℕ, (0 : ℝ)
  · apply tsum_congr
    intro i
    change g i * f i = 0
    by_cases hi : i + 1 ∈ s
    · have ht : i + 1 ∉ t := fun ht => Finset.disjoint_left.mp h hi ht
      rw [hg i ht, zero_mul]
    · rw [hf i hi, mul_zero]
  · simp

theorem primeSquareVector_orthogonal {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : inner ℝ (primeSquareVector p) (primeSquareVector q) = 0 :=
  inner_zero_disjoint _ _ _ _ (primeSquareVector_apply_zero p)
    (primeSquareVector_apply_zero q) (primeSquareSupport_disjoint hp hq hp2 hq2 hpq)

theorem smoothed_primeSquareVector_orthogonal {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : inner ℝ (B (primeSquareVector p)) (B (primeSquareVector q)) = 0 := by
  apply inner_zero_disjoint _ _ (primeSquareSupport p) (primeSquareSupport q)
  · intro i hi
    rw [B_apply, primeSquareVector_apply_zero p i hi, zero_div]
  · intro i hi
    rw [B_apply, primeSquareVector_apply_zero q i hi, zero_div]
  · exact primeSquareSupport_disjoint hp hq hp2 hq2 hpq

theorem B_evaluation (m : ℕ) : B (evaluation m) =
    (1 / ((m : ℝ) + 1)) • evaluation m := by
  cases m with
  | zero => simp [evaluation]
  | succ m =>
    simpa only [Nat.cast_add, Nat.cast_one,
      show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring] using B_evaluation_succ m

theorem smoothed_evaluation_inner (m n : ℕ) :
    inner ℝ (B (evaluation m)) (B (evaluation n)) =
      if m = n then zetaTwo * ((m : ℝ) / (m + 1)) ^ 2 else 0 := by
  rw [B_evaluation, B_evaluation, real_inner_smul_left, real_inner_smul_right,
    evaluation_inner]
  by_cases h : m = n
  · subst n
    simp only [ite_true]
    ring
  · simp [h]

private theorem smoothed_diagonal_le (m : ℕ) :
    zetaTwo * ((m : ℝ) / (m + 1)) ^ 2 ≤ zetaTwo := by
  have h0 : 0 ≤ (m : ℝ) / (m + 1) := by positivity
  have h1 : (m : ℝ) / (m + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hs : ((m : ℝ) / (m + 1)) ^ 2 ≤ 1 := by nlinarith
  nlinarith [zetaTwo_pos]

theorem smoothed_primeSquareVector_norm_sq_le (p : ℕ) (hp : 3 ≤ p) :
    ‖B (primeSquareVector p)‖ ^ 2 ≤ 4 * zetaTwo := by
  have hsep : p + 1 < p ^ 2 := by nlinarith
  rw [primeSquareVector, map_add, map_sub, map_sub, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
    smoothed_evaluation_inner]
  simp only [ite_true, if_neg (show p ^ 2 ≠ p ^ 2 - 1 by omega),
    if_neg (show p ^ 2 ≠ p by omega), if_neg (show p ^ 2 ≠ p - 1 by omega),
    if_neg (show p ^ 2 - 1 ≠ p ^ 2 by omega), if_neg (show p ^ 2 - 1 ≠ p by omega),
    if_neg (show p ^ 2 - 1 ≠ p - 1 by omega), if_neg (show p ≠ p ^ 2 by omega),
    if_neg (show p ≠ p ^ 2 - 1 by omega), if_neg (show p ≠ p - 1 by omega),
    if_neg (show p - 1 ≠ p ^ 2 by omega), if_neg (show p - 1 ≠ p ^ 2 - 1 by omega),
    if_neg (show p - 1 ≠ p by omega)]
  linarith [smoothed_diagonal_le (p ^ 2), smoothed_diagonal_le (p ^ 2 - 1),
    smoothed_diagonal_le p, smoothed_diagonal_le (p - 1)]

theorem primeSquareVector_norm_sq_lower (p : ℕ) (hp : 3 ≤ p) :
    zetaTwo * (p : ℝ) ^ 4 ≤ ‖primeSquareVector p‖ ^ 2 := by
  rw [primeSquareVector_norm_sq p hp]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpoly : (p : ℝ) ^ 4 ≤ 2 * (p : ℝ) ^ 4 - 2 * p + 2 := by
    nlinarith [sq_nonneg ((p : ℝ) - 1), sq_nonneg ((p : ℝ)^2 - 1)]
  exact mul_le_mul_of_nonneg_left hpoly zetaTwo_pos.le


theorem primeSquareVector_norm_sq_pos (p : ℕ) (hp : 3 ≤ p) :
    0 < ‖primeSquareVector p‖ ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  exact lt_of_lt_of_le (mul_pos zetaTwo_pos (pow_pos hpR 4))
    (primeSquareVector_norm_sq_lower p hp)

theorem smoothed_primeSquareVector_ratio (P p : ℕ)
    (hP : 0 < P) (hp : 3 ≤ p) (hPp : P ≤ p) :
    ‖B (primeSquareVector p)‖ ^ 2 ≤
      (4 / (P : ℝ) ^ 4) * ‖primeSquareVector p‖ ^ 2 := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hle : (P : ℝ) ≤ p := by exact_mod_cast hPp
  have hpow : (P : ℝ) ^ 4 ≤ (p : ℝ) ^ 4 := pow_le_pow_left₀ hPR.le hle 4
  have hn : zetaTwo * (P : ℝ) ^ 4 ≤ ‖primeSquareVector p‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left hpow zetaTwo_pos.le).trans
      (primeSquareVector_norm_sq_lower p hp)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hPR 4)).mpr
  have hb := mul_le_mul_of_nonneg_right (smoothed_primeSquareVector_norm_sq_le p hp)
    (pow_nonneg hPR.le 4)
  nlinarith

def primeSquareGain (k : QHilbert) (p : ℕ) : ℝ :=
  (inner ℝ (B k) (primeSquareVector p)) ^ 2 / ‖primeSquareVector p‖ ^ 2

abbrev OddPrime := {p : ℕ // Nat.Prime p ∧ p ≠ 2}
abbrev AbovePrime (P : ℕ) := {p : ℕ // Nat.Prime p ∧ p ≠ 2 ∧ P < p}

theorem primeSquareGain_complete_tail (k : QHilbert) (P : ℕ) (hP : 0 < P) :
    Summable (fun p : AbovePrime P => primeSquareGain k p) ∧
      (∑' p : AbovePrime P, primeSquareGain k p) ≤
        (4 / (P : ℝ) ^ 4) * ‖k‖ ^ 2 := by
  have hp (p : AbovePrime P) : 3 ≤ p.val := by
    have := p.property.1.two_le
    have := p.property.2.1
    omega
  have h := weighted_bessel_complete k
    (fun p : AbovePrime P => B (primeSquareVector p))
    (fun p : AbovePrime P => ‖primeSquareVector p‖ ^ 2)
    (fun p => primeSquareVector_norm_sq_pos p (hp p))
    (4 / (P : ℝ) ^ 4) (by positivity)
    (fun p q hpq => smoothed_primeSquareVector_orthogonal
      p.property.1 q.property.1 p.property.2.1 q.property.2.1
      (fun h => hpq (Subtype.ext h)))
    (fun p => smoothed_primeSquareVector_ratio P p hP (hp p) p.property.2.2.le)
  simpa only [primeSquareGain, ← B_symmetric] using h

theorem kernel_primeSquareGain_complete_tail (N n P : ℕ) (hP : 0 < P) :
    (∑' p : AbovePrime P, primeSquareGain (kernel N (n + 1)) p) ≤
      (4 / (P : ℝ) ^ 4) * (zetaTwo * ((n : ℝ) + 1) ^ 2) := by
  exact (primeSquareGain_complete_tail (kernel N (n + 1)) P hP).2.trans
    (mul_le_mul_of_nonneg_left (kernel_norm_sq_le N n) (by positivity))

theorem residualized_inner_primeSquareVector (N n p : ℕ) (hp : 0 < p) :
    inner ℝ (primeSquareVector p) (residualizedKernel N n) =
      inner ℝ (primeSquareVector p) (B (kernel N n)) := by
  rw [residualizedKernel, inner_sub_right,
    primeSquareVector_inner_stage N p hp ((stage N).starProjection_apply_mem _), sub_zero]

theorem finite_primeSquare_screening (N n : ℕ) {ι : Type*} [Fintype ι]
    (p : ι → OddPrime) (hinj : Function.Injective p) :
    ‖finiteSchurResidual (residualizedKernel N n)
      (fun i => primeSquareVector (p i))
      (fun i => inner ℝ (primeSquareVector (p i)) (B (kernel N n)) /
        ‖primeSquareVector (p i)‖ ^ 2)‖ ^ 2 =
      kernelEnergy N n - ∑ i, primeSquareGain (kernel N n) (p i) ∧
    (qSequence (movingCorrection N) n) ^ 2 ≤
      error N * (kernelEnergy N n - ∑ i, primeSquareGain (kernel N n) (p i)) := by
  have hp (i : ι) : 3 ≤ (p i).val := by
    have := (p i).property.1.two_le
    have := (p i).property.2
    omega
  have hz (i : ι) : ‖primeSquareVector (p i)‖ ^ 2 ≠ 0 :=
    ne_of_gt (primeSquareVector_norm_sq_pos (p i) (hp i))
  have ho (i j : ι) (hij : i ≠ j) :
      inner ℝ (primeSquareVector (p i)) (primeSquareVector (p j)) = 0 :=
    primeSquareVector_orthogonal (p i).property.1 (p j).property.1
      (p i).property.2 (p j).property.2
      (fun h => hij (hinj (Subtype.ext h)))
  have he (i : ι) := residualized_inner_primeSquareVector N n (p i) (by have := hp i; omega)
  constructor
  · have h := orthogonal_screening_norm_sq (residualizedKernel N n)
      (fun i => primeSquareVector (p i)) hz ho
    simpa only [he, kernelEnergy, primeSquareGain, real_inner_comm] using h
  · rw [movingCorrection_eq_pairing]
    have h := pairing_sq_le_orthogonal (ZetaTwoOptimizerStage.residual N) (residualizedKernel N n)
      (fun i => primeSquareVector (p i)) hz ho
      (fun i => residual_inner_primeSquareVector N (p i) (by have := hp i; omega))
    simpa only [he, kernelEnergy, error, primeSquareGain, real_inner_comm] using h


theorem primeSquareGain_summable (k : QHilbert) :
    Summable (fun p : OddPrime => primeSquareGain k p) := by
  have hp (p : OddPrime) : 3 ≤ p.val := by
    have := p.property.1.two_le
    have := p.property.2
    omega
  have h := weighted_bessel_complete (B k)
    (fun p : OddPrime => primeSquareVector p)
    (fun p : OddPrime => ‖primeSquareVector p‖ ^ 2)
    (fun p => primeSquareVector_norm_sq_pos p (hp p)) 1 zero_le_one
    (fun p q hpq => primeSquareVector_orthogonal p.property.1 q.property.1
      p.property.2 q.property.2 (fun h => hpq (Subtype.ext h)))
    (fun p => by simp)
  exact h.1

def completePrimeSquareEnergy (N n : ℕ) : ℝ :=
  kernelEnergy N n - ∑' p : OddPrime, primeSquareGain (kernel N n) p

theorem completePrimeSquareEnergy_nonneg (N n : ℕ) :
    0 ≤ completePrimeSquareEnergy N n := by
  have hp (p : OddPrime) : 3 ≤ p.val := by
    have := p.property.1.two_le
    have := p.property.2
    omega
  have h := weighted_bessel_complete (residualizedKernel N n)
    (fun p : OddPrime => primeSquareVector p)
    (fun p : OddPrime => ‖primeSquareVector p‖ ^ 2)
    (fun p => primeSquareVector_norm_sq_pos p (hp p)) 1 zero_le_one
    (fun p q hpq => primeSquareVector_orthogonal p.property.1 q.property.1
      p.property.2 q.property.2 (fun h => hpq (Subtype.ext h)))
    (fun p => by simp)
  have he (p : OddPrime) : inner ℝ (residualizedKernel N n) (primeSquareVector p) =
      inner ℝ (B (kernel N n)) (primeSquareVector p) := by
    rw [real_inner_comm, residualized_inner_primeSquareVector N n p
      (by have := hp p; omega), real_inner_comm]
  have hh : (∑' p : OddPrime, primeSquareGain (kernel N n) p) ≤ kernelEnergy N n := by
    simpa only [he, one_mul, primeSquareGain, kernelEnergy] using h.2
  exact sub_nonneg.mpr hh

theorem movingCorrection_sq_le_completePrimeSquare (N n : ℕ) :
    (qSequence (movingCorrection N) n) ^ 2 ≤ error N * completePrimeSquareEnergy N n := by
  have hs := primeSquareGain_summable (kernel N n)
  have ht : Tendsto
      (fun s : Finset OddPrime =>
        error N * (kernelEnergy N n - ∑ p ∈ s, primeSquareGain (kernel N n) p))
      atTop (𝓝 (error N * completePrimeSquareEnergy N n)) :=
    (tendsto_const_nhds.sub hs.hasSum).const_mul (error N)
  apply ge_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro s
  rw [← Finset.sum_coe_sort s (fun p => primeSquareGain (kernel N n) p)]
  exact (finite_primeSquare_screening N n (fun p : s => p.val) Subtype.val_injective).2

theorem completePrimeSquareEnergy_exact (N n : ℕ) :
    completePrimeSquareEnergy N n =
      ‖B (kernel N n)‖ ^ 2 -
      ‖(stage N).starProjection (B (kernel N n))‖ ^ 2 -
      ∑' p : OddPrime, primeSquareGain (kernel N n) p := by
  rw [completePrimeSquareEnergy, kernelEnergy_exact]


theorem primeSquareGain_truncation (k : QHilbert) (P : ℕ) (hP : 0 < P)
    (s : Finset OddPrime) (hcover : ∀ p : OddPrime, p.val ≤ P → p ∈ s) :
    0 ≤ (∑' p : OddPrime, primeSquareGain k p) - ∑ p ∈ s, primeSquareGain k p ∧
    (∑' p : OddPrime, primeSquareGain k p) - ∑ p ∈ s, primeSquareGain k p ≤
      (4 / (P : ℝ) ^ 4) * ‖k‖ ^ 2 := by
  have hp (p : {p : OddPrime // p ∉ s}) : 3 ≤ p.val.val := by
    have := p.val.property.1.two_le
    have := p.val.property.2
    omega
  have hPp (p : {p : OddPrime // p ∉ s}) : P ≤ p.val.val := by
    have hh : ¬p.val.val ≤ P := fun hh => p.property (hcover p.val hh)
    omega
  have h := weighted_bessel_complete k
    (fun p : {p : OddPrime // p ∉ s} => B (primeSquareVector p.val))
    (fun p : {p : OddPrime // p ∉ s} => ‖primeSquareVector p.val‖ ^ 2)
    (fun p => primeSquareVector_norm_sq_pos p.val (hp p))
    (4 / (P : ℝ) ^ 4) (by positivity)
    (fun p q hpq => smoothed_primeSquareVector_orthogonal
      p.val.property.1 q.val.property.1 p.val.property.2 q.val.property.2
      (fun h => hpq (Subtype.ext (Subtype.ext h))))
    (fun p => smoothed_primeSquareVector_ratio P p.val hP (hp p) (hPp p))
  have ht : (∑' p : {p : OddPrime // p ∉ s}, primeSquareGain k p.val) ≤
      (4 / (P : ℝ) ^ 4) * ‖k‖ ^ 2 := by
    simpa only [primeSquareGain, ← B_symmetric] using h.2
  have he := (primeSquareGain_summable k).sum_add_tsum_subtype_compl s
  have hEq : (∑' p : OddPrime, primeSquareGain k p) - ∑ p ∈ s, primeSquareGain k p =
      ∑' p : {p : OddPrime // p ∉ s}, primeSquareGain k p.val := by linarith
  rw [hEq]
  exact ⟨tsum_nonneg (fun p => div_nonneg (sq_nonneg _) (sq_nonneg _)), ht⟩

noncomputable def primeCutoff (P : ℕ) : Finset OddPrime :=
  (Finset.range (P + 1)).subtype (fun p : ℕ => Nat.Prime p ∧ p ≠ 2)

theorem primeCutoff_covers (P : ℕ) (p : OddPrime) (hp : p.val ≤ P) :
    p ∈ primeCutoff P := by
  simp only [primeCutoff, Finset.mem_subtype, Finset.mem_range]
  omega

def finitePrimeSquareEnergy (N n P : ℕ) : ℝ :=
  kernelEnergy N n - ∑ p ∈ primeCutoff P, primeSquareGain (kernel N n) p

theorem finite_complete_energy_gap (N n P : ℕ) (hP : 0 < P) :
    0 ≤ finitePrimeSquareEnergy N (n + 1) P - completePrimeSquareEnergy N (n + 1) ∧
    finitePrimeSquareEnergy N (n + 1) P - completePrimeSquareEnergy N (n + 1) ≤
      (4 / (P : ℝ) ^ 4) * (zetaTwo * ((n : ℝ) + 1) ^ 2) := by
  have h := primeSquareGain_truncation (kernel N (n + 1)) P hP
    (primeCutoff P) (primeCutoff_covers P)
  have he : finitePrimeSquareEnergy N (n + 1) P - completePrimeSquareEnergy N (n + 1) =
      (∑' p : OddPrime, primeSquareGain (kernel N (n + 1)) p) -
        ∑ p ∈ primeCutoff P, primeSquareGain (kernel N (n + 1)) p := by
    unfold finitePrimeSquareEnergy completePrimeSquareEnergy
    ring
  rw [he]
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (kernel_norm_sq_le N n) (by positivity))⟩

theorem finite_complete_energy_gap_le_constant (N n P : ℕ) (hP : 0 < P)
    (hsize : ((n : ℝ) + 1) ^ 2 ≤ (P : ℝ) ^ 4) :
    finitePrimeSquareEnergy N (n + 1) P - completePrimeSquareEnergy N (n + 1) ≤
      4 * zetaTwo := by
  apply (finite_complete_energy_gap N n P hP).2.trans
  have hpR : (0 : ℝ) < P := by exact_mod_cast hP
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hpR 4)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsize zetaTwo_pos.le]

end RiemannResearch.RH.QPrimeSquareKernelScreening
