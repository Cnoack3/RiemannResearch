/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring
import RiemannResearch.RH.ZetaTwoParitySignal
import Mathlib.Tactic.NormNum

/-!
# The exact inverse-square Fourier Gram kernel

Source: user-provided squarefree profinite lattice research agenda,
16 October 2026, Target 4. The proof is the direct absolutely convergent
weighted-character calculation. Pairings here are explicitly linear in
the first argument; Mathlib's complex `inner` has the opposite convention.

Every sum uses the complete physical Q law. These identities and the
entrywise bound do not assert an RH-strength bound for growing blocks.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QFourierKernel
open RiemannResearch.RH.ZetaTwoHilbert

/-- Ordinary additive characters on the positive physical coordinates. -/
def character (theta : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (theta : ℂ))

@[simp] theorem character_norm (theta : ℝ) (n : ℕ) :
    ‖character theta n‖ = 1 := by
  simp [character, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

@[simp] theorem character_zero (n : ℕ) : character 0 n = 1 := by
  simp [character]

/-- The sign of the frequency difference records linearity in the first slot. -/
theorem character_mul_conj (theta phi : ℝ) (n : ℕ) :
    character theta n * star (character phi n) = character (theta - phi) n := by
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.ofReal_sub, map_ofNat] <;> ring

theorem weighted_character_norm (theta : ℝ) (n : ℕ) :
    ‖(positiveQWeight n : ℂ) * character theta n‖ = positiveQWeight n := by
  rw [norm_mul, character_norm, mul_one]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (positiveQWeight_nonneg n)]

theorem weighted_character_norm_summable (theta : ℝ) :
    Summable (fun n => ‖(positiveQWeight n : ℂ) * character theta n‖) := by
  simpa only [weighted_character_norm] using positiveQWeight_summable

theorem weighted_character_summable (theta : ℝ) :
    Summable (fun n => (positiveQWeight n : ℂ) * character theta n) :=
  (weighted_character_norm_summable theta).of_norm

/-- `K_Q(theta)`: normalization is already in `positiveQWeight`. -/
def kernel (theta : ℝ) : ℂ :=
  ∑' n : ℕ, (positiveQWeight n : ℂ) * character theta n

/-- Literal Q pairing, linear in the first argument. -/
def pairing (f g : ℕ → ℂ) : ℂ :=
  ∑' n : ℕ, (positiveQWeight n : ℂ) * (f n * star (g n))

theorem character_gram (theta phi : ℝ) :
    pairing (character theta) (character phi) = kernel (theta - phi) := by
  unfold pairing kernel
  apply tsum_congr
  intro n
  rw [character_mul_conj]

@[simp] theorem kernel_zero : kernel 0 = 1 := by
  simp only [kernel, character_zero, mul_one]
  rw [← Complex.ofReal_tsum, positiveQWeight_tsum]
  rfl

/-- A genuine bound on every entry of the complete Q Fourier Gram matrix. -/
theorem kernel_norm_le_one (theta : ℝ) : ‖kernel theta‖ ≤ 1 := by
  calc
    ‖kernel theta‖ ≤ ∑' n, ‖(positiveQWeight n : ℂ) * character theta n‖ :=
      norm_tsum_le_tsum_norm (weighted_character_norm_summable theta)
    _ = 1 := by simp only [weighted_character_norm, positiveQWeight_tsum]

/-- Finite Fourier synthesis, allowing arbitrary real frequencies. -/
def synthesis {ι : Type*} [Fintype ι] (theta : ι → ℝ) (a : ι → ℂ)
    (n : ℕ) : ℂ := ∑ i, a i * character (theta i) n

theorem synthesis_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (theta : ι → ℝ) (phi : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) :
    pairing (synthesis theta a) (synthesis phi b) =
      ∑ i, ∑ j, a i * star (b j) * kernel (theta i - phi j) := by
  classical
  have hs (i : ι) (j : κ) : Summable (fun n : ℕ =>
      (a i * star (b j)) *
        ((positiveQWeight n : ℂ) * character (theta i - phi j) n)) :=
    (weighted_character_summable _).mul_left _
  have hexpand (n : ℕ) :
      (positiveQWeight n : ℂ) * (synthesis theta a n * star (synthesis phi b n)) =
      ∑ i, ∑ j, (a i * star (b j)) *
        ((positiveQWeight n : ℂ) * character (theta i - phi j) n) := by
    simp only [synthesis, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← character_mul_conj]
    ring
  unfold pairing
  simp_rw [hexpand]
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_mul_left]
  rfl

/-- Finite cyclic characters are the rational-frequency physical characters. -/
theorem stdAddChar_mul_natCast {L : ℕ} [NeZero L] (j : ZMod L) (n : ℕ) :
    ZMod.stdAddChar (j * (n : ZMod L)) = character ((j.val : ℝ) / L) n := by
  have he : j * (n : ZMod L) = (((j.val : ℤ) * (n : ℤ) : ℤ) : ZMod L) := by
    simp
  rw [he, ZMod.stdAddChar_coe]
  unfold character
  push_cast
  congr 1
  ring

/-- Normalized discrete Fourier coefficients of a complete residue table. -/
def coefficient {L : ℕ} [NeZero L] (f : ZMod L → ℂ) (j : ZMod L) : ℂ :=
  (L : ℂ)⁻¹ * ZMod.dft f j

/-- DFT inversion supplies the Fourier representation for every periodic table,
including legal atoms and the complete CRT carry functions. -/
theorem synthesis_coefficient {L : ℕ} [NeZero L] (f : ZMod L → ℂ) (n : ℕ) :
    synthesis (fun j : ZMod L => (j.val : ℝ) / L) (coefficient f) n =
      f (n : ZMod L) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) (n : ZMod L)
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul] at hinv
  calc
    _ = (L : ℂ)⁻¹ * ∑ j : ZMod L,
        ZMod.stdAddChar (j * (n : ZMod L)) * ZMod.dft f j := by
      unfold synthesis coefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [stdAddChar_mul_natCast]
      ring
    _ = _ := hinv

/-- Exact Fourier-kernel Gram formula for arbitrary periodic tables. The two
periods may differ. Neither Haar orthogonality nor a finite physical cutoff is used. -/
theorem periodic_gram {L M : ℕ} [NeZero L] [NeZero M]
    (f : ZMod L → ℂ) (g : ZMod M → ℂ) :
    pairing (fun n : ℕ => f (n : ZMod L)) (fun n : ℕ => g (n : ZMod M)) =
      ∑ i : ZMod L, ∑ j : ZMod M,
        coefficient f i * star (coefficient g j) *
          kernel ((i.val : ℝ) / L - (j.val : ℝ) / M) := by
  have hf : (fun n : ℕ => f (n : ZMod L)) =
      synthesis (fun i : ZMod L => (i.val : ℝ) / L) (coefficient f) :=
    funext (fun n => (synthesis_coefficient f n).symm)
  have hg : (fun n : ℕ => g (n : ZMod M)) =
      synthesis (fun j : ZMod M => (j.val : ℝ) / M) (coefficient g) :=
    funext (fun n => (synthesis_coefficient g n).symm)
  rw [hf, hg, synthesis_gram]

/-- The complete value table of a legal residue atom. -/
def residueTable (d : ℕ) [NeZero d] (r : ZMod d) : ℂ := (r.val : ℂ) / (d : ℂ)

theorem residueTable_physical (d : ℕ) [NeZero d] (n : ℕ) :
    residueTable d (n : ZMod d) =
      (RiemannResearch.RH.ArithmeticCumulative.residueFraction d n : ℂ) := by
  simp [residueTable, RiemannResearch.RH.ArithmeticCumulative.residueFraction,
    ZMod.val_natCast]

/-- Actual residue Gram entries have the exact finite non-Haar Fourier formula. -/
theorem qResidue_gram (d e : ℕ) [NeZero d] [NeZero e] :
    (inner ℝ (qResidue d) (qResidue e) : ℂ) =
      ∑ i : ZMod d, ∑ j : ZMod e,
        coefficient (residueTable d) i * star (coefficient (residueTable e) j) *
          kernel ((i.val : ℝ) / d - (j.val : ℝ) / e) := by
  rw [← periodic_gram]
  rw [qInner_weighted, qSequence_qResidue, qSequence_qResidue]
  rw [Complex.ofReal_tsum]
  unfold pairing
  apply tsum_congr
  intro n
  simp [residueTable_physical, Complex.ofReal_mul, mul_assoc]

/-- Exact complete-block cancellation: the all-ones Fourier packet has Q energy
one for every block size. The packet is `L * 1_{L divides n}` and includes the
constant frequency; this does not make it a legal residue approximant. -/
theorem complete_block_sum (L : ℕ) [NeZero L] :
    (∑ i : ZMod L, ∑ j : ZMod L,
      kernel ((i.val : ℝ) / L - (j.val : ℝ) / L)) = 1 := by
  classical
  let f : ZMod L → ℂ := fun j => if j = 0 then (L : ℂ) else 0
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hcoeff (i : ZMod L) : coefficient f i = 1 := by
    simp [coefficient, ZMod.dft_apply, f, smul_eq_mul, hLC]
  have hgram := periodic_gram f f
  simp only [hcoeff, star_one, one_mul] at hgram
  rw [← hgram]
  calc
    _ = ∑' n : ℕ, (((L : ℝ)^2 *
        (if L ∣ n then positiveQWeight n else 0) : ℝ) : ℂ) := by
      unfold pairing
      apply tsum_congr
      intro n
      by_cases hd : L ∣ n <;>
        simp [f, ZMod.natCast_eq_zero_iff, hd, pow_two] <;> ring
    _ = (((L : ℝ)^2 *
        (∑' n : ℕ, if L ∣ n then positiveQWeight n else 0) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_tsum, tsum_mul_left]
    _ = 1 := by
      rw [RiemannResearch.RH.ZetaTwoParitySignal.positiveQWeight_dvd_tsum L
        (Nat.pos_of_ne_zero (NeZero.ne L))]
      simp [hLR]

end RiemannResearch.RH.QFourierKernel
