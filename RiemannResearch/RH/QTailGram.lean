/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLargeConductorCapacity
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual complete-tail Q Gram matrices

Source: user-provided periodicity argument, 16 October 2026, for independence
after removal of finitely many physical sites. The shift below removes exactly
physical sites 1,...,H in weighted l2 coordinates. No infinite physical tail
is truncated, and neither squarefreeness nor an RH hypothesis is needed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTailGram
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QCovarianceInvertibility
open QLargeConductorCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

/-- Restrict weighted coordinates to physical sites strictly beyond H. -/
def tailMap (H : ℕ) : QHilbert →ₗ[ℝ] QHilbert where
  toFun f := ⟨fun n => f (n + H), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).mpr
    have hs := (summable_nat_add_iff H).mpr (qCoordinate_square_summable f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

@[simp] theorem tailMap_apply (H : ℕ) (f : QHilbert) (n : ℕ) :
    tailMap H f n = f (n + H) := rfl

theorem tailMap_norm_sq (H : ℕ) (f : QHilbert) :
    ‖tailMap H f‖ ^ 2 = tailEnergy H f := by
  rw [qNorm_sq]
  rfl

/-- The shifted l2 space retains the original Q weights at all physical tail sites. -/
theorem tailMap_inner_physical (H : ℕ) (f g : QHilbert) :
    inner ℝ (tailMap H f) (tailMap H g) =
      ∑' n : ℕ, positiveQWeight (n + H + 1) *
        qSequence f (n + H + 1) * qSequence g (n + H + 1) := by
  rw [lp.inner_eq_tsum]
  congr 1
  funext n
  change g (n + H) * f (n + H) = _
  rw [qSequence_weighted_product]
  ring

theorem tailMap_zero_sequence (H : ℕ) (f : QHilbert) (hf : tailMap H f = 0)
    (n : ℕ) (hn : H < n) : qSequence f n = 0 := by
  have hc := congrArg (fun g : QHilbert => g (n - H - 1)) hf
  change f (n - H - 1 + H) = 0 at hc
  rw [show n = (n - H - 1 + H) + 1 by omega, qSequence_succ, hc, zero_div]

/-- Polarization of the exact physical head energy, retaining signed pairings. -/
theorem inner_head_tail (H : ℕ) (f g : QHilbert) (s r : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s)
    (hg : ∀ n, 0 < n → n ≤ H → qSequence g n = (n : ℝ) * r) :
    inner ℝ f g = inner ℝ (tailMap H f) (tailMap H g) +
      (H : ℝ) / zetaTwo * s * r := by
  have hfg : ∀ n, 0 < n → n ≤ H →
      qSequence (f + g) n = (n : ℝ) * (s + r) := by
    intro n hn hnH
    change qSequenceLinear (f + g) n = _
    rw [map_add]
    change qSequence f n + qSequence g n = _
    rw [hf n hn hnH, hg n hn hnH]
    ring
  have hfE := linear_head_energy H f s hf
  have hgE := linear_head_energy H g r hg
  have hfgE := linear_head_energy H (f + g) (s + r) hfg
  have hfull := norm_add_sq_real f g
  have htail := norm_add_sq_real (tailMap H f) (tailMap H g)
  rw [← map_add, tailMap_norm_sq, tailMap_norm_sq, tailMap_norm_sq] at htail
  nlinarith only [hfE, hgE, hfgE, hfull, htail]

variable {ι : Type*} [Fintype ι]

def tailResidue (H : ℕ) (d : ι → ℕ) (i : ι) : QHilbert :=
  tailMap H (qResidue (d i))

theorem synthesis_sequence (d : ι → ℕ) (c : ι → ℝ) (n : ℕ) :
    qSequence (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n =
      ∑ i, c i * residueFraction (d i) n := by
  change qSequenceLinear (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n = _
  rw [Fintype.linearCombination_apply, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, c i * qSequence (qResidue (d i)) n) = _
  simp only [qSequence_qResidue]

theorem tailMap_synthesis (H : ℕ) (d : ι → ℕ) (c : ι → ℝ) :
    tailMap H (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) =
      Fintype.linearCombination ℝ (tailResidue H d) c := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, tailResidue]

/-- A periodic residue synthesis cannot be supported on a finite physical head. -/
theorem tail_synthesis_zero (H : ℕ) (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (c : ι → ℝ)
    (hz : tailMap H (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) = 0) :
    Fintype.linearCombination ℝ (fun i => qResidue (d i)) c = 0 := by
  classical
  let L : ℕ := (∑ i, d i + 1).factorial
  have hL : 0 < L := Nat.factorial_pos _
  have hdL (i : ι) : d i ∣ L := by
    have hi : d i ≤ ∑ j, d j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    apply Nat.dvd_factorial (by have := hd i; omega)
    omega
  apply qSequence_injective
  funext n
  have hn : H < n + (H + 1) * L := by
    have hmul : H + 1 ≤ (H + 1) * L := Nat.le_mul_of_pos_right _ hL
    omega
  have ht := tailMap_zero_sequence H _ hz (n + (H + 1) * L) hn
  rw [synthesis_sequence] at ht
  have hp (i : ι) : residueFraction (d i) (n + (H + 1) * L) =
      residueFraction (d i) n :=
    residueFraction_period_of_dvd (d i) ((H + 1) * L)
      (dvd_mul_of_dvd_right (hdL i) (H + 1)) n
  simp_rw [hp] at ht
  rw [synthesis_sequence]
  have hzero : qSequence (0 : QHilbert) n = 0 := by
    cases n <;> simp [qSequence]
  rw [hzero]
  exact ht

omit [Fintype ι] in
theorem tailResidue_linearIndependent [Finite ι] (H : ℕ) (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    LinearIndependent ℝ (tailResidue H d) := by
  classical
  let := Fintype.ofFinite ι
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hz : tailMap H (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) = 0 := by
    rw [tailMap_synthesis, Fintype.linearCombination_apply]
    exact hc
  have hfull := tail_synthesis_zero H d hd c hz
  rw [Fintype.linearCombination_apply] at hfull
  exact Fintype.linearIndependent_iff.mp (qResidue_linearIndependent d hd hinj) c hfull

/-- The actual tail Gram matrix, rather than a formal subtraction of matrices. -/
def tailGram (H : ℕ) (d : ι → ℕ) : Matrix ι ι ℝ :=
  gramMatrix (tailResidue H d)

omit [Fintype ι] in
theorem tailGram_entry (H : ℕ) (d : ι → ℕ) (i j : ι) :
    tailGram H d i j =
      ∑' n : ℕ, positiveQWeight (n + H + 1) *
        residueFraction (d i) (n + H + 1) * residueFraction (d j) (n + H + 1) := by
  change inner ℝ (tailMap H (qResidue (d i))) (tailMap H (qResidue (d j))) = _
  rw [tailMap_inner_physical]
  simp only [qSequence_qResidue]

omit [Fintype ι] in
theorem tailGram_posDef [Finite ι] (H : ℕ) (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    (tailGram H d).PosDef := by
  classical
  let := Fintype.ofFinite ι
  exact gramMatrix_posDef (tailResidue_linearIndependent H d hd hinj)

omit [Fintype ι] in
theorem residue_inner_head_tail (H : ℕ) (d : ι → ℕ) (hd : ∀ i, H < d i) (i j : ι) :
    inner ℝ (qResidue (d i)) (qResidue (d j)) =
      inner ℝ (tailResidue H d i) (tailResidue H d j) +
        (H : ℝ) / zetaTwo * normalizationSource d i * normalizationSource d j := by
  apply inner_head_tail
  all_goals
    intro n _ hnH
    rw [qSequence_qResidue]
    simp only [residueFraction, Nat.mod_eq_of_lt (lt_of_le_of_lt hnH (hd _)),
      normalizationSource]
    ring

omit [Fintype ι] in
theorem fullGram_eq_tail (H : ℕ) (d : ι → ℕ) (hd : ∀ i, H < d i) :
    gramMatrix (fun i => qResidue (d i)) =
      tailGram H d + ((H : ℝ) / zetaTwo) •
        Matrix.vecMulVec (normalizationSource d) (normalizationSource d) := by
  ext i j
  change inner ℝ (qResidue (d i)) (qResidue (d j)) =
    inner ℝ (tailResidue H d i) (tailResidue H d j) + _
  rw [residue_inner_head_tail H d hd]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

theorem gram_head_tail (H : ℕ) (d : ι → ℕ) (hd : ∀ i, H < d i)
    (c : ι → ℝ) (i : ι) :
    gram (fun j => qResidue (d j)) c i =
      gram (tailResidue H d) c i +
        (H : ℝ) / zetaTwo * normalizationSource d i *
          (∑ j, c j * normalizationSource d j) := by
  simp only [gram_apply, residue_inner_head_tail H d hd, add_mul, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype ι] in
theorem cross_head_tail (H : ℕ) (d : ι → ℕ) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s) (i : ι) :
    cross (fun j => qResidue (d j)) f i =
      cross (tailResidue H d) (tailMap H f) i +
        (H : ℝ) / zetaTwo * s * normalizationSource d i := by
  have hi : ∀ n, 0 < n → n ≤ H →
      qSequence (qResidue (d i)) n = (n : ℝ) * normalizationSource d i := by
    intro n _ hnH
    rw [qSequence_qResidue]
    simp only [residueFraction, Nat.mod_eq_of_lt (lt_of_le_of_lt hnH (hd i)),
      normalizationSource]
    ring
  have he := inner_head_tail H (qResidue (d i)) f (normalizationSource d i) s hi hf
  change _ = inner ℝ (tailResidue H d i) (tailMap H f) + _ at he
  unfold cross
  rw [he]
  ring

/-- Exact complete residual split for every coefficient vector, feasible or not. -/
theorem residual_head_tail (H : ℕ) (d : ι → ℕ) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s)
    (c : ι → ℝ) :
    ‖f - Fintype.linearCombination ℝ (fun i => qResidue (d i)) c‖ ^ 2 =
      (H : ℝ) / zetaTwo * (s - ∑ i, c i * normalizationSource d i) ^ 2 +
        ‖tailMap H f - Fintype.linearCombination ℝ (tailResidue H d) c‖ ^ 2 := by
  rw [← tailMap_synthesis, ← map_sub, tailMap_norm_sq]
  apply linear_head_energy
  intro n hn hnH
  change qSequenceLinear (f - _) n = _
  rw [map_sub]
  change qSequence f n - qSequence (Fintype.linearCombination ℝ
    (fun i => qResidue (d i)) c) n = _
  rw [hf n hn hnH, synthesis_head d H hd c n hnH]
  ring

end RiemannResearch.RH.QTailGram
