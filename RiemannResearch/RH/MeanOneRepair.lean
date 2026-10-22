/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoAtomPhysicalNorm
import RiemannResearch.RH.CesaroResidueMean
import RiemannResearch.RH.BaezDuarteCenteredBridge
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ordinary mean-one repairs in the physical squarefree Pareto space

Source: user-directed continuation of
`CriticalZeroMeanOneAdvance20261008.md`, Section 5. The sharper norm estimate
uses `ParetoAtomPhysicalNorm.normalizedAtom_norm_lt_four_thirds`.

The ordinary mean is the period/Cesaro mean, not `paretoMean`.
The closure repair uses a fresh prime conductor and the complete physical
Pareto norm. The equality of closures concerns the full family of finite
squarefree packets; it does not assert that their common closure contains
the constant target, or supply a rate on an arbitrary divisor chain.
-/

namespace RiemannResearch.RH.Pareto.MeanOneRepair
noncomputable section
open scoped BigOperators
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ArithmeticCumulative.CesaroResidue
open RiemannResearch.Probability.ConditionalIID (cesaro)
open RiemannResearch.RH.Pareto.BaezDuarte

/-- The ordinary period mean of a finite physical normalized-residue packet. -/
def packetOrdinaryMean (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s, a d * (((d : ℝ) - 1) / (2 * (d : ℝ)))

/-- The coefficient mean is the literal Cesaro mean at every positive common
period. Thus the affine constraint refers to the actual physical sequence. -/
theorem packetOrdinaryMean_eq_cesaro (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (L : ℕ) (hL : 0 < L)
    (hdiv : ∀ d ∈ s, d ∣ L) :
    cesaro (hilbertSequence (finiteResidueSum s a)) L = packetOrdinaryMean s a := by
  classical
  calc
    _ = ∑ d ∈ s, a d * cesaro (residueFraction d) L := by
      unfold cesaro
      simp_rw [finiteResidueSum_sequence s a hs]
      rw [Finset.sum_comm]
      simp [Finset.sum_div, Finset.mul_sum, mul_div_assoc, residueFraction]
    _ = _ := by
      unfold packetOrdinaryMean
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨q, hq⟩ := hdiv d hd
      have hqpos : 0 < q := by
        by_contra! hbad
        have hq0 : q = 0 := Nat.eq_zero_of_le_zero hbad
        rw [hq, hq0, Nat.mul_zero] at hL
        omega
      rw [hq, Nat.mul_comm d q, cesaro_residue_complete_periods d q (hs d hd) hqpos]

/-- A genuine mean-one repair vector; squarefreeness is required only when
placing it in the squarefree approximation class. -/
def repairVector (d : ℕ) (hd : 0 < d) : ThresholdHilbert :=
  (2 * (d : ℝ) / ((d : ℝ) - 1)) • normalizedResidueHilbert d hd

theorem repairVector_sequence (d : ℕ) (hd : 0 < d) :
    hilbertSequence (repairVector d hd) =
      fun k => (2 * (d : ℝ) / ((d : ℝ) - 1)) * normalizedAtom d k := by
  rw [repairVector, hilbertSequence_smul, normalizedResidueHilbert_sequence]
  rfl

/-- Every positive complete-period Cesaro mean of the repair is exactly one. -/
theorem repairVector_complete_period_mean (d k : ℕ) (hd : 1 < d) (hk : 0 < k) :
    cesaro (hilbertSequence (repairVector d (by omega))) (k * d) = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : 1 < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hscale (c : ℝ) (f : ℕ → ℝ) (n : ℕ) :
      cesaro (fun j => c * f j) n = c * cesaro f n := by
    unfold cesaro
    rw [← Finset.mul_sum]
    ring
  rw [repairVector_sequence]
  change cesaro (fun j => (2 * (d : ℝ) / ((d : ℝ) - 1)) * residueFraction d j)
    (k * d) = 1
  rw [hscale, cesaro_residue_complete_periods d k (by omega) hk]
  field_simp [hd0, hd1]

theorem normalizedResidueHilbert_norm_sq_eq (d : ℕ) (hd : 0 < d) :
    ‖normalizedResidueHilbert d hd‖ ^ 2 =
      paretoInner (normalizedAtom d) (normalizedAtom d) := by
  rw [hilbert_norm_weighted_sq, normalizedResidueHilbert_sequence]
  unfold paretoInner
  apply tsum_congr
  intro k
  simp only [residueFraction, normalizedAtom, residue, pow_two]

/-- The sharper complete physical estimate from the covariance-corrected
atom norm. No correction has been dropped from the identity used upstream. -/
theorem repairVector_norm_sq_lt (d : ℕ) (hd : 1 < d) :
    ‖repairVector d (by omega)‖ ^ 2 <
      16 * (d : ℝ) / (3 * ((d : ℝ) - 1) ^ 2) := by
  have hdR : (0 : ℝ) < d := by positivity
  have hd1 : 0 < (d : ℝ) - 1 := by
    have : 1 < (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [repairVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    normalizedResidueHilbert_norm_sq_eq]
  calc
    _ < (2 * (d : ℝ) / ((d : ℝ) - 1)) ^ 2 * (4 / (3 * (d : ℝ))) :=
      mul_lt_mul_of_pos_left (normalizedAtom_norm_lt_four_thirds d (by omega))
        (sq_pos_of_pos (by positivity))
    _ = _ := by field_simp [ne_of_gt hdR, ne_of_gt hd1]; ring

/-- A convenient envelope for selecting a new large conductor. -/
theorem repairVector_norm_sq_lt_inv (d : ℕ) (hd : 1 < d) :
    ‖repairVector d (by omega)‖ ^ 2 < 64 / (3 * (d : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  have hdR : (0 : ℝ) < d := by positivity
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  apply (repairVector_norm_sq_lt d hd).trans_le
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * ((d : ℝ) - 1) ^ 2)
    (by positivity : 0 < 3 * (d : ℝ))).mpr
  have hq : (d : ℝ) ^ 2 ≤ 4 * ((d : ℝ) - 1) ^ 2 := by nlinarith
  nlinarith

def squarefreePackets : Set ThresholdHilbert :=
  {f | ∃ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ d ∈ s, 0 < d) ∧ (∀ d ∈ s, Squarefree d) ∧ f = finiteResidueSum s a}

def meanOneSquarefreePackets : Set ThresholdHilbert :=
  {f | ∃ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ d ∈ s, 0 < d) ∧ (∀ d ∈ s, Squarefree d) ∧
      packetOrdinaryMean s a = 1 ∧ f = finiteResidueSum s a}

theorem meanOneSquarefreePackets_subset :
    meanOneSquarefreePackets ⊆ squarefreePackets := by
  rintro f ⟨s, a, hs, hsf, hm, hf⟩
  exact ⟨s, a, hs, hsf, hf⟩

/-- A repair with fresh prime conductor has exact ordinary mean one and
retains the original physical packet unchanged at every old coefficient. -/
theorem packet_repair (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (hsf : ∀ d ∈ s, Squarefree d)
    (p : ℕ) (hp : p.Prime) (hps : p ∉ s) :
    let β := (1 - packetOrdinaryMean s a) * (2 * (p : ℝ) / ((p : ℝ) - 1))
    let b : ℕ → ℝ := fun d => if d = p then β else a d
    packetOrdinaryMean (insert p s) b = 1 ∧
      finiteResidueSum (insert p s) b = finiteResidueSum s a +
        (1 - packetOrdinaryMean s a) • repairVector p hp.pos ∧
      finiteResidueSum (insert p s) b ∈ meanOneSquarefreePackets := by
  classical
  dsimp only
  let β := (1 - packetOrdinaryMean s a) * (2 * (p : ℝ) / ((p : ℝ) - 1))
  let b : ℕ → ℝ := fun d => if d = p then β else a d
  have hb (d : ℕ) (hd : d ∈ s) : b d = a d := by
    simp [b, show d ≠ p by intro h; subst d; exact hps hd]
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hm : packetOrdinaryMean (insert p s) b = 1 := by
    unfold packetOrdinaryMean
    rw [Finset.sum_insert hps]
    have hsum : (∑ d ∈ s, b d * (((d : ℝ) - 1) / (2 * (d : ℝ)))) =
        packetOrdinaryMean s a := by
      unfold packetOrdinaryMean
      apply Finset.sum_congr rfl
      intro d hd
      rw [hb d hd]
    have hbP : b p = β := by simp [b]
    rw [hbP, hsum]
    dsimp [β]
    field_simp [hpR, hp1]
    <;> ring
  have he : finiteResidueSum (insert p s) b = finiteResidueSum s a +
      (1 - packetOrdinaryMean s a) • repairVector p hp.pos := by
    unfold finiteResidueSum
    rw [Finset.sum_insert hps]
    have hsum : (∑ d ∈ s, b d • residueVector d) = ∑ d ∈ s, a d • residueVector d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hb d hd]
    rw [hsum]
    simp [b, β, residueVector, hp.pos, repairVector, mul_smul, add_comm]
  refine ⟨hm, he, ?_⟩
  refine ⟨insert p s, b, ?_, ?_, hm, rfl⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hp.pos
    · exact hs d hd
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hp.squarefree
    · exact hsf d hd

/-- The mean-one repair can be made arbitrarily small in the actual physical
Hilbert norm. The fresh conductor is an unconditionally existing prime. -/
theorem squarefreePackets_subset_closure_meanOne :
    squarefreePackets ⊆ closure meanOneSquarefreePackets := by
  classical
  rintro f ⟨s, a, hs, hsf, rfl⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t : ℝ := 1 - packetOrdinaryMean s a
  obtain ⟨N, hN⟩ := exists_nat_gt (64 * t ^ 2 / (3 * ε ^ 2))
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max (s.sup id + 1) (N + 1))
  have hpN : N < p := by omega
  have hps : p ∉ s := by
    intro hps
    have hle : p ≤ s.sup id := by
      simpa only [id_eq] using (Finset.le_sup (f := id) hps)
    omega
  have hscale : ‖t • repairVector p hp.pos‖ ^ 2 < ε ^ 2 := by
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have hNp : (N : ℝ) < p := by exact_mod_cast hpN
    have hsmall : 64 * t ^ 2 / (3 * (p : ℝ)) < ε ^ 2 := by
      have hden : (0 : ℝ) < 3 * ε ^ 2 := by positivity
      have h := (div_lt_iff₀ hden).mp (hN.trans hNp)
      apply (div_lt_iff₀ (by positivity : 0 < 3 * (p : ℝ))).mpr
      nlinarith
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ t ^ 2 * (64 / (3 * (p : ℝ))) :=
        mul_le_mul_of_nonneg_left (repairVector_norm_sq_lt_inv p hp.one_lt).le
          (sq_nonneg t)
      _ = 64 * t ^ 2 / (3 * (p : ℝ)) := by ring
      _ < ε ^ 2 := hsmall
  let β := t * (2 * (p : ℝ) / ((p : ℝ) - 1))
  let b : ℕ → ℝ := fun d => if d = p then β else a d
  have hre := packet_repair s a hs hsf p hp hps
  change packetOrdinaryMean (insert p s) b = 1 ∧
    finiteResidueSum (insert p s) b = finiteResidueSum s a + t • repairVector p hp.pos ∧
    finiteResidueSum (insert p s) b ∈ meanOneSquarefreePackets at hre
  refine ⟨finiteResidueSum (insert p s) b, hre.2.2, ?_⟩
  rw [hre.2.1, dist_eq_norm]
  have he : finiteResidueSum s a - (finiteResidueSum s a + t • repairVector p hp.pos) =
      -(t • repairVector p hp.pos) := by abel
  rw [he, norm_neg]
  nlinarith [norm_nonneg (t • repairVector p hp.pos)]

/-- Exact equality of physical closures. This is an unconditional reduction,
not target membership or the remaining arithmetic limit. -/
theorem closure_meanOneSquarefreePackets_eq :
    closure meanOneSquarefreePackets = closure squarefreePackets := by
  apply Set.Subset.antisymm
  · exact closure_mono meanOneSquarefreePackets_subset
  · exact closure_minimal squarefreePackets_subset_closure_meanOne isClosed_closure

end
end RiemannResearch.RH.Pareto.MeanOneRepair
