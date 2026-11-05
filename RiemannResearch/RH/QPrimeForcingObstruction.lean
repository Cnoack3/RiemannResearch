/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.AdjacentResidueHarmonic
import RiemannResearch.RH.QAdjacentConductorPacket
import RiemannResearch.RH.QPrimeAnchoredTarget
import RiemannResearch.RH.QFiniteEighthMoment
import RiemannResearch.Analysis.ProjectionTrialEnergy

/-! # Prime innovations with small Gram data and large output

Mirsky, *The number of representations of an integer as the sum of a prime and a
k-free integer*, Amer. Math. Monthly 56 (1949), supplies infinitely many primes
with squarefree predecessor. The estimates below are finite and do not use that
density theorem. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeForcingObstruction
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage ZetaTwoParetoTransfer
open SquarefreeRadicalDifference ArithmeticCumulative PrimePowerTarget
open RiemannResearch.Analysis RiemannResearch.Analysis.ExhaustiveWalk

/-- The new conductor is n + 3; the old stage ends at n + 2. -/
def innovation (n : ℕ) : QHilbert :=
  qResidue (n + 3) - (stage (n + 1)).starProjection (qResidue (n + 3))

theorem old_gram_zero (n : ℕ) (u : QHilbert) (hu : u ∈ stage (n + 1)) :
    inner ℝ u (innovation n) = 0 :=
  Submodule.inner_right_of_mem_orthogonal hu
    (Submodule.sub_starProjection_mem_orthogonal (K := stage (n + 1)) (qResidue (n + 3)))

theorem new_gram (n : ℕ) :
    inner ℝ (qResidue (n + 3)) (innovation n) = ‖innovation n‖ ^ 2 := by
  have h := old_gram_zero n _ ((stage (n + 1)).starProjection_apply_mem (qResidue (n + 3)))
  calc
    _ = inner ℝ (qResidue (n + 3) - (stage (n + 1)).starProjection (qResidue (n + 3)))
        (innovation n) := by rw [inner_sub_left, h,sub_zero]
    _ = _ := real_inner_self_eq_norm_sq _

private theorem charge_residue (n d : ℕ) (hd : 2 ≤ d) :
    anchoredCharge (n + 2) (qResidue d) = if d ∣ n + 3 then 1 else 0 := by
  change qSequence (qResidue d) 1 - (qSequence (qResidue d) (n + 3) -
    qSequence (qResidue d) (n + 3 - 1)) = _
  simp only [qSequence_qResidue]
  rw [residueFraction_difference d (n + 3) hd (by omega)]
  simp only [residueFraction, Nat.mod_eq_of_lt (by omega : 1 < d), Nat.cast_one]
  ring

private theorem old_charge_zero (n : ℕ) (hp : Nat.Prime (n + 3)) {x : QHilbert}
    (hx : x ∈ stage (n + 1)) : anchoredCharge (n + 2) x = 0 := by
  have hi : stage (n + 1) ≤ LinearMap.ker (anchoredCharge (n + 2)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change anchoredCharge (n + 2) (squarefreeAtom i) = 0
    unfold squarefreeAtom
    split_ifs with hs
    · rw [charge_residue n (i + 2) (by omega)]
      apply if_neg
      intro h
      rcases (Nat.dvd_prime hp).mp h with h | h <;> have := i.isLt <;> omega
    · exact map_zero _
  exact hi hx

/-- An old atom cannot change the exceptional prime jump at n + 3. -/
theorem peak (n : ℕ) (hp : Nat.Prime (n + 3)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n + 3 ∧ 1 ≤ 3 * |qSequence (innovation n) k| := by
  have hc : anchoredCharge (n + 2) (innovation n) = 1 := by
    rw [innovation, map_sub, old_charge_zero n hp
      ((stage (n + 1)).starProjection_apply_mem (qResidue (n + 3))),
      charge_residue n (n + 3) (by omega), if_pos (dvd_refl _), sub_zero]
  change qSequence (innovation n) 1 -
    (qSequence (innovation n) (n + 3) - qSequence (innovation n) (n + 2)) = 1 at hc
  by_contra! h
  have h₁ := h 1 (by omega) (by omega)
  have h₂ := h (n + 2) (by omega) (by omega)
  have h₃ := h (n + 3) (by omega) (by omega)
  linarith [le_abs_self (qSequence (innovation n) 1),
    le_abs_self (qSequence (innovation n) (n + 2)),
    neg_le_abs (qSequence (innovation n) (n + 3))]

/-- The actual aligned physical eighth head detects the exceptional jump. -/
theorem eighth_head_lower (n : ℕ) (hp : Nat.Prime (n + 3)) :
    1 ≤ 3 ^ 8 * ((n + 3 : ℕ) : ℝ) ^ 2 *
      QSquarefreeFiniteDisplacement.eighthHead (innovation n) (n + 3) := by
  obtain ⟨k,hk,hlen,hpeak⟩ := peak n hp
  let F (j : ℕ) := |qSequence (innovation n) j|^8 / (j : ℝ) ^ 2
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs : F k ≤ QSquarefreeFiniteDisplacement.eighthHead (innovation n) (n + 3) := by
    apply Finset.single_le_sum (f := F) (fun j _ => by dsimp [F]; positivity)
    exact Finset.mem_range.mpr (by omega)
  have hpow : (1 : ℝ) ^ 8 ≤ (3 * |qSequence (innovation n) k|) ^ 8 := by gcongr
  rw [one_pow,mul_pow] at hpow
  have hkR : (k : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast hlen
  have hterm : |qSequence (innovation n) k| ^ 8 = (k : ℝ) ^ 2 * F k := by
    dsimp [F]
    field_simp [hk'.ne']
  calc
    1 ≤ 3 ^ 8 * |qSequence (innovation n) k| ^ 8 := hpow
    _ = 3 ^ 8 * ((k : ℝ) ^ 2 * F k) := by rw [hterm]
    _ ≤ 3 ^ 8 * (((n + 3 : ℕ) : ℝ) ^ 2 *
        QSquarefreeFiniteDisplacement.eighthHead (innovation n) (n + 3)) := by
      have hpos : 0 ≤ F k := by dsimp [F]; positivity
      gcongr
    _ = _ := by ring

/-- Exact control of the only nonzero Gram datum from the complete P-energy
of the consecutive raw residue difference, including all periods. -/
theorem sole_datum_bound (n : ℕ) (hs : Squarefree (n + 2)) :
    zetaTwo * ((n + 3 : ℕ) : ℝ) ^ 2 * inner ℝ (qResidue (n + 3)) (innovation n)
      ≤ 2 * (harmonic (n + 2) : ℝ) := by
  let a : ℝ := ((n + 2 : ℕ) : ℝ)
  let b : ℝ := ((n + 3 : ℕ) : ℝ)
  let x := b • qResidue (n + 3)
  let y := a • qResidue (n + 2)
  have hprev : qResidue (n + 2) ∈ stage (n + 1) := by
    apply Submodule.subset_span
    refine ⟨⟨n,by omega⟩,?_⟩
    change squarefreeAtom n = _
    simp [squarefreeAtom,hs]
  have hy : y ∈ stage (n + 1) := (stage (n + 1)).smul_mem a hprev
  have hproj := projection_trial_energy (stage (n + 1)) x y hy
  have hscale : x - (stage (n + 1)).starProjection x = b • innovation n := by
    dsimp [x,innovation]
    rw [map_smul,smul_sub]
  rw [hscale,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hproj
  have hle : b ^ 2 * ‖innovation n‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
    rw [norm_sub_rev]
    linarith [sq_nonneg ‖(stage (n + 1)).starProjection x - y‖]
  have hphys (k : ℕ) : qSequence (y - x) k = Pareto.adjacentResidueDifference (n + 2) k := by
    change qSequenceLinear (a • qResidue (n + 2) - b • qResidue (n + 3)) k = _
    rw [map_sub,map_smul,map_smul]
    change a * qSequence (qResidue (n + 2)) k - b * qSequence (qResidue (n + 3)) k = _
    exact (QAdjacentConductorPacket.packet_eq_residue_combination (n + 2) k (by omega)).symm
  have hpbound : ‖toPareto (y - x)‖ ^ 2 ≤ (harmonic (n + 2) : ℝ) := by
    rw [Pareto.hilbert_norm_weighted_sq,toPareto_sequence]
    simp_rw [hphys]
    exact Pareto.adjacentResidueDifference_energy_upper (n + 2) (by omega)
  rw [new_gram]
  change zetaTwo * b ^ 2 * ‖innovation n‖ ^ 2 ≤ _
  rw [mul_assoc]
  exact ((mul_le_mul_of_nonneg_left hle zetaTwo_pos.le).trans
    (zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (y - x))).trans (by linarith)

end RiemannResearch.RH.QPrimeForcingObstruction
