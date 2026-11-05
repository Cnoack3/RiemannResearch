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
import Mathlib.NumberTheory.Harmonic.Bounds

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


/-- Consecutive raw residue atoms, including the entire infinite physical tail. -/
theorem raw_residue_adjacent_energy_le (d : ℕ) (hd : 0 < d) :
    zetaTwo * ‖((d + 1 : ℕ) : ℝ) • qResidue (d + 1) - (d : ℝ) • qResidue d‖ ^ 2 ≤
      2 * (harmonic d : ℝ) := by
  let x : QHilbert := (d : ℝ) • qResidue d - ((d + 1 : ℕ) : ℝ) • qResidue (d + 1)
  have hphys (k : ℕ) : qSequence x k = Pareto.adjacentResidueDifference d k := by
    change qSequenceLinear ((d : ℝ) • qResidue d - ((d + 1 : ℕ) : ℝ) • qResidue (d + 1)) k = _
    rw [map_sub, map_smul, map_smul]
    change (d : ℝ) * qSequence (qResidue d) k -
      ((d + 1 : ℕ) : ℝ) * qSequence (qResidue (d + 1)) k = _
    exact (QAdjacentConductorPacket.packet_eq_residue_combination d k hd).symm
  have hP : ‖toPareto x‖ ^ 2 ≤ (harmonic d : ℝ) := by
    rw [Pareto.hilbert_norm_weighted_sq, toPareto_sequence]
    simp_rw [hphys]
    exact Pareto.adjacentResidueDifference_energy_upper d hd
  have henergy := (zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq x).trans
    (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2))
  rw [norm_sub_rev]
  exact henergy

theorem raw_residue_adjacent_norm_le (d : ℕ) (hd : 0 < d) :
    ‖((d + 1 : ℕ) : ℝ) • qResidue (d + 1) - (d : ℝ) • qResidue d‖ ≤
      Real.sqrt (2 * (harmonic d : ℝ) / zetaTwo) := by
  apply Real.le_sqrt_of_sq_le
  exact (le_div_iff₀ zetaTwo_pos).mpr (by linarith only [raw_residue_adjacent_energy_le d hd])

/-- Crossing an arbitrary conductor gap costs at most its length times the
    largest adjacent harmonic norm. Intermediate conductors need no legality. -/
theorem raw_residue_gap_norm_le (p q : ℕ) (hq : 0 < q) (hqp : q ≤ p) :
    ‖(p : ℝ) • qResidue p - (q : ℝ) • qResidue q‖ ≤
      ((p - q : ℕ) : ℝ) * Real.sqrt (2 * (harmonic p : ℝ) / zetaTwo) := by
  let R (k : ℕ) : QHilbert := (k : ℝ) • qResidue k
  let C := Real.sqrt (2 * (harmonic p : ℝ) / zetaTwo)
  have hstep (d : ℕ) (hd : 0 < d) (hdp : d ≤ p) : ‖R (d + 1) - R d‖ ≤ C := by
    have hrat : harmonic d ≤ harmonic p := by
      unfold harmonic
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hdp)
        (fun i _ _ => by positivity)
    have hreal : (harmonic d : ℝ) ≤ (harmonic p : ℝ) := by exact_mod_cast hrat
    exact (raw_residue_adjacent_norm_le d hd).trans (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hreal (by norm_num)) zetaTwo_pos.le))
  have htel (j : ℕ) (hj : q + j ≤ p) : ‖R (q + j) - R q‖ ≤ (j : ℝ) * C := by
    induction j with
    | zero => simp
    | succ j ih =>
      have htriangle := dist_triangle (R (q + j + 1)) (R (q + j)) (R q)
      simp only [dist_eq_norm] at htriangle
      calc
        ‖R (q + (j + 1)) - R q‖ = ‖R (q + j + 1) - R q‖ := rfl
        _ ≤ ‖R (q + j + 1) - R (q + j)‖ + ‖R (q + j) - R q‖ := htriangle
        _ ≤ C + (j : ℝ) * C := add_le_add (hstep (q + j) (by omega) (by omega)) (ih (by omega))
        _ = ((j + 1 : ℕ) : ℝ) * C := by push_cast; ring
  have he : q + (p - q) = p := by omega
  have ht := htel (p - q) he.le
  rwa [he] at ht

/-- A purely logarithmic bound uniform in both conductors. -/
theorem raw_residue_gap_norm_le_log (p q : ℕ) (hq : 0 < q) (hqp : q ≤ p) :
    ‖(p : ℝ) • qResidue p - (q : ℝ) • qResidue q‖ ≤
      ((p - q : ℕ) : ℝ) * Real.sqrt (2 * (1 + Real.log (p : ℝ)) / zetaTwo) := by
  exact (raw_residue_gap_norm_le p q hq hqp).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log p) (by norm_num)) zetaTwo_pos.le))
    (Nat.cast_nonneg _))

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
  have hadj : zetaTwo * ‖y - x‖ ^ 2 ≤ 2 * (harmonic (n + 2) : ℝ) := by
    rw [norm_sub_rev]
    exact raw_residue_adjacent_energy_le (n + 2) (by omega)
  rw [new_gram]
  change zetaTwo * b ^ 2 * ‖innovation n‖ ^ 2 ≤ _
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hle zetaTwo_pos.le).trans hadj

end RiemannResearch.RH.QPrimeForcingObstruction
