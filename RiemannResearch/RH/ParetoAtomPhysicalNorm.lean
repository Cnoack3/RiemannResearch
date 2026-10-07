import RiemannResearch.RH.ParetoUnscaledDilation
import RiemannResearch.Analysis.NormCovariance
import Lean.Elab.Tactic.Omega

/-!
# Complete physical Pareto atom norm with its covariance loss

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


This module integrates the finite covariance equality into the literal infinite
Pareto inner product. Every correction is retained and its absolute convergence
is discharged by the actual complete physical block masses.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

open RiemannResearch.Analysis.NormCovariance

/-- Literal complete-weight summand in the normalized atom squared norm. -/
def atomPhysicalTerm (p k : ℕ) : ℝ := positiveWeight k * (normalizedAtom p k) ^ 2

/-- Uniform residue second moment, used only inside the exact covariance equality. -/
def atomUniformSecondMoment (p : ℕ) : ℝ :=
  ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (6 * (p : ℝ) ^ 2)

theorem atomUniformSecondMoment_nonneg (p : ℕ) (hp : 0 < p) :
    0 ≤ atomUniformSecondMoment p := by
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  have hleft : 0 ≤ (p : ℝ) - 1 := by linarith
  have hright : 0 ≤ 2 * (p : ℝ) - 1 := by linarith
  unfold atomUniformSecondMoment
  exact div_nonneg (mul_nonneg hleft hright) (by positivity)

theorem atomUniformSecondMoment_lt_third (p : ℕ) (hp : 0 < p) :
    atomUniformSecondMoment p < 1 / 3 := by
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  unfold atomUniformSecondMoment
  apply (div_lt_iff₀ (by positivity : 0 < 6 * (p : ℝ) ^ 2)).mpr
  nlinarith

theorem atomPhysicalTerm_nonneg (p k : ℕ) : 0 ≤ atomPhysicalTerm p k := by
  unfold atomPhysicalTerm
  exact mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)

theorem atomPhysicalTerm_summable (p : ℕ) (hp : 0 < p) :
    Summable (atomPhysicalTerm p) := by
  have hs := weighted_summable_of_bounded (bounded_product
    (fun k => normalizedAtom_abs_le_one p k hp)
    (fun k => normalizedAtom_abs_le_one p k hp))
  change Summable (fun k => positiveWeight k * (normalizedAtom p k) ^ 2)
  simpa only [pow_two] using hs

theorem atomPhysicalTerm_tsum (p : ℕ) :
    (∑' k, atomPhysicalTerm p k) = paretoInner (normalizedAtom p) (normalizedAtom p) := by
  simp only [atomPhysicalTerm, paretoInner, pow_two]

/-- Literal physical-site indexing agrees with the finite covariance functions. -/
theorem atomPhysicalTerm_block_cell (p j r : ℕ) (hr : r < p) :
    atomPhysicalTerm p (p * j + r) =
      residueSquare (p : ℝ) r * physicalWeight ((j : ℝ) * (p : ℝ)) r := by
  have hmod : (p * j + r) % p = r := by
    rw [Nat.add_mod]
    simp [Nat.mul_mod, Nat.mod_eq_of_lt hr]
  unfold atomPhysicalTerm positiveWeight normalizedAtom residue residueSquare physicalWeight
  rw [hmod]
  simp only [Nat.cast_add, Nat.cast_mul, div_pow]
  rw [mul_comm (p : ℝ) (j : ℝ)]
  ring

/-- Exact complete-block identity with the covariance correction retained. -/
theorem atomPhysicalTerm_tail_block (p j : ℕ) (hp : 0 < p) (hj : 0 < j) :
    (∑ k ∈ Finset.Ico (p * j) (p * (j + 1)), atomPhysicalTerm p k) =
      atomUniformSecondMoment p / (p : ℝ) * positiveWeight j - blockCorrection p j := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : p * (j + 1) - p * j = p := by simp [Nat.mul_add]
  rw [hlen]
  calc
    _ = ∑ r ∈ Finset.range p,
        residueSquare (p : ℝ) r * physicalWeight ((j : ℝ) * (p : ℝ)) r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact atomPhysicalTerm_block_cell p j r (Finset.mem_range.mp hr)
    _ = atomUniformSecondMoment p *
        (1 / ((j : ℝ) * (p : ℝ)) - 1 / ((j : ℝ) * (p : ℝ) + (p : ℝ))) -
        blockCorrection p j := physical_block_eq_uniform_sub_correction p j hp hj
    _ = _ := by
      unfold positiveWeight
      have hp0 : (p : ℝ) ≠ 0 := by positivity
      have hj0 : (j : ℝ) ≠ 0 := by positivity
      have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
      have hjpp : (j : ℝ) * (p : ℝ) + (p : ℝ) ≠ 0 := by positivity
      field_simp [hp0, hj0, hj1, hjpp]
      <;> ring

/-- Exact finite block regrouping; it is proved before passing to the infinite norm. -/
theorem atomPhysicalTerm_partial_blocks (p N : ℕ) (hp : 0 < p) :
    (∑ k ∈ Finset.range (p * (N + 1)), atomPhysicalTerm p k) =
      (∑ k ∈ Finset.range p, atomPhysicalTerm p k) +
        (atomUniformSecondMoment p / (p : ℝ)) *
          (∑ j ∈ Finset.range N, positiveWeight (j + 1)) -
        (∑ j ∈ Finset.range N, blockCorrection p (j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show p * (N + 1 + 1) = p * (N + 1) + p by simp [Nat.mul_add],
      Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    have hb := atomPhysicalTerm_tail_block p (N + 1) hp (by omega)
    rw [Finset.sum_Ico_eq_sum_range] at hb
    have hlen : p * (N + 1 + 1) - p * (N + 1) = p := by simp [Nat.mul_add]
    rw [hlen] at hb
    rw [hb]
    ring

/-- Nonnegative corrections are dominated by summable literal block masses. -/
theorem blockCorrection_le_physical_mass (p j : ℕ) (hp : 0 < p) (hj : 0 < j) :
    blockCorrection p j ≤ atomUniformSecondMoment p / (p : ℝ) * positiveWeight j := by
  have hnonneg : 0 ≤ ∑ k ∈ Finset.Ico (p * j) (p * (j + 1)), atomPhysicalTerm p k :=
    Finset.sum_nonneg (fun k hk => atomPhysicalTerm_nonneg p k)
  rw [atomPhysicalTerm_tail_block p j hp hj] at hnonneg
  linarith

theorem blockCorrection_summable (p : ℕ) (hp : 0 < p) :
    Summable (fun j => blockCorrection p (j + 1)) := by
  have hm : Summable (fun j =>
      (atomUniformSecondMoment p / (p : ℝ)) * positiveWeight (j + 1)) :=
    ((summable_nat_add_iff 1).mpr positiveWeight_summable).mul_left _
  apply hm.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (blockCorrection_nonneg p (j + 1) hp (by omega))]
  exact blockCorrection_le_physical_mass p (j + 1) hp (by omega)

/-- Complete physical norm equality, with every covariance loss still visible. -/
theorem normalizedAtom_norm_eq_head_uniform_sub_correction (p : ℕ) (hp : 0 < p) :
    paretoInner (normalizedAtom p) (normalizedAtom p) =
      (∑ k ∈ Finset.range p, atomPhysicalTerm p k) +
        atomUniformSecondMoment p / (p : ℝ) -
        (∑' j, blockCorrection p (j + 1)) := by
  have hcut : Filter.Tendsto (fun N : ℕ => p * (N + 1)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun N => ?_) Filter.tendsto_id
    exact (Nat.le_succ N).trans (Nat.le_mul_of_pos_left (N + 1) hp)
  have hn := (atomPhysicalTerm_summable p hp).hasSum.tendsto_sum_nat.comp hcut
  simp only [Function.comp_def, atomPhysicalTerm_tsum] at hn
  have hw : (∑' j, positiveWeight (j + 1)) = 1 := by
    have h := positiveWeight_summable.tsum_eq_zero_add
    rw [positiveWeight_tsum] at h
    have hzero : positiveWeight 0 = 0 := by norm_num [positiveWeight]
    rw [hzero, zero_add] at h
    exact h.symm
  have hs := (summable_nat_add_iff 1).mpr positiveWeight_summable
  have hc := (blockCorrection_summable p hp).hasSum.tendsto_sum_nat
  have hheadlim : Filter.Tendsto
      (fun _ : ℕ => ∑ k ∈ Finset.range p, atomPhysicalTerm p k) Filter.atTop
      (nhds (∑ k ∈ Finset.range p, atomPhysicalTerm p k)) := tendsto_const_nhds
  have hcalc := (hheadlim.add
    (hs.hasSum.tendsto_sum_nat.const_mul (atomUniformSecondMoment p / (p : ℝ)))).sub hc
  rw [hw] at hcalc
  simp only [mul_one] at hcalc
  have heq : (fun N => (∑ k ∈ Finset.range p, atomPhysicalTerm p k) +
      (atomUniformSecondMoment p / (p : ℝ)) *
        (∑ j ∈ Finset.range N, positiveWeight (j + 1)) -
      (∑ j ∈ Finset.range N, blockCorrection p (j + 1))) =
      (fun N => ∑ k ∈ Finset.range (p * (N + 1)), atomPhysicalTerm p k) := by
    funext N
    exact (atomPhysicalTerm_partial_blocks p N hp).symm
  rw [heq] at hcalc
  exact tendsto_nhds_unique hn hcalc

/-- The head is computed exactly, including its zero-weight initial site. -/
theorem atomPhysicalTerm_head_eq (p : ℕ) (hp : 0 < p) :
    (∑ k ∈ Finset.range p, atomPhysicalTerm p k) =
      ((p : ℝ) - ∑ k ∈ Finset.range p, 1 / ((k : ℝ) + 1)) / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ k ∈ Finset.range p, (1 - 1 / ((k : ℝ) + 1)) / (p : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold atomPhysicalTerm positiveWeight normalizedAtom residue
      rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
      by_cases hk0 : k = 0
      · subst k
        norm_num
      · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
        have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hp0, hkR, hk1]
        <;> ring
    _ = _ := by simp [← Finset.sum_div, Finset.sum_sub_distrib]

/-- Literal infinite atom norm with its harmonic head and exact convergent loss. -/
theorem normalizedAtom_norm_eq_harmonic_sub_correction (p : ℕ) (hp : 0 < p) :
    paretoInner (normalizedAtom p) (normalizedAtom p) =
      ((p : ℝ) - ∑ k ∈ Finset.range p, 1 / ((k : ℝ) + 1)) / (p : ℝ) ^ 2 +
        atomUniformSecondMoment p / (p : ℝ) -
        (∑' j, blockCorrection p (j + 1)) := by
  rw [normalizedAtom_norm_eq_head_uniform_sub_correction p hp, atomPhysicalTerm_head_eq p hp]

/-- The uniform-block upper envelope keeps the harmonic head exactly. -/
theorem normalizedAtom_norm_eq_explicit_envelope_sub_correction (p : ℕ) (hp : 0 < p) :
    paretoInner (normalizedAtom p) (normalizedAtom p) =
      4 / (3 * (p : ℝ)) -
        ((∑ k ∈ Finset.range p, 1 / ((k : ℝ) + 1)) + 1 / 2) / (p : ℝ) ^ 2 +
        1 / (6 * (p : ℝ) ^ 3) - (∑' j, blockCorrection p (j + 1)) := by
  rw [normalizedAtom_norm_eq_harmonic_sub_correction p hp]
  unfold atomUniformSecondMoment
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp [hp0]
  <;> ring

/-- At least the first strict physical correction survives in the complete sum. -/
theorem blockCorrection_tsum_pos (p : ℕ) (hp : 1 < p) :
    0 < ∑' j, blockCorrection p (j + 1) := by
  have hp0 : 0 < p := by omega
  have hle := Summable.sum_le_tsum ({0} : Finset ℕ)
    (fun j hj => blockCorrection_nonneg p (j + 1) hp0 (by omega))
    (blockCorrection_summable p hp0)
  simp only [Finset.sum_singleton, zero_add] at hle
  exact lt_of_lt_of_le (blockCorrection_pos p 1 hp (by omega)) hle

/-- A strict, sharper actual atom bound for every nontrivial modulus. -/
theorem normalizedAtom_norm_lt_explicit_envelope (p : ℕ) (hp : 1 < p) :
    paretoInner (normalizedAtom p) (normalizedAtom p) <
      4 / (3 * (p : ℝ)) -
        ((∑ k ∈ Finset.range p, 1 / ((k : ℝ) + 1)) + 1 / 2) / (p : ℝ) ^ 2 +
        1 / (6 * (p : ℝ) ^ 3) := by
  rw [normalizedAtom_norm_eq_explicit_envelope_sub_correction p (by omega)]
  exact sub_lt_self _ (blockCorrection_tsum_pos p hp)

/-- A uniform strict bound obtained from the actual full Pareto norm. -/
theorem normalizedAtom_norm_lt_four_thirds (p : ℕ) (hp : 0 < p) :
    paretoInner (normalizedAtom p) (normalizedAtom p) < 4 / (3 * (p : ℝ)) := by
  have hpR : 0 < (p : ℝ) := by positivity
  have hhead : (∑ k ∈ Finset.range p, atomPhysicalTerm p k) ≤ 1 / (p : ℝ) := by
    rw [atomPhysicalTerm_head_eq p hp]
    have hh : 0 ≤ ∑ k ∈ Finset.range p, 1 / ((k : ℝ) + 1) := by positivity
    calc
      _ ≤ (p : ℝ) / (p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (sub_le_self _ hh) (sq_nonneg _)
      _ = _ := by
        field_simp [ne_of_gt hpR]
        <;> ring
  have hc : 0 ≤ ∑' j, blockCorrection p (j + 1) :=
    tsum_nonneg (fun j => blockCorrection_nonneg p (j + 1) hp (by omega))
  have hm := (div_lt_div_iff_of_pos_right hpR).mpr (atomUniformSecondMoment_lt_third p hp)
  rw [normalizedAtom_norm_eq_head_uniform_sub_correction p hp]
  calc
    _ ≤ 1 / (p : ℝ) + atomUniformSecondMoment p / (p : ℝ) := by linarith
    _ < 1 / (p : ℝ) + (1 / 3) / (p : ℝ) := by linarith
    _ = _ := by
      field_simp [ne_of_gt hpR]
      <;> ring

/-- Every positive projected pivot bounded by the physical atom norm inherits
an improved prime-ray certificate. The arithmetic source remains explicit. -/
theorem normalizedAtom_pivot_gain_ge (p : ℕ) (hp : 0 < p) (σ η : ℝ)
    (hσ : 0 < σ)
    (hσatom : σ ≤ paretoInner (normalizedAtom p) (normalizedAtom p)) :
    (3 * (p : ℝ) / 4) * η ^ 2 ≤ η ^ 2 / σ := by
  have hpR : 0 < (p : ℝ) := by positivity
  have hupper : σ < 4 / (3 * (p : ℝ)) :=
    hσatom.trans_lt (normalizedAtom_norm_lt_four_thirds p hp)
  have hs4 : σ * (3 * (p : ℝ)) < 4 :=
    (lt_div_iff₀ (by positivity : 0 < 3 * (p : ℝ))).mp hupper
  have hb : (3 * (p : ℝ) / 4) * σ ≤ 1 := by nlinarith
  apply (le_div_iff₀ hσ).mpr
  have hmul := mul_le_mul_of_nonneg_right hb (sq_nonneg η)
  nlinarith only [hmul]

end
end RiemannResearch.RH.Pareto
