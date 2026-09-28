import RiemannResearch.RH.IntegerDPPMellinObstruction
import RiemannResearch.RH.ParetoCoordinateBounds
import RiemannResearch.RH.ParetoCriticalMellinCutoff
import RiemannResearch.RH.ProjectedDualMellinWitness
import RiemannResearch.RH.CriticalLineZeros

/-!
# Coefficient-free conductor control for the first-site vacancy

Source: the user's DPP/Mellin research request, 28 September 2026.
The argument combines periodic coordinate control with the existing critical
Mellin cutoff. CriticalLineZeros documents the upstream zero provider.

This finite-stage estimate uses the actual Pareto norm and the ordinary
convergent Mellin transform. It neither assumes RH nor proves the vacancy
converges to zero. Critical-line zero existence is provided by the imported
CriticalLineZeros theorem. No bound for an inverse Gram matrix is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.Cesaro

/-- Every finite residue combination can be evaluated in one conductor block. -/
theorem finiteSpace_sequence_eq_mod_conductor (n L : ℕ)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace n) (k : ℕ) :
    hilbertSequence f k = hilbertSequence f (k % L) := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n f hf
  rw [ha]
  change hilbertSequenceLinear (∑ i : Fin n, a i • residueAtom i.val) k =
    hilbertSequenceLinear (∑ i : Fin n, a i • residueAtom i.val) (k % L)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change hilbertSequence (residueAtom i.val) k =
    hilbertSequence (residueAtom i.val) (k % L)
  simp only [residueAtom, normalizedResidueHilbert_sequence]
  unfold ArithmeticCumulative.residueFraction
  rw [Nat.mod_mod_of_dvd k (hL i)]

/-- A coefficient-free uniform bound: only the conductor and Hilbert norm occur. -/
theorem finiteSpace_sequence_abs_le_conductor_norm (n L : ℕ) (hLpos : 0 < L)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace n) (k : ℕ) :
    |hilbertSequence f k| ≤ (L : ℝ) * ‖f‖ := by
  rw [finiteSpace_sequence_eq_mod_conductor n L hL f hf k]
  have hr : ((k % L : ℕ) : ℝ) + 1 ≤ (L : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mod_lt k hLpos)
  have hr0 : (0 : ℝ) ≤ ((k % L : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hfactor : ((k % L : ℕ) : ℝ) * (((k % L : ℕ) : ℝ) + 1) ≤
      (L : ℝ)^2 := by
    nlinarith
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hL0 (norm_nonneg _))).mp
  rw [sq_abs, mul_pow]
  exact (hilbertSequence_sq_le_norm_sq f (k % L)).trans
    (mul_le_mul_of_nonneg_right hfactor (sq_nonneg ‖f‖))

theorem firstPoint_sequence_abs_le_one (k : ℕ) :
    |hilbertSequence (paretoPointHilbert 0) k| ≤ (1 : ℝ) := by
  rw [hilbertSequence_paretoPoint]
  simp only [paretoPointSequence]
  split_ifs <;> norm_num

/-- The point target's Mellin identity on the full positive half-plane. -/
theorem firstPoint_mellin_positiveHalfPlane (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (paretoPointHilbert 0) s = (1 - (2 : ℂ)^(-s)) / s := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have h := hasSum_first_mellin_pairing_of_bounded
    (paretoPointHilbert 0) 1 firstPoint_sequence_abs_le_one s hs
  have he : s * paretoMellin (paretoPointHilbert 0) s = 1 - (2 : ℂ)^(-s) := by
    calc
      _ = ∑ k ∈ Finset.range 1, mellinFirst s (k+1) *
          (hilbertSequence (paretoPointHilbert 0) (k+1) : ℂ) := by
        rw [← h.tsum_eq]
        apply tsum_eq_sum
        intro k hk
        have hk0 : k ≠ 0 := by simpa only [Finset.mem_range, Nat.lt_one_iff] using hk
        have heq : hilbertSequence (paretoPointHilbert 0) (k+1) = 0 := by
          rw [hilbertSequence_paretoPoint]
          simp [paretoPointSequence, hk0]
        rw [heq]
        simp
      _ = _ := by
        rw [Finset.sum_range_one, hilbertSequence_paretoPoint]
        norm_num [paretoPointSequence, mellinFirst]
  apply (eq_div_iff hs0).mpr
  simpa only [mul_comm] using he

theorem firstPoint_mellin_positiveHalfPlane_ne_zero (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (paretoPointHilbert 0) s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have hn : ‖(2 : ℂ)^(-s)‖ < 1 := by
    change ‖((2 : ℝ) : ℂ)^(-s)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [firstPoint_mellin_positiveHalfPlane s hs]
  apply div_ne_zero _ hs0
  intro hz
  have he : (2 : ℂ)^(-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [he, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

/-- Projection contractivity and periodicity eliminate all coefficient norms. -/
theorem firstPoint_projection_sequence_abs_le_conductor (n L : ℕ) (hLpos : 0 < L)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (k : ℕ) :
    |hilbertSequence ((finiteSpace n).starProjection (paretoPointHilbert 0)) k| ≤
      (L : ℝ) := by
  let p := (finiteSpace n).starProjection (paretoPointHilbert 0)
  have he : (1 / 2 : ℝ) = ‖paretoPointHilbert 0 - p‖^2 + ‖p‖^2 := by
    have ht := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
      (finiteSpace n) bot_le (paretoPointHilbert 0)
    simpa [firstPoint_norm_sq, p] using ht
  have hp : ‖p‖ ≤ 1 := by
    nlinarith [sq_nonneg ‖paretoPointHilbert 0 - p‖, norm_nonneg p]
  exact (finiteSpace_sequence_abs_le_conductor_norm n L hLpos hL p
      ((finiteSpace n).starProjection_apply_mem _) k).trans
    (by simpa using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg L))

theorem firstPoint_error_sequence_abs_le_conductor (n L : ℕ) (hLpos : 0 < L)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (k : ℕ) :
    |hilbertSequence (paretoPointHilbert 0 -
      (finiteSpace n).starProjection (paretoPointHilbert 0)) k| ≤ (L : ℝ) + 1 := by
  change |hilbertSequenceLinear (paretoPointHilbert 0 -
    (finiteSpace n).starProjection (paretoPointHilbert 0)) k| ≤ _
  rw [map_sub]
  change |hilbertSequence (paretoPointHilbert 0) k -
    hilbertSequence ((finiteSpace n).starProjection (paretoPointHilbert 0)) k| ≤ _
  calc
    _ ≤ |hilbertSequence (paretoPointHilbert 0) k| +
        |hilbertSequence ((finiteSpace n).starProjection (paretoPointHilbert 0)) k| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
        (hilbertSequence (paretoPointHilbert 0) k) 0
        (hilbertSequence ((finiteSpace n).starProjection (paretoPointHilbert 0)) k)
    _ ≤ 1 + (L : ℝ) := add_le_add (firstPoint_sequence_abs_le_one k)
      (firstPoint_projection_sequence_abs_le_conductor n L hLpos hL k)
    _ = _ := by ring

theorem firstPoint_error_mellin_at_zero (n L : ℕ) (hLpos : 0 < L)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (s : ℂ) (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    paretoMellin (paretoPointHilbert 0 -
      (finiteSpace n).starProjection (paretoPointHilbert 0)) s =
        paretoMellin (paretoPointHilbert 0) s := by
  let p := (finiteSpace n).starProjection (paretoPointHilbert 0)
  have hn : ∀ j, |hilbertSequence (-p) j| ≤ (L : ℝ) := by
    intro j
    change |hilbertSequenceLinear (-p) j| ≤ _
    rw [map_neg]
    change |-(hilbertSequence p j)| ≤ _
    simpa only [abs_neg] using firstPoint_projection_sequence_abs_le_conductor
      n L hLpos hL j
  have hmneg : paretoMellin (-p) s = -paretoMellin p s := by
    simpa only [neg_one_smul] using paretoMellin_smul (-1 : ℝ) p s
  have hpzero : paretoMellin p s = 0 := paretoMellin_eq_zero_of_mem_finiteSpace
    n p ((finiteSpace n).starProjection_apply_mem _) s hs hs1 hz
  change paretoMellin (paretoPointHilbert 0 - p) s = _
  rw [sub_eq_add_neg, paretoMellin_add_of_bounded _ _
    firstPoint_sequence_abs_le_one hn s hs, hmneg, hpzero, neg_zero, add_zero]

/-- Actual critical Mellin cutoff with no inverse-Gram or coefficient-mass input. -/
theorem firstPoint_critical_conductor_cutoff (n L : ℕ) (hLpos : 0 < L)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (s : ℂ)
    (hs : s.re = 1 / 2) (hz : riemannZeta s = 0) (R : ℝ) (hR : 0 < R) :
    ‖paretoMellin (paretoPointHilbert 0) s‖ ≤
      ‖paretoPointHilbert 0 - (finiteSpace n).starProjection (paretoPointHilbert 0)‖ *
        Real.sqrt R + 2 * ((L : ℝ) + 1) * Real.exp (-R / 2) := by
  have hs1 : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have h := paretoMellin_critical_cutoff
    (paretoPointHilbert 0 - (finiteSpace n).starProjection (paretoPointHilbert 0))
    (firstPoint_error_sequence_abs_le_conductor n L hLpos hL) s hs R hR
  rw [firstPoint_error_mellin_at_zero n L hLpos hL s (by linarith) hs1 hz] at h
  exact h

/-- Once the explicit physical tail costs at most half the witness, vacancy
times the logarithmic cutoff is bounded below by a positive constant. -/
theorem firstPoint_critical_vacancy_cutoff_lower_bound (n L : ℕ) (hLpos : 0 < L)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (s : ℂ)
    (hs : s.re = 1 / 2) (hz : riemannZeta s = 0) (R : ℝ) (hR : 0 < R)
    (htail : 2 * ((L : ℝ) + 1) * Real.exp (-R / 2) ≤
      ‖paretoMellin (paretoPointHilbert 0) s‖ / 2) :
    ‖paretoMellin (paretoPointHilbert 0) s‖^2 ≤ 2 * vacancy n * R := by
  have h := firstPoint_critical_conductor_cutoff n L hLpos hL s hs hz R hR
  have hhead : ‖paretoMellin (paretoPointHilbert 0) s‖ / 2 ≤
      ‖paretoPointHilbert 0 - (finiteSpace n).starProjection (paretoPointHilbert 0)‖ *
        Real.sqrt R := by linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤
      ‖paretoMellin (paretoPointHilbert 0) s‖ / 2)
    (by positivity : 0 ≤
      ‖paretoPointHilbert 0 - (finiteSpace n).starProjection (paretoPointHilbert 0)‖ *
        Real.sqrt R)).mpr hhead
  rw [mul_pow, Real.sq_sqrt hR.le] at hsq
  have hv : vacancy n = 2 *
      ‖paretoPointHilbert 0 - (finiteSpace n).starProjection (paretoPointHilbert 0)‖^2 := rfl
  rw [hv]
  nlinarith


/-- Explicit logarithmic vacancy obstruction, with only conductor divisibility
and an actual critical zero as hypotheses. All coefficient dependence is gone. -/
theorem firstPoint_critical_vacancy_log_bound (n L : ℕ) (hLpos : 0 < L)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (s : ℂ)
    (hs : s.re = 1 / 2) (hz : riemannZeta s = 0) :
    let a := ‖paretoMellin (paretoPointHilbert 0) s‖
    a^2 ≤ 4 * vacancy n * Real.log (4 * ((L : ℝ) + 1 + a) / a) := by
  let a := ‖paretoMellin (paretoPointHilbert 0) s‖
  have ha : 0 < a := norm_pos_iff.mpr
    (firstPoint_mellin_positiveHalfPlane_ne_zero s (by linarith))
  let X := 4 * ((L : ℝ) + 1 + a) / a
  have hX : 1 < X := by
    apply (lt_div_iff₀ ha).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hXp : 0 < X := lt_trans zero_lt_one hX
  have hR : 0 < 2 * Real.log X := mul_pos (by norm_num) (Real.log_pos hX)
  have ht : 2 * ((L : ℝ) + 1) * Real.exp (-(2 * Real.log X) / 2) ≤ a / 2 := by
    rw [show -(2 * Real.log X) / 2 = -Real.log X by ring,
      Real.exp_neg, Real.exp_log hXp]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hXp).mpr
    have he : a / 2 * X = 2 * ((L : ℝ) + 1 + a) := by
      dsimp [X]
      field_simp [ha.ne']
      ring
    rw [he]
    linarith
  have h := firstPoint_critical_vacancy_cutoff_lower_bound
    n L hLpos hL s hs hz (2 * Real.log X) hR ht
  change a^2 ≤ 4 * vacancy n * Real.log X
  change a^2 ≤ 2 * vacancy n * (2 * Real.log X) at h
  nlinarith only [h]

/-- An unconditional conductor-scale vacancy obstruction. The imported
critical-zero theorem supplies the witness, with no RH hypothesis. -/
theorem exists_uniform_conductor_vacancy_obstruction :
    ∃ a : ℝ, 0 < a ∧ ∀ n L : ℕ, 0 < L →
      (∀ d : Fin n, d.val + 2 ∣ L) →
      a^2 ≤ 4 * vacancy n * Real.log (4 * ((L : ℝ) + 1 + a) / a) := by
  obtain ⟨s, hz, hs⟩ := RiemannResearch.RH.exists_critical_zero
  refine ⟨‖paretoMellin (paretoPointHilbert 0) s‖, ?_, ?_⟩
  · exact norm_pos_iff.mpr
      (firstPoint_mellin_positiveHalfPlane_ne_zero s (by linarith))
  · intro n L hLpos hL
    exact firstPoint_critical_vacancy_log_bound n L hLpos hL s hs hz

end RiemannResearch.RH.Pareto.IntegerDPP
