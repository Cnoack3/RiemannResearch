import RiemannResearch.RH.IntegerDPPExistence

/-!
# Arithmetic exclusion for the actual weighted residue DPP

Source: user-provided arithmetic DPP argument (2026-09-20). Equal physical
residue features give proportional counting-kernel columns after the Pareto
square-root factors are retained. No RH or limiting-vacancy assumption occurs.
Any common conductor works, in particular lcm(2,...,n+1).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Probability.DPP

private theorem finiteSpace_physical_expansion (n : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ finiteSpace n) :
    ∃ a : Fin n → ℝ,
      hilbertSequence x = ∑ d : Fin n, a d • residueFraction (d.val + 2) := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n x hx
  refine ⟨a, ?_⟩
  rw [ha]
  change hilbertSequenceLinear (∑ d : Fin n, a d • residueAtom d.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul]
  change a d • hilbertSequence (residueAtom d.val) = _
  rw [residueAtom, normalizedResidueHilbert_sequence]

theorem finiteSpace_sequence_eq_of_residue_congr (n i j : ℕ)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2))
    (x : ThresholdHilbert) (hx : x ∈ finiteSpace n) :
    hilbertSequence x (i + 1) = hilbertSequence x (j + 1) := by
  obtain ⟨a, ha⟩ := finiteSpace_physical_expansion n x hx
  rw [ha]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [residueFraction, hres d]

theorem finiteSpace_sequence_zero_of_divisibility (n i : ℕ)
    (hdiv : ∀ d : Fin n, d.val + 2 ∣ i + 1)
    (x : ThresholdHilbert) (hx : x ∈ finiteSpace n) :
    hilbertSequence x (i + 1) = 0 := by
  obtain ⟨a, ha⟩ := finiteSpace_physical_expansion n x hx
  rw [ha]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro d hd
  simp [residueFraction, Nat.mod_eq_zero_of_dvd (hdiv d)]

/-- Projection kernel entries equal coordinates of projected counting vectors. -/
theorem integerKernel_eq_coordinate (n i j : ℕ) :
    integerKernel n i j = ((finiteSpace n).starProjection (countingBasis i)) j := by
  have ho : inner ℝ ((finiteSpace n).starProjection (countingBasis i))
      (countingBasis j - (finiteSpace n).starProjection (countingBasis j)) = 0 :=
    ((finiteSpace n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (countingBasis j)) _
      ((finiteSpace n).starProjection_apply_mem (countingBasis i))
  simp only [inner_sub_right] at ho
  have hc : inner ℝ ((finiteSpace n).starProjection (countingBasis i))
      (countingBasis j) = ((finiteSpace n).starProjection (countingBasis i)) j := by
    rw [real_inner_comm]
    simp [countingBasis, lp.inner_single_left]
  unfold integerKernel
  linarith

/-- Equal physical features give proportional columns with exact Pareto factors. -/
theorem integerKernel_weighted_residue_congr (n i j k : ℕ)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2)) :
    Real.sqrt (paretoWeight j) * integerKernel n k i =
      Real.sqrt (paretoWeight i) * integerKernel n k j := by
  have h := finiteSpace_sequence_eq_of_residue_congr n i j hres
    ((finiteSpace n).starProjection (countingBasis k))
    ((finiteSpace n).starProjection_apply_mem (countingBasis k))
  simp only [hilbertSequence_succ] at h
  rw [← integerKernel_eq_coordinate n k i, ← integerKernel_eq_coordinate n k j] at h
  have hi : Real.sqrt (paretoWeight i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos i))
  have hj : Real.sqrt (paretoWeight j) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos j))
  simpa only [mul_comm] using (div_eq_div_iff hi hj).mp h

theorem integerKernel_pair_det_zero_of_residue_congr (n i j : ℕ)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2)) :
    integerKernel n i i * integerKernel n j j -
      integerKernel n i j * integerKernel n j i = 0 := by
  have hi := integerKernel_weighted_residue_congr n i j i hres
  have hj := integerKernel_weighted_residue_congr n i j j hres
  have hz : Real.sqrt (paretoWeight j) *
      (integerKernel n i i * integerKernel n j j -
        integerKernel n i j * integerKernel n j i) = 0 := by
    calc
      _ = (Real.sqrt (paretoWeight j) * integerKernel n i i) * integerKernel n j j -
          integerKernel n i j * (Real.sqrt (paretoWeight j) * integerKernel n j i) := by ring
      _ = (Real.sqrt (paretoWeight i) * integerKernel n i j) * integerKernel n j j -
          integerKernel n i j * (Real.sqrt (paretoWeight i) * integerKernel n j j) := by
        rw [hi, hj]
      _ = 0 := by ring
  exact (mul_eq_zero.mp hz).resolve_left
    (ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos j)))

theorem integerKernel_diagonal_zero_of_divisibility (n i : ℕ)
    (hdiv : ∀ d : Fin n, d.val + 2 ∣ i + 1) : integerKernel n i i = 0 := by
  rw [integerKernel_eq_coordinate]
  have h := finiteSpace_sequence_zero_of_divisibility n i hdiv
    ((finiteSpace n).starProjection (countingBasis i))
    ((finiteSpace n).starProjection_apply_mem (countingBasis i))
  simp only [hilbertSequence_succ] at h
  have hi : Real.sqrt (paretoWeight i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos i))
  simpa only [zero_mul] using (div_eq_iff hi).mp h

/-- The diagonal intensity divided by Pareto weight is constant on each complete
residue class. This is the exact one-site lift-weight identity. -/
theorem integerKernel_weighted_diagonal_residue_congr (n i j : ℕ)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2)) :
    paretoWeight j * integerKernel n i i = paretoWeight i * integerKernel n j j := by
  have hi := integerKernel_weighted_residue_congr n i j i hres
  have hj := integerKernel_weighted_residue_congr n i j j hres
  have hs : integerKernel n i j = integerKernel n j i := real_inner_comm _ _
  calc
    _ = (Real.sqrt (paretoWeight j) * Real.sqrt (paretoWeight j)) *
        integerKernel n i i := by rw [Real.mul_self_sqrt (paretoWeight_pos j).le]
    _ = Real.sqrt (paretoWeight j) *
        (Real.sqrt (paretoWeight j) * integerKernel n i i) := by ring
    _ = Real.sqrt (paretoWeight j) *
        (Real.sqrt (paretoWeight i) * integerKernel n i j) := by rw [hi]
    _ = Real.sqrt (paretoWeight i) *
        (Real.sqrt (paretoWeight j) * integerKernel n j i) := by rw [hs]; ring
    _ = Real.sqrt (paretoWeight i) *
        (Real.sqrt (paretoWeight i) * integerKernel n j j) := by rw [hj]
    _ = (Real.sqrt (paretoWeight i) * Real.sqrt (paretoWeight i)) *
        integerKernel n j j := by ring
    _ = _ := by rw [Real.mul_self_sqrt (paretoWeight_pos i).le]

theorem integerLaw_occupation_per_weight_residue_congr (n i j : ℕ)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2)) :
    (integerLaw n).real {x | x i = true} / paretoWeight i =
      (integerLaw n).real {x | x j = true} / paretoWeight j := by
  have hi : (integerLaw n).real {x | x i = true} = integerKernel n i i :=
    (integerLaw_isDPP n).occupation i
  have hj : (integerLaw n).real {x | x j = true} = integerKernel n j j :=
    (integerLaw_isDPP n).occupation j
  rw [hi, hj]
  apply (div_eq_div_iff (ne_of_gt (paretoWeight_pos i))
    (ne_of_gt (paretoWeight_pos j))).mpr
  simpa only [mul_comm] using integerKernel_weighted_diagonal_residue_congr n i j hres

/-- Distinct integers with the same complete residue feature cannot both occur. -/
theorem integerLaw_pair_exclusion (n i j : ℕ) (hij : i ≠ j)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2)) :
    (integerLaw n).real {x | x i = true ∧ x j = true} = 0 := by
  calc
    _ = integerKernel n i i * integerKernel n j j -
        integerKernel n i j * integerKernel n j i := (integerLaw_isDPP n).two_point hij
    _ = 0 := integerKernel_pair_det_zero_of_residue_congr n i j hres

theorem integerLaw_ae_pair_exclusion (n i j : ℕ) (hij : i ≠ j)
    (hres : ∀ d : Fin n, (i + 1) % (d.val + 2) = (j + 1) % (d.val + 2)) :
    ∀ᵐ x ∂integerLaw n, ¬(x i = true ∧ x j = true) := by
  rw [ae_iff, ← measureReal_eq_zero_iff]
  simpa only [not_not] using integerLaw_pair_exclusion n i j hij hres

theorem integerLaw_occupation_zero_of_divisibility (n i : ℕ)
    (hdiv : ∀ d : Fin n, d.val + 2 ∣ i + 1) :
    (integerLaw n).real {x | x i = true} = 0 := by
  calc
    _ = integerKernel n i i := (integerLaw_isDPP n).occupation i
    _ = 0 := integerKernel_diagonal_zero_of_divisibility n i hdiv

/-- Any common conductor works, in particular lcm(2,...,n+1). -/
theorem integerLaw_common_conductor_exclusion (n L i j : ℕ)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (hij : i ≠ j)
    (hmod : (i + 1) % L = (j + 1) % L) :
    (integerLaw n).real {x | x i = true ∧ x j = true} = 0 := by
  apply integerLaw_pair_exclusion n i j hij
  intro d
  have hh := congrArg (fun k : ℕ => k % (d.val + 2)) hmod
  simpa only [Nat.mod_mod_of_dvd (i + 1) (hL d),
    Nat.mod_mod_of_dvd (j + 1) (hL d)] using hh

theorem integerLaw_common_conductor_multiple_absent (n L i : ℕ)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) (hi : L ∣ i + 1) :
    (integerLaw n).real {x | x i = true} = 0 :=
  integerLaw_occupation_zero_of_divisibility n i (fun d => (hL d).trans hi)

/-- All residue classes simultaneously contain at most one occupied site. -/
theorem integerLaw_ae_common_conductor_injective (n L : ℕ)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) :
    ∀ᵐ x ∂integerLaw n, ∀ i j, x i = true → x j = true →
      (i + 1) % L = (j + 1) % L → i = j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun x _ _ _ => hij)
  by_cases hmod : (i + 1) % L = (j + 1) % L
  · have hp : ∀ᵐ x ∂integerLaw n, ¬(x i = true ∧ x j = true) := by
      rw [ae_iff, ← measureReal_eq_zero_iff]
      simpa only [not_not] using integerLaw_common_conductor_exclusion n L i j hL hij hmod
    filter_upwards [hp] with x hx
    intro hi hj hm
    exact False.elim (hx ⟨hi, hj⟩)
  · exact Filter.Eventually.of_forall (fun x _ _ hm => False.elim (hmod hm))

/-- Multiples of the common conductor are simultaneously absent almost surely. -/
theorem integerLaw_ae_common_conductor_multiples_absent (n L : ℕ)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L) :
    ∀ᵐ x ∂integerLaw n, ∀ i, L ∣ i + 1 → x i = false := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : L ∣ i + 1
  · have hp : ∀ᵐ x ∂integerLaw n, ¬x i = true := by
      rw [ae_iff, ← measureReal_eq_zero_iff]
      simpa only [not_not] using integerLaw_common_conductor_multiple_absent n L i hL hi
    filter_upwards [hp] with x hx
    intro hdiv
    cases hxi : x i <;> simp_all
  · exact Filter.Eventually.of_forall (fun x hdiv => False.elim (hi hdiv))

end RiemannResearch.RH.Pareto.IntegerDPP
