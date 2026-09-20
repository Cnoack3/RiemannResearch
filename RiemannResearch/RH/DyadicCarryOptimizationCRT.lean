import RiemannResearch.RH.DyadicCarryOptimization

/-!
# Full CRT certificates for finite optimized dyadic repairs

Source: user-provided dyadic-block/CRT argument of 20 September 2026,
Sections 6 and 7. This identifies the complete signed infinite residual energy
with its finite CRT certificate after every finite legal correction, and then
specializes to the actual inverse-Gram optimizer. No limiting estimate is used.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization

/-- The exact arithmetic residual after an arbitrary finite correction that
preserves the jointly repaired head. All cross terms remain inside the square. -/
def dyadicCorrectedError (k N L : ℕ) (c : Fin L → ℝ) : ℕ → ℝ := fun n =>
  dyadicCarryJointError k N n -
    ∑ i : Fin L, c i * (residue (N+2+i.val) n - residue (N+1) n)

theorem dyadicCorrectedError_head (k N L : ℕ) (c : Fin L → ℝ)
    (n : ℕ) (hn : n ≤ N) : dyadicCorrectedError k N L c n = 0 := by
  unfold dyadicCorrectedError
  rw [dyadicCarryJointError_head k N n hn]
  have hz : (∑ i : Fin L,
      c i * (residue (N+2+i.val) n - residue (N+1) n)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [residue, Nat.mod_eq_of_lt (show n < N+2+i.val by omega),
      Nat.mod_eq_of_lt (show n < N+1 by omega)]
  rw [hz, sub_self]

/-- The finite correction lies in the actual finite legal residue span;
boundedness is derived from that membership, not assumed for the error. -/
theorem dyadicCorrectedError_bounded (k N L : ℕ) (c : Fin L → ℝ) :
    ∃ C : ℝ, ∀ n, |dyadicCorrectedError k N L c n| ≤ C := by
  have hz : (∑ i : Fin L,
      c i • (residue (N+2+i.val) - residue (N+1))) ∈
      finiteResidueSubspace (N+L+1) := by
    apply Submodule.sum_mem
    intro i hi
    apply (finiteResidueSubspace (N+L+1)).smul_mem
    apply (finiteResidueSubspace (N+L+1)).sub_mem
    · exact residue_mem_finiteResidueSubspace (by omega)
        (by have hiL := i.isLt; omega)
    · exact residue_mem_finiteResidueSubspace (by omega) (by omega)
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded (Set.Ici 1)
    (by intro a ha; change 1 ≤ a at ha; omega)
    (finiteResidueSubspace_le_full_legal (N+L+1) hz)
  have hC' : ∀ n, |∑ i : Fin L,
      c i * (residue (N+2+i.val) n - residue (N+1) n)| ≤ C := by
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using hC
  obtain ⟨C₀, hC₀⟩ := dyadicCarryJointError_bounded k N
  exact ⟨C₀+C, bounded_sub hC₀ hC'⟩

theorem dyadicCorrectedError_period (k N L P : ℕ) (c : Fin L → ℝ)
    (hkP : 2^k+1 ∣ P)
    (hP : ∀ m, 0 < m → m ≤ N+L+1 → m ∣ P) (n : ℕ) :
    dyadicCorrectedError k N L c (n+P) = dyadicCorrectedError k N L c n := by
  unfold dyadicCorrectedError
  rw [dyadicCarryJointError_period k N P hkP
    (fun m hm hmN => hP m hm (by omega))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [residue_period_of_dvd (hP (N+2+i.val) (by omega)
      (by have hiL := i.isLt; omega)),
    residue_period_of_dvd (hP (N+1) (by omega) (by omega))]

theorem dyadicCorrectedError_summable (k N L : ℕ) (c : Fin L → ℝ) :
    Summable (fun n => positiveWeight n * (dyadicCorrectedError k N L c n)^2) := by
  obtain ⟨C, hC⟩ := dyadicCorrectedError_bounded k N L c
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hC hC)

/-- The displayed arithmetic coordinates are those of the actual Hilbert
residual for the same finite coefficient vector. -/
theorem dyadicCorrectedError_sequence (k N L : ℕ) (c : Fin L → ℝ) :
    hilbertSequence (dyadicJointResidual k N -
      Fintype.linearCombination ℝ (fun i : Fin L => headNullHilbert N i.val) c) =
        dyadicCorrectedError k N L c := by
  change hilbertSequenceLinear (_ - _) = _
  rw [map_sub, Fintype.linearCombination_apply, map_sum]
  funext n
  simp only [Pi.sub_apply, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  change hilbertSequence (dyadicJointResidual k N) n -
    (∑ i : Fin L, c i * hilbertSequence (headNullHilbert N i.val) n) = _
  rw [dyadicJointResidual_sequence]
  simp only [headNullHilbert_sequence]
  rfl

theorem dyadicCorrectedError_norm (k N L : ℕ) (c : Fin L → ℝ) :
    ‖dyadicJointResidual k N -
      Fintype.linearCombination ℝ (fun i : Fin L => headNullHilbert N i.val) c‖^2 =
      ∑' n, positiveWeight n * (dyadicCorrectedError k N L c n)^2 := by
  rw [hilbert_norm_weighted_sq, dyadicCorrectedError_sequence]

/-- All periodic returns and mixed terms of the corrected energy are retained.
The equality holds at every positive common period of the finite data. -/
theorem dyadicCorrectedError_energy_crt (k N L P : ℕ) (c : Fin L → ℝ)
    (hP0 : 0 < P) (hkP : 2^k+1 ∣ P)
    (hP : ∀ m, 0 < m → m ≤ N+L+1 → m ∣ P) :
    (∑' n, positiveWeight n * (dyadicCorrectedError k N L c n)^2) =
      ∑ r : Fin P, progressionWeight P (r.val+1) *
        (dyadicCorrectedError k N L c (r.val+1))^2 := by
  obtain ⟨C, hC⟩ := dyadicCorrectedError_bounded k N L c
  simpa only [paretoInner, pow_two] using
    periodic_paretoInner P hP0 (dyadicCorrectedError k N L c) hC
      (dyadicCorrectedError_period k N L P c hkP hP)

theorem dyadicCorrectedError_energy_eq_tail (k N L : ℕ) (c : Fin L → ℝ) :
    (∑' n, positiveWeight n * (dyadicCorrectedError k N L c n)^2) =
      ∑' n, if N < n then positiveWeight n * (dyadicCorrectedError k N L c n)^2
        else 0 := by
  apply tsum_congr
  intro n
  by_cases hn : N < n
  · rw [if_pos hn]
  · rw [if_neg hn, dyadicCorrectedError_head k N L c n (by omega)]
    simp

/-- The fully optimized signed Schur remainder itself has an exact finite CRT
certificate. The coefficient vector is the constructed inverse-Gram minimizer. -/
theorem dyadicRepairEnergy_crt (k N L P : ℕ) (hP0 : 0 < P)
    (hkP : 2^k+1 ∣ P)
    (hP : ∀ m, 0 < m → m ≤ N+L+1 → m ∣ P) :
    dyadicRepairEnergy k N L =
      ∑ r : Fin P, progressionWeight P (r.val+1) *
        (dyadicCorrectedError k N L
          (headCorrectionCoefficients N L (dyadicJointResidual k N)) (r.val+1))^2 := by
  rw [dyadicRepairEnergy, ← headCorrection_energy]
  unfold headCorrection
  rw [dyadicCorrectedError_norm]
  exact dyadicCorrectedError_energy_crt k N L P _ hP0 hkP hP

end RiemannResearch.RH.Pareto
