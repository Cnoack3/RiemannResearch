import RiemannResearch.Analysis.FiniteHilbertHeadConstraint
import RiemannResearch.RH.ParetoOddMomentNormalizedSchur
import RiemannResearch.RH.ParetoParityBlockEnergy

/-!
# Independent even correction of actual Pareto candidates

Source: the next concrete target in the user's parity-closure handoff,
21 September 2026. The even dictionary has its own size, unrelated to the
finite candidate's sieve conductor. Refinement decreases the complete norm
by an exact squared increment while preserving every odd contrast. The
remaining-energy decay needed for RH is not assumed or proved here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.ArithmeticCumulative

/-- The actual finite even correction with exact certificate normalization. -/
def independentEvenCorrection (n : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  headConstrainedResidual (evenTailAtom_independent n) f (infiniteCoprimeCertificate 2)

theorem evenTail_synthesisSpan_mono {n m : ℕ} (hnm : n ≤ m) :
    synthesisSpan (evenTailAtom n) ≤ synthesisSpan (evenTailAtom m) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨⟨i.val.val, lt_of_lt_of_le i.val.isLt hnm⟩, i.property⟩, rfl⟩

theorem independentEvenCorrection_observation (n : ℕ) (hn : 0 < n) (f : ThresholdHilbert) :
    inner ℝ (independentEvenCorrection n f) (infiniteCoprimeCertificate 2) = 0 :=
  headConstrainedResidual_observation _ _ _ (ne_of_gt (evenHeadEnergy_pos n hn))

/-- All original signed Gram terms and the head-normalization cost remain exact. -/
theorem independentEvenCorrection_energy (n : ℕ) (hn : 0 < n) (f : ThresholdHilbert) :
    ‖independentEvenCorrection n f‖^2 =
      ‖f‖^2 - ∑ i, inverseCoeff (evenTailAtom_independent n) f i *
        inner ℝ (evenTailAtom n i) f +
      (inner ℝ (f - headProjection (evenTailAtom_independent n) f)
        (infiniteCoprimeCertificate 2))^2 / evenHeadEnergy n := by
  rw [independentEvenCorrection, headConstrainedResidual_energy _ _ _
    (ne_of_gt (evenHeadEnergy_pos n hn))]
  rw [show ‖f - headProjection (evenTailAtom_independent n) f‖^2 =
      ‖f‖^2 - ∑ i, inverseCoeff (evenTailAtom_independent n) f i *
        inner ℝ (evenTailAtom n i) f from residual_schur_value _ _]
  rfl

theorem independentEvenCorrection_refinement {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (f : ThresholdHilbert) :
    ‖independentEvenCorrection n f‖^2 = ‖independentEvenCorrection m f‖^2 +
      ‖independentEvenCorrection n f - independentEvenCorrection m f‖^2 :=
  headConstrainedResidual_refinement _ _ _ _
    (ne_of_gt (evenHeadEnergy_pos n hn))
    (ne_of_gt (evenHeadEnergy_pos m (lt_of_lt_of_le hn hnm)))
    (evenTail_synthesisSpan_mono hnm)

theorem independentEvenCorrection_energy_antitone (f : ThresholdHilbert) :
    Antitone (fun n : ℕ => ‖independentEvenCorrection (n+1) f‖^2) := by
  intro n m hnm
  have h := independentEvenCorrection_refinement (by omega : 0 < n+1)
    (by omega : n+1 ≤ m+1) f
  linarith [sq_nonneg ‖independentEvenCorrection (n+1) f - independentEvenCorrection (m+1) f‖]

theorem independentEvenCorrection_energy_le (n : ℕ) (hn : 0 < n) (f : ThresholdHilbert)
    (hf : inner ℝ f (infiniteCoprimeCertificate 2) = 0) :
    ‖independentEvenCorrection n f‖^2 ≤ ‖f‖^2 :=
  headConstrainedResidual_energy_le _ _ _ (ne_of_gt (evenHeadEnergy_pos n hn)) hf

theorem evenTail_pairContrast_eq_certificate (n k : ℕ) (hk : 0 < k)
    (ho : ¬ 2 ∣ k+2) (a : EvenTailIndex n → ℝ) :
    inner ℝ (differenceCertificate k) (Fintype.linearCombination ℝ (evenTailAtom n) a) =
      inner ℝ (Fintype.linearCombination ℝ (evenTailAtom n) a) (infiniteCoprimeCertificate 2) := by
  rw [Fintype.linearCombination_apply, inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right, real_inner_smul_left]
  unfold evenTailAtom
  rw [differenceCertificate_inner_tailAtom k i.val.val hk,
    infiniteCoprimeCertificate_all_observations 2 i.val.val (by decide) (by decide),
    coprimeObservationDefect_two, if_pos i.property]
  have hd : ¬ i.val.val+2 ∣ k+2 := fun h => ho (dvd_trans i.property h)
  simp [divisorIndicator, hd]

/-- At exact normalization, every finite even correction preserves all odd contrasts. -/
theorem independentEvenCorrection_pairContrast (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) (ho : ¬ 2 ∣ k+2) (f : ThresholdHilbert)
    (hf : inner ℝ f (infiniteCoprimeCertificate 2) = 0) :
    inner ℝ (differenceCertificate k) (independentEvenCorrection n f) =
      inner ℝ (differenceCertificate k) f := by
  have hz := independentEvenCorrection_observation n hn f
  change inner ℝ (f + Fintype.linearCombination ℝ (evenTailAtom n)
    (headConstrainedCoeff (evenTailAtom_independent n) f (infiniteCoprimeCertificate 2)))
    (infiniteCoprimeCertificate 2) = 0 at hz
  rw [inner_add_left, hf, zero_add] at hz
  change inner ℝ (differenceCertificate k) (f + _) = _
  rw [inner_add_right, evenTail_pairContrast_eq_certificate n k hk ho, hz, add_zero]

theorem independentEvenCorrection_fullContrast (n : ℕ) (hn : 0 < n)
    (f : ThresholdHilbert) (hf : inner ℝ f (infiniteCoprimeCertificate 2) = 0) :
    fullOddPairContrastEnergy (independentEvenCorrection n f) = fullOddPairContrastEnergy f := by
  apply tsum_congr
  intro p
  by_cases hp : coprimePairIndex 2 p
  · have hk : 0 < p-2 := by have := hp.1; omega
    have ho : ¬ 2 ∣ p-2+2 := by have := hp.2.1; have := hp.1; omega
    rw [independentEvenCorrection_pairContrast n (p-2) hn hk ho f hf]
  · simp [coprimePairMass, hp]

theorem independentEvenCorrection_remaining_refinement {n m : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) (f : ThresholdHilbert)
    (hf : inner ℝ f (infiniteCoprimeCertificate 2) = 0) :
    fullParityRemainingEnergy (independentEvenCorrection n f) =
      fullParityRemainingEnergy (independentEvenCorrection m f) +
        ‖independentEvenCorrection n f - independentEvenCorrection m f‖^2 := by
  unfold fullParityRemainingEnergy
  rw [independentEvenCorrection_fullContrast n hn f hf,
    independentEvenCorrection_fullContrast m (lt_of_lt_of_le hn hnm) f hf,
    independentEvenCorrection_refinement hn hnm f]
  ring

theorem independentEvenCorrection_mem_tailSpan (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ Submodule.span ℝ (Set.range tailAtom)) :
    independentEvenCorrection n f ∈ Submodule.span ℝ (Set.range tailAtom) := by
  apply Submodule.add_mem _ hf
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i.val.val, rfl⟩

theorem tailSpan_firstCoordinate_zero (f : ThresholdHilbert)
    (hf : f ∈ Submodule.span ℝ (Set.range tailAtom)) : hilbertSequence f 1 = 0 := by
  have hs : Submodule.span ℝ (Set.range tailAtom) ≤
      LinearMap.ker (anchoredEvaluationCLM 1).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact tailMap_evaluation (CoefficientStabilization.residueAtom i)
  have hv : anchoredEvaluationCLM 1 f = 0 := hs hf
  simpa only [anchoredEvaluationCLM_apply] using hv

theorem sieveMobiusTail_certificate (P : ℕ) (a : ℝ) :
    inner ℝ (sieveMobiusTail P a) (infiniteCoprimeCertificate 2) =
      sieveMobiusHead P a - oddHeadConstant * sieveMobiusOddMoment P a := by
  rw [sieveMobiusTail, sum_inner]
  simp only [sum_inner, real_inner_smul_left]
  unfold sieveMobiusHead sieveMobiusOddMoment
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 := sieve_nonunit_divisor_ge_two P d hd
  rw [infiniteCoprimeCertificate_all_observations 2 (d-2) (by decide) (by decide),
    coprimeObservationDefect_two, Nat.sub_add_cancel hd2]
  have hc : Nat.Coprime d 2 ↔ ¬ 2 ∣ d := by
    rw [Nat.coprime_comm]
    exact Nat.prime_two.coprime_iff_not_dvd
  simp only [hc]
  by_cases he : 2 ∣ d <;> simp only [he, if_true, if_false, not_true_eq_false,
    not_false_eq_true, oddHeadConstant] <;> ring

theorem sieveMobiusNormalizedTail_certificate (P : ℕ) (a : ℝ) :
    inner ℝ (sieveMobiusNormalizedTail P a) (infiniteCoprimeCertificate 2) =
      oddHeadConstant * (1-sieveMobiusOddMoment P a) := by
  rw [sieveMobiusNormalizedTail, inner_add_left, real_inner_smul_left,
    sieveMobiusTail_certificate, coprimeCertificate_two_observation_zero]
  ring

theorem sieveMobiusUnitTail_certificate (P : ℕ) (hP : P ≠ 0) (h3 : 3 ∣ P) :
    inner ℝ (sieveMobiusNormalizedTail P (1/sieveMobiusOddMoment P 1))
      (infiniteCoprimeCertificate 2) = 0 := by
  rw [sieveMobiusNormalizedTail_certificate,
    sieveMobiusOddMoment_normalized P (ne_of_gt (sieveMobiusOddMoment_pos P hP h3))]
  ring

/-- The normalized sieve and even dictionary have fully independent sizes. -/
def independentlyCorrectedSieve (P m : ℕ) : ThresholdHilbert :=
  independentEvenCorrection (m+1)
    (sieveMobiusNormalizedTail P (1/sieveMobiusOddMoment P 1))

theorem independentlyCorrectedSieve_fullContrast (P m : ℕ) (hP : P ≠ 0) (h3 : 3 ∣ P) :
    fullOddPairContrastEnergy (independentlyCorrectedSieve P m) =
      fullOddPairContrastEnergy (sieveMobiusNormalizedTail P (1/sieveMobiusOddMoment P 1)) :=
  independentEvenCorrection_fullContrast (m+1) (by omega) _
    (sieveMobiusUnitTail_certificate P hP h3)

theorem independentlyCorrectedSieve_firstCoordinate (P m : ℕ) :
    hilbertSequence (independentlyCorrectedSieve P m) 1 = 0 :=
  tailSpan_firstCoordinate_zero _ (independentEvenCorrection_mem_tailSpan _ _
    (sieveMobiusNormalizedTail_mem_tailSpan _ _))

/-- The solved arithmetic contrast and the unsolved block means appear in one exact identity. -/
theorem independentlyCorrectedSieve_energy_exact (P m : ℕ) (hP : P ≠ 0) (h3 : 3 ∣ P) :
    ‖independentlyCorrectedSieve P m‖^2 =
      ((∑' p, coprimePairMass 2 p)+1)^2 * (∑' p, coprimePairMass (2*P) p) /
        (2*(∑' p, coprimePairMass 2 p)*
          ((∑' p, coprimePairMass 2 p)-(∑' p, coprimePairMass (2*P) p))) +
      2*‖dyadicHalfAdjoint (independentlyCorrectedSieve P m)‖^2 := by
  rw [zero_head_fullParity_energy_completion _ (independentlyCorrectedSieve_firstCoordinate P m),
    independentlyCorrectedSieve_fullContrast P m hP h3,
    sieveMobiusNormalizedTail_unitMoment_contrast_exact P hP h3]

/-- Every schedule for the independently growing even dictionary retains contrast closure. -/
theorem independentlyCorrectedSieve_contrast_tendsto (m : ℕ → ℕ) :
    Tendsto (fun n => fullOddPairContrastEnergy
      (independentlyCorrectedSieve (n+2).factorial (m n))) atTop (𝓝 0) := by
  apply factorial_sieve_fullOddPairContrast_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (independentlyCorrectedSieve_fullContrast (n+2).factorial (m n)
    (Nat.factorial_ne_zero _) (Nat.dvd_factorial (by norm_num) (by omega))).symm

/-- The complete remaining norm is exactly the outstanding two-scale estimate. -/
theorem independentlyCorrectedSieve_fullEnergy_iff_remaining (m : ℕ → ℕ) :
    Tendsto (fun n => ‖independentlyCorrectedSieve (n+2).factorial (m n)‖^2) atTop (𝓝 0) ↔
      Tendsto (fun n => fullParityRemainingEnergy
        (independentlyCorrectedSieve (n+2).factorial (m n))) atTop (𝓝 0) :=
  fullParity_norm_sq_tendsto_zero_iff _ (independentlyCorrectedSieve_contrast_tendsto m)

/-- The next arithmetic estimate is the norm of the actual half-scale block means. -/
theorem independentlyCorrectedSieve_fullEnergy_iff_blockMeans (m : ℕ → ℕ) :
    Tendsto (fun n => ‖independentlyCorrectedSieve (n+2).factorial (m n)‖^2) atTop (𝓝 0) ↔
      Tendsto (fun n => ‖dyadicHalfAdjoint
        (independentlyCorrectedSieve (n+2).factorial (m n))‖^2) atTop (𝓝 0) := by
  rw [independentlyCorrectedSieve_fullEnergy_iff_remaining]
  have he (n : ℕ) := fullParityRemainingEnergy_eq_halfAdjoint _
    (independentlyCorrectedSieve_firstCoordinate (n+2).factorial (m n))
  simp only [he]
  constructor
  · intro h
    simpa using h.div_const 2
  · intro h
    simpa using h.const_mul 2

end RiemannResearch.RH.Pareto
