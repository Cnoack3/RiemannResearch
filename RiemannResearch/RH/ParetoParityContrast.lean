import RiemannResearch.RH.ParetoOddMomentHeadNormalization
import RiemannResearch.RH.ParetoRoughTailCertificates

/-!
# Exact finite parity-contrast extraction

Source: independently derived continuation of the user's Pareto
head-normalization handoff, 21 September 2026. The actual full tail norm
has the displayed arithmetic component plus an exact orthogonal remainder.
No small-remainder or unconditional RH assertion is made.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

def parityContrastProjection (s : Finset ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  ∑ k ∈ s, (inner ℝ (differenceCertificate k) f /
    (2 * ((k : ℝ) + 2)^2)) • differenceCertificate k

def parityContrastEnergy (s : Finset ℕ) (f : ThresholdHilbert) : ℝ :=
  ∑ k ∈ s, (inner ℝ (differenceCertificate k) f)^2 /
    (2 * ((k : ℝ) + 2)^2)

theorem parityContrastProjection_norm_sq (s : Finset ℕ) (f : ThresholdHilbert)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k)) :
    ‖parityContrastProjection s f‖^2 = parityContrastEnergy s f := by
  rw [parityContrastProjection, differenceCertificate_sum_norm_sq s _ hsep]
  unfold parityContrastEnergy
  apply Finset.sum_congr rfl
  intro k hk
  have hp : 2 * ((k : ℝ) + 2)^2 ≠ 0 := by positivity
  field_simp

theorem parityContrastProjection_inner (s : Finset ℕ) (f : ThresholdHilbert) :
    inner ℝ f (parityContrastProjection s f) = parityContrastEnergy s f := by
  rw [parityContrastProjection, inner_sum]
  simp only [inner_sum, inner_smul_right]
  unfold parityContrastEnergy
  apply Finset.sum_congr rfl
  intro k hk
  rw [real_inner_comm f (differenceCertificate k)]
  ring

/-- The entire signed norm has an exact, non-discarded orthogonal remainder. -/
theorem parityContrast_energy_completion (s : Finset ℕ) (f : ThresholdHilbert)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k)) :
    ‖f‖^2 = parityContrastEnergy s f + ‖f - parityContrastProjection s f‖^2 := by
  rw [norm_sub_sq_real, parityContrastProjection_norm_sq s f hsep,
    parityContrastProjection_inner]
  ring

theorem parityContrastEnergy_le_full (s : Finset ℕ) (f : ThresholdHilbert)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k)) :
    parityContrastEnergy s f ≤ ‖f‖^2 := by
  rw [parityContrast_energy_completion s f hsep]
  exact le_add_of_nonneg_right (sq_nonneg _)

def coefficientDivisorSum (n : ℕ) (c : Fin n → ℝ) (p : ℕ) : ℝ :=
  ∑ i, c i * divisorIndicator (i.val + 2) p

theorem differenceCertificate_inner_tailAtom (k i : ℕ) (hk : 0 < k) :
    inner ℝ (differenceCertificate k) (tailAtom i) =
      1 / ((i+2 : ℕ) : ℝ) - divisorIndicator (i+2) (k+2) := by
  change inner ℝ (differenceCertificate k)
    (residueAtom i -
      (anchoredEvaluationCLM 1 (residueAtom i)) • paretoPointHilbert 0) = _
  rw [inner_sub_right, inner_smul_right, differenceCertificate_inner_firstPoint k hk,
    mul_zero, sub_zero]
  exact differenceCertificate_inner_residue k (i+2) (by omega)

/-- Actual signed arithmetic contrasts of the legal tail, including composite divisors. -/
theorem tailCombination_pairContrast (n k : ℕ) (c : Fin n → ℝ) (hk : 0 < k) :
    inner ℝ (differenceCertificate k)
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c) =
    oddMomentHead n c - coefficientDivisorSum n c (k+2) := by
  simp only [Fintype.linearCombination_apply, inner_sum, inner_smul_right,
    differenceCertificate_inner_tailAtom k _ hk]
  simp only [oddMomentHead, coefficientDivisorSum, mul_sub,
    Finset.sum_sub_distrib, mul_one_div]

theorem parityContrastEnergy_arithmetic (n : ℕ) (c : Fin n → ℝ) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 0 < k) :
    parityContrastEnergy s
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c) =
    ∑ k ∈ s, (oddMomentHead n c - coefficientDivisorSum n c (k+2))^2 /
      (2 * ((k : ℝ) + 2)^2) := by
  unfold parityContrastEnergy
  apply Finset.sum_congr rfl
  intro k hk
  rw [tailCombination_pairContrast n k c (hs k hk)]

/-- Under the exact admissible head normalization, all finite odd-site
contrast energy is explicit; the full unestimated remainder is retained. -/
theorem normalizedHead_parity_energy_completion (n : ℕ) (c : Fin n → ℝ)
    (s : Finset ℕ) (hs : ∀ k ∈ s, 0 < k)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k))
    (hh : oddMomentHead n c = oddHeadConstant) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 =
    (∑ k ∈ s, (oddHeadConstant - coefficientDivisorSum n c (k+2))^2 /
      (2 * ((k : ℝ) + 2)^2)) +
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c -
      parityContrastProjection s
        (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)‖^2 := by
  rw [parityContrast_energy_completion s _ hsep, parityContrastEnergy_arithmetic n c s hs,
    hh]

theorem coefficientDivisorSum_add (n p : ℕ) (c e : Fin n → ℝ) :
    coefficientDivisorSum n (c+e) p =
      coefficientDivisorSum n c p + coefficientDivisorSum n e p := by
  simp [coefficientDivisorSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Even coefficients cannot change an odd-site divisor sum. -/
theorem evenCorrection_divisorSum_zero (n p : ℕ) (e : Fin n → ℝ)
    (hp : ¬ 2 ∣ p) (he : ∀ i, ¬ 2 ∣ i.val+2 → e i = 0) :
    coefficientDivisorSum n e p = 0 := by
  unfold coefficientDivisorSum
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hd : 2 ∣ i.val+2
  · have hnot : ¬ (i.val+2) ∣ p := fun h => hp (dvd_trans hd h)
    simp [divisorIndicator, hnot]
  · rw [he i hd, zero_mul]

theorem evenCorrection_preserves_oddDivisorSum (n p : ℕ) (c e : Fin n → ℝ)
    (hp : ¬ 2 ∣ p) (he : ∀ i, ¬ 2 ∣ i.val+2 → e i = 0) :
    coefficientDivisorSum n (c+e) p = coefficientDivisorSum n c p := by
  rw [coefficientDivisorSum_add, evenCorrection_divisorSum_zero n p e hp he, add_zero]

/-- The canonical finite range of odd pair contrasts satisfies separation. -/
theorem oddContrastIndices_separated (M : ℕ) :
    (((Finset.range M).image (fun r => 2*r+1) : Finset ℕ) : Set ℕ).Pairwise
      (fun k l => k + 1 < l ∨ l + 1 < k) := by
  intro k hk l hl hne
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hl
  omega

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
