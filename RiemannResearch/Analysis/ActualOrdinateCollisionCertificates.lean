import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.FiniteCollisionCertificates

/-!
Source: user-supplied `Zeta_Zero_Harmonic_Analysis_20261011 (1)(1).md`, Section 12.
These finite deductions make no publication-priority claim.

# Exact finite collision certificates for actual zeta-zero ordinates

These statements are about the actual multiplicity copies of `riemannZeta`.
They have no RH premise, sampling law, density estimate, or spacing assumption.
The exact adapted gap kernel is a finite product of squared normalized sines.
Its associated Fourier convolution representation is not formalized here.
-/

noncomputable section
open Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate FiniteCollisionCertificates

/-- All ordered equal-ordinate occurrence pairs, with the diagonal retained. -/
def collisionEnergy (T : ℝ) : ℝ := collisionCount (copyOrdinate T)

/-- An exact gap-adapted positive sine-kernel energy. -/
def adaptedGapEnergy (T : ℝ) : ℝ :=
  ∑ i : Copies T, ∑ j : Copies T,
    gapKernel (sampleGaps (copyOrdinate T))
      (copyOrdinate T i - copyOrdinate T j)

theorem adaptedGapEnergy_eq_collisionEnergy (T : ℝ) :
    adaptedGapEnergy T = collisionEnergy T :=
  sampleGapKernelEnergy_eq_collisionCount (copyOrdinate T)

/-- The first possible excess is exactly two distinct-occurrence collisions. -/
theorem collisionEnergy_lt_count_add_two_iff (T : ℝ) :
    collisionEnergy T < (Ncount 0 T : ℝ) + 2 ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  unfold collisionEnergy
  rw [← card_copies T]
  exact (collisionCount_lt_card_add_two_iff (copyOrdinate T)).trans
    (copyOrdinate_injective_iff T)

/-- At finite height the adapted sine filter gives an exact equivalence. -/
theorem adaptedGapEnergy_lt_count_add_two_iff (T : ℝ) :
    adaptedGapEnergy T < (Ncount 0 T : ℝ) + 2 ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  rw [adaptedGapEnergy_eq_collisionEnergy]
  exact collisionEnergy_lt_count_add_two_iff T

/-- Every nonnegative pair kernel normalized on coincident ordinates
provides a sufficient finite-height certificate. -/
theorem critical_and_simple_of_kernel_certificate (T : ℝ)
    (K : Copies T → Copies T → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (heq : ∀ i j, copyOrdinate T i = copyOrdinate T j → K i j = 1)
    (hcert : (∑ i, ∑ j, K i j) < (Ncount 0 T : ℝ) + 2) :
    ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  apply (copyOrdinate_injective_iff T).mp
  apply injective_of_kernelEnergy_lt_card_add_two (copyOrdinate T) K hK heq
  simpa only [card_copies] using hcert

/-- A cofinal family of finite-height certificates controls every actual
positive zero, so certificates at every single height are unnecessary. -/
theorem all_cutoffs_critical_and_simple_of_cofinal_kernel_certificates
    (K : (T : ℝ) → Copies T → Copies T → ℝ)
    (hK : ∀ T i j, 0 ≤ K T i j)
    (heq : ∀ T i j,
      copyOrdinate T i = copyOrdinate T j → K T i j = 1)
    (hcert : ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      (∑ i, ∑ j, K T i j) < (Ncount 0 T : ℝ) + 2) :
    ∀ H : ℝ, ∀ ρ ∈ cutoff H, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  intro H ρ hρ
  obtain ⟨T, hHT, hT⟩ := hcert H
  have hρT : ρ ∈ cutoff T := by
    obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hρ
    exact mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩
  exact critical_and_simple_of_kernel_certificate T (K T) (hK T) (heq T) hT ρ hρT

/-- For the exact adapted filter, cofinal certificates are equivalent to
criticality and simplicity in every actual positive-height cutoff. -/
theorem cofinal_adaptedGap_certificates_iff :
    (∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      adaptedGapEnergy T < (Ncount 0 T : ℝ) + 2) ↔
      (∀ H : ℝ, ∀ ρ ∈ cutoff H, ρ.re = 1 / 2 ∧ zeroMult ρ = 1) := by
  constructor
  · intro hcert H ρ hρ
    obtain ⟨T, hHT, hT⟩ := hcert H
    have hρT : ρ ∈ cutoff T := by
      obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hρ
      exact mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩
    exact (adaptedGapEnergy_lt_count_add_two_iff T).mp hT ρ hρT
  · intro hall H
    exact ⟨H, le_rfl, (adaptedGapEnergy_lt_count_add_two_iff H).mpr (hall H)⟩

/-- Every actual positive zero is covered by the cofinal certificates. -/
theorem positive_zero_critical_and_simple_of_cofinal_adaptedGap_certificates
    (hcert : ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      adaptedGapEnergy T < (Ncount 0 T : ℝ) + 2)
    {ρ : ℂ} (hz : IsNontrivialZero ρ) (hpos : 0 < ρ.im) :
    ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  exact cofinal_adaptedGap_certificates_iff.mp hcert ρ.im ρ
    (mem_cutoff.mpr ⟨hz, hpos, le_rfl⟩)


open ZeroOrdinate FiniteCollisionCertificates

/-- Distinct actual zeros in the cutoff, sampled once each. -/
abbrev DistinctZeros (T : ℝ) := {z : ℂ // z ∈ cutoff T}

/-- Ordinate sampling of distinct actual zeros. -/
def distinctOrdinate (T : ℝ) : DistinctZeros T → ℝ := fun ρ => ρ.1.im

theorem card_distinctZeros (T : ℝ) :
    Fintype.card (DistinctZeros T) = (cutoff T).card := by
  simp [DistinctZeros]

/-- Reflection detects off-line zeros without requiring analytic simplicity. -/
theorem distinctOrdinate_injective_iff (T : ℝ) :
    Function.Injective (distinctOrdinate T) ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  constructor
  · intro hinj ρ hρ
    let a : DistinctZeros T := ⟨ρ, hρ⟩
    let b : DistinctZeros T := ⟨reflect ρ, reflect_mem hρ⟩
    have him : distinctOrdinate T a = distinctOrdinate T b := by
      simp [distinctOrdinate, a, b, reflect_im]
    have hab : a = b := hinj him
    have hre : ρ.re = (reflect ρ).re :=
      congrArg (fun z : DistinctZeros T => z.1.re) hab
    rw [reflect_re] at hre
    linarith
  · intro hline a b him
    apply Subtype.ext
    apply Complex.ext
    · rw [hline a.1 a.2, hline b.1 b.2]
    · exact him

/-- Exact gap-adapted energy of distinct actual zero ordinates. -/
def distinctAdaptedGapEnergy (T : ℝ) : ℝ :=
  ∑ i : DistinctZeros T, ∑ j : DistinctZeros T,
    gapKernel (sampleGaps (distinctOrdinate T))
      (distinctOrdinate T i - distinctOrdinate T j)

/-- Exact finite-height criticality certificate; multiple critical zeros are allowed. -/
theorem distinctAdaptedGapEnergy_lt_card_add_two_iff (T : ℝ) :
    distinctAdaptedGapEnergy T < ((cutoff T).card : ℝ) + 2 ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  have h := (gapKernel_certificate_iff_injective
    (distinctOrdinate T) (sampleGaps (distinctOrdinate T))
    (abs_sub_mem_sampleGaps (distinctOrdinate T))).trans
      (distinctOrdinate_injective_iff T)
  simpa only [distinctAdaptedGapEnergy, card_distinctZeros] using h

/-- Cofinal distinct-zero certificates are equivalent to criticality
in every actual positive-height cutoff, without imposing simplicity. -/
theorem cofinal_distinctAdaptedGap_certificates_iff :
    (∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      distinctAdaptedGapEnergy T < ((cutoff T).card : ℝ) + 2) ↔
      (∀ H : ℝ, ∀ ρ ∈ cutoff H, ρ.re = 1 / 2) := by
  constructor
  · intro hcert H ρ hρ
    obtain ⟨T, hHT, hT⟩ := hcert H
    have hρT : ρ ∈ cutoff T := by
      obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hρ
      exact mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩
    exact (distinctAdaptedGapEnergy_lt_card_add_two_iff T).mp hT ρ hρT
  · intro hall H
    exact ⟨H, le_rfl, (distinctAdaptedGapEnergy_lt_card_add_two_iff H).mpr (hall H)⟩

theorem positive_zero_critical_of_cofinal_distinctAdaptedGap_certificates
    (hcert : ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      distinctAdaptedGapEnergy T < ((cutoff T).card : ℝ) + 2)
    {ρ : ℂ} (hz : IsNontrivialZero ρ) (hpos : 0 < ρ.im) :
    ρ.re = 1 / 2 := by
  exact cofinal_distinctAdaptedGap_certificates_iff.mp hcert ρ.im ρ
    (mem_cutoff.mpr ⟨hz, hpos, le_rfl⟩)

/-- Exact agreement between the distinct-ordinate certificate and the
existing actual horizontal-energy obstruction. -/
theorem distinctAdaptedGapEnergy_lt_card_add_two_iff_horizontalEnergy_zero (T : ℝ) :
    distinctAdaptedGapEnergy T < ((cutoff T).card : ℝ) + 2 ↔
      horizontalEnergy T = 0 :=
  (distinctAdaptedGapEnergy_lt_card_add_two_iff T).trans
    (horizontalEnergy_eq_zero_iff T).symm

end RiemannResearch.Analysis.ActualZeroOrdinate
