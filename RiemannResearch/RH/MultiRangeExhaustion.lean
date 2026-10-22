import RiemannResearch.RH.MultiRangeCompleteness

/-!
# Exhaustion by finite anchored divisor ranges
Source: user-provided argument `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`,
Sections 4 and 9, for the claims and proof strategy. These are exact statements
about all finite legal witnesses, without an energy-growth hypothesis.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID

/-- The anchor itself is a redundant zero direction. -/
theorem divisorAnchorDirection_self (A : ℕ) : divisorAnchorDirection A A = 0 := by
  funext n
  by_cases hA : A = 0
  · simp [hA, divisorAnchorDirection, ArithmeticCumulative.residueFraction]
  · simp [divisorAnchorDirection, hA]

/-- Removing the anchor makes the support agree with the manuscript's chart. -/
theorem divisorRangeCorrection_erase_anchor (A : ℕ) (s : Finset ℕ) (x : ℕ → ℝ) :
    divisorRangeCorrection A (s.erase A) x = divisorRangeCorrection A s x := by
  classical
  funext n
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro d hd hde
  have he : d = A := by
    by_contra h
    exact hde (Finset.mem_erase.mpr ⟨h, hd⟩)
  subst d
  simp only [divisorAnchorDirection_self, Pi.zero_apply, mul_zero]

/-- Every exact head has support strictly beyond the anchor. -/
theorem conditionalHeadClass_exists_strict_divisor_ranges (Y : ℕ) (hY : 0 < Y)
    {F : ℕ → ℝ} (hF : F ∈ conditionalHeadClass Y) :
    ∃ (s : Finset ℕ) (x : ℕ → ℝ),
      (∀ d ∈ s, Y + 1 < d) ∧ correctedMobiusHead Y s x = F := by
  classical
  obtain ⟨s,x,hs,hx⟩ := conditionalHeadClass_exists_divisor_ranges Y hY hF
  refine ⟨s.erase (Y+1),x,?_,?_⟩
  · intro d hd
    obtain ⟨hne,hd⟩ := Finset.mem_erase.mp hd
    have := hs d hd
    omega
  · unfold correctedMobiusHead at *
    rw [divisorRangeCorrection_erase_anchor]
    exact hx

/-- Equality of energy sets, stronger than equality of their infima. -/
theorem conditionalHeadEnergies_eq_divisor_range_energies (Y : ℕ) (hY : 0 < Y) :
    conditionalHeadEnergies Y =
      {E : ℝ | ∃ (s : Finset ℕ) (x : ℕ → ℝ),
        (∀ d ∈ s, Y+1 < d) ∧ conditionalMeanSquare (correctedMobiusHead Y s x) = E} := by
  ext E
  constructor
  · rintro ⟨F,hF,rfl⟩
    obtain ⟨s,x,hs,hx⟩ := conditionalHeadClass_exists_strict_divisor_ranges Y hY hF
    exact ⟨s,x,hs,by rw [hx]⟩
  · rintro ⟨s,x,hs,rfl⟩
    exact ⟨_,correctedMobiusHead_mem_class Y s x (by intro d hd; have := hs d hd; omega),rfl⟩

/-- Unrestricted anchored optimization is exactly the existing legal infimum. -/
theorem conditionalHeadMinimum_eq_divisor_range_infimum (Y : ℕ) (hY : 0 < Y) :
    conditionalHeadMinimum Y =
      sInf {E : ℝ | ∃ (s : Finset ℕ) (x : ℕ → ℝ),
        (∀ d ∈ s, Y+1 < d) ∧ conditionalMeanSquare (correctedMobiusHead Y s x) = E} := by
  unfold conditionalHeadMinimum
  rw [conditionalHeadEnergies_eq_divisor_range_energies Y hY]

/-- Choice supplies one deterministic finite vector per family member;
there is no coefficient choice depending on the latent index. -/
theorem exact_head_family_exists_divisor_ranges (Y : ℕ → ℕ) (hY : ∀ j, 0 < Y j)
    (F : ℕ → ℕ → ℝ) (hF : ∀ j, F j ∈ conditionalHeadClass (Y j)) :
    ∃ (s : ℕ → Finset ℕ) (x : ℕ → ℕ → ℝ),
      (∀ j d, d ∈ s j → Y j + 1 < d) ∧
      (∀ j, correctedMobiusHead (Y j) (s j) (x j) = F j) := by
  classical
  choose s x hs hx using fun j =>
    conditionalHeadClass_exists_strict_divisor_ranges (Y j) (hY j) (hF j)
  exact ⟨s,x,hs,hx⟩

/-- No ansatz restriction is introduced for positive cofinal exact heads.
The subpolynomial hypothesis remains an explicit, unproved arithmetic input. -/
theorem multiRangeSubpolynomialTarget_of_legal_family
    (Y : ℕ → ℕ) (hY : ∀ j, 0 < Y j)
    (hcofinal : Filter.Tendsto Y Filter.atTop Filter.atTop)
    (F : ℕ → ℕ → ℝ) (hF : ∀ j, F j ∈ conditionalHeadClass (Y j))
    (hsub : SubpolynomialConditionalMean F Y) : MultiRangeSubpolynomialTarget := by
  obtain ⟨s,x,hs,hx⟩ := exact_head_family_exists_divisor_ranges Y hY F hF
  refine ⟨Y,s,x,hcofinal,?_,?_⟩
  · intro j d hd
    have := hs j d hd
    omega
  · have he : (fun j => correctedMobiusHead (Y j) (s j) (x j)) = F := funext hx
    rw [he]
    exact hsub

end RiemannResearch.RH.Pareto
