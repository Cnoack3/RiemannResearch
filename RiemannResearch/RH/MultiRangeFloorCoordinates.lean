import RiemannResearch.RH.MultiRangeCompleteness
import RiemannResearch.RH.CRTLegalCoordinates

/-!
# Balanced finite floor coordinates

Section 2 of `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`:
finite floor coefficients, including the modulus-one coefficient explicitly,
are balanced precisely when their linear slopes cancel. The exact head forces
that coefficient to one and the remaining low coefficients to Möbius values.
No estimate for the energy is assumed or concluded.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative CRTBlock

/-- The first term is the coefficient of `floor(n/1) = n`. -/
def finiteFloorSynthesis (s : Finset ℕ) (a : ℕ → ℝ) (a₁ : ℝ) (n : ℕ) : ℝ :=
  a₁ * (n : ℝ) + ∑ d ∈ s, a d * (n / d : ℕ)

/-- Cancel slopes before passing to legal bounded residue coordinates. -/
theorem finiteFloorSynthesis_eq_normalized_of_balance
    (s : Finset ℕ) (a : ℕ → ℝ) (a₁ : ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d)
    (hb : a₁ + ∑ d ∈ s, a d / (d : ℝ) = 0) :
    finiteFloorSynthesis s a a₁ = normalizedResidueSynthesis s (fun d => -a d) := by
  funext n
  have he (d : ℕ) (hd : d ∈ s) :
      ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) - residueFraction d n := by
    have hdR : (d : ℝ) ≠ 0 := by have := hs d hd; positivity
    have hdiv : ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mod_add_div n d
    unfold residueFraction
    field_simp
    nlinarith
  unfold finiteFloorSynthesis normalizedResidueSynthesis
  calc
    _ = a₁ * (n : ℝ) + ∑ d ∈ s,
        a d * ((n : ℝ) / (d : ℝ) - residueFraction d n) := by
      congr 1
      exact Finset.sum_congr rfl (fun d hd => by rw [he d hd])
    _ = (a₁ + ∑ d ∈ s, a d / (d : ℝ)) * (n : ℝ) +
        ∑ d ∈ s, (-a d) * residueFraction d n := by
      have hsum : (∑ d ∈ s, a d * ((n : ℝ) / (d : ℝ) - residueFraction d n)) =
          ∑ d ∈ s, ((a d / (d : ℝ)) * (n : ℝ) + (-a d) * residueFraction d n) := by
        apply Finset.sum_congr rfl
        intro d _
        ring
      rw [hsum, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring
    _ = _ := by rw [hb, zero_mul, zero_add]

/-- A balanced finite floor sequence is a genuine globally legal function. -/
theorem finiteFloorSynthesis_legal_of_balance
    (s : Finset ℕ) (a : ℕ → ℝ) (a₁ : ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d)
    (hb : a₁ + ∑ d ∈ s, a d / (d : ℝ) = 0) :
    finiteFloorSynthesis s a a₁ ∈ legalSeedSpan (Set.Ici 1) := by
  rw [finiteFloorSynthesis_eq_normalized_of_balance s a a₁ hs hb]
  exact normalizedResidueSynthesis_legal s (fun d => -a d) hs

/-- Exact low Möbius coefficients characterize the head of every balanced floor sum. -/
theorem finiteFloorSynthesis_exact_head_iff
    (s : Finset ℕ) (a : ℕ → ℝ) (a₁ : ℝ) (Y : ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hY : 0 < Y)
    (hb : a₁ + ∑ d ∈ s, a d / (d : ℝ) = 0) :
    (∀ n, 0 < n → n ≤ Y → finiteFloorSynthesis s a a₁ n = 1) ↔
      a₁ = 1 ∧ ∀ n, 1 < n → n ≤ Y →
        (if n ∈ s then a n else 0) = (ArithmeticFunction.moebius n : ℝ) := by
  classical
  rw [finiteFloorSynthesis_eq_normalized_of_balance s a a₁ hs hb,
    normalizedResidueSynthesis_exact_head_iff s (fun d => -a d) Y hs hY]
  have hm : (∑ d ∈ s, -a d / (d : ℝ)) = a₁ := by
    simp only [neg_div, Finset.sum_neg_distrib]
    linarith
  rw [hm]
  constructor
  · rintro ⟨h₁, hc⟩
    refine ⟨h₁, ?_⟩
    intro n hn hnY
    have h := hc n hn hnY
    split_ifs at h ⊢ <;> linarith
  · rintro ⟨h₁, hc⟩
    refine ⟨h₁, ?_⟩
    intro n hn hnY
    have h := hc n hn hnY
    split_ifs at h ⊢ <;> linarith

/-- Every legal exact head, and only such a head, has finite balanced floor
coefficients whose low entries equal the Möbius function. -/
theorem conditionalHeadClass_iff_balanced_floor_coordinates
    (Y : ℕ) (hY : 0 < Y) (F : ℕ → ℝ) :
    F ∈ conditionalHeadClass Y ↔
      ∃ (s : Finset ℕ) (a : ℕ → ℝ),
        (∀ d ∈ s, 2 ≤ d) ∧
        (1 + ∑ d ∈ s, a d / (d : ℝ) = 0) ∧
        (∀ n, 1 < n → n ≤ Y →
          (if n ∈ s then a n else 0) = (ArithmeticFunction.moebius n : ℝ)) ∧
        finiteFloorSynthesis s a 1 = F := by
  classical
  constructor
  · intro hF
    obtain ⟨s, c, hs, hc⟩ := legal_exists_normalized_synthesis hF.1
    have hh : ∀ n, 0 < n → n ≤ Y → normalizedResidueSynthesis s c n = 1 := by
      rw [hc]
      exact hF.2
    obtain ⟨hm, hlo⟩ := (normalizedResidueSynthesis_exact_head_iff s c Y hs hY).mp hh
    have hb : 1 + ∑ d ∈ s, -c d / (d : ℝ) = 0 := by
      simp only [neg_div, Finset.sum_neg_distrib]
      rw [hm]
      ring
    refine ⟨s, fun d => -c d, hs, hb, ?_, ?_⟩
    · intro n hn hnY
      have h := hlo n hn hnY
      split_ifs at h ⊢ <;> linarith
    · rw [finiteFloorSynthesis_eq_normalized_of_balance s (fun d => -c d) 1 hs hb]
      simpa only [neg_neg] using hc
  · rintro ⟨s, a, hs, hb, hlo, rfl⟩
    exact ⟨finiteFloorSynthesis_legal_of_balance s a 1 hs hb,
      (finiteFloorSynthesis_exact_head_iff s a 1 Y hs hY hb).mpr ⟨rfl, hlo⟩⟩

end RiemannResearch.RH.Pareto
