import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ConditionalMeanSignedProjection
import RiemannResearch.RH.ConditionalMeanSubpolynomial

/-!
# Balanced multi-range divisor corrections

Source: user-provided argument `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`,
Sections 3--4 and 9, for the construction and research target. The baseline
canonical witness already has a stronger linear bound in the project.
The subpolynomial bound below is a proposition, not an asserted theorem.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative Probability.ConditionalIID

/-- Balance is eliminated before energy is formed. -/
def divisorAnchorDirection (A d : ℕ) (n : ℕ) : ℝ :=
  (A : ℝ) / (d : ℝ) * residueFraction A n - residueFraction d n

private theorem normalized_residue_legal (d : ℕ) (hd : 0 < d) :
    residueFraction d ∈ legalSeedSpan (Set.Ici 1) := by
  have hr : residue d ∈ legalSeedSpan (Set.Ici 1) := by
    simpa only [dilation_one] using
      (dilation_generator_mem (Set.Ici 1) (a := d) (m := 1) hd (by omega))
  have he : residueFraction d = (1 / (d : ℝ)) • residue d := by
    funext n
    simp [residueFraction, residue, div_eq_mul_inv, mul_comm]
  rw [he]
  exact (legalSeedSpan _).smul_mem _ hr

theorem divisorAnchorDirection_legal (A d : ℕ) (hA : 0 < A) (hd : 0 < d) :
    divisorAnchorDirection A d ∈ legalSeedSpan (Set.Ici 1) := by
  exact (legalSeedSpan _).sub_mem
    ((legalSeedSpan _).smul_mem _ (normalized_residue_legal A hA))
    (normalized_residue_legal d hd)

/-- Exact equality with the two cancelling raw floors. -/
theorem divisorAnchorDirection_floor (A d n : ℕ) (hA : 0 < A) (hd : 0 < d) :
    divisorAnchorDirection A d n =
      ((n / d : ℕ) : ℝ) - (A : ℝ) / (d : ℝ) * ((n / A : ℕ) : ℝ) := by
  have ha : ((n % A : ℕ) : ℝ) + (A : ℝ) * ((n / A : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n A
  have hb : ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n d
  have hAR : (A : ℝ) ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by positivity
  unfold divisorAnchorDirection residueFraction
  field_simp
  nlinarith

theorem divisorAnchorDirection_zero_head (Y A d n : ℕ)
    (hYA : Y < A) (hYd : Y < d) (hn : n ≤ Y) :
    divisorAnchorDirection A d n = 0 := by
  rw [divisorAnchorDirection_floor A d n (by omega) (by omega),
    Nat.div_eq_of_lt (by omega : n < d), Nat.div_eq_of_lt (by omega : n < A)]
  simp

/-- One finite coefficient vector is shared by every sequence index. -/
def divisorRangeCorrection (A : ℕ) (s : Finset ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ s, x d * divisorAnchorDirection A d n

theorem divisorRangeCorrection_legal (A : ℕ) (s : Finset ℕ) (x : ℕ → ℝ)
    (hA : 0 < A) (hs : ∀ d ∈ s, 0 < d) :
    divisorRangeCorrection A s x ∈ legalSeedSpan (Set.Ici 1) := by
  have h : (∑ d ∈ s, x d • divisorAnchorDirection A d) ∈ legalSeedSpan (Set.Ici 1) := by
    apply Submodule.sum_mem
    intro d hd
    exact Submodule.smul_mem _ _ (divisorAnchorDirection_legal A d hA (hs d hd))
  convert h using 1
  funext n
  simp only [divisorRangeCorrection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem divisorRangeCorrection_zero_head (Y A : ℕ) (s : Finset ℕ) (x : ℕ → ℝ)
    (hYA : Y < A) (hs : ∀ d ∈ s, Y < d) (n : ℕ) (hn : n ≤ Y) :
    divisorRangeCorrection A s x n = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [divisorAnchorDirection_zero_head Y A d n hYA (hs d hd) hn, mul_zero]

/-- The anchor coefficient is solved exactly, with its sign preserved. -/
theorem divisorRangeCorrection_floor (A : ℕ) (s : Finset ℕ) (x : ℕ → ℝ)
    (hA : 0 < A) (hs : ∀ d ∈ s, 0 < d) (n : ℕ) :
    divisorRangeCorrection A s x n =
      (∑ d ∈ s, x d * ((n / d : ℕ) : ℝ)) -
        ((A : ℝ) * ∑ d ∈ s, x d / (d : ℝ)) * ((n / A : ℕ) : ℝ) := by
  unfold divisorRangeCorrection
  calc
    _ = ∑ d ∈ s, (x d * ((n / d : ℕ) : ℝ) -
        (A : ℝ) * (x d / (d : ℝ)) * ((n / A : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [divisorAnchorDirection_floor A d n hA (hs d hd)]
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]

/-- Combining disjoint ranges does not change the shared deterministic vector. -/
theorem divisorRangeCorrection_union (A : ℕ) (s t : Finset ℕ) (x : ℕ → ℝ)
    (hst : Disjoint s t) (n : ℕ) :
    divisorRangeCorrection A (s ∪ t) x n =
      divisorRangeCorrection A s x n + divisorRangeCorrection A t x n := by
  exact Finset.sum_union hst

def correctedMobiusHead (Y : ℕ) (s : Finset ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  canonicalMobiusHead Y n + divisorRangeCorrection (Y + 1) s x n

theorem correctedMobiusHead_mem_class (Y : ℕ) (s : Finset ℕ) (x : ℕ → ℝ)
    (hs : ∀ d ∈ s, Y < d) : correctedMobiusHead Y s x ∈ conditionalHeadClass Y := by
  have hR := divisorRangeCorrection_legal (Y + 1) s x (by omega)
    (by intro d hd; have := hs d hd; omega)
  refine ⟨(legalSeedSpan _).add_mem (canonicalMobiusHead_mem_legal Y) hR, ?_⟩
  intro n hn hnY
  change canonicalMobiusHead Y n + divisorRangeCorrection (Y + 1) s x n = 1
  rw [canonicalMobiusHead_exact Y n hn hnY,
    divisorRangeCorrection_zero_head Y (Y + 1) s x (by omega) hs n hnY, add_zero]

/-- Full signed range energy; all within-range covariance is inside E(R). -/
theorem correctedMobiusHead_energy (Y : ℕ) (s : Finset ℕ) (x : ℕ → ℝ)
    (hs : ∀ d ∈ s, Y < d) :
    conditionalMeanSquare (correctedMobiusHead Y s x) =
      conditionalMeanSquare (canonicalMobiusHead Y) +
        2 * conditionalMeanInner (canonicalMobiusHead Y) (divisorRangeCorrection (Y + 1) s x) +
        conditionalMeanSquare (divisorRangeCorrection (Y + 1) s x) := by
  have hR := divisorRangeCorrection_legal (Y + 1) s x (by omega)
    (by intro d hd; have := hs d hd; omega)
  unfold correctedMobiusHead
  simpa only [one_mul, mul_one, one_pow] using
    conditionalMeanSquare_add_mul (canonicalMobiusHead Y) (divisorRangeCorrection (Y + 1) s x)
      (canonicalMobiusHead_mem_legal Y) hR 1

/-- Explicit unresolved existence obligation; defining it provides no witness. -/
def MultiRangeSubpolynomialTarget : Prop :=
  ∃ (Y : ℕ → ℕ) (s : ℕ → Finset ℕ) (x : ℕ → ℕ → ℝ),
    Filter.Tendsto Y Filter.atTop Filter.atTop ∧
    (∀ j d, d ∈ s j → Y j < d) ∧
    SubpolynomialConditionalMean (fun j => correctedMobiusHead (Y j) (s j) (x j)) Y

/-- Conditional research reduction. The sole arithmetic input is still open. -/
theorem riemannHypothesis_of_multiRangeSubpolynomialTarget
    (h : MultiRangeSubpolynomialTarget) : RiemannHypothesis := by
  obtain ⟨Y, s, x, hY, hs, hcost⟩ := h
  have hc (j : ℕ) := correctedMobiusHead_mem_class (Y j) (s j) (x j) (hs j)
  exact riemannHypothesis_of_subpolynomial_conditionalMean_heads
    (Set.Ici 1) (by intro a ha; exact ha)
    (fun j => correctedMobiusHead (Y j) (s j) (x j)) Y
    (fun j => (hc j).1) (fun j => (hc j).2) hY hcost

end RiemannResearch.RH.Pareto
