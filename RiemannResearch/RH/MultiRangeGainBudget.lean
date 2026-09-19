import RiemannResearch.RH.MultiRangeMinimumExhaustion

/-!
# Exact budgets for reoptimized divisor ranges
Source: user-provided argument `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`,
Sections 6 and 9. The energies here are the complete infima after every addition,
so old coefficients are reoptimized. A fractional-gain hypothesis is explicit.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Energy removed by reoptimizing the enlarged complete dictionary. -/
def divisorRangeGain (Y : ℕ) (s : ℕ → Finset ℕ) (j : ℕ) : ℝ :=
  divisorRangeMinimum Y (s j) - divisorRangeMinimum Y (s (j+1))

def divisorRangeResidual (Y : ℕ) (s : Finset ℕ) : ℝ :=
  divisorRangeMinimum Y s - (Y : ℝ)/((Y : ℝ)+2)

theorem divisorRangeResidual_nonneg (Y : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, Y < d) : 0 ≤ divisorRangeResidual Y s := by
  have h := (conditionalHeadMinimum_ge_head_mass Y).trans
    (conditionalHeadMinimum_le_divisorRangeMinimum Y s hs)
  exact sub_nonneg.mpr h

theorem divisorRangeGain_nonneg (Y : ℕ) (s : ℕ → Finset ℕ)
    (hs : Monotone s) (j : ℕ) : 0 ≤ divisorRangeGain Y s j :=
  sub_nonneg.mpr (divisorRangeMinimum_antitone Y _ _ (hs (Nat.le_succ j)))

/-- Exact telescoping for reoptimized minima, rather than scalar coordinate descent. -/
theorem divisorRangeGain_sum (Y : ℕ) (s : ℕ → Finset ℕ) (J : ℕ) :
    (∑ j ∈ Finset.range J, divisorRangeGain Y s j) =
      divisorRangeMinimum Y (s 0) - divisorRangeMinimum Y (s J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold divisorRangeGain
    ring

theorem divisorRangeGain_budget (Y : ℕ) (s : ℕ → Finset ℕ)
    (hs : Monotone s) (hlegal : ∀ j d, d ∈ s j → Y < d) (J : ℕ) :
    0 ≤ (∑ j ∈ Finset.range J, divisorRangeGain Y s j) ∧
    (∑ j ∈ Finset.range J, divisorRangeGain Y s j) ≤ divisorRangeResidual Y (s 0) := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => divisorRangeGain_nonneg Y s hs j)
  · rw [divisorRangeGain_sum]
    have h := divisorRangeResidual_nonneg Y (s J) (hlegal J)
    unfold divisorRangeResidual at *
    linarith

/-- Conditional mechanism only: a fixed fraction of true residual energy would
force geometric decay. No lower bound on gains is proved by this declaration. -/
theorem divisorRangeResidual_le_geometric (Y : ℕ) (s : ℕ → Finset ℕ)
    (δ : ℝ) (hδ : δ ≤ 1)
    (hgain : ∀ j, δ * divisorRangeResidual Y (s j) ≤ divisorRangeGain Y s j)
    (J : ℕ) :
    divisorRangeResidual Y (s J) ≤ divisorRangeResidual Y (s 0) * (1-δ)^J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hstep : divisorRangeResidual Y (s (J+1)) ≤
        (1-δ) * divisorRangeResidual Y (s J) := by
      have h := hgain J
      unfold divisorRangeResidual divisorRangeGain at *
      nlinarith
    calc
      _ ≤ (1-δ) * divisorRangeResidual Y (s J) := hstep
      _ ≤ (1-δ) * (divisorRangeResidual Y (s 0) * (1-δ)^J) :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hδ)
      _ = _ := by rw [pow_succ]; ring

/-- Exact product form while each previous residual is nonzero. -/
theorem divisorRangeResidual_product (Y : ℕ) (s : ℕ → Finset ℕ) (J : ℕ)
    (hne : ∀ j < J, divisorRangeResidual Y (s j) ≠ 0) :
    divisorRangeResidual Y (s J) = divisorRangeResidual Y (s 0) *
      ∏ j ∈ Finset.range J, (1 - divisorRangeGain Y s j / divisorRangeResidual Y (s j)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hp := ih (by intro j hj; exact hne j (by omega))
    rw [Finset.prod_range_succ, ← mul_assoc, ← hp]
    have hz := hne J (Nat.lt_succ_self J)
    field_simp
    unfold divisorRangeResidual divisorRangeGain
    ring

/-- The empty dictionary has exactly the canonical starting energy. -/
theorem divisorRangeMinimum_empty (Y : ℕ) :
    divisorRangeMinimum Y ∅ =
      conditionalMeanSquare (canonicalMobiusHead Y) := by
  have he (x : ℕ → ℝ) : correctedMobiusHead Y ∅ x = canonicalMobiusHead Y := by
    funext n
    simp [correctedMobiusHead, divisorRangeCorrection]
  simp [divisorRangeMinimum, divisorRangeEnergies, he]

/-- Exact starting-family gain budget, with no discarded signed correlations. -/
theorem divisorRangeGain_from_canonical (Y : ℕ) (s : ℕ → Finset ℕ)
    (hzero : s 0 = ∅) (J : ℕ) :
    divisorRangeMinimum Y (s J) =
      conditionalMeanSquare (canonicalMobiusHead Y) -
        ∑ j ∈ Finset.range J, divisorRangeGain Y s j := by
  have h := divisorRangeGain_sum Y s J
  rw [hzero, divisorRangeMinimum_empty] at h
  linarith

end RiemannResearch.RH.Pareto
