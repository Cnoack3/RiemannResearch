import RiemannResearch.RH.MultiRangeExhaustion

/-!
# Finite divisor minima exhaust the legal infimum
Source: user-provided argument `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`,
Section 9, for the statement and finite-support proof. No rate or attainment
of the unrestricted infimum is asserted.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID

/-- Extend a vector by zero when its divisor dictionary is enlarged. -/
theorem divisorRangeCorrection_extend (A : ℕ) (s t : Finset ℕ) (x : ℕ → ℝ)
    (hst : s ⊆ t) :
    divisorRangeCorrection A t (fun d => if d ∈ s then x d else 0) =
      divisorRangeCorrection A s x := by
  classical
  funext n
  unfold divisorRangeCorrection
  symm
  calc
    _ = ∑ d ∈ s, (if d ∈ s then x d else 0) * divisorAnchorDirection A d n := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [if_pos hd]
    _ = _ := by
      apply Finset.sum_subset hst
      intro d _ hd
      rw [if_neg hd, zero_mul]

def divisorRangeEnergies (Y : ℕ) (s : Finset ℕ) : Set ℝ :=
  Set.range (fun x : ℕ → ℝ => conditionalMeanSquare (correctedMobiusHead Y s x))

def divisorRangeMinimum (Y : ℕ) (s : Finset ℕ) : ℝ :=
  sInf (divisorRangeEnergies Y s)

theorem divisorRangeEnergies_nonempty (Y : ℕ) (s : Finset ℕ) :
    (divisorRangeEnergies Y s).Nonempty := ⟨_, ⟨0,rfl⟩⟩

theorem divisorRangeEnergies_bddBelow (Y : ℕ) (s : Finset ℕ) :
    BddBelow (divisorRangeEnergies Y s) := by
  refine ⟨0,?_⟩
  rintro E ⟨x,rfl⟩
  exact conditionalMeanSquare_nonneg _

theorem divisorRangeMinimum_le (Y : ℕ) (s : Finset ℕ) (x : ℕ → ℝ) :
    divisorRangeMinimum Y s ≤ conditionalMeanSquare (correctedMobiusHead Y s x) :=
  csInf_le (divisorRangeEnergies_bddBelow Y s) ⟨x,rfl⟩

theorem conditionalHeadMinimum_le_divisorRangeMinimum (Y : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, Y < d) :
    conditionalHeadMinimum Y ≤ divisorRangeMinimum Y s := by
  apply le_csInf (divisorRangeEnergies_nonempty Y s)
  rintro E ⟨x,rfl⟩
  exact conditionalHeadMinimum_le Y (correctedMobiusHead_mem_class Y s x hs)

/-- Adding any finite range cannot raise the infimum. -/
theorem divisorRangeMinimum_antitone (Y : ℕ) (s t : Finset ℕ) (hst : s ⊆ t) :
    divisorRangeMinimum Y t ≤ divisorRangeMinimum Y s := by
  apply le_csInf (divisorRangeEnergies_nonempty Y s)
  rintro E ⟨x,rfl⟩
  have h := divisorRangeMinimum_le Y t (fun d => if d ∈ s then x d else 0)
  unfold correctedMobiusHead at h
  rw [divisorRangeCorrection_extend (Y+1) s t x hst] at h
  exact h

/-- Consecutive finite ranges are cofinal; finite support supplies convergence.
This is an equality of limits, not a quantitative uniform estimate. -/
theorem tendsto_divisorRangeMinimum_conditionalHeadMinimum (Y : ℕ) (hY : 0 < Y) :
    Tendsto (fun J : ℕ => divisorRangeMinimum Y (Finset.Icc (Y+2) (Y+2+J)))
      atTop (𝓝 (conditionalHeadMinimum Y)) := by
  classical
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with J
    exact ha.trans_le (conditionalHeadMinimum_le_divisorRangeMinimum Y _
      (by intro d hd; have := (Finset.mem_Icc.mp hd).1; omega))
  · intro b hb
    obtain ⟨F,hF,hE⟩ := exists_head_energy_lt Y
      (b - conditionalHeadMinimum Y) (sub_pos.mpr hb)
    obtain ⟨s,x,hs,hx⟩ := conditionalHeadClass_exists_strict_divisor_ranges Y hY hF
    filter_upwards [eventually_ge_atTop (s.sup id)] with J hJ
    have hst : s ⊆ Finset.Icc (Y+2) (Y+2+J) := by
      intro d hd
      have hlo := hs d hd
      have hhi : d ≤ s.sup id := Finset.le_sup (f := id) hd
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hbound := (divisorRangeMinimum_antitone Y s _ hst).trans
      (divisorRangeMinimum_le Y s x)
    rw [hx] at hbound
    linarith

end RiemannResearch.RH.Pareto
