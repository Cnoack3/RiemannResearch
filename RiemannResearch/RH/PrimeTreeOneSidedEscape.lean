/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrefixNoEscape
import RiemannResearch.RH.QChargeDilation

/-! # One-sided escape through the children of a prime prefix

Source: the upward question in Prime Trees, Carries and Zeta Zeros
(5 November 2026), §7.2. Combining the exact signed child-limit formula
with the physical one-sided charge criterion allows opposite-sign leakage
and finite total adverse charge. The control of the actual displacement
in the hypotheses below is open.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open Pareto ZetaTwoHilbert QSquarefreeDisplacementRigidity

private theorem rh_of_nonroot_adverse_charge_bound (σ C : ℝ) (hσ : |σ| = 1)
    (hc : ∀ R, (∑ r ∈ Finset.Icc 2 R, max (-(σ * charge displacement r)) 0) ≤ C) :
    RiemannHypothesis := by
  let a (r : ℕ) := max (-(σ * charge displacement r)) 0
  apply QChargeDilation.riemannHypothesis_of_one_sided_charges σ (a 1 + C) hσ
  intro R
  change (∑ r ∈ Finset.Icc 1 R, a r) ≤ a 1 + C
  by_cases hR : R = 0
  · have hC : 0 ≤ C := by simpa using hc 0
    have ha : 0 ≤ a 1 := le_max_right _ _
    simpa [hR] using add_nonneg ha hC
  · have hsplit : Finset.Icc 1 R = insert 1 (Finset.Icc 2 R) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    exact add_le_add le_rfl (hc R)

/-- This exact limit uses arbitrary cutoffs for the finitely many parents.
The factor r recovers unweighted adverse charge from reciprocal escape. -/
theorem finite_adverse_escape_tendsto (b : ℕ → ℝ) (σ : ℝ) (K : ℕ → ℕ) (R : ℕ)
    (ht : ∀ r : ℕ, 2 ≤ r → Tendsto (fun H => subtree b H r) atTop (𝓝 0)) :
    Tendsto (fun H => ∑ r ∈ Finset.Icc 2 R,
      (r : ℝ) * max (σ * escapingChildMass b r (K r) H) 0) atTop
      (𝓝 (∑ r ∈ Finset.Icc 2 R, max (-(σ * b r)) 0)) := by
  apply tendsto_finsetSum
  intro r hr
  have hr2 := (Finset.mem_Icc.mp hr).1
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hv := (escapingChildMass_tendsto b r (K r) hr2 ht).const_mul σ
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h := (hv.max hz).const_mul (r : ℝ)
  have he : (r : ℝ) * max (σ * -(b r / (r : ℝ))) 0 = max (-(σ * b r)) 0 := by
    rw [mul_max_of_nonneg _ _ hr0.le, mul_zero]
    congr 1
    field_simp [hr0.ne']
  rw [he] at h
  exact h

/-- A one-sided signed escape budget through finitely many roots suffices.
Horizons may depend on the root horizon R; K may depend on the individual root. -/
theorem rh_of_cofinal_adverse_child_escape (σ C : ℝ) (hσ : |σ| = 1) (K : ℕ → ℕ)
    (ht : ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun H => subtree (charge displacement) H r) atTop (𝓝 0))
    (he : ∀ R : ℕ, ∃ᶠ H : ℕ in atTop, (∑ r ∈ Finset.Icc 2 R,
      (r : ℝ) * max (σ * escapingChildMass (charge displacement) r (K r) H) 0) ≤ C) :
    RiemannHypothesis := by
  apply rh_of_nonroot_adverse_charge_bound σ C hσ
  intro R
  exact le_of_tendsto_of_frequently (finite_adverse_escape_tendsto _ σ K R ht) (he R)

/-- With a common sign at every vertex the cutoffs can be chosen separately
at each tolerance. Only arbitrarily late upper bounds are required. -/
theorem rh_of_one_sided_child_escape (σ : ℝ) (hσ : |σ| = 1)
    (ht : ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun H => subtree (charge displacement) H r) atTop (𝓝 0))
    (he : ∀ r : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∃ᶠ H : ℕ in atTop, σ * escapingChildMass (charge displacement) r K H ≤ ε) :
    RiemannHypothesis := by
  apply rh_of_nonroot_adverse_charge_bound σ 0 hσ
  intro R
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro r hr
  have hr2 := (Finset.mem_Icc.mp hr).1
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hs : σ * -(charge displacement r / (r : ℝ)) ≤ 0 := by
    by_contra! hp
    obtain ⟨K, hk⟩ := he r hr2 _ (half_pos hp)
    have h := le_of_tendsto_of_frequently
      ((escapingChildMass_tendsto _ r K hr2 ht).const_mul σ) hk
    linarith
  apply max_eq_right
  have h := mul_nonpos_of_nonpos_of_nonneg hs hr0.le
  have ident : (σ * -(charge displacement r / (r : ℝ))) * (r : ℝ) =
      -(σ * charge displacement r) := by field_simp [hr0.ne']
  rwa [ident] at h

end RiemannResearch.RH.QPrimeSubtreeBudget
