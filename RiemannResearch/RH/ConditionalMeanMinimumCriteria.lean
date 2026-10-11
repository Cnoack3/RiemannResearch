import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.ConditionalMeanSubpolynomial

/-!
# Cofinal and subpolynomial criteria for actual legal minimum energies

Source: user-requested completion, `CofinalMinimumProof.md`, Sections 1--3.
The proof selects genuine near-minimizers once, independently of the growth
exponent, and exposes the unresolved arithmetic bound in the theorem type.
-/
noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto

/-- The new infimum formulation implies actual mathlib RH, without an assumed NB bridge. -/
theorem riemannHypothesis_of_bounded_conditionalHeadMinimum
    (h : ∃ C : ℝ, ∀ N, conditionalHeadMinimum N ≤ C) : RiemannHypothesis := by
  obtain ⟨C, hC⟩ := bounded_minimum_iff_bounded_legal_heads.mp h
  choose g hg hbound using hC
  apply riemannHypothesis_of_bounded_conditionalMean_heads (Set.Ici 1)
    (by intro a ha; exact ha) g id
    (fun N => (hg N).1) (fun j n hn hnj => (hg j).2 n hn hnj)
    tendsto_id C hbound


/-- Cofinal eventual bounds already bound every exact-head infimum. -/
theorem conditionalHeadMinimum_bound_of_cofinal_eventually
    (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop) (C : ℝ)
    (hC : ∀ᶠ j in atTop, conditionalHeadMinimum (Y j) ≤ C) :
    ∀ N, conditionalHeadMinimum N ≤ C := by
  intro N
  obtain ⟨j, hjN, hjC⟩ :=
    ((hY.eventually (eventually_ge_atTop N)).and hC).exists
  exact (conditionalHeadMinimum_mono hjN).trans hjC

theorem bounded_conditionalHeadMinimum_iff_cofinal_eventually
    (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop) :
    (∃ C : ℝ, ∀ N, conditionalHeadMinimum N ≤ C) ↔
      ∃ C : ℝ, ∀ᶠ j in atTop, conditionalHeadMinimum (Y j) ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, Filter.Eventually.of_forall fun j => hC (Y j)⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, conditionalHeadMinimum_bound_of_cofinal_eventually Y hY C hC⟩

/-- This is a growth condition on the actual infimum, not an assumed witness family. -/
def SubpolynomialConditionalHeadMinimum (Y : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ j : ℕ in atTop, conditionalHeadMinimum (Y j) ≤ C * (Y j : ℝ) ^ ε

/-- One choice of actual near-minimizers works for every exponent. -/
theorem subpolynomial_conditionalHeadMinimum_iff_actual_heads
    (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop) :
    SubpolynomialConditionalHeadMinimum Y ↔
      ∃ g : ℕ → ℕ → ℝ, (∀ j, g j ∈ conditionalHeadClass (Y j)) ∧
        SubpolynomialConditionalMean g Y := by
  constructor
  · intro h
    have hex (j : ℕ) := exists_head_energy_lt (Y j) 1 (by norm_num)
    choose g hg he using hex
    refine ⟨g, hg, ?_⟩
    intro ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C + 1, by linarith, ?_⟩
    filter_upwards [hbound, hY.eventually (eventually_ge_atTop 1)] with j hj hjY
    have hjR : (1 : ℝ) ≤ Y j := by exact_mod_cast hjY
    have hp := Real.one_le_rpow hjR hε.le
    nlinarith [he j]
  · rintro ⟨g, hg, hsub⟩ ε hε
    obtain ⟨C, hC, hbound⟩ := hsub ε hε
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with j hj
    exact (conditionalHeadMinimum_le (Y j) (hg j)).trans hj

/-- Cofinal subpolynomial infima imply actual mathlib RH. -/
theorem riemannHypothesis_of_subpolynomial_conditionalHeadMinimum
    (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop)
    (h : SubpolynomialConditionalHeadMinimum Y) : RiemannHypothesis := by
  obtain ⟨g, hg, hsub⟩ :=
    (subpolynomial_conditionalHeadMinimum_iff_actual_heads Y hY).mp h
  exact riemannHypothesis_of_subpolynomial_conditionalMean_heads (Set.Ici 1)
    (by intro a ha; exact ha) g Y (fun j => (hg j).1)
    (fun j n hn hnY => (hg j).2 n hn hnY) hY hsub

theorem riemannHypothesis_of_cofinal_bounded_conditionalHeadMinimum
    (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop)
    (h : ∃ C : ℝ, ∀ᶠ j in atTop, conditionalHeadMinimum (Y j) ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_bounded_conditionalHeadMinimum
    ((bounded_conditionalHeadMinimum_iff_cofinal_eventually Y hY).mpr h)

/-- Every hypothetical right-half-plane zero forces polynomial growth
of the infimum itself, with the explicit previously proved constant. -/
theorem conditionalHeadMinimum_polynomial_obstruction_eventually
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop,
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1) ≤ conditionalHeadMinimum N := by
  filter_upwards [exact_head_polynomial_obstruction_eventually (Set.Ici 1)
    (by intro a ha; exact ha) s hs hs1 hz] with N hN
  apply le_csInf (conditionalHeadEnergies_nonempty N)
  rintro x ⟨g, hg, rfl⟩
  exact hN g hg.1 hg.2

#print axioms RiemannResearch.RH.Pareto.riemannHypothesis_of_bounded_conditionalHeadMinimum
end RiemannResearch.RH.Pareto
