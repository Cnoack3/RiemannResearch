import RiemannResearch.Analysis.ContractiveProducts
import RiemannResearch.RH.BurnolZeroFactors
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.WeilExplicitFormula.Statement.SeamClosed
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Burnol's scalar product over the actual off-line zeros

Source: the product appearing in Theorem 1.2 of J.-F. Burnol,
*A note on Nyman's equivalent formulation of the Riemann Hypothesis*,
arXiv:math/9910055, https://arxiv.org/abs/math/9910055.

This module constructs the squared scalar zero product over the actual
nontrivial zeros of Mathlib's `riemannZeta` lying strictly to the right of
the critical line. The exponent is the actual analytic multiplicity, not
a user-supplied weight. Both positive and negative ordinates are included.

The finite-subset net avoids choosing an enumeration, and permits the empty
zero family under RH. Its limit is a real number in `[0,1]`. The equality
of this scalar product with a continuous Nyman--Beurling projection norm
is a separate analytic theorem and is not asserted here. Nor do the
order-theoretic results alone prove that this limit is strictly positive.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.Burnol

/-- Actual nontrivial zeta zeros strictly to the right of the critical line. -/
abbrev RightZero :=
  {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ (1 / 2 : ℝ) < ρ.re}

theorem rightZero_ne_zero (ρ : RightZero) : (ρ : ℂ) ≠ 0 := by
  intro h
  have hpos := ρ.property.1.2.1
  simp [h] at hpos

theorem rightZero_ne_one (ρ : RightZero) : (ρ : ℂ) ≠ 1 := by
  intro h
  have hlt := ρ.property.1.2.2
  simp [h] at hlt

theorem rightZero_mult_pos (ρ : RightZero) : 0 < Zeta23.zeroMult ρ := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Zeta23.zetaSeam.one_le_mult ρ ρ.property.1)

/-- The squared norm ratio, with the zero's full analytic multiplicity. -/
def weightedFactorSq (ρ : RightZero) : ℝ := factorSq ρ ^ Zeta23.zeroMult ρ

theorem weightedFactorSq_nonneg (ρ : RightZero) : 0 ≤ weightedFactorSq ρ := by
  exact pow_nonneg (factorSq_nonneg _) _

theorem weightedFactorSq_pos (ρ : RightZero) : 0 < weightedFactorSq ρ := by
  exact pow_pos (factorSq_pos (rightZero_ne_zero ρ) (rightZero_ne_one ρ)) _

theorem weightedFactorSq_lt_one (ρ : RightZero) : weightedFactorSq ρ < 1 := by
  exact pow_lt_one₀ (factorSq_nonneg _) (factorSq_lt_one ρ.property.2)
    (ne_of_gt (rightZero_mult_pos ρ))

theorem weightedFactorSq_le_one (ρ : RightZero) : weightedFactorSq ρ ≤ 1 :=
  (weightedFactorSq_lt_one ρ).le

/-- The product over any finite set of distinct off-line zeros; multiplicity
is already carried by each factor. -/
def finiteProductSq (F : Finset RightZero) : ℝ := ∏ ρ ∈ F, weightedFactorSq ρ

@[simp] theorem finiteProductSq_empty : finiteProductSq ∅ = 1 := by
  simp [finiteProductSq]

@[simp] theorem finiteProductSq_singleton (ρ : RightZero) :
    finiteProductSq {ρ} = weightedFactorSq ρ := by
  simp [finiteProductSq]

theorem finiteProductSq_nonneg (F : Finset RightZero) : 0 ≤ finiteProductSq F := by
  exact Finset.prod_nonneg fun ρ _ => weightedFactorSq_nonneg ρ

theorem finiteProductSq_pos (F : Finset RightZero) : 0 < finiteProductSq F := by
  exact Finset.prod_pos fun ρ _ => weightedFactorSq_pos ρ

theorem finiteProductSq_antitone : Antitone finiteProductSq := by
  intro F G hFG
  exact Finset.prod_le_prod_of_subset_of_le_one hFG
    (fun ρ _ => weightedFactorSq_nonneg ρ) (fun ρ _ _ => weightedFactorSq_le_one ρ)

theorem finiteProductSq_le_one (F : Finset RightZero) : finiteProductSq F ≤ 1 := by
  simpa using finiteProductSq_antitone (Finset.empty_subset F)

theorem finiteProductSq_bddBelow : BddBelow (Set.range finiteProductSq) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨F, rfl⟩
  exact finiteProductSq_nonneg F

/-- The canonical squared zero product, as the infimum of all finite products. -/
def productSq : ℝ := ⨅ F : Finset RightZero, finiteProductSq F

theorem productSq_nonneg : 0 ≤ productSq := by
  exact le_ciInf fun F => finiteProductSq_nonneg F

theorem productSq_le_finiteProductSq (F : Finset RightZero) :
    productSq ≤ finiteProductSq F := by
  exact ciInf_le finiteProductSq_bddBelow F

theorem productSq_le_one : productSq ≤ 1 := by
  simpa using productSq_le_finiteProductSq ∅

theorem productSq_le_weightedFactorSq (ρ : RightZero) :
    productSq ≤ weightedFactorSq ρ := by
  simpa using productSq_le_finiteProductSq {ρ}

/-- Unconditional convergence of the directed net of finite zero products. -/
theorem tendsto_finiteProductSq :
    Tendsto finiteProductSq atTop (𝓝 productSq) := by
  exact tendsto_atTop_ciInf finiteProductSq_antitone finiteProductSq_bddBelow

/-- The infimum construction is the unconditional infinite product in Mathlib. -/
theorem hasProd_weightedFactorSq : HasProd weightedFactorSq productSq := by
  change Tendsto (fun F : Finset RightZero => ∏ ρ ∈ F, weightedFactorSq ρ)
    atTop (𝓝 productSq)
  exact tendsto_finiteProductSq

theorem tprod_weightedFactorSq : (∏' ρ : RightZero, weightedFactorSq ρ) = productSq :=
  hasProd_weightedFactorSq.tprod_eq

/-- A single actual right-hand zero forces a strict scalar product loss. -/
theorem productSq_lt_one_of_rightZero (ρ : RightZero) : productSq < 1 := by
  exact lt_of_le_of_lt (productSq_le_weightedFactorSq ρ) (weightedFactorSq_lt_one ρ)

/-- RH makes the indexing type empty, so every finite product is exactly one. -/
theorem finiteProductSq_eq_one_of_rh (hRH : RiemannHypothesis)
    (F : Finset RightZero) : finiteProductSq F = 1 := by
  apply Finset.prod_eq_one
  intro ρ _
  exact False.elim
    ((riemannHypothesis_iff_right_half_strip_zero_free.mp hRH)
      ρ ρ.property.2 ρ.property.1.2.2 ρ.property.1.1)

theorem productSq_eq_one_of_rh (hRH : RiemannHypothesis) : productSq = 1 := by
  unfold productSq
  simp only [finiteProductSq_eq_one_of_rh hRH, ciInf_const]

/-- An exact reformulation of RH using the scalar product of actual zeros.
This does not assert that the equivalent equality `productSq = 1` holds. -/
theorem productSq_eq_one_iff_rh : productSq = 1 ↔ RiemannHypothesis := by
  constructor
  · intro hp
    apply riemannHypothesis_iff_right_half_strip_zero_free.mpr
    intro s hhalf h1 hz
    let ρ : RightZero := ⟨s, ⟨⟨hz, by linarith, h1⟩, hhalf⟩⟩
    have hlt := productSq_lt_one_of_rightZero ρ
    rw [hp] at hlt
    exact (lt_irrefl 1) hlt
  · exact productSq_eq_one_of_rh

theorem productSq_lt_one_iff_not_rh : productSq < 1 ↔ ¬ RiemannHypothesis := by
  constructor
  · intro hlt hRH
    rw [productSq_eq_one_of_rh hRH] at hlt
    exact (lt_irrefl 1) hlt
  · intro hn
    by_contra hlt
    have heq : productSq = 1 := le_antisymm productSq_le_one (not_lt.mp hlt)
    exact hn (productSq_eq_one_iff_rh.mp heq)

/-- The exact multiplicity-corrected loss attached to a single zero. -/
theorem one_sub_weightedFactorSq (ρ : RightZero) :
    1 - weightedFactorSq ρ =
      ((2 * (ρ : ℂ).re - 1) / Complex.normSq (ρ : ℂ)) *
        ∑ k ∈ Finset.range (Zeta23.zeroMult ρ), factorSq ρ ^ k := by
  rw [weightedFactorSq, Real.one_sub_pow_eq_mul_sum,
    one_sub_factorSq (rightZero_ne_zero ρ)]

/-- Each off-line zero gives a quantitative lower bound for the total loss. -/
theorem singleZero_defect_le_product_defect (ρ : RightZero) :
    1 - weightedFactorSq ρ ≤ 1 - productSq := by
  exact sub_le_sub_left (productSq_le_weightedFactorSq ρ) 1

theorem singleZero_exact_defect_le_product_defect (ρ : RightZero) :
    ((2 * (ρ : ℂ).re - 1) / Complex.normSq (ρ : ℂ)) *
      (∑ k ∈ Finset.range (Zeta23.zeroMult ρ), factorSq ρ ^ k) ≤ 1 - productSq := by
  rw [← one_sub_weightedFactorSq]
  exact singleZero_defect_le_product_defect ρ

end RiemannResearch.RH.Burnol
