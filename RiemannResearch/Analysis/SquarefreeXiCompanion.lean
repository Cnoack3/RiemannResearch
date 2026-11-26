import RiemannResearch.Analysis.LiCriterionImport.Lc.LiCriterion.HadamardSummabilityBridge
import RiemannResearch.Analysis.LiCriterionImport.Lc.LiCriterion.XiGrowth
import RiemannResearch.Analysis.LiCriterionImport.Hadamard.General.Factorization

/-!
# An entire function with one simple zero per distinct nontrivial zeta zero

Apply the genus-one Hadamard product to the distinct complex zeros, with each
index assigned multiplicity one. The original completed zeta function supplies
the inverse-square summability through its unconditional growth bound. The
multiplicity of this new product is a statement about the companion itself.
-/

noncomputable section
open LiCriterion Hadamard

namespace RiemannResearch.Analysis.SquarefreeXiCompanion

def unitZeroSet : ZeroSetMultiplicity riemannXi where
  toZeroSet := xiZeroSet
  mult := fun _ => 1
  mult_pos := fun _ => Nat.zero_lt_one

private instance : Countable unitZeroSet.Zero := by
  change Countable NontrivialZero
  infer_instance

private theorem weightedSummable :
    Summable (fun ρ : unitZeroSet.Zero =>
      (unitZeroSet.mult ρ : ℝ) / ‖unitZeroSet.z ρ‖ ^ (2 : ℕ)) := by
  dsimp only [unitZeroSet, xiZeroSet]
  simpa only [Nat.cast_one] using xi_genus_one_of_hadamard_order_one
    XiGrowth.riemannXi_hasFiniteOrder XiGrowth.riemannXi_order_le_one

private theorem zero_injective : Function.Injective unitZeroSet.z :=
  fun _ _ h => Subtype.ext h

private theorem zero_nonzero (ρ : unitZeroSet.Zero) : unitZeroSet.z ρ ≠ 0 :=
  ρ.ne_zero

def companion : ℂ → ℂ := General.canonicalProductZeroSetMultiplicityRank unitZeroSet 1

/-- Explicit genus-one product over the distinct complex zero locations. -/
theorem companion_eq_product (s : ℂ) :
    companion s = ∏' ρ : NontrivialZero, weierstrass_E 1 (s / ρ.val) := by
  have h := General.canonicalProductZeroSetMultiplicityRank_eq_tprod_pow
    unitZeroSet (p := 1) weightedSummable zero_nonzero s
  simpa only [companion, unitZeroSet, xiZeroSet, pow_one] using h

theorem companion_entire : Differentiable ℂ companion :=
  General.canonicalProductZeroSetMultiplicityRank_differentiable
    unitZeroSet (p := 1) weightedSummable zero_nonzero

theorem companion_zero_iff (s : ℂ) :
    companion s = 0 ↔ ∃ ρ : NontrivialZero, s = ρ.val :=
  General.canonicalProductZeroSetMultiplicityRank_eq_zero_iff
    unitZeroSet (p := 1) weightedSummable zero_injective zero_nonzero s

theorem companion_zero_iff_xi (s : ℂ) :
    companion s = 0 ↔ riemannXi s = 0 :=
  (companion_zero_iff s).trans (xi_zeros_are_nontrivial_zeros s).symm

theorem companion_zero_iff_zeta (s : ℂ) :
    companion s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  rw [companion_zero_iff]
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ρ.property
  · intro h
    exact ⟨⟨s,h⟩, rfl⟩

theorem companion_orderNat_at_zero (ρ : NontrivialZero) :
    analyticOrderNatAt companion ρ.val = 1 :=
  General.analyticOrderNatAt_canonicalProductZeroSetMultiplicityRank
    unitZeroSet (p := 1) weightedSummable zero_injective zero_nonzero ρ

theorem companion_order_at_zero (ρ : NontrivialZero) :
    analyticOrderAt companion ρ.val = 1 := by
  have hn := companion_orderNat_at_zero ρ
  have hf : analyticOrderAt companion ρ.val ≠ ⊤ := by
    intro h
    simp [analyticOrderNatAt, h] at hn
  simpa only [hn, Nat.cast_one] using (Nat.cast_analyticOrderNatAt hf).symm

theorem companion_order_off_support {s : ℂ} (hs : riemannXi s ≠ 0) :
    analyticOrderAt companion s = 0 :=
  (companion_entire.analyticAt s).analyticOrderAt_eq_zero.mpr
    (fun h => hs ((companion_zero_iff_xi s).mp h))

/-- Away from the zero divisor, multiplying by the companion does not change
the analytic order of another holomorphic germ. -/
theorem analyticOrderAt_mul_companion {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s)
    (hs : riemannXi s ≠ 0) :
    analyticOrderAt (fun w => f w * companion w) s = analyticOrderAt f s := by
  change analyticOrderAt (f * companion) s = analyticOrderAt f s
  rw [analyticOrderAt_mul hf (companion_entire.analyticAt s),
    companion_order_off_support hs, add_zero]

end RiemannResearch.Analysis.SquarefreeXiCompanion
