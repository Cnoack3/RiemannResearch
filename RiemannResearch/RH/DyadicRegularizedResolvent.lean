import RiemannResearch.RH.DyadicQuotientAbel
/-!
# Exact arithmetic columns and finite and infinite triadic resolvents

Source: user-provided DyadicGramPrefixVerification20260910(1).md,
September 10 continuation, arithmetic-series and normalization obligations.
Every Mobius sign and the full finite terminal column are retained.
Infinite regrouping explicitly requires actual product-series summability;
this module does not supply that analytic provider or the norm remainder.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem dyadicRegularizedTerm_succ (ε : ℝ) (m j : ℕ) :
    dyadicRegularizedTerm ε (m,j+1) =
      triadicDampingRatio ε •
        dyadicQuotientDilation 3 (by norm_num) (dyadicRegularizedTerm ε (m,j)) := by
  have hc : dyadicRegularizationCoefficient ε m (j+1) =
      triadicDampingRatio ε * dyadicRegularizationCoefficient ε m j := by
    unfold dyadicRegularizationCoefficient
    rw [pow_succ]
    ring
  have hi : (m+1)*3^(j+1) = 3*((m+1)*3^j) := by rw [pow_succ]; ring
  simp only [dyadicRegularizedTerm, hc, map_smul,
    dyadicQuotientDilation_apply, dyadicQuotientProjection_dilation_projection,
    hilbertDilation_comp, smul_smul, hi]

def dyadicRegularizedColumn (ε : ℝ) (j : ℕ) : ThresholdHilbert :=
  ∑' m : ℕ, dyadicRegularizedTerm ε (m,j)

theorem dyadicRegularizedTerm_column_summable (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) (j : ℕ) :
    Summable (fun m : ℕ => dyadicRegularizedTerm ε (m,j)) := by
  exact hs.comp_injective (fun a b h => by simpa using congrArg Prod.fst h)

theorem dyadicRegularizedColumn_summable (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) :
    Summable (dyadicRegularizedColumn ε) := by
  have ht := hs.comp_injective (Equiv.prodComm ℕ ℕ).injective
  exact ht.prod

theorem dyadicRegularizedFamily_eq_columns (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) :
    dyadicRegularizedFamily ε =
      dyadicRegularizationNormalization ε • ∑' j : ℕ, dyadicRegularizedColumn ε j := by
  unfold dyadicRegularizedFamily dyadicRegularizedColumn
  congr 1
  exact hs.tsum_prod.trans
    (Summable.tsum_comm (f := fun m j => dyadicRegularizedTerm ε (m,j)) hs).symm

theorem dyadicRegularizedColumn_succ (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) (j : ℕ) :
    dyadicRegularizedColumn ε (j+1) =
      triadicDampingRatio ε •
        dyadicQuotientDilation 3 (by norm_num) (dyadicRegularizedColumn ε j) := by
  let L : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
    triadicDampingRatio ε • dyadicQuotientDilation 3 (by norm_num)
  have hmap := L.map_tsum (dyadicRegularizedTerm_column_summable ε hs j)
  change L (dyadicRegularizedColumn ε j) = ∑' m : ℕ,
    L (dyadicRegularizedTerm ε (m,j)) at hmap
  rw [dyadicRegularizedColumn]
  calc
    _ = ∑' m : ℕ, L (dyadicRegularizedTerm ε (m,j)) :=
      tsum_congr (fun m => dyadicRegularizedTerm_succ ε m j)
    _ = _ := hmap.symm

theorem dyadicRegularizedFamily_resolvent (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) :
    dyadicRegularizedFamily ε -
        triadicDampingRatio ε •
          dyadicQuotientDilation 3 (by norm_num) (dyadicRegularizedFamily ε) =
      dyadicRegularizationNormalization ε • dyadicRegularizedColumn ε 0 := by
  let L : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
    triadicDampingRatio ε • dyadicQuotientDilation 3 (by norm_num)
  have hc := dyadicRegularizedColumn_summable ε hs
  have hmap := L.map_tsum hc
  have hrec : L (∑' j : ℕ, dyadicRegularizedColumn ε j) =
      ∑' j : ℕ, dyadicRegularizedColumn ε (j+1) := by
    rw [hmap]
    exact tsum_congr (fun j => (dyadicRegularizedColumn_succ ε hs j).symm)
  have hhead := hc.tsum_eq_zero_add
  rw [dyadicRegularizedFamily_eq_columns ε hs, map_smul]
  change dyadicRegularizationNormalization ε • (∑' j, dyadicRegularizedColumn ε j) -
    triadicDampingRatio ε • (dyadicRegularizationNormalization ε •
      dyadicQuotientDilation 3 (by norm_num) (∑' j, dyadicRegularizedColumn ε j)) = _
  rw [smul_comm (triadicDampingRatio ε) (dyadicRegularizationNormalization ε)]
  change dyadicRegularizationNormalization ε • (∑' j, dyadicRegularizedColumn ε j) -
    dyadicRegularizationNormalization ε • L (∑' j, dyadicRegularizedColumn ε j) = _
  rw [hrec, ← smul_sub, hhead]
  congr 1
  abel
end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Exact finite resolvent with its full terminal term, for each Mobius index. -/
theorem dyadicRegularizedTerm_finite_resolvent (ε : ℝ) (m J : ℕ) :
    (∑ j ∈ Finset.range J, dyadicRegularizedTerm ε (m,j)) -
      triadicDampingRatio ε • dyadicQuotientDilation 3 (by norm_num)
        (∑ j ∈ Finset.range J, dyadicRegularizedTerm ε (m,j)) =
    dyadicRegularizedTerm ε (m,0) - dyadicRegularizedTerm ε (m,J) := by
  induction J with
  | zero => simp only [Finset.sum_range_zero, map_zero, smul_zero, sub_self]
  | succ J ih =>
    simp only [Finset.sum_range_succ, map_add, smul_add]
    calc
      _ = ((∑ j ∈ Finset.range J, dyadicRegularizedTerm ε (m,j)) -
          triadicDampingRatio ε • dyadicQuotientDilation 3 (by norm_num)
            (∑ j ∈ Finset.range J, dyadicRegularizedTerm ε (m,j))) +
          (dyadicRegularizedTerm ε (m,J) -
            triadicDampingRatio ε • dyadicQuotientDilation 3 (by norm_num)
              (dyadicRegularizedTerm ε (m,J))) := by abel
      _ = _ := by rw [ih, ← dyadicRegularizedTerm_succ]; abel

/-- Every finite raw arithmetic rectangle retains the last triadic column.
No convergence or damping restriction is needed. -/
theorem dyadicRegularizedRectangle_resolvent (ε : ℝ) (M J : ℕ) :
    dyadicRegularizedRectangle ε M J -
      triadicDampingRatio ε • dyadicQuotientDilation 3 (by norm_num)
        (dyadicRegularizedRectangle ε M J) =
    dyadicRegularizationNormalization ε •
      ∑ m ∈ Finset.range M,
        (dyadicRegularizedTerm ε (m,0) - dyadicRegularizedTerm ε (m,J)) := by
  rw [dyadicRegularizedRectangle_eq_sum, map_smul,
    smul_comm (triadicDampingRatio ε) (dyadicRegularizationNormalization ε),
    ← smul_sub, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun m hm => dyadicRegularizedTerm_finite_resolvent ε m J)

/-- The actual arithmetic columns are the damped orbit of their genuine head. -/
theorem dyadicRegularizedColumn_eq_orbit (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) (j : ℕ) :
    dyadicRegularizedColumn ε j =
      triadicDampingRatio ε ^ j •
        RiemannResearch.Analysis.AbelCoboundary.orbit
          (dyadicQuotientDilation 3 (by norm_num)) (dyadicRegularizedColumn ε 0) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [dyadicRegularizedColumn_succ ε hs j, ih, map_smul, smul_smul,
      RiemannResearch.Analysis.AbelCoboundary.orbit_succ, pow_succ']
end
end RiemannResearch.RH.Pareto
