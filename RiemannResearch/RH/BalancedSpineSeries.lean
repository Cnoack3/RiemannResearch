import RiemannResearch.RH.SpineSeriesObstruction
import RiemannResearch.RH.BalancedContinuousCoordinates
import RiemannResearch.RH.BalancedCoefficientTargets

/-!
# Actual balanced dictionary spine and its series obstruction

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 4. The spine consists of the actual indices with rough part one and
equal positive exponents. A coefficient table will identify their targets.
-/

namespace RiemannResearch.RH.Pareto
open Filter
open scoped Topology BigOperators
noncomputable section

def balancedSpineIndex (k : ℕ) : BalancedArithmeticIndex :=
  ⟨1, k+1, k+1, by norm_num [IsTwoThreeRough]⟩

theorem balancedSpineIndex_injective : Function.Injective balancedSpineIndex := by
  intro k l h
  have he := congrArg BalancedArithmeticIndex.a h
  change k+1 = l+1 at he
  omega

theorem balancedSpineIndex_generator (k : ℕ) :
    balancedIndexHilbert (balancedSpineIndex k) =
      hilbertDilation (6^(k+1)) (pow_pos (by norm_num) _)
        (digitHilbert 2 1 (by norm_num) (by norm_num)) := by
  apply hilbertSequence_injective
  rw [hilbertSequence_balancedIndex, hilbertDilation_sequence,
    hilbertSequence_digitHilbert, balancedResidueEdge_eq]
  have hp : 2^(k+1)*3^(k+1)*1 = (6:ℕ)^(k+1) := by
    rw [mul_one, ← mul_pow]
    norm_num
  simp only [balancedSpineIndex, le_refl, if_true, hp]
  congr 1
  funext n
  simp [digitSequence, residue]

/-- Once the exact finite Möbius table is supplied, the resulting fixed
coefficient series diverges in every enumeration of the actual dictionary. -/
theorem balancedTarget_no_series_in_any_order_of_spine
    (hcoeff : ∀ k, balancedCoefficientTarget (balancedSpineIndex k) = 1/3)
    (e : ℕ ≃ BalancedArithmeticIndex) (limit : ThresholdHilbert) :
    ¬ Tendsto (fun N => ∑ n ∈ Finset.range N,
      balancedCoefficientTarget (e n) • balancedIndexHilbert (e n))
        atTop (𝓝 limit) := by
  apply indexedSpineDictionary_no_series_in_any_order
    (fun i => balancedCoefficientTarget i • balancedIndexHilbert i)
    balancedSpineIndex balancedSpineIndex_injective _ dyadicResidue_nonzero
  intro k
  rw [hcoeff, balancedSpineIndex_generator]
  rfl

theorem balancedSpineIndex_target (k : ℕ) :
    balancedCoefficientTarget (balancedSpineIndex k) = 1/3 := by
  change RiemannResearch.RH.FiniteSeedComponentCharge.componentSignal
    (balancedArithmeticCut 1 (k+1) (k+1)) = 1/3
  rw [balancedCut_signal_diagonal 1 k (by norm_num [IsTwoThreeRough])]
  norm_num

/-- The actual forced coefficient series cannot converge in any enumeration.
There are no coefficient-provider hypotheses in this final statement. -/
theorem balancedTarget_no_series_in_any_order
    (e : ℕ ≃ BalancedArithmeticIndex) (limit : ThresholdHilbert) :
    ¬ Tendsto (fun N => ∑ n ∈ Finset.range N,
      balancedCoefficientTarget (e n) • balancedIndexHilbert (e n))
        atTop (𝓝 limit) :=
  balancedTarget_no_series_in_any_order_of_spine balancedSpineIndex_target e limit

/-- Continuity of the individual coordinates forces every coefficient of
any alleged series representation of one, even for ordinary ordered sums. -/
theorem balancedSeries_coefficients_forced
    (c : BalancedArithmeticIndex → ℝ) (e : ℕ ≃ BalancedArithmeticIndex)
    (hconv : Tendsto (fun N => ∑ n ∈ Finset.range N,
      c (e n) • balancedIndexHilbert (e n)) atTop (𝓝 hilbertOne))
    (i : BalancedArithmeticIndex) : c i = balancedCoefficientTarget i := by
  classical
  have heval : ∀ N, e.symm i < N →
      balancedCoefficientCLM i (∑ n ∈ Finset.range N,
        c (e n) • balancedIndexHilbert (e n)) = c i := by
    intro N hN
    rw [map_sum]
    rw [Finset.sum_eq_single (e.symm i)]
    · simp only [Equiv.apply_symm_apply, map_smul,
        balancedCoefficientCLM_biorthogonal, if_true, smul_eq_mul, mul_one]
    · intro n hn hne
      have hi : i ≠ e n := by
        intro he
        have hh := congrArg e.symm he
        simp only [Equiv.symm_apply_apply] at hh
        exact hne hh.symm
      simp only [map_smul, balancedCoefficientCLM_biorthogonal,
        if_neg hi, smul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hN))
  have hlim : Tendsto (fun N => balancedCoefficientCLM i
      (∑ n ∈ Finset.range N, c (e n) • balancedIndexHilbert (e n)))
        atTop (𝓝 (balancedCoefficientTarget i)) := by
    rw [← balancedCoefficientCLM_one i]
    exact (balancedCoefficientCLM i).continuous.tendsto _ |>.comp hconv
  have hconst : Tendsto (fun N => balancedCoefficientCLM i
      (∑ n ∈ Finset.range N, c (e n) • balancedIndexHilbert (e n)))
        atTop (𝓝 (c i)) := by
    apply tendsto_const_nhds.congr'
    apply eventually_atTop.2
    refine ⟨e.symm i + 1, ?_⟩
    intro N hN
    exact (heval N (by omega)).symm
  exact tendsto_nhds_unique hconst hlim

/-- No ordering of the actual balanced algebraic dictionary gives a series
representation of one, with any choice of fixed coefficients. -/
theorem balancedDictionary_no_series_representation_one
    (c : BalancedArithmeticIndex → ℝ) (e : ℕ ≃ BalancedArithmeticIndex) :
    ¬ Tendsto (fun N => ∑ n ∈ Finset.range N,
      c (e n) • balancedIndexHilbert (e n)) atTop (𝓝 hilbertOne) := by
  intro hconv
  have hc : c = balancedCoefficientTarget :=
    funext (balancedSeries_coefficients_forced c e hconv)
  rw [hc] at hconv
  exact balancedTarget_no_series_in_any_order e hilbertOne hconv

end
end RiemannResearch.RH.Pareto
