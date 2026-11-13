import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ResidueClosureDensity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Pareto coordinate domination and cofinal prime legality

Source: user-provided convolution-exponential argument, 13 November 2026.
These declarations give the Hilbert-space limit and closed-subspace assembly.
The application must provide the actual exponential family, its summable
majorant, and its pointwise limit. The RH implication uses the existing
first-coordinate residue criterion. No reverse RH approximation provider is
assumed silently.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Dominated convergence in the actual physical Pareto coordinates. -/
theorem tendsto_of_dominated_physical_coordinates
    (u : ℕ → ThresholdHilbert) (v : ThresholdHilbert) (M : ℕ → ℝ)
    (hM : Summable (fun n => positiveWeight n * M n ^ 2))
    (hpoint : ∀ n, Tendsto (fun k => hilbertSequence (u k) n) atTop
      (𝓝 (hilbertSequence v n)))
    (hbound : ∀ k n,
      (hilbertSequence (u k) n - hilbertSequence v n) ^ 2 ≤ M n ^ 2) :
    Tendsto u atTop (𝓝 v) := by
  have hp (n : ℕ) :
      Tendsto (fun k => positiveWeight n *
        (hilbertSequence (u k) n - hilbertSequence v n) ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using (((hpoint n).sub_const (hilbertSequence v n)).pow 2).const_mul
      (positiveWeight n)
  have hb : ∀ᶠ k : ℕ in atTop, ∀ n,
      ‖positiveWeight n *
        (hilbertSequence (u k) n - hilbertSequence v n) ^ 2‖ ≤
        positiveWeight n * M n ^ 2 := by
    apply Filter.Eventually.of_forall
    intro k n
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hbound k n) (positiveWeight_nonneg n)
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun k n => positiveWeight n *
      (hilbertSequence (u k) n - hilbertSequence v n) ^ 2)
    (g := fun _ : ℕ => (0 : ℝ)) hM hp hb
  have he (k n : ℕ) :
      hilbertSequence (u k - v) n =
        hilbertSequence (u k) n - hilbertSequence v n :=
    congrFun (hilbertSequenceLinear.map_sub (u k) v) n
  have hs : Tendsto (fun k => ‖u k - v‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hilbert_norm_weighted_sq, he, tsum_zero] using ht
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hn' : Tendsto (fun k => ‖u k - v‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero]
      using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

namespace CoefficientStabilization

/-- Legality along arbitrarily large prime conductors, for an actual Hilbert family. -/
def UnboundedPrimeLegality (E : ℕ → ThresholdHilbert) : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ E p ∈ closedSpace

/-- A cofinal legal prime subsequence transfers the actual unit limit into V. -/
theorem firstPoint_mem_of_unbounded_prime_legality
    (E : ℕ → ThresholdHilbert)
    (hlim : Tendsto E atTop (𝓝 (paretoPointHilbert 0)))
    (hlegal : UnboundedPrimeLegality E) :
    paretoPointHilbert 0 ∈ closedSpace := by
  classical
  choose p hpN hpPrime hpMem using hlegal
  have hp : Tendsto p atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hk.trans (hpN k)
  have hc : IsClosed (closedSpace : Set ThresholdHilbert) :=
    Submodule.isClosed_topologicalClosure _
  exact hc.mem_of_tendsto (hlim.comp hp) (Filter.Eventually.of_forall hpMem)

/-- Given the unit limit, unbounded prime legality is exactly full Pareto density. -/
theorem unbounded_prime_legality_iff_closedSpace_eq_top
    (E : ℕ → ThresholdHilbert)
    (hlim : Tendsto E atTop (𝓝 (paretoPointHilbert 0))) :
    UnboundedPrimeLegality E ↔ closedSpace = ⊤ := by
  constructor
  · intro hlegal
    exact closedSpace_eq_top_iff_one_mem.mpr
      (firstPoint_mem_iff_one_mem.mp
        (firstPoint_mem_of_unbounded_prime_legality E hlim hlegal))
  · intro htop N
    obtain ⟨p, hpN, hpPrime⟩ := Nat.exists_infinite_primes N
    refine ⟨p, hpN, hpPrime, ?_⟩
    rw [htop]
    trivial

/-- The unit-limit criterion consumes actual prime legality as its open hypothesis. -/
theorem riemannHypothesis_of_unbounded_prime_legality
    (E : ℕ → ThresholdHilbert)
    (hlim : Tendsto E atTop (𝓝 (paretoPointHilbert 0)))
    (hlegal : UnboundedPrimeLegality E) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr
      (firstPoint_mem_iff_one_mem.mp
        (firstPoint_mem_of_unbounded_prime_legality E hlim hlegal)))

end CoefficientStabilization
end RiemannResearch.RH.Pareto
