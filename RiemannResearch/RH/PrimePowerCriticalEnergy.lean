import RiemannResearch.Analysis.ReciprocalCellEnergy
import RiemannResearch.Analysis.CumulativeEnergySummability
import RiemannResearch.Analysis.GapEnergySummability
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Actual von Mangoldt critical interval energy and finite reset corrections

Source: user-provided continuation, Sections 12, 14, and 15.
The sequence q is increasing and positive; actualJump uses Mathlib's actual
von Mangoldt function. CompleteThrough records exactly the support-completeness
input needed for the finite Chebyshev identification. No particular global
prime-power enumeration is silently chosen. The integral identities cover
[q 0, q N], not an omitted initial interval.

The weights are 1/q_i - 1/q_(i+1), NOT integer Pareto weights. All earlier-current
signed cross terms and the terminal Abel term are retained. The total reset
cost is a squared cumulative-energy norm, with zero cumulative tail.

See VectorSpacesZetaFormalization20260916.md for open analytic providers and
the unproved RH-equivalent arithmetic estimate. This module proves neither
RH nor that critical undamped arithmetic energy is uniformly bounded.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.LinearAlgebra.CumulativeCellEnergy
open RiemannResearch.Analysis.ReciprocalCellEnergy
open RiemannResearch.Analysis.NonnegativeEnergy
open RiemannResearch.Analysis.GapEnergy

namespace RiemannResearch.RH.PrimePowerCriticalEnergy

/-- Actual von Mangoldt coefficients, not free proxy coefficients. -/
def actualJump (q : ℕ → ℕ) (i : ℕ) : ℝ := ArithmeticFunction.vonMangoldt (q i)

def cellWeight (q : ℕ → ℕ) (i : ℕ) : ℝ :=
  intervalWeight (q i) (q (i + 1))

def logMoment (q : ℕ → ℕ) (i : ℕ) : ℝ := Real.log ((q (i + 1) : ℝ) / q i)

def cellLength (q : ℕ → ℕ) (i : ℕ) : ℝ := (q (i + 1) : ℝ) - q i

def referenceJump (q : ℕ → ℕ) (i : ℕ) : ℝ :=
  targetLevel (cellWeight q) (logMoment q) (i + 1) -
    targetLevel (cellWeight q) (logMoment q) i

/-- Signed arithmetic-minus-geometric charge. -/
def signedJump (q : ℕ → ℕ) (i : ℕ) : ℝ := actualJump q i - referenceJump q i

theorem cumulative_signedJump (q : ℕ → ℕ) (n : ℕ) :
    cumulative (signedJump q) n = cumulative (actualJump q) n -
      targetLevel (cellWeight q) (logMoment q) n := by
  unfold cumulative signedJump referenceJump
  rw [Finset.sum_sub_distrib, cumulative_difference]
  simp [targetLevel]

theorem cellWeight_pos (q : ℕ → ℕ) (hq : StrictMono q)
    (hpos : ∀ i, 0 < q i) (i : ℕ) : 0 < cellWeight q i := by
  apply intervalWeight_pos
  · exact_mod_cast hpos i
  · exact_mod_cast hq (Nat.lt_succ_self i)

/-- Complete support through a cutoff, needed to identify an enumeration
prefix with the actual Chebyshev sum; no completeness is silently assumed. -/
def CompleteThrough (q : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range (q n + 1), ArithmeticFunction.vonMangoldt k ≠ 0 →
    ∃ i ∈ Finset.range (n + 1), q i = k

theorem actualCumulative_eq_chebyshev (q : ℕ → ℕ) (hq : StrictMono q)
    (n : ℕ) (hcomplete : CompleteThrough q n) :
    cumulative (actualJump q) (n + 1) =
      ∑ k ∈ Finset.range (q n + 1), ArithmeticFunction.vonMangoldt k := by
  classical
  have hsubset : (Finset.range (n + 1)).image q ⊆ Finset.range (q n + 1) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (hq.monotone (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  calc
    _ = ∑ k ∈ (Finset.range (n + 1)).image q, ArithmeticFunction.vonMangoldt k := by
      rw [Finset.sum_image]
      · rfl
      · intro i hi j hj hij
        exact hq.injective hij
    _ = _ := by
      apply Finset.sum_subset hsubset
      intro k hk hnot
      by_contra hne
      obtain ⟨i, hi, he⟩ := hcomplete k hk hne
      exact hnot (Finset.mem_image.mpr ⟨i, hi, he⟩)

theorem actual_integral_energy (q : ℕ → ℕ) (hq : StrictMono q)
    (hpos : ∀ i, 0 < q i) (N : ℕ) :
    (∑ i ∈ Finset.range N,
      ∫ x in (q i : ℝ)..(q (i + 1) : ℝ),
        (cumulative (actualJump q) (i + 1) - x) ^ 2 / x ^ 2) =
      signedCellEnergy N (cellWeight q) (logMoment q) (cellLength q) (actualJump q) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_residual_square (by exact_mod_cast hpos i)
    (by exact_mod_cast hq (Nat.lt_succ_self i)) _

theorem actual_energy_split (q : ℕ → ℕ) (hq : StrictMono q)
    (hpos : ∀ i, 0 < q i) (N : ℕ) :
    signedCellEnergy N (cellWeight q) (logMoment q) (cellLength q) (actualJump q) =
      weightedPrefixEnergy (cellWeight q) (signedJump q) N +
        freeCellEnergy N (cellWeight q) (logMoment q) (cellLength q) := by
  rw [signedCellEnergy_eq_excess_add_free N _ _ _ _
    (fun i _ => ne_of_gt (cellWeight_pos q hq hpos i))]
  congr 1
  unfold weightedPrefixEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [cumulative_signedJump]
  rfl

/-- Exact signed expansion at the actual interval weights 1/q_i - 1/q_(i+1). -/
theorem actual_signed_abel_identity (q : ℕ → ℕ) (N : ℕ) :
    weightedPrefixEnergy (cellWeight q) (signedJump q) N =
      (∑ i ∈ Finset.range N, (1 / (q i : ℝ)) *
        ((signedJump q i) ^ 2 + 2 * signedJump q i * cumulative (signedJump q) i)) -
      (1 / (q N : ℝ)) * cumulative (signedJump q) N ^ 2 :=
  weightedPrefixEnergy_signed_identity (signedJump q) (fun i => 1 / (q i : ℝ)) N

theorem actual_reset_cost (q : ℕ → ℕ) (hq : StrictMono q)
    (hpos : ∀ i, 0 < q i) (N M : ℕ) (hNM : N < M) (τ : ℝ) :
    correctionEnergy M (cellWeight q)
      (resetJump (optimalJumpCorrection (cellWeight q) (logMoment q) (actualJump q)) N) τ =
        weightedPrefixEnergy (cellWeight q) (signedJump q) N := by
  rw [reset_correction_energy_exact N M _ _ (cellLength q) _ τ hNM
    (fun i _ => ne_of_gt (cellWeight_pos q hq hpos i)), actual_energy_split q hq hpos]
  ring

/-- The entire squared energy of the reset correction is exactly the signed
arithmetic discrepancy energy; no terminal or infinite-tail penalty remains. -/
theorem actual_total_reset_cost (q : ℕ → ℕ) (hq : StrictMono q)
    (hpos : ∀ i, 0 < q i) (N : ℕ) :
    totalCumulativeEnergy (cellWeight q)
      (resetJump (optimalJumpCorrection (cellWeight q) (logMoment q) (actualJump q)) N) =
        weightedPrefixEnergy (cellWeight q) (signedJump q) N := by
  rw [reset_total_correction_energy_exact N _ _ (cellLength q) _
    (fun i _ => ne_of_gt (cellWeight_pos q hq hpos i)), actual_energy_split q hq hpos]
  ring

theorem actual_interval_energy_split (q : ℕ → ℕ) (hq : StrictMono q)
    (hpos : ∀ i, 0 < q i) (N : ℕ) :
    (∑ i ∈ Finset.range N,
      ∫ x in (q i : ℝ)..(q (i + 1) : ℝ),
        (cumulative (actualJump q) (i + 1) - x) ^ 2 / x ^ 2) =
      weightedPrefixEnergy (cellWeight q) (signedJump q) N +
        ∑ i ∈ Finset.range N, intervalRemainder (q i) (q (i + 1)) := by
  rw [actual_integral_energy q hq hpos, actual_energy_split q hq hpos]
  rfl

/-- A boundedness equivalence, not a proof of the bound. In particular the
critical, undamped boundedness on the right is not an RH conclusion. -/
theorem actual_discrepancy_summable_iff_bounded_prefix (q : ℕ → ℕ)
    (hq : StrictMono q) (hpos : ∀ i, 0 < q i) :
    Summable (fun i => cellWeight q i * cumulative (signedJump q) (i + 1) ^ 2) ↔
      ∃ C : ℝ, ∀ N, weightedPrefixEnergy (cellWeight q) (signedJump q) N ≤ C := by
  exact summable_iff_nonnegative_prefix_bound _
    (fun i => mul_nonneg (cellWeight_pos q hq hpos i).le (sq_nonneg _))

/-- The arithmetic specialization of the geometric reduction. The required
cubic-gap summability is an explicit external input, not an RH-strength
estimate for the signed von Mangoldt discrepancy. -/
theorem actual_remainder_summable_of_external_cubic_gap (q : ℕ → ℕ)
    (hq : StrictMono q) (hpos : ∀ i, 0 < q i)
    (externalPrimePowerCubicGapSummability :
      Summable (fun i => cellLength q i ^ 3 / (q i : ℝ) ^ 2)) :
    Summable (fun i => intervalRemainder (q i) (q (i + 1))) := by
  apply summable_remainder_of_cubic_gap _ (cellLength q) (fun i => (q i : ℝ))
  · intro i
    exact intervalRemainder_nonneg (by exact_mod_cast hpos i)
      (by exact_mod_cast hq (Nat.lt_succ_self i))
  · intro i
    exact intervalRemainder_le_cubic (by exact_mod_cast hpos i)
      (by exact_mod_cast hq (Nat.lt_succ_self i))
  · exact externalPrimePowerCubicGapSummability

end RiemannResearch.RH.PrimePowerCriticalEnergy
