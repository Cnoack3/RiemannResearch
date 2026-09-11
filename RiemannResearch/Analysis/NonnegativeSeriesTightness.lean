import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic.Linarith

/-!
# Nonnegative series: coordinate convergence and escaping tail energy

Source: independently developed standard finite-head/tail argument, motivated
by the user's FourierSignedBridgeVerification20260911(2).md. This does not
claim a new abstract convergence theorem. Its RH consumer keeps the complete
signed Fourier sum inside each nonnegative boundary-coordinate energy.
-/

namespace RiemannResearch.Analysis

open Filter
open scoped BigOperators
noncomputable section

/-- Arbitrarily small complete tails after a fixed finite cutoff, eventually
along the parameter filter. The cutoff may depend on the tolerance, but must
be chosen before the parameter tends to its limit. -/
def NonnegativeSeriesTailTightAt {α ι : Type*}
    (f : α → ι → ℝ) (l : Filter α) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ s : Finset ι,
    ∀ᶠ a in l, (∑' i : {i : ι // i ∉ s}, f a i) < η

/-- Pointwise convergence gives convergence of each fixed finite head. -/
theorem finite_sum_tendsto_zero_of_coordinate_tendsto
    {α ι : Type*} {l : Filter α} {f : α → ι → ℝ}
    (hcoord : ∀ i, Tendsto (fun a => f a i) l (nhds 0)) (s : Finset ι) :
    Tendsto (fun a => ∑ i ∈ s, f a i) l (nhds 0) := by
  simpa using tendsto_finsetSum s (fun i _ => hcoord i)

/-- In a nonnegative summable row, the entire complementary tail is bounded
by the complete sum, without replacing that tail by a partial sum. -/
theorem complementary_tsum_le_tsum_of_nonnegative
    {ι : Type*} {f : ι → ℝ} (hpos : ∀ i, 0 ≤ f i)
    (hsum : Summable f) (s : Finset ι) :
    (∑' i : {i : ι // i ∉ s}, f i) ≤ ∑' i, f i := by
  have hsplit := hsum.sum_add_tsum_subtype_compl s
  have hhead : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg (fun i _ => hpos i)
  linarith

/-- Exact zero-limit criterion. Coordinate convergence alone leaves precisely
the asymptotic tail-tightness obligation. -/
theorem nonnegative_tsum_tendsto_zero_iff_tail_tight
    {α ι : Type*} {l : Filter α} {f : α → ι → ℝ}
    (hpos : ∀ᶠ a in l, ∀ i, 0 ≤ f a i)
    (hsum : ∀ᶠ a in l, Summable (f a))
    (hcoord : ∀ i, Tendsto (fun a => f a i) l (nhds 0)) :
    Tendsto (fun a => ∑' i, f a i) l (nhds 0) ↔
      NonnegativeSeriesTailTightAt f l := by
  constructor
  · intro h η hη
    refine ⟨∅, ?_⟩
    filter_upwards [h.eventually_lt_const hη, hpos, hsum] with a ha hp hs
    exact (complementary_tsum_le_tsum_of_nonnegative
      hp hs ∅).trans_lt ha
  · intro htight
    apply tendsto_order.2
    constructor
    · intro b hb
      filter_upwards [hpos] with a hp
      exact hb.trans_le (tsum_nonneg hp)
    · intro η hη
      obtain ⟨s, hs⟩ := htight (η / 2) (by linarith)
      have hhead := finite_sum_tendsto_zero_of_coordinate_tendsto hcoord s
      filter_upwards [hs, hhead.eventually_lt_const (show (0 : ℝ) < η / 2 by linarith),
        hsum] with a htail hhead hsum
      have hsplit := hsum.sum_add_tsum_subtype_compl s
      linarith

/-- If the total energy stays above `c > 0` while each coordinate vanishes,
at least `c / 2` eventually lies outside every fixed finite boundary set. -/
theorem complementary_tsum_eventually_ge_of_total_lower
    {α ι : Type*} {l : Filter α} {f : α → ι → ℝ}
    (hsum : ∀ᶠ a in l, Summable (f a))
    (hcoord : ∀ i, Tendsto (fun a => f a i) l (nhds 0))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ a in l, c ≤ ∑' i, f a i) (s : Finset ι) :
    ∀ᶠ a in l, c / 2 ≤ ∑' i : {i : ι // i ∉ s}, f a i := by
  have hhead := finite_sum_tendsto_zero_of_coordinate_tendsto hcoord s
  filter_upwards [hlower,
    hhead.eventually_lt_const (show (0 : ℝ) < c / 2 by linarith), hsum]
    with a ha hhead hsum
  have hsplit := hsum.sum_add_tsum_subtype_compl s
  linarith

end
end RiemannResearch.Analysis
