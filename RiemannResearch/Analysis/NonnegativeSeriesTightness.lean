import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Finset.Lattice.Fold
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


/-- Strengthened full criterion, with arbitrary coordinate index type and only
eventual row hypotheses. Vanishing of the complete nonnegative sum itself
forces each coordinate to vanish. -/
theorem nonnegative_tsum_tendsto_zero_iff_coordinates_and_tail_tight
    {α ι : Type*} {l : Filter α} {f : α → ι → ℝ}
    (hpos : ∀ᶠ a in l, ∀ i, 0 ≤ f a i)
    (hsum : ∀ᶠ a in l, Summable (f a)) :
    Tendsto (fun a => ∑' i, f a i) l (nhds 0) ↔
      (∀ i, Tendsto (fun a => f a i) l (nhds 0)) ∧
        NonnegativeSeriesTailTightAt f l := by
  classical
  constructor
  · intro h
    have hcoord (i : ι) : Tendsto (fun a => f a i) l (nhds 0) := by
      apply squeeze_zero' (hpos.mono (fun a ha => ha i)) _ h
      filter_upwards [hpos, hsum] with a ha hs
      simpa only [Finset.sum_singleton] using
        hs.sum_le_tsum ({i} : Finset ι) (fun j hj => ha j)
    exact ⟨hcoord, (nonnegative_tsum_tendsto_zero_iff_tail_tight hpos hsum hcoord).mp h⟩
  · rintro ⟨hcoord, htight⟩
    exact (nonnegative_tsum_tendsto_zero_iff_tail_tight hpos hsum hcoord).mpr htight

namespace NonnegativeSeriesTightness

/-- Natural-prefix version of the existing arbitrary finite-complement notion. -/
def UniformTails {α : Type*} (a : α → ℕ → ℝ) (l : Filter α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ i in l, (∑' n, a i (n + N)) < ε

/-- Natural prefixes are cofinal among finite coordinate sets. Thus both
complete-tail notions agree under the same eventual row hypotheses. -/
theorem uniformTails_iff_finiteTails {α : Type*} {l : Filter α}
    (a : α → ℕ → ℝ) (hpos : ∀ᶠ i in l, ∀ n, 0 ≤ a i n)
    (hsum : ∀ᶠ i in l, Summable (a i)) :
    UniformTails a l ↔ NonnegativeSeriesTailTightAt a l := by
  classical
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨Finset.range N, ?_⟩
    filter_upwards [hN, hsum] with i hi hs
    have hnat := hs.sum_add_tsum_nat_add N
    have hfin := hs.sum_add_tsum_subtype_compl (Finset.range N)
    linarith
  · intro h ε hε
    obtain ⟨s, hs⟩ := h ε hε
    let N : ℕ := s.sup id + 1
    have hsub : s ⊆ Finset.range N := by
      intro n hn
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
    refine ⟨N, ?_⟩
    filter_upwards [hs, hpos, hsum] with i hi hp hsum
    have hhead : (∑ n ∈ s, a i n) ≤ ∑ n ∈ Finset.range N, a i n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => hp n)
    have hnat := hsum.sum_add_tsum_nat_add N
    have hfin := hsum.sum_add_tsum_subtype_compl s
    linarith

/-- Natural-prefix specialization of the stronger existing-owner criterion. -/
theorem tsum_tendsto_zero_iff_eventually {α : Type*} {l : Filter α}
    (a : α → ℕ → ℝ) (ha : ∀ᶠ i in l, ∀ n, 0 ≤ a i n)
    (hs : ∀ᶠ i in l, Summable (a i)) :
    Tendsto (fun i => ∑' n, a i n) l (nhds 0) ↔
      (∀ n, Tendsto (fun i => a i n) l (nhds 0)) ∧ UniformTails a l :=
  (nonnegative_tsum_tendsto_zero_iff_coordinates_and_tail_tight ha hs).trans
    (and_congr Iff.rfl (uniformTails_iff_finiteTails a ha hs).symm)

/-- Convenient globally summable-row specialization for Hilbert consumers. -/
theorem tsum_tendsto_zero_iff {α : Type*} {l : Filter α}
    (a : α → ℕ → ℝ) (ha : ∀ i n, 0 ≤ a i n) (hs : ∀ i, Summable (a i)) :
    Tendsto (fun i => ∑' n, a i n) l (nhds 0) ↔
      (∀ n, Tendsto (fun i => a i n) l (nhds 0)) ∧ UniformTails a l :=
  tsum_tendsto_zero_iff_eventually a (Eventually.of_forall ha) (Eventually.of_forall hs)

end NonnegativeSeriesTightness

end
end RiemannResearch.Analysis
