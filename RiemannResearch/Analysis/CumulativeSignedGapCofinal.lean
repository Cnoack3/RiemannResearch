/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CumulativeSignedGap

/-!
# Cofinal bounded-prefix absorption and direct frequent cancellation

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


These consumers retain the complete signed head and tail sums.  A bounded
negative prefix is absorbed into the terminal denominator.  The second
consumer needs arbitrarily small normalized budgets on unbounded indices,
without choosing or controlling a subsequence in advance.
The arithmetic signed-budget providers are hypotheses, not asserted results.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.HeadTailStrengthening

theorem limit_eq_zero_of_cofinal_signed_prefix_floor
    (D H L a Z : ℕ → ℝ) (k : ℕ → ℕ) (delta C : ℝ)
    (hdelta : 0 ≤ delta) (hD : Tendsto D atTop (𝓝 delta))
    (hk : Tendsto k atTop atTop) (hmono : Antitone D)
    (hid : ∀ n, D n = H n + L n) (hC : 0 ≤ C)
    (hfloor : ∀ i, -C ≤ signedGapPrefix a (i+1))
    (hpos : ∀ᶠ n in atTop, 0 < signedGapPrefix a (k n) + C)
    (hbudget : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range (k n), (L i - (1-a i)*D i)) ≤ Z (k n))
    (hsmall : Tendsto (fun n =>
      ((∑ i ∈ Finset.range (k n), H i) + Z (k n) + C*D 0) /
        (signedGapPrefix a (k n) + C)) atTop (𝓝 0)) : delta = 0 := by
  have hb : ∀ᶠ n in atTop, D (k n) ≤
      ((∑ i ∈ Finset.range (k n), H i) + Z (k n) + C*D 0) /
        (signedGapPrefix a (k n) + C) := by
    filter_upwards [hpos, hbudget] with n hn hb
    exact signed_prefix_gap_floor_bound D H L a (Z (k n)) C (k n)
      hmono hid hC (fun i _ => hfloor i) hn hb
  exact le_antisymm (le_of_tendsto_of_tendsto (hD.comp hk) hsmall hb) hdelta

/-- Direct frequent smallness is enough; the good stages may depend on the
requested precision. Negative prefixes are charged by their exact energy
variation, rather than by the total variation of the signed increments. -/
theorem limit_eq_zero_of_frequently_small_signed_prefix_variation
    (D H L a Z : ℕ → ℝ) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hD : Tendsto D atTop (𝓝 delta))
    (hmono : Antitone D) (hid : ∀ n, D n = H n + L n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop,
      0 < signedGapPrefix a n ∧
      (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) ≤ Z n ∧
      ((∑ i ∈ Finset.range n, H i) + Z n +
        negativePrefixVariationPenalty a D n) / signedGapPrefix a n ≤ ε) :
    delta = 0 := by
  by_contra hne
  have hd : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hne)
  have hh : delta / 2 < delta := by linarith
  have hevent : ∀ᶠ n in atTop, delta / 2 < D n :=
    hD.eventually (Ioi_mem_nhds hh)
  obtain ⟨n, ⟨hn, hbn, hqn⟩, hdn⟩ :=
    ((hsmall (delta / 2) (by linarith)).and_eventually hevent).exists
  have hbound := signed_prefix_gap_variation_bound D H L a (Z n) n
    hmono hid hn hbn
  exact (not_lt_of_ge (hbound.trans hqn)) hdn

end RiemannResearch.Analysis.HeadTailStrengthening
