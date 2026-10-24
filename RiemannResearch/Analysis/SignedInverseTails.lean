import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordered signed inverse limits and exact asymptotic tail criteria

Source: independently developed finite-head argument. The limit series is
only required to converge in its natural order; absolute summability and
interchange of infinite sums are not assumed. The cutoff is fixed before
passing to the parameter limit. Absolute values are taken after each entire
signed tail sum, so every cancellation remains present.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.SignedInverseTails

variable {α : Type*} {l : Filter α}

/-- Complete signed tails at every sufficiently late fixed cutoff. The order
of the quantifiers is deliberate; the eventual stage can depend on the cutoff. -/
def AsymptoticTails (A : α → ℝ) (f : α → ℕ → ℝ) (l : Filter α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ K : ℕ, J ≤ K →
    ∀ᶠ i in l, ‖A i - ∑ j ∈ Finset.range K, f i j‖ < ε

/-- Coordinate limits and a conditionally convergent ordered limit series
leave exactly this signed-tail obstruction, with both directions proved. -/
theorem tendsto_iff_asymptoticTails (A : α → ℝ) (f : α → ℕ → ℝ)
    (g : ℕ → ℝ) (L : ℝ)
    (hcoord : ∀ j, Tendsto (fun i => f i j) l (𝓝 (g j)))
    (hseries : Tendsto (fun K => ∑ j ∈ Finset.range K, g j) atTop (𝓝 L)) :
    Tendsto A l (𝓝 L) ↔ AsymptoticTails A f l := by
  have hhead (K : ℕ) : Tendsto (fun i => ∑ j ∈ Finset.range K, f i j) l
      (𝓝 (∑ j ∈ Finset.range K, g j)) :=
    tendsto_finsetSum _ (fun j _ => hcoord j)
  have hnorm : Tendsto (fun K => ‖(∑ j ∈ Finset.range K, g j) - L‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hseries
  constructor
  · intro hA ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.1
      (hnorm.eventually_lt_const (show (0 : ℝ) < ε by exact hε))
    refine ⟨J, ?_⟩
    intro K hK
    have ht := (hA.sub (hhead K)).norm
    have hb : ‖L - ∑ j ∈ Finset.range K, g j‖ < ε := by
      rw [norm_sub_rev]
      exact hJ K hK
    exact ht.eventually_lt_const hb
  · intro ht
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply tendsto_order.2
    constructor
    · intro b hb
      exact Eventually.of_forall (fun i => hb.trans_le (norm_nonneg _))
    · intro ε hε
      have he : 0 < ε / 3 := by linarith
      obtain ⟨J, hJ⟩ := ht (ε / 3) he
      obtain ⟨J', hJ'⟩ := eventually_atTop.1 (hnorm.eventually_lt_const he)
      let K := max J J'
      have hG : ‖(∑ j ∈ Finset.range K, g j) - L‖ < ε / 3 :=
        hJ' K (le_max_right _ _)
      have hH := (tendsto_iff_norm_sub_tendsto_zero.mp (hhead K)).eventually_lt_const he
      filter_upwards [hJ K (le_max_left _ _), hH] with i hi hhead
      have hid : A i - L =
          (A i - ∑ j ∈ Finset.range K, f i j) +
          ((∑ j ∈ Finset.range K, f i j) - ∑ j ∈ Finset.range K, g j) +
          ((∑ j ∈ Finset.range K, g j) - L) := by ring
      rw [hid]
      have hfirst :
          ‖(A i - ∑ j ∈ Finset.range K, f i j) +
            ((∑ j ∈ Finset.range K, f i j) - ∑ j ∈ Finset.range K, g j)‖ ≤
          ‖A i - ∑ j ∈ Finset.range K, f i j‖ +
            ‖(∑ j ∈ Finset.range K, f i j) - ∑ j ∈ Finset.range K, g j‖ :=
        norm_add_le _ _
      have hsecond :
          ‖(A i - ∑ j ∈ Finset.range K, f i j) +
            ((∑ j ∈ Finset.range K, f i j) - ∑ j ∈ Finset.range K, g j) +
            ((∑ j ∈ Finset.range K, g j) - L)‖ ≤
          ‖(A i - ∑ j ∈ Finset.range K, f i j) +
            ((∑ j ∈ Finset.range K, f i j) - ∑ j ∈ Finset.range K, g j)‖ +
            ‖(∑ j ∈ Finset.range K, g j) - L‖ :=
        norm_add_le _ _
      linarith

end RiemannResearch.Analysis.SignedInverseTails
