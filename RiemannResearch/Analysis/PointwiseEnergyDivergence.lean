import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Basic

/-!
# Divergence of nonnegative energies under pointwise convergence

Source: the finite-sum proof of Fatou's inequality, used in the September 14,
2026 arithmetic component analysis. No arithmetic hypotheses occur here.
-/
namespace RiemannResearch.Analysis
open scoped BigOperators Topology
open Filter
noncomputable section

/-- Discrete Fatou consequence stated as divergence of the whole energy.
The proof retains all finite coordinates before comparing with the full sum. -/
theorem total_nonnegative_energy_tendsto_atTop
    (E : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (hE : ∀ j n, 0 ≤ E j n) (he : ∀ n, 0 ≤ e n)
    (hs : ∀ j, Summable (E j))
    (hp : ∀ n, Tendsto (fun j => E j n) atTop (𝓝 (e n)))
    (hn : ¬ Summable e) :
    Tendsto (fun j => ∑' n : ℕ, E j n) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro C
  have hex : ∃ s : Finset ℕ, C < ∑ n ∈ s, e n := by
    by_contra! hb
    exact hn (summable_of_sum_le he hb)
  obtain ⟨s, hsC⟩ := hex
  have ht : Tendsto (fun j => ∑ n ∈ s, E j n) atTop (𝓝 (∑ n ∈ s, e n)) := by
    apply tendsto_finsetSum
    intro n _
    exact hp n
  have hlarge : ∀ᶠ j in atTop, C < ∑ n ∈ s, E j n :=
    (tendsto_order.1 ht).1 C hsC
  filter_upwards [hlarge] with j hj
  exact hj.le.trans ((hs j).sum_le_tsum s (fun n _ => hE j n))

/-- Filter version of `total_nonnegative_energy_tendsto_atTop`. Eventual
nonnegativity and summability are sufficient. The parameter need not be
discrete; the summation index is arbitrary. -/
theorem total_nonnegative_energy_tendsto_atTop_filter
    {ι κ : Type*} (F : Filter κ) (E : κ → ι → ℝ) (e : ι → ℝ)
    (hE : ∀ᶠ j in F, ∀ n, 0 ≤ E j n) (he : ∀ n, 0 ≤ e n)
    (hs : ∀ᶠ j in F, Summable (E j))
    (hp : ∀ n, Tendsto (fun j => E j n) F (𝓝 (e n)))
    (hn : ¬ Summable e) :
    Tendsto (fun j => ∑' n, E j n) F atTop := by
  classical
  apply tendsto_atTop.2
  intro C
  have hex : ∃ s : Finset ι, C < ∑ n ∈ s, e n := by
    by_contra! hb
    exact hn (summable_of_sum_le he hb)
  obtain ⟨s, hsC⟩ := hex
  have ht : Tendsto (fun j => ∑ n ∈ s, E j n) F (𝓝 (∑ n ∈ s, e n)) := by
    apply tendsto_finsetSum
    intro n _
    exact hp n
  have hlarge : ∀ᶠ j in F, C < ∑ n ∈ s, E j n :=
    (tendsto_order.1 ht).1 C hsC
  filter_upwards [hlarge, hE, hs] with j hj hEj hsj
  exact hj.le.trans (hsj.sum_le_tsum s (fun n _ => hEj n))

/-- Source: the user-provided squarefree moving-head continuation.
Fixed finite-prefix convergence transfers cofinal growing-head bounds. -/
theorem fixed_prefix_le_of_frequently_head_bound
    (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ j n, 0 ≤ f j n)
    (hlim : ∀ n, Tendsto (fun j => f j n) atTop (𝓝 (g n)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hbound : ∃ᶠ j : ℕ in atTop,
      (∑ n ∈ Finset.range (H j), f j n) ≤ C)
    (M : ℕ) : (∑ n ∈ Finset.range M, g n) ≤ C := by
  have hfinite (L : ℕ) : Tendsto
      (fun j => ∑ n ∈ Finset.range L, f j n) atTop
      (𝓝 (∑ n ∈ Finset.range L, g n)) := by
    induction L with
    | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | succ L ih =>
        simpa only [Finset.sum_range_succ] using ih.add (hlim L)
  by_contra hbad
  have hgt := (hfinite M).eventually (Ioi_mem_nhds (lt_of_not_ge hbad))
  have hlarge := hH.eventually (eventually_ge_atTop M)
  obtain ⟨j, hj⟩ := ((hbound.and_eventually hlarge).and_eventually hgt).exists
  rcases hj with ⟨⟨hb, hM⟩, hstrict⟩
  have hmono : (∑ n ∈ Finset.range M, f j n) ≤
      ∑ n ∈ Finset.range (H j), f j n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
      (fun n _ _ => hf j n)
  exact (not_lt_of_ge (hmono.trans hb)) hstrict

/-- A frequent uniform bound on expanding finite heads suffices for full
summability of the pointwise limit, with the same total-energy bound. -/
theorem summable_of_frequently_head_bound
    (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ j n, 0 ≤ f j n)
    (hlim : ∀ n, Tendsto (fun j => f j n) atTop (𝓝 (g n)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hbound : ∃ᶠ j : ℕ in atTop,
      (∑ n ∈ Finset.range (H j), f j n) ≤ C) :
    Summable g ∧ (∑' n : ℕ, g n) ≤ C := by
  have hg : ∀ n, 0 ≤ g n := by
    intro n
    exact ge_of_tendsto (hlim n) (Eventually.of_forall (fun j => hf j n))
  have hprefix := fixed_prefix_le_of_frequently_head_bound f g hf hlim H hH C hbound
  exact ⟨summable_of_sum_range_le hg hprefix, Real.tsum_le_of_sum_range_le hg hprefix⟩


end
end RiemannResearch.Analysis
