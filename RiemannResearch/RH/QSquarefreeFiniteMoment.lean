import RiemannResearch.RH.QSquarefreeSmoothedProjection
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Finite conductor stages and physical cutoffs are independent. For each fixed
physical head, cofinally many conductor stages must satisfy the same bound. -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteMoment
open ZetaTwoHilbert QSquarefreeSmoothedProjection

/-- The first `K` physical summands, including the harmless site zero. -/
def momentHead (w : ℕ → ℝ) (u : QHilbert) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, w n * |qSequence u n|

theorem momentHead_tendsto {v : ℕ → QHilbert} {u : QHilbert}
    (h : Tendsto v atTop (𝓝 u)) (w : ℕ → ℝ) (K : ℕ) :
    Tendsto (fun N => momentHead w (v N) K) atTop (𝓝 (momentHead w u K)) := by
  induction K with
  | zero => simpa [momentHead] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ K ih =>
    simpa only [momentHead, Finset.sum_range_succ] using
      ih.add ((qSequence_tendsto_of_tendsto h K).abs.const_mul (w K))

theorem momentHead_mono (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (u : QHilbert) :
    Monotone (momentHead w u) := by
  intro k l hkl
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
    (fun n _ _ => mul_nonneg (hw n) (abs_nonneg _))

/-- The conductor subsequence may depend on the physical head; only `C` is uniform. -/
theorem weighted_moment_of_cofinal_heads {v : ℕ → QHilbert} {u : QHilbert}
    (hv : Tendsto v atTop (𝓝 u)) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (C : ℝ)
    (hC : ∀ K, ∃ᶠ N in atTop, momentHead w (v N) K ≤ C) :
    Summable (fun n => w n * |qSequence u n|) ∧ (∑' n, w n * |qSequence u n|) ≤ C := by
  have hhead (K : ℕ) : momentHead w u K ≤ C := by
    by_contra h
    have hg := (momentHead_tendsto hv w K).eventually (Ioi_mem_nhds (lt_of_not_ge h))
    obtain ⟨N, hN, hgt⟩ := ((hC K).and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt
  have hnonneg (n : ℕ) : 0 ≤ w n * |qSequence u n| := mul_nonneg (hw n) (abs_nonneg _)
  exact ⟨summable_of_sum_range_le hnonneg hhead, Real.tsum_le_of_sum_range_le hnonneg hhead⟩

/-- For the actual first correction, this finite test is exactly summability.
The converse uses one unit of slack so no uniformity of convergence in `K` is needed. -/
theorem correction_moment_iff_cofinal_moving_heads (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    Summable (fun n => w n * |qSequence correction n|) ↔
      ∃ C : ℝ, ∀ K, ∃ᶠ N in atTop, momentHead w (movingCorrection N) K ≤ C := by
  constructor
  · intro hs
    let S := ∑' n, w n * |qSequence correction n|
    refine ⟨S + 1, fun K => ?_⟩
    have hK : momentHead w correction K ≤ S :=
      hs.sum_le_tsum (Finset.range K) (fun n _ => mul_nonneg (hw n) (abs_nonneg _))
    have hlt : momentHead w correction K < S + 1 := lt_of_le_of_lt hK (by linarith)
    have hg := (momentHead_tendsto movingCorrection_tendsto w K).eventually (Iio_mem_nhds hlt)
    exact hg.frequently.mono (fun _ h => le_of_lt h)
  · rintro ⟨C, hC⟩
    exact (weighted_moment_of_cofinal_heads movingCorrection_tendsto w hw C hC).1

/-- One unbounded physical cutoff along good stages suffices; for example take `J N = N`.
Strong convergence in Hilbert norm alone supplies no such bound. -/
theorem correction_moment_of_cofinal_diagonal (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (C : ℝ)
    (J : ℕ → ℕ) (hJ : Tendsto J atTop atTop)
    (hC : ∃ᶠ N in atTop, momentHead w (movingCorrection N) (J N) ≤ C) :
    Summable (fun n => w n * |qSequence correction n|) ∧
      (∑' n, w n * |qSequence correction n|) ≤ C := by
  apply weighted_moment_of_cofinal_heads movingCorrection_tendsto w hw C
  intro K
  exact (hC.and_eventually (hJ.eventually (eventually_ge_atTop K))).mono
    (fun N h => (momentHead_mono w hw (movingCorrection N) h.2).trans h.1)

end RiemannResearch.RH.QSquarefreeFiniteMoment
