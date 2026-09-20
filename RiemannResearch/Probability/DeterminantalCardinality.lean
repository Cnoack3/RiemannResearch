import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact cardinality from a determinantal rank bound and trace

Source: Hough--Krishnapur--Peres--Virag, Determinantal Processes and
Independence, arXiv:math/0503110, for the fixed-cardinality property of finite-rank
projection DPPs. The proof below uses zero correlations of order N+1, a
countable union of null events, and Tonelli's theorem for the expected count.
It requires no spatial monotone coupling.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace RiemannResearch.Probability.DPP

/-- The extended number of elements of a subset of the positive-integer
coordinate set (whose Lean indexing starts at zero). -/
def setCount (s : Set ℕ) : ℝ≥0∞ := ∑' i, s.indicator (1 : ℕ → ℝ≥0∞) i

theorem setCount_le_of_no_embedding (s : Set ℕ) (N : ℕ)
    (hno : ∀ e : Fin (N + 1) ↪ ℕ, ¬ ∀ i, e i ∈ s) : setCount s ≤ N := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro m
  let A : Finset ℕ := (Finset.range m).filter (fun i => i ∈ s)
  have hcard : A.card ≤ N := by
    by_contra hle
    have hN : N + 1 ≤ Fintype.card A := by
      simpa using Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
    let f : Fin (N + 1) ↪ Fin (Fintype.card A) :=
      ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hN⟩,
        fun i j hij => Fin.ext (congrArg (fun k : Fin (Fintype.card A) => k.val) hij)⟩
    let q : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
    let e : Fin (N + 1) ↪ ℕ :=
      f.trans (q.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ A)))
    apply hno e
    intro i
    exact (Finset.mem_filter.mp (q (f i)).property).2
  have hsum : (∑ i ∈ Finset.range m, s.indicator (1 : ℕ → ℝ≥0∞) i) = A.card := by
    calc
      _ = ∑ i ∈ A, (1 : ℝ≥0∞) := by
        simp [A, Finset.sum_filter, Set.indicator_apply]
      _ = _ := by simp
  rw [hsum]
  exact_mod_cast hcard

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set ℕ} {K : ℕ → ℕ → ℝ}

/-- Tonelli identifies the expected total particle count with the kernel trace. -/
theorem IsDPP.expected_setCount (h : IsDPP μ X K)
    (hs : Summable (fun i => K i i)) :
    (∫⁻ ω, setCount (X ω) ∂μ) = ENNReal.ofReal (∑' i, K i i) := by
  let f : ℕ → Ω → ℝ≥0∞ := fun i =>
    ({ω | i ∈ X ω} : Set Ω).indicator (1 : Ω → ℝ≥0∞)
  have hm (i : ℕ) : AEMeasurable (f i) μ :=
    (measurable_const.indicator (h.measurable_occupancy i)).aemeasurable
  change (∫⁻ ω, ∑' i, f i ω ∂μ) = _
  rw [lintegral_tsum (f := f) hm]
  have he (i : ℕ) :
      (∫⁻ ω, f i ω ∂μ) =
        ENNReal.ofReal (K i i) := by
    change (∫⁻ ω, ({ω | i ∈ X ω} : Set Ω).indicator (1 : Ω → ℝ≥0∞) ω ∂μ) = _
    rw [lintegral_indicator_one (h.measurable_occupancy i)]
    rw [← h.occupation i, Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)]
  simp_rw [he]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun i => (h.diagonal_bounds i).1) hs).symm

/-- Vanishing correlations of order N+1 give an almost-sure rank bound for the
actual random subset. Countability lets us exclude all injective tuples at once. -/
theorem IsDPP.setCount_le_ae_of_rank (h : IsDPP μ X K) (N : ℕ)
    (hrank : ∀ e : Fin (N + 1) ↪ ℕ,
      Matrix.det (Matrix.of (fun i j => K (e i) (e j))) = 0) :
    ∀ᵐ ω ∂μ, setCount (X ω) ≤ N := by
  have he (e : Fin (N + 1) ↪ ℕ) : ∀ᵐ ω ∂μ, ¬ ∀ i, e i ∈ X ω := by
    have hz : μ {ω | ∀ i, e i ∈ X ω} = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top μ _)).mp
        ((h.correlation (N + 1) e).trans (hrank e))
    exact ae_iff.mpr (by simpa only [not_not] using hz)
  letI : Countable (Fin (N + 1) ↪ ℕ) :=
    Function.Injective.countable
      (f := fun e : Fin (N + 1) ↪ ℕ => (e : Fin (N + 1) → ℕ))
      Function.Embedding.coe_injective
  have hall : ∀ᵐ ω ∂μ, ∀ e : Fin (N + 1) ↪ ℕ, ¬ ∀ i, e i ∈ X ω :=
    ae_all_iff.mpr he
  filter_upwards [hall] with ω hω
  exact setCount_le_of_no_embedding (X ω) N hω

/-- A rank-N DPP with trace N has exactly N occupied sites almost surely. The
rank condition and trace are deterministic kernel facts; no coupling or
approximation-to-the-constant hypothesis occurs here. -/
theorem IsDPP.setCount_eq_ae_of_rank_trace (h : IsDPP μ X K) (N : ℕ)
    (hrank : ∀ e : Fin (N + 1) ↪ ℕ,
      Matrix.det (Matrix.of (fun i j => K (e i) (e j))) = 0)
    (hs : Summable (fun i => K i i))
    (htrace : (∑' i, K i i) = N) :
    ∀ᵐ ω ∂μ, setCount (X ω) = N := by
  have hint : (∫⁻ ω, setCount (X ω) ∂μ) = N := by
    rw [h.expected_setCount hs, htrace]
    simp
  apply ae_eq_of_ae_le_of_lintegral_le (h.setCount_le_ae_of_rank N hrank)
  · rw [hint]
    simp
  · exact measurable_const.aemeasurable
  · simp [hint]

end RiemannResearch.Probability.DPP
