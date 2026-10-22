import RiemannResearch.Analysis.AnalyticCircleSquareBounds
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Real.Sqrt

/-!
Finite empirical transfer from scalar circle second moments to squared compact
uniform norms. The only analytic input is the proved Cauchy/mean-value control
in `AnalyticCircleSquareBounds`; all probability weights remain explicit.
-/

open Complex Filter Metric Real Set MeasureTheory

namespace RiemannResearch.Analysis
namespace AnalyticCircleSquareBounds

/-- Squared uniform norm on a compact set, with value zero for the empty set. -/
noncomputable def compactSquareSup (K : Set ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup (insert 0 ((fun z => ‖f z‖ ^ 2) '' K))

theorem compactSquareSup_bddAbove {K : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddAbove (insert 0 ((fun z => ‖f z‖ ^ 2) '' K)) :=
  bddAbove_insert.mpr (hK.bddAbove_image (hf.norm.pow 2))

theorem compactSquareSup_nonneg {K : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hf : ContinuousOn f K) : 0 ≤ compactSquareSup K f := by
  exact le_csSup (compactSquareSup_bddAbove hK hf) (mem_insert 0 _)

theorem sq_norm_le_compactSquareSup {K : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hf : ContinuousOn f K) {z : ℂ} (hz : z ∈ K) :
    ‖f z‖ ^ 2 ≤ compactSquareSup K f := by
  apply le_csSup (compactSquareSup_bddAbove hK hf)
  apply mem_insert_of_mem
  exact mem_image_of_mem (fun z => ‖f z‖ ^ 2) hz

theorem compactSquareSup_le {K : Set ℂ} {f : ℂ → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ z ∈ K, ‖f z‖ ^ 2 ≤ B) : compactSquareSup K f ≤ B := by
  apply csSup_le (by simp)
  intro x hx
  rcases mem_insert_iff.mp hx with (rfl | hx)
  · exact hB
  · rcases hx with ⟨z, hz, rfl⟩
    exact hf z hz

/-- The bundled continuous function obtained by restricting to a compact set. -/
def compactRestriction (K : Set ℂ) (f : ℂ → ℂ) (hf : ContinuousOn f K) : C(K, ℂ) :=
  ⟨fun z => f z, hf.domRestrict⟩

/-- The concrete squared compact supremum equals the square of the norm in
    the Banach algebra of continuous functions on the compact set. -/
theorem compactSquareSup_eq_norm_sq {K : Set ℂ} [CompactSpace K]
    {f : ℂ → ℂ} (hf : ContinuousOn f K) :
    compactSquareSup K f = ‖compactRestriction K f hf‖ ^ 2 := by
  let F := compactRestriction K f hf
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  change compactSquareSup K f = ‖F‖ ^ 2
  apply le_antisymm
  · apply compactSquareSup_le (sq_nonneg ‖F‖)
    intro z hz
    have hn := F.norm_coe_le_norm ⟨z, hz⟩
    change ‖f z‖ ≤ ‖F‖ at hn
    nlinarith [norm_nonneg (f z), norm_nonneg F]
  · have hB0 := compactSquareSup_nonneg hK hf
    have hn : ‖F‖ ≤ Real.sqrt (compactSquareSup K f) := by
      apply (F.norm_le (Real.sqrt_nonneg _)).mpr
      intro z
      have hp := sq_norm_le_compactSquareSup hK hf z.property
      have hs := Real.sq_sqrt hB0
      change ‖f z‖ ≤ Real.sqrt (compactSquareSup K f)
      nlinarith [norm_nonneg (f z), Real.sqrt_nonneg (compactSquareSup K f)]
    have hs := Real.sq_sqrt hB0
    nlinarith [norm_nonneg F, Real.sqrt_nonneg (compactSquareSup K f)]

/-- Finite weighted sums and circle averages commute. -/
theorem circleAverage_weighted_sum {ι : Type*} {I : Finset ι}
    {h : ι → ℂ → ℝ} {w : ι → ℝ} {c : ℂ} {R : ℝ}
    (hh : ∀ i ∈ I, ContinuousOn (h i) (sphere c |R|)) :
    circleAverage (fun z => ∑ i ∈ I, w i * h i z) c R =
      ∑ i ∈ I, w i * circleAverage (h i) c R := by
  have hci : ∀ i ∈ I, CircleIntegrable (fun z => w i * h i z) c R := by
    intro i hi
    exact (continuousOn_const.mul (hh i hi)).circleIntegrable'
  rw [circleAverage_fun_sum hci]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [smul_eq_mul] using circleAverage_fun_smul (a := w i) (f := h i)

/-- A fixed finite circle cover upgrades uniform scalar second-moment bounds
    to uniform compact second-moment bounds for any finite weighted sample.
    The weights may encode a uniform empirical measure or multiplicities. -/
theorem weighted_compactSquareSup_le {K U : Set ℂ}
    {S : Finset K} {R : K → ℝ}
    (hR : ∀ c : K, 0 < R c ∧ closedBall (c : ℂ) (R c) ⊆ U)
    (hcontrol : ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f U → ∀ z ∈ K,
      ‖f z‖ ^ 2 ≤ 4 * ∑ c ∈ S, circleAverage (fun v => ‖f v‖ ^ 2) (c : ℂ) (R c))
    {ι : Type*} (I : Finset ι) (w : ι → ℝ) (f : ι → ℂ → ℂ) (B : ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hf : ∀ i ∈ I, DifferentiableOn ℂ (f i) U)
    (hscalar : ∀ c ∈ S, ∀ z ∈ sphere (c : ℂ) |R c|,
      ∑ i ∈ I, w i * ‖f i z‖ ^ 2 ≤ B) :
    ∑ i ∈ I, w i * compactSquareSup K (f i) ≤ 4 * (S.card : ℝ) * B := by
  classical
  let A : ι → K → ℝ := fun i c => circleAverage (fun z => ‖f i z‖ ^ 2) (c : ℂ) (R c)
  have hA0 : ∀ i c, 0 ≤ A i c := by
    intro i c
    exact circleAverage_nonneg_of_nonneg (fun z hz => sq_nonneg ‖f i z‖)
  have hsup : ∀ i ∈ I, compactSquareSup K (f i) ≤ 4 * ∑ c ∈ S, A i c := by
    intro i hi
    apply compactSquareSup_le
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun c hc => hA0 i c))
    · exact hcontrol (f i) (hf i hi)
  have hcont : ∀ c : K, ∀ i ∈ I,
      ContinuousOn (fun z => ‖f i z‖ ^ 2) (sphere (c : ℂ) |R c|) := by
    intro c i hi
    apply ContinuousOn.pow _ 2
    apply ContinuousOn.norm
    apply (hf i hi).continuousOn.mono
    rw [abs_of_pos (hR c).1]
    exact sphere_subset_closedBall.trans (hR c).2
  have hbound : ∀ c ∈ S, ∑ i ∈ I, w i * A i c ≤ B := by
    intro c hc
    change (∑ i ∈ I, w i * circleAverage (fun z => ‖f i z‖ ^ 2) (c : ℂ) (R c)) ≤ B
    rw [← circleAverage_weighted_sum (hcont c)]
    apply circleAverage_mono_on_of_le_circle _ (hscalar c hc)
    apply ContinuousOn.circleIntegrable'
    apply continuousOn_finsetSum
    intro i hi
    exact continuousOn_const.mul (hcont c i hi)
  calc
    ∑ i ∈ I, w i * compactSquareSup K (f i)
      ≤ ∑ i ∈ I, w i * (4 * ∑ c ∈ S, A i c) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hsup i hi) (hw i hi)
    _ = ∑ i ∈ I, ∑ c ∈ S, 4 * (w i * A i c) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = ∑ c ∈ S, ∑ i ∈ I, 4 * (w i * A i c) := Finset.sum_comm
    _ = 4 * ∑ c ∈ S, ∑ i ∈ I, w i * A i c := by
      simp only [Finset.mul_sum]
    _ ≤ 4 * ∑ c ∈ S, B := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun c hc => hbound c hc)
    _ = 4 * (S.card : ℝ) * B := by simp [nsmul_eq_mul, mul_assoc]

/-- On every compact subset of an open domain, uniformly bounded scalar
    second moments along finitely many fixed circles imply bounded compact
    second moments, with an explicit cover-dependent coefficient. -/
theorem exists_weighted_compactSquareSup_control {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (S : Finset K) (R : K → ℝ),
      (∀ c : K, 0 < R c ∧ closedBall (c : ℂ) (R c) ⊆ U) ∧
      ∀ {ι : Type*} (I : Finset ι) (w : ι → ℝ) (f : ι → ℂ → ℂ) (B : ℝ),
        (∀ i ∈ I, 0 ≤ w i) →
        (∀ i ∈ I, DifferentiableOn ℂ (f i) U) →
        (∀ c ∈ S, ∀ z ∈ sphere (c : ℂ) |R c|,
          ∑ i ∈ I, w i * ‖f i z‖ ^ 2 ≤ B) →
        ∑ i ∈ I, w i * compactSquareSup K (f i) ≤ 4 * (S.card : ℝ) * B := by
  obtain ⟨S, R, hR, hcontrol⟩ := exists_compact_circleSquare_control hK hU hKU
  exact ⟨S, R, hR, fun I w f B hw hf hscalar =>
    weighted_compactSquareSup_le hR hcontrol I w f B hw hf hscalar⟩

end AnalyticCircleSquareBounds
end RiemannResearch.Analysis
