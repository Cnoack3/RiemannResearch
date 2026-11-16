import RiemannResearch.Analysis.NuclearSynthesis
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Symmetrizing and flattening absolutely summable nuclear expansions

The RH consumer is `RH/WeilDampedPrimeNuclear`.
Source: the standard rank-one series proof of closure of nuclear operators
under adjoints and absolutely convergent sums; see the reference in
`Analysis/NuclearSynthesis`. All scalar signs are preserved.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.SquareSummableSynthesis
set_option maxHeartbeats 800000
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rankOne_adjoint (x y : H) : (rankOne x y).adjoint = rankOne y x := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_left ℂ
  intro t
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [rankOne_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem rankOne_smul_left (c : ℂ) (x y : H) :
    rankOne (c • x) y = c • rankOne x y := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [rankOne_apply, smul_apply, smul_smul]
  rw [mul_comm]

theorem symmetrized_nuclear_representation (T : H →L[ℂ] H) (p q : κ → H)
    (hc : Summable (fun k => ‖p k‖ * ‖q k‖))
    (hT : HasSum (fun k => rankOne (p k) (q k)) T) {w : ℝ} (hw : 0 ≤ w) :
    ∃ u v : κ ⊕ κ → H,
      Summable (fun k => ‖u k‖ * ‖v k‖) ∧
      (∑' k, ‖u k‖ * ‖v k‖) = 2 * w * ∑' k, ‖p k‖ * ‖q k‖ ∧
      HasSum (fun k => rankOne (u k) (v k)) ((-w : ℂ) • (T + T.adjoint)) := by
  let u : κ ⊕ κ → H := Sum.elim (fun k => (-w : ℂ) • p k) (fun k => (-w : ℂ) • q k)
  let v : κ ⊕ κ → H := Sum.elim q p
  have hcn : ‖(-w : ℂ)‖ = w := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  have hl : HasSum ((fun k => ‖u k‖ * ‖v k‖) ∘ Sum.inl)
      (w * ∑' k, ‖p k‖ * ‖q k‖) := by
    simpa only [u, v, Function.comp_def, Sum.elim_inl, norm_smul, hcn, mul_assoc] using
      hc.hasSum.mul_left w
  have hr : HasSum ((fun k => ‖u k‖ * ‖v k‖) ∘ Sum.inr)
      (w * ∑' k, ‖p k‖ * ‖q k‖) := by
    have he : (fun k => ‖u (Sum.inr k)‖ * ‖v (Sum.inr k)‖) =
        (fun k => w * (‖p k‖ * ‖q k‖)) := by
      funext k
      simp only [u, v, Sum.elim_inr, norm_smul, hcn]
      ring
    change HasSum (fun k => ‖u (Sum.inr k)‖ * ‖v (Sum.inr k)‖) _
    rw [he]
    exact hc.hasSum.mul_left w
  have hsum := hl.sum hr
  refine ⟨u, v, hsum.summable, hsum.tsum_eq.trans (by ring), ?_⟩
  have ha : HasSum (fun k => rankOne (q k) (p k)) T.adjoint := by
    simpa only [Function.comp_def, rankOne_adjoint] using
      hT.map ContinuousLinearMap.adjoint ContinuousLinearMap.adjoint.continuous
  have hL : HasSum ((fun k => rankOne (u k) (v k)) ∘ Sum.inl) ((-w : ℂ) • T) := by
    simpa only [u, v, Function.comp_def, Sum.elim_inl, rankOne_smul_left] using hT.const_smul (-w : ℂ)
  have hR : HasSum ((fun k => rankOne (u k) (v k)) ∘ Sum.inr) ((-w : ℂ) • T.adjoint) := by
    simpa only [u, v, Function.comp_def, Sum.elim_inr, rankOne_smul_left] using ha.const_smul (-w : ℂ)
  simpa only [smul_add] using hL.sum hR

theorem nuclear_series_flatten (p q : ℕ → κ → H) (T : ℕ → H →L[ℂ] H)
    (hc : ∀ n, Summable (fun k => ‖p n k‖ * ‖q n k‖))
    (hcost : Summable (fun n => ∑' k, ‖p n k‖ * ‖q n k‖))
    (hT : ∀ n, HasSum (fun k => rankOne (p n k) (q n k)) (T n)) :
    Summable (fun z : ℕ × κ => ‖p z.1 z.2‖ * ‖q z.1 z.2‖) ∧
      HasSum (fun z : ℕ × κ => rankOne (p z.1 z.2) (q z.1 z.2)) (∑' n, T n) := by
  have hall : Summable (fun z : ℕ × κ => ‖p z.1 z.2‖ * ‖q z.1 z.2‖) :=
    (summable_prod_of_nonneg (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ⟨hc, hcost⟩
  have hs : Summable (fun z : ℕ × κ => rankOne (p z.1 z.2) (q z.1 z.2)) :=
    (Summable.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => rankOne_norm_le _ _) hall).of_norm
  refine ⟨hall, ?_⟩
  have he : (∑' z : ℕ × κ, rankOne (p z.1 z.2) (q z.1 z.2)) = ∑' n, T n := by
    rw [hs.tsum_prod]
    apply tsum_congr
    intro n
    exact (hT n).tsum_eq
  rw [← he]
  exact hs.hasSum

end RiemannResearch.Analysis.SquareSummableSynthesis
