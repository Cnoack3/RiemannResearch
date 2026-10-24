import RiemannResearch.Analysis.FiniteRegularizedConstraints
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact action of the regularization path

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
Each decrease in complete observation mismatch equals both physical and
observation displacement energies divided by the penalty increment. The
finite identity telescopes exactly and yields summability of the full action.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.RegularizedPathAction
open FiniteHilbertGram FiniteRegularizedConstraints
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem mismatch_equal_iff_coefficients_equal {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) :
    mismatchEnergy B t (coefficients hv B f t ρ) =
      mismatchEnergy B t (coefficients hv B f t σ) ↔
      coefficients hv B f t ρ = coefficients hv B f t σ := by
  constructor
  · intro he
    have h := penalty_difference_exact hv B f t ρ σ
    rw [he, sub_self, mul_zero] at h
    have hp := mul_nonneg (add_nonneg (sq_nonneg ρ) (sq_nonneg σ))
      (observationEnergy_nonneg B (coefficients hv B f t ρ - coefficients hv B f t σ))
    have hz : ‖Fintype.linearCombination ℝ v
        (coefficients hv B f t ρ - coefficients hv B f t σ)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ v
        (coefficients hv B f t ρ - coefficients hv B f t σ)‖]
    apply sub_eq_zero.mp
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro he
    rw [he]

theorem mismatch_strict_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 ≤ σ ^ 2) :
    mismatchEnergy B t (coefficients hv B f t σ) <
      mismatchEnergy B t (coefficients hv B f t ρ) ↔
      coefficients hv B f t ρ ≠ coefficients hv B f t σ := by
  have hm := mismatch_antitone_of_sq_le hv B f t ρ σ hρσ
  have he := mismatch_equal_iff_coefficients_equal hv B f t ρ σ
  constructor
  · intro h hc
    rw [hc] at h
    exact (lt_irrefl _) h
  · intro hn
    exact lt_of_le_of_ne hm (Ne.symm (fun h => hn (he.mp h)))

/-- The numerator contains both complete displacement energies. -/
def penaltyAction {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) : ℝ :=
  (2 * ‖Fintype.linearCombination ℝ v
      (coefficients hv B f t ρ - coefficients hv B f t σ)‖ ^ 2 +
    (ρ ^ 2 + σ ^ 2) * observationEnergy B
      (coefficients hv B f t ρ - coefficients hv B f t σ)) / (σ ^ 2 - ρ ^ 2)

theorem penaltyAction_exact {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 < σ ^ 2) :
    penaltyAction hv B f t ρ σ =
      mismatchEnergy B t (coefficients hv B f t ρ) -
      mismatchEnergy B t (coefficients hv B f t σ) := by
  unfold penaltyAction
  apply (div_eq_iff (sub_pos.mpr hρσ).ne').mpr
  have h := penalty_difference_exact hv B f t ρ σ
  nlinarith

theorem penaltyAction_nonneg {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 < σ ^ 2) :
    0 ≤ penaltyAction hv B f t ρ σ := by
  rw [penaltyAction_exact hv B f t ρ σ hρσ]
  exact sub_nonneg.mpr (mismatch_antitone_of_sq_le hv B f t ρ σ hρσ.le)

/-- Only the finitely many penalty steps occurring in the identity are assumed increasing. -/
theorem finite_path_action_exact {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : ℕ → ℝ) (N : ℕ)
    (hr : ∀ k < N, (r k) ^ 2 < (r (k + 1)) ^ 2) :
    (∑ k ∈ Finset.range N, penaltyAction hv B f t (r k) (r (k + 1))) =
      mismatchEnergy B t (coefficients hv B f t (r 0)) -
      mismatchEnergy B t (coefficients hv B f t (r N)) := by
  have htel (a : ℕ → ℝ) (M : ℕ) :
      (∑ k ∈ Finset.range M, (a k - a (k + 1))) = a 0 - a M := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ = ∑ k ∈ Finset.range N,
        (mismatchEnergy B t (coefficients hv B f t (r k)) -
          mismatchEnergy B t (coefficients hv B f t (r (k + 1)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact penaltyAction_exact hv B f t _ _ (hr k (Finset.mem_range.mp hk))
    _ = _ := htel _ N

/-- The complete physical-plus-observation action is summable without any feasibility assumption. -/
theorem path_action_summable {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : ℕ → ℝ)
    (hr : ∀ k, (r k) ^ 2 < (r (k + 1)) ^ 2) :
    Summable (fun k => penaltyAction hv B f t (r k) (r (k + 1))) := by
  apply summable_of_sum_range_le
    (fun k => penaltyAction_nonneg hv B f t _ _ (hr k))
    (c := mismatchEnergy B t (coefficients hv B f t (r 0)))
  intro N
  rw [finite_path_action_exact hv B f t r N (fun k _ => hr k)]
  exact sub_le_self _ (mismatchEnergy_nonneg B t _)

/-- When the mismatch limit is identified, no term of the infinite action is discarded. -/
theorem path_action_tsum {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : ℕ → ℝ)
    (hr : ∀ k, (r k) ^ 2 < (r (k + 1)) ^ 2) (L : ℝ)
    (hL : Tendsto (fun k => mismatchEnergy B t (coefficients hv B f t (r k))) atTop (𝓝 L)) :
    (∑' k, penaltyAction hv B f t (r k) (r (k + 1))) =
      mismatchEnergy B t (coefficients hv B f t (r 0)) - L := by
  have hs := (path_action_summable hv B f t r hr).hasSum.tendsto_sum_nat
  have he : Tendsto (fun N => ∑ k ∈ Finset.range N,
      penaltyAction hv B f t (r k) (r (k + 1))) atTop
      (𝓝 (mismatchEnergy B t (coefficients hv B f t (r 0)) - L)) := by
    have ht := (tendsto_const_nhds (x := mismatchEnergy B t (coefficients hv B f t (r 0)))).sub hL
    convert ht using 1
    funext N
    exact finite_path_action_exact hv B f t r N (fun k _ => hr k)
  exact tendsto_nhds_unique hs he

end RiemannResearch.Analysis.RegularizedPathAction
