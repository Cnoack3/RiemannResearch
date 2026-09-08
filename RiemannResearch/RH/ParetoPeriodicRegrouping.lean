import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.Analysis.SumOverResidueClass

/-!
Source: RH_Two_Seed_Threshold.tex, revised 7 September 2026, Section 10.
The finite weighted residue norm is exactly the genuine infinite Pareto norm.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem periodic_add_mul (N : ℕ) (f : ℕ → ℝ)
    (hp : ∀ k, f (k+N) = f k) (k j : ℕ) : f (k+N*j) = f k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : k+N*(j+1) = (k+N*j)+N := by ring
    rw [he, hp, ih]

/-- Exact residue regrouping, retaining every term of a bounded periodic sequence. -/
theorem periodic_paretoMean (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hp : ∀ k, f (k+N) = f k) :
    paretoMean f = ∑ r : Fin N, progressionWeight N (r.val+1) * f (r.val+1) := by
  cases N with
  | zero => omega
  | succ n =>
    let g : ℕ → ℝ := fun k => positiveWeight (k+1) * f (k+1)
    have hg : Summable g := by
      exact (weighted_summable_of_bounded hf).comp_injective (fun _ _ h => Nat.add_right_cancel h)
    calc
      paretoMean f = ∑' k, g k := by
        unfold paretoMean
        rw [(weighted_summable_of_bounded hf).tsum_eq_zero_add]
        simp [positiveWeight, g]
      _ = ∑ r : Fin (n+1), ∑' j : ℕ, g (r.val+(n+1)*j) :=
        Nat.sumByResidueClasses hg (n+1)
      _ = ∑ r : Fin (n+1), progressionWeight (n+1) (r.val+1) * f (r.val+1) := by
        apply Finset.sum_congr rfl
        intro r _
        have he (j : ℕ) : g (r.val+(n+1)*j) =
            positiveWeight (r.val+1+(n+1)*j) * f (r.val+1) := by
          change positiveWeight (r.val+(n+1)*j+1) * f (r.val+(n+1)*j+1) = _
          have hh : r.val+(n+1)*j+1 = r.val+1+(n+1)*j := by omega
          rw [hh, periodic_add_mul (n+1) f hp]
        simp_rw [he]
        exact (progressionWeight_summable (n+1) (r.val+1) hN).tsum_mul_right _

/-- Positive residue representatives `1,...,N` carry total mass exactly one.
The representative `N` retains the complete zero congruence class. -/
theorem progressionWeight_normalization (N : ℕ) (hN : 0 < N) :
    (∑ r : Fin N, progressionWeight N (r.val+1)) = 1 := by
  have h := periodic_paretoMean N hN (fun _ => (1:ℝ))
    (C := 1) (by intro k; norm_num) (by intro k; rfl)
  simpa [paretoMean, positiveWeight_tsum] using h.symm

theorem positiveWeight_le_progressionWeight (N r : ℕ) (hN : 0 < N) :
    positiveWeight r ≤ progressionWeight N r := by
  have h := (progressionWeight_summable N r hN).sum_le_tsum ({0} : Finset ℕ)
    (fun j _ => positiveWeight_nonneg _)
  simpa [progressionWeight] using h

/-- Every actual finite-quotient weight is strictly positive. -/
theorem progressionWeight_pos (N r : ℕ) (hN : 0 < N) (hr : 0 < r) :
    0 < progressionWeight N r := by
  have h : 0 < positiveWeight r := by unfold positiveWeight; positivity
  exact h.trans_le (positiveWeight_le_progressionWeight N r hN)

/-- Exact weighted finite-residue squared norm, with all infinite tails retained. -/
theorem periodic_paretoInner (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hp : ∀ k, f (k+N) = f k) :
    paretoInner f f =
      ∑ r : Fin N, progressionWeight N (r.val+1) * (f (r.val+1))^2 := by
  have h := periodic_paretoMean N hN (fun k => f k * f k)
    (bounded_product hf hf) (by intro k; rw [hp])
  simpa only [paretoMean, paretoInner, pow_two] using h

/-- The mixed finite-residue formula keeps all signed cross terms. -/
theorem periodic_paretoInner_mixed (N : ℕ) (hN : 0 < N) (f g : ℕ → ℝ) {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hpf : ∀ k, f (k+N) = f k) (hpg : ∀ k, g (k+N) = g k) :
    paretoInner f g = ∑ r : Fin N, progressionWeight N (r.val+1) *
      (f (r.val+1) * g (r.val+1)) := by
  have h := periodic_paretoMean N hN (fun k => f k * g k)
    (bounded_product hf hg) (by intro k; rw [hpf, hpg])
  simpa only [paretoMean, paretoInner] using h

/-- Exact finite-quotient pushforward compatibility for every multiple `N*b`.
Each coarse progression is partitioned into its `b` finer progressions. -/
theorem progressionWeight_compatibility (N b r : ℕ) (hN : 0 < N) (hb : 0 < b) :
    progressionWeight N r =
      ∑ s : Fin b, progressionWeight (N*b) (r+N*s.val) := by
  cases b with
  | zero => omega
  | succ b =>
    unfold progressionWeight
    rw [Nat.sumByResidueClasses (progressionWeight_summable N r hN) (b+1)]
    apply Finset.sum_congr rfl
    intro s _
    apply tsum_congr
    intro j
    congr 1
    change r + N * ((s : Fin (b+1)).val + (b+1)*j) =
      r + N * (s : Fin (b+1)).val + N*(b+1)*j
    ring

end
end RiemannResearch.RH.Pareto
