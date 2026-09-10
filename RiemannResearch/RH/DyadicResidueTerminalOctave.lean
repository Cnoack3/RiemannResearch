import RiemannResearch.RH.DyadicResidueStepApproximation

/-!
# The exact surviving terminal octave for the binary residue

Source: user-provided DyadicSignedBoundaryAbelVerification20260910(1).md
and the retained DyadicBoundaryFourierResearchNote20260910.md, September 10, 2026.
The present proofs establish the stated bounded continuation targets.

Finite cancellation preserves the terminal octave. Its complete boundary
error is at most 1/(2N+1). No difference of divergent infinite sums is used.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Finite terminal-octave cancellation. Its hypothesis is exactly what
dyadic invariance of the step coefficient supplies after division by the
positive physical step index. No infinite harmonic sums are split apart. -/
private theorem dyadicResidueTwo_jump_prefix_eq_octave
    (g : ℕ → ℝ) (hg : ∀ j, 2 * g (2*j+1) = g j) (N : ℕ) :
    (∑ j ∈ Finset.range (2*N),
      ((((j+1) % 2 : ℕ) : ℝ) - ((j % 2 : ℕ) : ℝ)) * g j) =
      ∑ j ∈ Finset.range N, g (N+j) := by
  have hprefix : ∀ N : ℕ,
      (∑ j ∈ Finset.range (2*N),
        ((((j+1) % 2 : ℕ) : ℝ) - ((j % 2 : ℕ) : ℝ)) * g j) =
        (∑ j ∈ Finset.range (2*N), g j) - ∑ j ∈ Finset.range N, g j := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hidx : 2 * (N + 1) = 2*N + 1 + 1 := by omega
      have h0 : (2*N) % 2 = 0 := by omega
      have h1 : (2*N+1) % 2 = 1 := by omega
      have h2 : (2*N+1+1) % 2 = 0 := by omega
      simp only [hidx, Finset.sum_range_succ]
      simp only [h0, h1, h2, Nat.cast_zero, Nat.cast_one,
        sub_zero, zero_sub, one_mul, neg_mul]
      linarith [hg N]
  rw [hprefix]
  have hsum := Finset.sum_range_add g N N
  have hidx : N + N = 2*N := by omega
  rw [hidx] at hsum
  linarith

def dyadicResidueTwoTerminalOctave (N i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
    dyadicBoundaryCoordinate (dyadicProjectedStep (N+j+1) (by positivity)) i /
      (N+j+1 : ℝ)

theorem hilbertResidue_two_stepJumpPrefix_boundary_eq_octave (N i : ℕ) :
    dyadicBoundaryCoordinate
      (hilbertStepJumpPrefix (hilbertResidue 2 (by norm_num)) (2*N)) i =
        dyadicResidueTwoTerminalOctave N i := by
  let g : ℕ → ℝ := fun j =>
    dyadicBoundaryCoordinate (dyadicProjectedStep (j+1) (by positivity)) i / (j+1 : ℝ)
  have hg : ∀ j, 2 * g (2*j+1) = g j := by
    intro j
    dsimp [g]
    have hi : 2*j+1+1 = 2*(j+1) := by omega
    have hv : dyadicBoundaryCoordinate
        (dyadicProjectedStep (2*j+1+1) (by positivity)) i =
        dyadicBoundaryCoordinate (dyadicProjectedStep (j+1) (by positivity)) i := by
      simpa only [hi] using dyadicBoundaryCoordinate_step_double (j+1) (by positivity) i
    rw [hv]
    push_cast
    have hj : (j+1 : ℝ) ≠ 0 := by positivity
    have hj2 : (2*(j+1) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hilbertStepJumpPrefix_boundaryCoordinate]
  calc
    _ = ∑ j ∈ Finset.range (2*N),
        ((((j+1)%2 : ℕ) : ℝ) - ((j%2 : ℕ) : ℝ)) * g j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hilbertResidue_sequence, residue]
      dsimp [g]
      ring
    _ = _ := by
      have h := dyadicResidueTwo_jump_prefix_eq_octave g hg N
      simpa only [g, dyadicResidueTwoTerminalOctave, Nat.cast_add] using h

theorem hilbertResidue_two_terminalOctave_full_boundary_error_le (N : ℕ) :
    (∑' i : ℕ, (1/4 : ℝ) *
      (dyadicResidueTwoTerminalOctave N i -
        dyadicBoundaryCoordinate (hilbertResidue 2 (by norm_num)) i)^2) ≤
      1 / (2*N+1 : ℝ) := by
  simpa only [hilbertResidue_two_stepJumpPrefix_boundary_eq_octave, Nat.cast_mul,
    Nat.cast_ofNat, show ((2 : ℝ)-1)^2 = 1 by norm_num] using
      hilbertResidue_stepJumpPrefix_boundary_error_le 2 (by norm_num) (2*N)

open Filter

/-- The surviving octave tends to the actual binary residue coefficient. -/
theorem hilbertResidue_two_terminalOctave_tendsto (i : ℕ) :
    Tendsto (fun N => dyadicResidueTwoTerminalOctave N i) atTop
      (nhds (dyadicBoundaryCoordinate (hilbertResidue 2 (by norm_num)) i)) := by
  have hc : Continuous (fun f : ThresholdHilbert => dyadicBoundaryCoordinate f i) := by
    unfold dyadicBoundaryCoordinate
    exact continuous_const.mul (continuous_const.inner continuous_id)
  have hN : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (by norm_num)) tendsto_id
  have ht := (hc.tendsto _).comp ((hilbertResidue_stepJumpPrefix_tendsto 2
    (by norm_num)).comp hN)
  simpa only [Function.comp_def,
    hilbertResidue_two_stepJumpPrefix_boundary_eq_octave] using ht

end
end RiemannResearch.RH.Pareto
