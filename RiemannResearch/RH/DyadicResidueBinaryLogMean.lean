import RiemannResearch.Analysis.ScaledHarmonicBlock
import RiemannResearch.Analysis.LogarithmicTentIntegral
import RiemannResearch.RH.DyadicBoundaryTents
import RiemannResearch.RH.DyadicResidueTerminalOctave

/-!
# Exact harmonic blocks for the binary terminal octave

This finite bridge identifies the checked terminal octave with two finite
harmonic blocks. All operations are finite, and the two signed tent pieces
are retained together. It does not assume any Fourier expansion or RH bound.

Source: user-provided `DyadicTentTerminalVerification20260910(1).md`
and the September 10, 2026 continuation. The real tent integral is evaluated
separately in `Analysis/LogarithmicTentIntegral.lean`.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

private theorem dyadicBoundaryCoordinate_step_index_congr
    (i m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m = n) :
    dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i =
      dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i := by
  subst n
  rfl

/-- The zero gap between consecutive dyadic copies of a boundary tent. -/
theorem dyadicBoundaryCoordinate_step_tent_gap
    (i m : ℕ) (hm : 0 < m)
    (hlo : 2*(i+1)+2 ≤ m) (hhi : m ≤ 4*(i+1)) :
    dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i = 0 := by
  have hm' : 0 < m / 2 := by omega
  by_cases he : m % 2 = 0
  · have hi : m = 2*(m/2) := by omega
    rw [dyadicBoundaryCoordinate_step_index_congr i m (2*(m/2)) hm
      (by positivity) hi, dyadicBoundaryCoordinate_step_double (m/2) hm' i]
    exact dyadicBoundaryCoordinate_step_zero (m/2) hm' i (by omega)
  · have hi : m = 2*(m/2)+1 := by omega
    rw [dyadicBoundaryCoordinate_step_index_congr i m (2*(m/2)+1) hm
      (by positivity) hi, dyadicBoundaryCoordinate_step_odd (m/2) hm' i,
      if_neg (show i+1 ≠ m/2 by omega),
      dyadicBoundaryCoordinate_step_zero (m/2) hm' i (by omega),
      dyadicBoundaryCoordinate_step_zero (m/2+1) (by positivity) i (by omega)]
    norm_num

/-- Exact zero interpolation across every dyadic subdivision of the gap. -/
theorem dyadicBoundaryCoordinate_step_tent_gap_refinement
    (i h q r : ℕ) (hlo : 2*(i+1)+2 ≤ q)
    (hhi : q+1 ≤ 4*(i+1)) (hr : r ≤ 2^h) :
    dyadicBoundaryCoordinate
      (dyadicProjectedStep (2^h*q+r)
        (by
          have hq : 0 < q := by omega
          positivity)) i = 0 := by
  have hi := dyadicBoundaryCoordinate_step_interpolation i q h r (by omega) hr
  rw [dyadicBoundaryCoordinate_step_tent_gap i q (by omega) hlo (by omega),
    dyadicBoundaryCoordinate_step_tent_gap i (q+1) (by omega) (by omega) hhi,
    mul_zero, mul_zero, zero_add] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by positivity)

/-- The actual binary terminal octave is exactly a difference of two finite
harmonic blocks. The apparent constant pieces of the rising and falling
tents cancel pairwise before any limiting operation. -/
theorem dyadicResidueTwoTerminalOctave_eq_harmonic_blocks (i h : ℕ) :
    dyadicResidueTwoTerminalOctave (2^h*(2*(i+1))) i =
      (2*(i+1)+2 : ℝ) *
        (∑ j ∈ Finset.range (2^h),
          1 / ((2 : ℝ)^h * (2*(i+1)+1) + j+1)) -
      (2*(i+1) : ℝ) *
        (∑ j ∈ Finset.range (2^h),
          1 / ((2 : ℝ)^h * (2*(i+1)) + j+1)) := by
  let D : ℕ := 2^h
  let N : ℕ := D*(2*(i+1))
  let g : ℕ → ℝ := fun j =>
    dyadicBoundaryCoordinate (dyadicProjectedStep (N+j+1) (by positivity)) i /
      (N+j+1 : ℝ)
  have hd : 0 < D := by dsimp [D]; positivity
  have hdR : (D : ℝ) ≠ 0 := by positivity
  have hN : N = D + (D + D*(2*i)) := by dsimp [N]; ring
  have htail : (∑ j ∈ Finset.range (D*(2*i)), g (D+(D+j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt : j < D*(2*i) := Finset.mem_range.mp hj
    have hquot : j / D < 2*i := by
      apply (Nat.div_lt_iff_lt_mul hd).2
      simpa only [Nat.mul_comm] using hjlt
    have hrem : j % D + 1 ≤ D := by
      have := Nat.mod_lt j hd
      omega
    have hidx : N+(D+(D+j))+1 =
        D*(2*(i+1)+2+j/D)+(j%D+1) := by
      have hjdecomp : D*(j/D)+j%D = j := Nat.div_add_mod j D
      dsimp [N]
      nlinarith only [hjdecomp]
    have hv : dyadicBoundaryCoordinate
        (dyadicProjectedStep (N+(D+(D+j))+1) (by positivity)) i = 0 := by
      rw [dyadicBoundaryCoordinate_step_index_congr i (N+(D+(D+j))+1)
        (D*(2*(i+1)+2+j/D)+(j%D+1)) (by positivity) (by positivity) hidx]
      exact dyadicBoundaryCoordinate_step_tent_gap_refinement
        i h (2*(i+1)+2+j/D) (j%D+1) (Nat.le_add_right _ _) (by omega) hrem
    dsimp only [g]
    rw [hv, zero_div]
  have hsplit : (∑ j ∈ Finset.range N, g j) =
      (∑ j ∈ Finset.range D, g j) +
        ∑ j ∈ Finset.range D, g (D+j) := by
    have h₁ := Finset.sum_range_add g D (D+D*(2*i))
    have h₂ := Finset.sum_range_add (fun j => g (D+j)) D (D*(2*i))
    rw [← hN, h₂, htail, add_zero] at h₁
    exact h₁
  have hpair (j : ℕ) (hj : j ∈ Finset.range D) :
      g j + g (D+j) =
        (2*(i+1)+2 : ℝ) * (1 / ((D : ℝ)*(2*(i+1)+1)+j+1)) -
        (2*(i+1) : ℝ) * (1 / ((D : ℝ)*(2*(i+1))+j+1)) := by
    have hjD : j+1 ≤ D := by have := Finset.mem_range.mp hj; omega
    have hidx₁ : N+j+1 = D*(2*(i+1))+(j+1) := by dsimp [N]; omega
    have hidx₂ : N+(D+j)+1 = D*(2*(i+1)+1)+(j+1) := by dsimp [N]; ring
    have hrise : dyadicBoundaryCoordinate
        (dyadicProjectedStep (N+j+1) (by positivity)) i = (j+1 : ℝ)/(D : ℝ) := by
      rw [dyadicBoundaryCoordinate_step_index_congr i (N+j+1)
        (D*(2*(i+1))+(j+1)) (by positivity) (by positivity) hidx₁]
      simpa only [D, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
        dyadicBoundaryCoordinate_step_tent_rising i h (j+1) hjD
    have hfall : dyadicBoundaryCoordinate
        (dyadicProjectedStep (N+(D+j)+1) (by positivity)) i =
          1 - (j+1 : ℝ)/(D : ℝ) := by
      rw [dyadicBoundaryCoordinate_step_index_congr i (N+(D+j)+1)
        (D*(2*(i+1)+1)+(j+1)) (by positivity) (by positivity) hidx₂]
      simpa only [D, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
        dyadicBoundaryCoordinate_step_tent_falling i h (j+1) hjD
    dsimp only [g]
    rw [hrise, hfall]
    have hden₁ : (D : ℝ)*(2*(i+1))+j+1 ≠ 0 := by positivity
    have hden₂ : (D : ℝ)*(2*(i+1)+1)+j+1 ≠ 0 := by positivity
    have hNR : (N : ℝ) = (D : ℝ)*(2*(i+1)) := by dsimp [N]; push_cast; rfl
    rw [hNR]
    push_cast
    field_simp
    ring
  change (∑ j ∈ Finset.range N, g j) = _
  rw [hsplit, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range D,
        ((2*(i+1)+2 : ℝ) * (1 / ((D : ℝ)*(2*(i+1)+1)+j+1)) -
        (2*(i+1) : ℝ) * (1 / ((D : ℝ)*(2*(i+1))+j+1))) := by
      exact Finset.sum_congr rfl hpair
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [D, Nat.cast_pow, Nat.cast_ofNat]

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open Filter RiemannResearch.Analysis
open scoped BigOperators
noncomputable section

/-- The explicit logarithmic second difference of the binary residue boundary. -/
def dyadicBinaryBoundaryLog (i : ℕ) : ℝ :=
  (2*(i+1) : ℝ) * Real.log (2*(i+1)) -
    2*(2*(i+1)+1) * Real.log (2*(i+1)+1) +
    (2*(i+1)+2) * Real.log (2*(i+1)+2)

/-- Every actual binary residue coefficient equals its explicit logarithmic
second difference. Both signed harmonic blocks are retained through the limit. -/
theorem dyadicBoundaryCoordinate_residue_two_eq_log (i : ℕ) :
    dyadicBoundaryCoordinate (hilbertResidue 2 (by norm_num)) i =
      dyadicBinaryBoundaryLog i := by
  have hp : Tendsto (fun h : ℕ => 2^h) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hidx : Tendsto (fun h : ℕ => 2^h*(2*(i+1))) atTop atTop := by
    apply tendsto_atTop_mono _ hp
    intro h
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have ht := (hilbertResidue_two_terminalOctave_tendsto i).comp hidx
  have he (h : ℕ) :
      dyadicResidueTwoTerminalOctave (2^h*(2*(i+1))) i =
        (2*(i+1)+2 : ℝ) * scaledHarmonicBlock (2*(i+1)+1) (2^h) -
        (2*(i+1) : ℝ) * scaledHarmonicBlock (2*(i+1)) (2^h) := by
    simpa only [scaledHarmonicBlock, Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat] using
      dyadicResidueTwoTerminalOctave_eq_harmonic_blocks i h
  simp only [Function.comp_def, he] at ht
  have hright := ((scaledHarmonicBlock_tendsto (2*(i+1)+1)
    (by positivity)).comp hp).const_mul (2*(i+1)+2 : ℝ)
  have hleft := ((scaledHarmonicBlock_tendsto (2*(i+1))
    (by positivity)).comp hp).const_mul (2*(i+1) : ℝ)
  have h := tendsto_nhds_unique ht (hright.sub hleft)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  rw [h]
  unfold dyadicBinaryBoundaryLog
  have heq : (2 : ℝ)*(i+1)+1+1 = 2*(i+1)+2 := by ring
  rw [heq]
  ring

/-- The complete terminal-octave square error now has an explicit logarithmic
target at every boundary index, with no scalar-limit or Fourier assumption. -/
theorem dyadicResidueTwoTerminalOctave_log_full_error_le (N : ℕ) :
    (∑' i : ℕ, (1/4 : ℝ) *
      (dyadicResidueTwoTerminalOctave N i - dyadicBinaryBoundaryLog i)^2) ≤
      1 / (2*N+1 : ℝ) := by
  simpa only [dyadicBoundaryCoordinate_residue_two_eq_log] using
    hilbertResidue_two_terminalOctave_full_boundary_error_le N

/-- The zero-frequency contribution is the actual logarithmic tent integral. -/
theorem dyadicBoundaryCoordinate_residue_two_eq_tent_integral (i : ℕ) :
    dyadicBoundaryCoordinate (hilbertResidue 2 (by norm_num)) i =
      ∫ x in (2*(i+1) : ℝ)..2*(i+1)+2,
        rootTent (2*(i+1)) x / x := by
  rw [dyadicBoundaryCoordinate_residue_two_eq_log,
    integral_rootTent_div (by positivity)]
  rfl

end
end RiemannResearch.RH.Pareto
