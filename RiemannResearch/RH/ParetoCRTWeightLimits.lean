import RiemannResearch.RH.ParetoExactHeadCRT

/-!
# Pareto CRT weights retain their atomic masses

Source: independently derived for the user's CRT/regression convergence
request, 19 September 2026. The existing exact progression decomposition and
telescoping tail bound squeeze each fixed residue mass to its first atom.
CRT compatibility therefore does not turn the complete Pareto Gram matrix
into a uniform-residue Gram matrix. No novelty claim is made.
-/

open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Along growing moduli, a fixed residue retains its first positive atom. -/
theorem progressionWeight_tendsto_atom (r : ℕ) :
    Tendsto (fun Q => progressionWeight (Q+1) r) atTop (𝓝 (positiveWeight r)) := by
  have hi : Tendsto (fun Q : ℕ => 1 / ((Q : ℝ)+1)) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun Q : ℕ => (Q : ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun Q => by linarith) tendsto_natCast_atTop_atTop
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have hu : Tendsto (fun Q : ℕ =>
      positiveWeight r + 1 / (((Q : ℝ)+1)*((r : ℝ)+1))) atTop
      (𝓝 (positiveWeight r)) := by
    have h := (tendsto_const_nhds (x := positiveWeight r)).add (hi.mul_const (1 / ((r : ℝ)+1)))
    simpa only [zero_mul, add_zero, one_div_mul_one_div] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun Q => positiveWeight_le_progressionWeight (Q+1) r (by omega))
    (fun Q => by simpa only [Nat.cast_add, Nat.cast_one] using
      progressionWeight_upper_one (Q+1) r (by omega))

/-- The defect at residue one tends to one half, not zero. -/
theorem uniformDefect_one_tendsto_half :
    Tendsto (fun Q => ExactHeadCRT.uniformDefect (Q+1) 1) atTop (𝓝 (1/2 : ℝ)) := by
  have hi : Tendsto (fun Q : ℕ => 1 / ((Q : ℝ)+1)) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun Q : ℕ => (Q : ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun Q => by linarith) tendsto_natCast_atTop_atTop
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have h := (progressionWeight_tendsto_atom 1).sub hi
  simpa only [ExactHeadCRT.uniformDefect, Nat.cast_add, Nat.cast_one,
    positiveWeight, Nat.cast_one, one_mul, one_add_one_eq_two, sub_zero] using h

theorem uniformDefect_one_not_tendsto_zero :
    ¬ Tendsto (fun Q => ExactHeadCRT.uniformDefect (Q+1) 1) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have he := tendsto_nhds_unique uniformDefect_one_tendsto_half h
  norm_num at he

end
end RiemannResearch.RH.Pareto
