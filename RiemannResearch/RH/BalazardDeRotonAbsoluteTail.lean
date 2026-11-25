import RiemannResearch.RH.BalazardDeRotonNaturalTail
import RiemannResearch.RH.DampedMobiusHeadApproximation

/-! # An explicit natural reciprocal-zeta tail in absolute convergence

The same Dirichlet-series tail majorant applies at every ordinate.
After integration the prefactor is the exact physical fractional-part
energy. The saving degenerates as the damping decreases to one half. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.Pareto.BalazardDeRoton

set_option maxHeartbeats 1200000 in
-- Comparing the shifted Dirichlet series and its complex norm tail needs extra reductions.
/-- Uniform in the imaginary part, on every line of absolute convergence. -/
theorem polynomial_reciprocal_error_le (d : ℝ) (s : ℂ) (hs : 1 < d+s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖(riemannZeta (s+(d:ℂ)))⁻¹-polynomial d N s‖ ≤
      (N:ℝ) ^ (1-(d+s.re)) / (d+s.re-1) := by
  let f := LSeries.term (fun n => (dampedMobiusWeight d n : ℂ)) s
  let a (m:ℕ) := f (m+1)
  have h := dampedMobiusWeight_LSeriesHasSum (ε := d) (s := s)
    (by simpa [add_comm] using hs)
  change HasSum f _ at h
  have ha : HasSum a (riemannZeta (s+(d:ℂ)))⁻¹ := by
    apply (hasSum_nat_add_iff (f := f) 1).mpr
    simpa [f,LSeries.term_zero] using h
  have he (N:ℕ) : polynomial d N s = ∑ m ∈ Finset.range N, a m := by
    apply Finset.sum_congr rfl
    intro m _
    rw [show a m = LSeries.term (fun n => (dampedMobiusWeight d n : ℂ)) s (m+1) by rfl,
      LSeries.term_of_ne_zero (Nat.succ_ne_zero m),div_eq_mul_inv,Complex.cpow_neg]
  let b (m:ℕ) := ((m+1:ℕ):ℝ)^(-(d+s.re))
  have hp : Summable (fun m : ℕ => (m:ℝ)^(-(d+s.re))) := Real.summable_nat_rpow.mpr (by linarith)
  have hb : Summable b := (summable_nat_add_iff (f := fun m : ℕ => (m:ℝ)^(-(d+s.re))) 1).mpr hp
  have hab (m:ℕ) : ‖a m‖ ≤ b m := by
    have hm : (0:ℝ) < ((m+1:ℕ):ℝ) := by positivity
    have hmu : ‖(ArithmeticFunction.moebius (m+1) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m+1)
    rw [show a m = LSeries.term (fun n => (dampedMobiusWeight d n : ℂ)) s (m+1) by rfl,
      dampedMobiusWeight_LSeries_term, norm_div]
    have hn : ‖((m+1:ℕ):ℂ)^(s+(d:ℂ))‖ = ((m+1:ℕ):ℝ)^(d+s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m),Complex.add_re,Complex.ofReal_re,add_comm]
    rw [hn]
    exact (div_le_div_of_nonneg_right hmu (Real.rpow_nonneg hm.le _)).trans_eq
      (by dsimp only [b];rw [Real.rpow_neg hm.le,one_div])
  have hn : Summable (fun m => ‖a m‖) := hb.of_nonneg_of_le (fun _ => norm_nonneg _) hab
  have ht : (∑' j : ℕ, a (j+N)) =
      (riemannZeta (s+(d:ℂ)))⁻¹ - ∑ m ∈ Finset.range N, a m :=
    ((hasSum_nat_add_iff' (f := a) N).mpr ha).tsum_eq
  rw [he,←ht]
  calc
    _ ≤ ∑' j : ℕ, ‖a (j+N)‖ := norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr hn)
    _ ≤ ∑' j : ℕ, b (j+N) := ((summable_nat_add_iff (f := fun m => ‖a m‖) N).mpr hn).tsum_le_tsum
      (fun j => hab (j+N)) ((summable_nat_add_iff (f := b) N).mpr hb)
    _ ≤ _ := Real.tsum_nat_rpow_tail_le hs hN

/-- Complete angular energy of the natural tail, with an explicit cutoff rate. -/
theorem natural_tail_energy_of_half_lt {d : ℝ} (hd : 1/2 < d) {N : ℕ} (hN : 1 ≤ N) :
    lineEnergy (fun t => naturalTruncationTail d N (criticalPoint t)) ≤
      ((N:ℝ)^(1/2-d)/(d-1/2))^2 * (Real.log (2*Real.pi)-Real.eulerMascheroniConstant) := by
  let B := (N:ℝ)^(1/2-d)/(d-1/2)
  let f (t:ℝ) := riemannZeta (criticalPoint t) / criticalPoint t
  have hf : Integrable (fun t => ‖f t‖^2) :=
    (memLp_two_iff_integrable_sq_norm zeta_div_criticalPoint_memLp.1).mp zeta_div_criticalPoint_memLp
  have b (t:ℝ) : ‖(riemannZeta (criticalPoint t+(d:ℂ)))⁻¹-polynomial d N (criticalPoint t)‖ ≤ B := by
    have h := polynomial_reciprocal_error_le d (criticalPoint t) (by rw [criticalPoint_re]; linarith) hN
    rwa [criticalPoint_re,show 1-(d+1/2)=1/2-d by ring,show d+1/2-1=d-1/2 by ring] at h
  have hI : (∫ t, ‖naturalTruncationTail d N (criticalPoint t)‖^2) ≤ ∫ t, B^2*‖f t‖^2 := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) (hf.const_mul _) (Eventually.of_forall _)
    intro t
    change ‖naturalTruncationTail d N (criticalPoint t)‖^2 ≤ B^2 * ‖f t‖^2
    rw [naturalTruncationTail,norm_mul,mul_pow,mul_comm (B^2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (b t) 2) (sq_nonneg _)
  rw [integral_const_mul] at hI
  have hval := RiemannResearch.RH.PrimeTreeScalingEnergy.critical_integral
  change (∫ t, ‖f t‖^2) = _ at hval
  rw [hval] at hI
  apply (mul_le_mul_of_nonneg_left hI (show 0 ≤ 1/(2*Real.pi) by positivity)).trans_eq
  change 1/(2*Real.pi) * (B^2 * (2*Real.pi * _)) = B^2 * _
  field_simp [ne_of_gt Real.pi_pos]

theorem natural_tail_energy_tendsto_of_half_lt {d : ℝ} (hd : 1/2 < d) :
    Tendsto (fun N => lineEnergy (fun t => naturalTruncationTail d N (criticalPoint t)))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hd)).comp tendsto_natCast_atTop_atTop
  have hz := ((h.div_const (d-1/2)).pow 2).mul_const (Real.log (2*Real.pi)-Real.eulerMascheroniConstant)
  apply squeeze_zero' (Eventually.of_forall fun n => show 0 ≤ lineEnergy _ from
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
    ((eventually_ge_atTop 1).mono fun N hN => natural_tail_energy_of_half_lt hd hN)
  simpa only [Function.comp_apply,neg_sub,zero_div,zero_pow (by decide : 2 ≠ 0),zero_mul] using hz

/-- At every positive cutoff the whole natural tail is square-integrable. -/
theorem naturalTruncationTail_memLp_of_half_lt {d : ℝ} (hd : 1/2 < d) {N : ℕ} (hN : 1 ≤ N) :
    MemLp (fun t => naturalTruncationTail d N (criticalPoint t)) 2 := by
  let B := (N:ℝ)^(1/2-d)/(d-1/2)
  have hB : 0 ≤ B := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith)
  have hcp : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  have hr t : 1 < (criticalPoint t+(d:ℂ)).re := by rw [Complex.add_re,criticalPoint_re,Complex.ofReal_re];linarith
  have hne t : criticalPoint t+(d:ℂ) ≠ 1 := fun h => by have := hr t;rw [h,Complex.one_re] at this;linarith
  have hden : Continuous (fun t => riemannZeta (criticalPoint t+(d:ℂ))) := continuous_iff_continuousAt.mpr
    fun t => (differentiableAt_riemannZeta (hne t)).continuousAt.comp (x := t) (hcp.add continuous_const).continuousAt
  have hnum : Continuous (fun t => polynomial d N (criticalPoint t)) := by
    unfold polynomial
    apply continuous_finsetSum
    intro m _
    rw [show (fun t => (dampedMobiusWeight d (m+1):ℂ)*((m+1:ℕ):ℂ)^(-criticalPoint t)) =
      fun t => (dampedMobiusWeight d (m+1):ℂ)*Complex.exp (Complex.log ((m+1:ℕ):ℂ)*(-criticalPoint t)) by
      funext t;rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero m)]]
    fun_prop
  have hsub := (hden.inv₀ fun t => riemannZeta_ne_zero_of_one_le_re (hr t).le).sub hnum
  let Z (t:ℝ) := riemannZeta (criticalPoint t)/criticalPoint t
  have hZ : MemLp Z 2 := zeta_div_criticalPoint_memLp
  apply (hZ.norm.const_mul B).mono (hZ.1.mul hsub.aestronglyMeasurable) (Filter.Eventually.of_forall _)
  intro t
  have h := polynomial_reciprocal_error_le d (criticalPoint t) (by rw [criticalPoint_re];linarith) hN
  rw [criticalPoint_re,show 1-(d+1/2)=1/2-d by ring,show d+1/2-1=d-1/2 by ring] at h
  change ‖Z t * _‖ ≤ ‖B*‖Z t‖‖
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hB (norm_nonneg _)),mul_comm B]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

end RiemannResearch.RH.Pareto.BalazardDeRoton

namespace RiemannResearch.RH.Pareto.BalazardDeRoton

/--
info: 'RiemannResearch.RH.Pareto.BalazardDeRoton.natural_tail_energy_tendsto_of_half_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms natural_tail_energy_tendsto_of_half_lt

end RiemannResearch.RH.Pareto.BalazardDeRoton

namespace RiemannResearch.RH.Pareto.BalazardDeRoton

/--
info: 'RiemannResearch.RH.Pareto.BalazardDeRoton.naturalTruncationTail_memLp_of_half_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms naturalTruncationTail_memLp_of_half_lt

end RiemannResearch.RH.Pareto.BalazardDeRoton
