import RiemannResearch.RH.PrimeTreeCriticalPlancherel
import RiemannResearch.Analysis.BoundedPrimitiveAbel
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal
import RiemannResearch.RH.DampedMobiusMetricDiscrepancy
import RiemannResearch.RH.BalazardDeRotonCriticalEnergy

/-! # The finite reciprocal charge as damping tends to zero

The PNT controls the signed undamped prefixes. Finite Abel summation gives a
bound uniform over the positive damping and the later cutoff. Consequently
the actual reciprocal charge tends to zero on every schedule of cutoffs
tending to infinity. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.BalazardDeRoton

theorem realCharge_zero_damping (N : ℕ) : realCharge 0 N = mobiusReciprocalSum N := by
  induction N with
  | zero => simp [realCharge, mobiusReciprocalSum]
  | succ n ih =>
    rw [mobiusReciprocalSum_succ, ← ih]
    simp [realCharge, Finset.sum_range_succ]

private theorem continuous_charge_at_fixed_cutoff (N : ℕ) : Continuous (fun ε => realCharge ε N) := by
  unfold realCharge
  apply continuous_finsetSum
  intro m _
  have hpos : 0 < ((m+1 : ℕ) : ℝ) := by positivity
  exact (continuous_const.mul ((Real.continuous_const_rpow hpos.ne').comp continuous_neg)).div_const _

/-- All later damped charges are close to the base charge whenever all later
undamped signed reciprocal prefixes are small. -/
theorem realCharge_tail_le {M N : ℕ} (hMN : M ≤ N) {ε C : ℝ} (he : 0 ≤ ε)
    (hC : ∀ m ≥ M, |mobiusReciprocalSum m| ≤ C) :
    |realCharge ε N - realCharge ε M| ≤ 2*C := by
  let B := fun k : ℕ => mobiusReciprocalSum (M+k) + C
  let f := fun k : ℕ => ((M+k+1 : ℕ) : ℝ)^(-ε)
  have hb (k : ℕ) : 0 ≤ B k ∧ B k ≤ 2*C := by
    obtain ⟨h1,h2⟩ := abs_le.mp (hC (M+k) (by omega))
    dsimp [B]
    constructor <;> linarith
  have hf (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hm : Antitone f := by
    intro a b hab
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    exact_mod_cast (show M+a+1 ≤ M+b+1 by omega)
  have h0 : f 0 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by dsimp [f]; exact_mod_cast (show 1 ≤ M+0+1 by omega)) (by linarith)
  have hbound := RiemannResearch.Analysis.boundedPrimitive_weighted_interval_bound B f (2*C) (N-M) hb hf hm
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC M le_rfl)
  have heq : N = M+(N-M) := by omega
  have heq' : realCharge ε N - realCharge ε M =
      ∑ k ∈ Finset.range (N-M), (B (k+1)-B k) * f k := by
    conv_lhs => lhs; rw [heq]
    rw [realCharge, Finset.sum_range_add, ← realCharge, add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro m _
    dsimp [B, f, dampedMobiusWeight]
    rw [show M+(m+1) = (M+m)+1 by omega, mobiusReciprocalSum_succ]
    ring
  rw [heq']
  exact hbound.trans (mul_le_of_le_one_right (by linarith : 0 ≤ 2*C) h0)

/-- Joint damping and cutoff limit, with no lower bound on their relative rate. -/
theorem realCharge_tendsto_of_cutoff_tendsto (N : ℝ → ℕ)
    (hN : Tendsto N (𝓝[>] (0:ℝ)) atTop) :
    Tendsto (fun ε => realCharge ε (N ε)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hm := mobiusReciprocalSum_tendsto_zero.abs.eventually_lt_const (show |(0:ℝ)| < δ/5 by simpa using (show 0 < δ/5 by positivity))
  obtain ⟨M,hM⟩ := eventually_atTop.1 hm
  have hc : Tendsto (fun ε => realCharge ε M) (𝓝[>] (0:ℝ)) (𝓝 (realCharge 0 M)) :=
    ((continuous_charge_at_fixed_cutoff M).tendsto 0).mono_left nhdsWithin_le_nhds
  have hnear := (Metric.tendsto_nhds.mp hc) (δ/5) (by positivity)
  filter_upwards [hN.eventually (eventually_ge_atTop M), hnear,
    (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε)] with ε hMN hfix he
  change 0 < ε at he
  change dist (realCharge ε M) (realCharge 0 M) < δ/5 at hfix
  have htail := realCharge_tail_le hMN he.le (fun m hm => (hM m hm).le)
  rw [Real.dist_eq, realCharge_zero_damping] at hfix
  rw [Real.dist_eq, sub_zero]
  have hab := abs_add_le (realCharge ε (N ε)-realCharge ε M)
    (realCharge ε M-mobiusReciprocalSum M)
  have hab' := abs_add_le (realCharge ε (N ε)-mobiusReciprocalSum M) (mobiusReciprocalSum M)
  simp only [sub_add_sub_cancel, sub_add_cancel] at hab hab'
  linarith only [hδ, hfix, htail, hab, hab', hM M le_rfl]

theorem charge_tendsto_of_cutoff_tendsto (N : ℝ → ℕ)
    (hN : Tendsto N (𝓝[>] (0:ℝ)) atTop) :
    Tendsto (fun ε => charge ε (N ε)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have he (ε : ℝ) (n : ℕ) : charge ε n = (realCharge ε n : ℂ) := by
    simp [charge, realCharge]
  simp_rw [he]
  simpa only [Complex.ofReal_zero, Function.comp_def] using
    (Complex.continuous_ofReal.tendsto 0).comp (realCharge_tendsto_of_cutoff_tendsto N hN)

/-- The natural reciprocal-zeta truncation in the continuous criterion. -/
def naturalTruncationTail (ε : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s / s * ((riemannZeta (s + ε))⁻¹ - polynomial ε N s)

/-- The finite exterior charge has this exact critical-line energy. -/
theorem corrected_natural_tail_distance (ε : ℝ) (N : ℕ) :
    lineEnergy (fun t => correctedTail ε N (criticalPoint t) -
      naturalTruncationTail ε N (criticalPoint t)) =
      ‖charge ε N‖^2 * (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) := by
  have he (t : ℝ) : correctedTail ε N (criticalPoint t) - naturalTruncationTail ε N (criticalPoint t) =
      charge ε N * (riemannZeta (criticalPoint t) / criticalPoint t) := by
    unfold correctedTail naturalTruncationTail
    ring
  unfold lineEnergy
  simp_rw [he, norm_mul, mul_pow]
  rw [MeasureTheory.integral_const_mul]
  change _ * (_ * (∫ t:ℝ, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I) / ((1/2:ℂ) + (t:ℂ)*Complex.I)‖^2)) = _
  rw [RiemannResearch.RH.PrimeTreeScalingEnergy.critical_integral]
  field_simp [Real.pi_ne_zero]

/-- The continuous and discrete truncation tails approach each other in full
critical-line energy along every divergent cutoff schedule, unconditionally. -/
theorem corrected_natural_tail_distance_tendsto (N : ℝ → ℕ)
    (hN : Tendsto N (𝓝[>] (0:ℝ)) atTop) :
    Tendsto (fun ε => lineEnergy (fun t => correctedTail ε (N ε) (criticalPoint t) -
      naturalTruncationTail ε (N ε) (criticalPoint t))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simp_rw [corrected_natural_tail_distance]
  simpa using ((charge_tendsto_of_cutoff_tendsto N hN).norm.pow 2).mul_const
    (Real.log (2*Real.pi)-Real.eulerMascheroniConstant)

end RiemannResearch.RH.Pareto.BalazardDeRoton

namespace RiemannResearch.RH.Pareto.BalazardDeRoton

/--
info: 'RiemannResearch.RH.Pareto.BalazardDeRoton.corrected_natural_tail_distance_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms corrected_natural_tail_distance_tendsto

end RiemannResearch.RH.Pareto.BalazardDeRoton
