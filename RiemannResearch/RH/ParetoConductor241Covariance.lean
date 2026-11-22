import RiemannResearch.RH.ParetoGroupedResidueMass
import RiemannResearch.RH.ParetoRawTrialPeriodicTail

/-! # Signed tail of the conductor-241 residue trial

The same 147 coefficients and the same 65,536 rounded head terms are used
throughout. The cross terms of the residual square enter with their signs. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.GroupedResidueMass.Conductor241
open Pareto Pareto.CoefficientStabilization
open RamanujanResidueMass.Certificate (signal)

private def support : Finset ℕ := (rows.map Prod.fst).toFinset
private def coefficient (d : ℕ) : ℤ := (rows.lookup d).getD 0

private theorem sum_by_rows (l : List (ℕ × ℤ)) (c : ℕ → ℤ) (f : ℕ → ℤ → ℤ)
    (hn : (l.map Prod.fst).Nodup) (hc : ∀ t ∈ l, c t.1 = t.2) :
    ∑ d ∈ (l.map Prod.fst).toFinset, f d (c d) =
      (l.map (fun t => f t.1 t.2)).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    obtain ⟨d, a⟩ := t
    obtain ⟨hd, htail⟩ := List.nodup_cons.mp hn
    have hd' : d ∉ (l.map Prod.fst).toFinset := by simpa using hd
    have ha : c d = a := hc (d, a) (by simp)
    have ht := ih htail (fun t h => hc t (by simp [h]))
    simp only [List.map_cons, List.toFinset_cons, Finset.sum_insert hd',
      List.sum_cons, ha, ht]

set_option maxRecDepth 100000 in
private theorem unique_rows : (rows.map Prod.fst).Nodup ∧
    ∀ t ∈ rows, coefficient t.1 = t.2 := by decide +kernel

private theorem sum_support (f : ℕ → ℤ → ℤ) :
    ∑ d ∈ support, f d (coefficient d) = (rows.map (fun t => f t.1 t.2)).sum :=
  sum_by_rows rows coefficient f unique_rows.1 unique_rows.2

private theorem signal_list (l : List (ℕ × ℤ)) (k : ℕ) :
    signal l k = (l.map (fun t => t.2 * ((k % t.1 : ℕ) : ℤ))).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => cases t; simp [signal, ih]

private theorem raw_error (k : ℕ) :
    RawTrialTail.error support (fun d => (coefficient d : ℝ)) 1000000 k =
      (ParetoRawTrial.difference rows k : ℝ) := by
  have hs := (sum_support (fun d z => z * ((k % d : ℕ) : ℤ))).trans (signal_list rows k).symm
  have hr := congrArg (fun x : ℤ => (x : ℝ)) hs
  simpa only [RawTrialTail.error, ParetoRawTrial.difference, residue, Int.cast_sum,
    Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_ofNat] using
    congrArg (fun y : ℝ => 1000000-y) hr

private theorem raw_head :
    (∑ k ∈ Finset.range 65536, positiveWeight (k+1) *
      (RawTrialTail.error support (fun d => (coefficient d : ℝ)) 1000000 (k+1))^2) ≤
      8592966019 := by
  have h := ParetoRawTrial.rounded_head_loss_upper rows 512
  have hU : (∑ j ∈ Finset.range 512, ParetoRawTrial.block rows j) = 8592966019 :=
    head_units_total
  rw [hU, show (512 * 128 : ℕ) = 65536 by decide] at h
  simp only [div_pow, ← mul_div_assoc, ← Finset.sum_div] at h
  simp only [raw_error]
  norm_num at h
  linarith only [h]

private def pairTerm (d : ℕ) (z : ℤ) (e : ℕ) (w : ℤ) : ℤ :=
  z * w * (((d.gcd e : ℕ) : ℤ)^2-1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The kernel reduces all 147 by 147 signed covariance entries.
private theorem signed_covariance :
    (∑ d ∈ support, ∑ e ∈ support, pairTerm d (coefficient d) e (coefficient e)) =
      5241591082916 := by
  simp_rw [sum_support (pairTerm _ _)]
  rw [sum_support (fun d z => (rows.map (fun t => pairTerm d z t.1 t.2)).sum)]
  decide +kernel

/-- Upper bound on the squared distance from the constant to the closed residue span. -/
theorem limitEnergy_le_conductor_241_covariance :
    limitEnergy ≤ (2093945167971946997 : ℝ)/238620217000000000000 := by
  let c := fun d => (coefficient d : ℝ)
  have hmZ : (∑ d ∈ support, coefficient d*((d : ℤ)-1)) = 2015268 := by
    rw [sum_support (fun d z => z*((d : ℤ)-1))]
    decide +kernel
  have haZ : (∑ d ∈ support, |coefficient d| * (d : ℤ)*((d : ℤ)-1)) = 2456298660 := by
    rw [sum_support (fun d z => |z| * (d : ℤ)*((d : ℤ)-1))]
    decide +kernel
  have hm : RawTrialTail.mean support c 1000000 = -7634 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hmZ
    simp at h
    unfold RawTrialTail.mean c
    linarith only [h]
  have ha : RawTrialTail.amplitude support c = 2456298660 := by
    simpa [RawTrialTail.amplitude, c] using congrArg (fun z : ℤ => (z : ℝ)) haZ
  have hg : RawTrialTail.gcdEnergy support c = 5241591082916 := by
    simpa [RawTrialTail.gcdEnergy, pairTerm, c] using
      congrArg (fun z : ℤ => (z : ℝ)) signed_covariance
  have hs (d : ℕ) (hd : d ∈ support) : 2 ≤ d := by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact (rows_range t ht).1
  have h := RawTrialTail.limitEnergy_le_of_head support c 1000000 _ 65536 (by norm_num) hs raw_head
  unfold RawTrialTail.uniformSquare RawTrialTail.discrepancy at h
  rw [hm, ha, hg] at h
  norm_num at h ⊢
  exact h

/-- Squared error of the normalized screened parity vector in the full Pareto norm. -/
theorem screenedTwo_squared_distance_le_covariance :
    ‖hilbertOne - PrimePowerSchur.normalizedScreenedTwo‖^2 ≤
      (2093945167971946997 : ℝ)/236526271832028053003 := by
  rw [norm_sub_rev, PrimePowerSchur.normalizedScreenedTwo_error_sq_eq_limitEnergy]
  apply (div_le_div_iff₀ (by linarith [limitEnergy_le_conductor_241_covariance] :
    0 < 1 - limitEnergy) (by norm_num : (0:ℝ) < 236526271832028053003)).mpr
  linarith only [limitEnergy_le_conductor_241_covariance]

end RiemannResearch.RH.GroupedResidueMass.Conductor241
