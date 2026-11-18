import RiemannResearch.Analysis.ParetoProgressionCertificates
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-!
# A complete Pareto certificate for conductors two through six

The rational coefficients come from rounding a five-column Wolfram normal
solve. A rational upper enclosure on each of the sixty complete progression
masses yields a lower bound on the exact projection mass.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanSixMass
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ParetoProgressionCertificates

/-- One minus the rational trial in raw residue coordinates. -/
private def residual (k : ℕ) : ℚ :=
  1 - (43365457*((k%2 : ℕ) : ℚ) + 29484414*((k%3 : ℕ) : ℚ) + 7603448*((k%4 : ℕ) : ℚ) +
    15622522*((k%5 : ℕ) : ℚ) - 979754*((k%6 : ℕ) : ℚ) : ℚ) / 100000000

/-- Outward rounding keeps the sixty upper endpoints on a common grid. -/
private def upperUnits (r : Fin 60) : ℤ :=
  ⌈(10^15 : ℚ) * ((paretoProgressionInterval ((r.val+1 : ℕ) : ℚ) 60 4).hi * residual (r.val+1)^2)⌉

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Evaluate all sixty rational progression enclosures and their outward rounding in the kernel.
private theorem upperUnits_total :
    (∑ r : Fin 60, upperUnits r) = 36208034636966 := by decide +kernel

private def trial : ThresholdHilbert :=
  (1/100000000 : ℝ) •
    ((43365457 : ℝ) • rawResidueAtom 0 + (29484414 : ℝ) • rawResidueAtom 1 +
      (7603448 : ℝ) • rawResidueAtom 2 + (15622522 : ℝ) • rawResidueAtom 3 -
      (979754 : ℝ) • rawResidueAtom 4)

private theorem trial_mem : trial ∈ finiteSpace 5 := by
  have hm (i : Fin 5) : rawResidueAtom i.val ∈ finiteSpace 5 := by
    apply (finiteSpace 5).smul_mem
    exact Submodule.subset_span ⟨i,rfl⟩
  exact (finiteSpace 5).smul_mem _ ((finiteSpace 5).sub_mem
    ((finiteSpace 5).add_mem ((finiteSpace 5).add_mem
      ((finiteSpace 5).add_mem ((finiteSpace 5).smul_mem _ (hm 0))
        ((finiteSpace 5).smul_mem _ (hm 1))) ((finiteSpace 5).smul_mem _ (hm 2)))
      ((finiteSpace 5).smul_mem _ (hm 3))) ((finiteSpace 5).smul_mem _ (hm 4)))

private theorem trial_sequence (k : ℕ) : 1 - hilbertSequence trial k = (residual k : ℝ) := by
  rw [← anchoredEvaluationCLM_apply]
  simp only [trial, map_smul, map_sub, map_add, smul_eq_mul, anchoredEvaluationCLM_apply,
    rawResidueAtom_sequence, residue, Nat.reduceAdd]
  unfold residual
  push_cast
  ring

private theorem trial_loss :
    ‖hilbertOne - trial‖^2 =
      ∑ r : Fin 60, progressionWeight 60 (r.val+1) * (residual (r.val+1) : ℝ)^2 := by
  let u (k : ℕ) : ℝ := residual k
  have hp (k : ℕ) : u (k+60) = u k := by norm_num [u, residual, Nat.add_mod]
  have hu (k : ℕ) : |u k| ≤ ∑ r : Fin 60, |u r.val| := by
    let r : Fin 60 := ⟨k%60, Nat.mod_lt k (by decide)⟩
    have he : u k = u r.val := by
      simpa only [Nat.mod_add_div, r] using periodic_add_mul 60 u hp (k%60) (k/60)
    rw [he]
    exact Finset.single_le_sum (f := fun i : Fin 60 => |u i.val|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ r)
  rw [← periodic_paretoInner 60 (by decide) u hu hp, hilbert_norm_weighted_sq]
  unfold paretoInner
  apply tsum_congr
  intro k
  cases k with
  | zero => simp [positiveWeight]
  | succ k =>
    have he : hilbertSequence (hilbertOne - trial) (k+1) = u (k+1) := by
      rw [← anchoredEvaluationCLM_apply, map_sub, anchoredEvaluationCLM_apply,
        anchoredEvaluationCLM_apply, hilbertOne_sequence]
      simpa only [zeroAnchor, Nat.succ_ne_zero, if_false] using trial_sequence (k+1)
    rw [he, pow_two]

private theorem row_upper (r : Fin 60) :
    progressionWeight 60 (r.val+1) * (residual (r.val+1) : ℝ)^2 ≤
      (upperUnits r : ℝ) / 10^15 := by
  let I := paretoProgressionInterval ((r.val+1 : ℕ) : ℚ) 60 4
  have hm : progressionWeight 60 (r.val+1) ≤ (I.hi : ℝ) := by
    have h := (paretoProgressionInterval_contains ((r.val+1 : ℕ) : ℚ) 60 4
      (by positivity) (by norm_num) (by decide)).2
    rw [← paretoProgression_eq_progressionWeight]
    simpa only [Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_ofNat, I] using h
  have hc : I.hi * residual (r.val+1)^2 ≤ (upperUnits r : ℚ) / 10^15 := by
    apply (le_div_iff₀ (by norm_num : (0:ℚ) < 10^15)).mpr
    simpa only [upperUnits, I, Nat.cast_add, Nat.cast_one, mul_comm] using
      Int.le_ceil ((10^15 : ℚ) * (I.hi * residual (r.val+1)^2))
  exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans (by exact_mod_cast hc)

private theorem trial_loss_upper :
    ‖hilbertOne - trial‖^2 ≤ (36208034636966 : ℝ) / 10^15 := calc
  _ = _ := trial_loss
  _ ≤ ∑ r : Fin 60, (upperUnits r : ℝ) / 10^15 := Finset.sum_le_sum fun r _ => row_upper r
  _ = _ := by rw [← Finset.sum_div, ← Int.cast_sum, upperUnits_total]; norm_num

/-- A rational certificate on all sixty complete progressions persists at
every larger stage of the Pareto/von Mangoldt normal equations. -/
theorem packetMass_ge_six (n : ℕ) (hn : 5 ≤ n) :
    (963791965363034 : ℝ) / 10^15 ≤ packetMass n := by
  have hm : trial ∈ Submodule.span ℝ
      (Set.range (fun i : Fin 5 => ramanujanPacketHilbert (i.val+2))) := by
    rw [finitePacket_span_eq]
    exact trial_mem
  rw [← Fintype.range_linearCombination] at hm
  obtain ⟨a,ha⟩ := hm
  have he := packet_completion 5 a
  rw [ha] at he
  have hs := sq_nonneg ‖Fintype.linearCombination ℝ
    (fun i : Fin 5 => ramanujanPacketHilbert (i.val+2)) (a-packetCoefficients 5)‖
  apply le_trans _ (packetMass_monotone hn)
  linarith [trial_loss_upper]

theorem limitEnergy_le_six : limitEnergy ≤ (36208034636966 : ℝ) / 10^15 := by
  have h : (963791965363034 : ℝ) / 10^15 ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto (eventually_atTop.2 ⟨5,fun n hn => packetMass_ge_six n hn⟩)
  linarith

/-- Every remaining Schur gain and the terminal defect share the same budget. -/
theorem remaining_gain_identity (n : ℕ) :
    limitEnergy + (∑' j : ℕ, packetGain (j+n)) = 1 - packetMass n := by
  have hp (k : ℕ) : ∑ j ∈ Finset.range k, packetGain j = packetMass k := by
    induction k with
    | zero => simp [packetMass]
    | succ k ih => rw [Finset.sum_range_succ, ih, packetGain]; ring
  have h := packetGain_hasSum.summable.sum_add_tsum_nat_add n
  rw [hp, packetGain_hasSum.tsum_eq] at h
  linarith

theorem remaining_schur_budget (n : ℕ) (hn : 5 ≤ n) :
    limitEnergy + (∑' j : ℕ, packetGain (j+n)) ≤ (36208034636966 : ℝ) / 10^15 := by
  rw [remaining_gain_identity]
  linarith [packetMass_ge_six n hn]

end RiemannResearch.RH.RamanujanSixMass

/--
info: 'RiemannResearch.RH.RamanujanSixMass.limitEnergy_le_six' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.RamanujanSixMass.limitEnergy_le_six
