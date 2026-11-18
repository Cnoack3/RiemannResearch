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

private theorem periodic_loss (x : ThresholdHilbert) (u : ℕ → ℝ)
    (hs : ∀ k, 1 - hilbertSequence x k = u k) (hp : ∀ k, u (k + 60) = u k) :
    ‖hilbertOne - x‖^2 =
      ∑ r : Fin 60, progressionWeight 60 (r.val+1) * u (r.val+1)^2 := by
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
    have he : hilbertSequence (hilbertOne - x) (k+1) = u (k+1) := by
      rw [← anchoredEvaluationCLM_apply, map_sub, anchoredEvaluationCLM_apply,
        anchoredEvaluationCLM_apply, hilbertOne_sequence]
      simpa only [zeroAnchor, Nat.succ_ne_zero, if_false] using hs (k+1)
    rw [he, pow_two]

private theorem trial_loss :
    ‖hilbertOne - trial‖^2 =
      ∑ r : Fin 60, progressionWeight 60 (r.val+1) * (residual (r.val+1) : ℝ)^2 :=
  periodic_loss trial (fun k => (residual k : ℝ)) trial_sequence
    (fun k => by norm_num [residual, Nat.add_mod])

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

/-- Signed dual masses on the sixty residue classes, in units of `10⁻¹⁴`.
Their five integer moments vanish exactly. -/
private def dualNumerator : Fin 60 → ℤ :=
  ![2454118232098, -578367174501, -846261040259, 602140710457, -169993595859,
    1674163982677, -472952490236, -55309720907, -120778053865, 559910484784,
    -284481826649, 464709619357, -153741979697, -176919063861, 165296606885,
    235253352371, -130108992168, 122738539337, -167997800026, 115331751463,
    89460527658, 63468669268, -140852877409, 73115123566, 37287787270,
    20653506814, 8787349934, 41270048436, -95285474044, 113032218430,
    -13003399552, 14063955217, 5807704565, -3535696381, -20929098508,
    83330316530, -10128044891, -17277249399, -22345739405, 62106391251,
    -16580271229, 41374726540, -30943607977, -14012510142, 36070122139,
    29257068926, -33427866763, 33403386899, -25568631576, 16419667085,
    12127097752, 24064582156, -28111431991, 11748120830, 2727053613,
    13662823532, 10081409897, 5861507758, -38271669707, 45144325197]

private def dualWeight (r : Fin 60) : ℝ := (dualNumerator r : ℝ) / 10^14

private def lowerWeight (r : Fin 60) : ℚ :=
  (paretoProgressionInterval ((r.val+1 : ℕ) : ℚ) 60 4).lo

private def dualUnits (r : Fin 60) : ℤ :=
  ⌈(10^15 : ℚ) * (((dualNumerator r : ℚ)/10^14)^2 / lowerWeight r)⌉

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
-- Check the signed moments, the denominators and every outward-rounded dual cost.
private theorem dual_checks :
    (∀ i : Fin 5, (∑ r : Fin 60, dualNumerator r * (((r.val+1)%(i.val+2) : ℕ) : ℤ)) = 0) ∧
    (∑ r : Fin 60, dualNumerator r) = 3620803463690 ∧
    (∀ r : Fin 60, 0 < lowerWeight r) ∧
    (∑ r : Fin 60, dualUnits r) = 36208034636938 := by decide +kernel

private def residualFor (a : Fin 5 → ℝ) (k : ℕ) : ℝ :=
  1 - ∑ i : Fin 5, a i * ((k%(i.val+2) : ℕ) : ℝ)

private theorem dual_pairing (a : Fin 5 → ℝ) :
    (∑ r : Fin 60, dualWeight r * residualFor a (r.val+1)) = ∑ r, dualWeight r := by
  have hcol (i : Fin 5) : (∑ r : Fin 60, dualWeight r *
      (a i * (((r.val+1)%(i.val+2) : ℕ) : ℝ))) = 0 := by
    have hi : (∑ r : Fin 60, (dualNumerator r : ℝ) * (((r.val+1)%(i.val+2) : ℕ) : ℝ)) = 0 := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (dual_checks.1 i)
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero] using h
    calc
      _ = (a i / 10^14) *
          ∑ r : Fin 60, (dualNumerator r : ℝ) * (((r.val+1)%(i.val+2) : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        unfold dualWeight
        ring
      _ = 0 := by rw [hi, mul_zero]
  simp only [residualFor, mul_sub, mul_one, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [hcol, Finset.sum_const_zero, sub_zero]

private theorem dual_cost_upper (r : Fin 60) :
    dualWeight r ^ 2 / progressionWeight 60 (r.val+1) ≤ (dualUnits r : ℝ) / 10^15 := by
  have hlo : (lowerWeight r : ℝ) ≤ progressionWeight 60 (r.val+1) := by
    have h := (paretoProgressionInterval_contains ((r.val+1 : ℕ) : ℚ) 60 4
      (by positivity) (by norm_num) (by decide)).1
    rw [← paretoProgression_eq_progressionWeight]
    simpa only [lowerWeight, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_ofNat] using h
  have hpos : (0 : ℝ) < (lowerWeight r : ℝ) := by exact_mod_cast dual_checks.2.2.1 r
  have hc : ((dualNumerator r : ℚ) / 10^14)^2 / lowerWeight r ≤ (dualUnits r : ℚ) / 10^15 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 10^15)).mpr
    simpa only [dualUnits, mul_comm] using
      Int.le_ceil ((10^15 : ℚ) * (((dualNumerator r : ℚ) / 10^14)^2 / lowerWeight r))
  apply (div_le_div_of_nonneg_left (sq_nonneg _) hpos hlo).trans
  unfold dualWeight
  exact_mod_cast hc

/-- Exact dual completion for every coefficient vector in raw residue coordinates. -/
private theorem dual_completion (a : Fin 5 → ℝ) :
    (∑ r : Fin 60, progressionWeight 60 (r.val+1) * residualFor a (r.val+1)^2) =
      2*(∑ r : Fin 60, dualWeight r) -
      (∑ r : Fin 60, dualWeight r^2 / progressionWeight 60 (r.val+1)) +
      ∑ r : Fin 60, progressionWeight 60 (r.val+1) *
        (residualFor a (r.val+1) - dualWeight r / progressionWeight 60 (r.val+1))^2 := by
  rw [← dual_pairing a, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hw := progressionWeight_pos 60 (r.val+1) (by decide) (by omega)
  field_simp [hw.ne']
  ring

theorem packetMass_six_upper : packetMass 5 ≤ (963791965363138 : ℝ) / 10^15 := by
  have hx : packetCandidate 5 ∈ finiteSpace 5 := by
    rw [packetCandidate_eq_projection]
    exact (finiteSpace 5).starProjection_apply_mem _
  obtain ⟨c,hc⟩ := finiteSpace_expansion 5 _ hx
  let a (i : Fin 5) : ℝ := c i / ((i.val+2 : ℕ) : ℝ)
  have hs (k : ℕ) : 1-hilbertSequence (packetCandidate 5) k = residualFor a k := by
    rw [hc, ← anchoredEvaluationCLM_apply]
    simp only [map_sum, map_smul, smul_eq_mul, anchoredEvaluationCLM_apply,
      residueAtom, normalizedResidueHilbert_sequence]
    change 1 - (∑ i : Fin 5, c i * (((k%(i.val+2) : ℕ) : ℝ) / ((i.val+2 : ℕ) : ℝ))) = _
    unfold residualFor
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold a
    ring
  have hp (k : ℕ) : residualFor a (k+60) = residualFor a k := by
    have hd : ∀ i : Fin 5, i.val+2 ∣ 60 := by decide
    unfold residualFor
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hd i), add_zero, Nat.mod_mod]
  have hid := periodic_loss _ _ hs hp
  rw [packet_error, dual_completion] at hid
  have hsum : (∑ r : Fin 60, dualWeight r) = (3620803463690 : ℝ)/10^14 := by
    simp only [dualWeight, ← Finset.sum_div, ← Int.cast_sum, dual_checks.2.1]
    norm_num
  have hcost :
      (∑ r : Fin 60, dualWeight r^2 / progressionWeight 60 (r.val+1)) ≤
        (36208034636938 : ℝ) / 10^15 := calc
    _ ≤ ∑ r : Fin 60, (dualUnits r : ℝ) / 10^15 := Finset.sum_le_sum fun r _ => dual_cost_upper r
    _ = _ := by rw [← Finset.sum_div, ← Int.cast_sum, dual_checks.2.2.2]; norm_num
  have hrem : 0 ≤ ∑ r : Fin 60, progressionWeight 60 (r.val+1) *
      (residualFor a (r.val+1) - dualWeight r / progressionWeight 60 (r.val+1))^2 :=
    Finset.sum_nonneg fun r _ => mul_nonneg
      (progressionWeight_pos 60 (r.val+1) (by decide) (by omega)).le (sq_nonneg _)
  rw [hsum] at hid
  linarith

/-- Primal and dual rational certificates enclose the exact optimum for
conductors two through six. The interval has width 104 units of 10⁻¹⁵. -/
theorem packetMass_six_interval :
    (963791965363034 : ℝ)/10^15 ≤ packetMass 5 ∧
      packetMass 5 ≤ (963791965363138 : ℝ)/10^15 :=
  ⟨packetMass_ge_six 5 le_rfl, packetMass_six_upper⟩

end RiemannResearch.RH.RamanujanSixMass

/--
info: 'RiemannResearch.RH.RamanujanSixMass.limitEnergy_le_six' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.RamanujanSixMass.limitEnergy_le_six

/--
info: 'RiemannResearch.RH.RamanujanSixMass.packetMass_six_interval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.RamanujanSixMass.packetMass_six_interval
