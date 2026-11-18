import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanResidueMassData
import RiemannResearch.RH.ParetoHiddenNoiseMoments
import Mathlib.Tactic

/-!
# A complete physical upper bound on the Pareto residual

An integer combination of raw residues through conductor 124 is tested on
the first 32768 positive sites. A uniform range estimate and the exact
Pareto tail probability enclose all remaining terms.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanResidueMass
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer Certificate

private def lo (s : List (ℕ × ℤ)) : ℤ :=
  (s.map fun t => min 0 (t.2 * ((t.1-1 : ℕ) : ℤ))).sum

private def hi (s : List (ℕ × ℤ)) : ℤ :=
  (s.map fun t => max 0 (t.2 * ((t.1-1 : ℕ) : ℤ))).sum

private theorem signal_bounds (s : List (ℕ × ℤ))
    (hs : ∀ t ∈ s, 2 ≤ t.1) (k : ℕ) : lo s ≤ signal s k ∧ signal s k ≤ hi s := by
  induction s with
  | nil => simp [lo, hi, signal]
  | cons t s ih =>
    obtain ⟨d,z⟩ := t
    have hd : 2 ≤ d := hs (d,z) (by simp)
    have hh := ih (fun t ht => hs t (by simp [ht]))
    have hmod : (0 : ℤ) ≤ ((k%d : ℕ) : ℤ) := by positivity
    have hmax : ((k%d : ℕ) : ℤ) ≤ ((d-1 : ℕ) : ℤ) := by
      exact_mod_cast (show k%d ≤ d-1 by have := Nat.mod_lt k (by omega : 0<d); omega)
    have h0 : (0 : ℤ) ≤ ((d-1 : ℕ) : ℤ) := by positivity
    have hrow : min 0 (z*((d-1 : ℕ) : ℤ)) ≤ z*((k%d : ℕ) : ℤ) ∧
        z*((k%d : ℕ) : ℤ) ≤ max 0 (z*((d-1 : ℕ) : ℤ)) := by
      rcases le_total 0 z with hz | hz
      · exact ⟨(min_le_left _ _).trans (mul_nonneg hz hmod),
          (mul_le_mul_of_nonneg_left hmax hz).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hmax hz),
          (mul_nonpos_of_nonpos_of_nonneg hz hmod).trans (le_max_left _ _)⟩
    exact ⟨add_le_add hrow.1 hh.1, add_le_add hrow.2 hh.2⟩

private theorem rows_range : ∀ t ∈ rows, 2 ≤ t.1 ∧ t.1 ≤ 124 := by decide

private theorem scaled_abs_bound (k : ℕ) : |difference k| ≤ 7063991 := by
  have h := signal_bounds rows (fun t ht => (rows_range t ht).1) k
  have hlo : lo rows = -6063991 := by decide
  have hhi : hi rows = 8063935 := by decide
  rw [hlo,hhi] at h
  unfold difference
  rw [abs_le]
  omega

private def synthesis : List (ℕ × ℤ) → ThresholdHilbert
  | [] => 0
  | (d,z)::s => (z : ℝ) • rawResidueAtom (d-2) + synthesis s

private theorem synthesis_spec (n : ℕ) (s : List (ℕ × ℤ))
    (hs : ∀ t ∈ s, 2 ≤ t.1 ∧ t.1 ≤ n + 1) :
    synthesis s ∈ finiteSpace n ∧ ∀ k, hilbertSequence (synthesis s) k = (signal s k : ℝ) := by
  induction s with
  | nil =>
    refine ⟨(finiteSpace n).zero_mem,fun k => ?_⟩
    simp [synthesis, signal, ← anchoredEvaluationCLM_apply]
  | cons t s ih =>
    obtain ⟨d,z⟩ := t
    have hd : 2 ≤ d ∧ d ≤ n+1 := hs (d,z) (by simp)
    obtain ⟨hm,hk⟩ := ih (fun t ht => hs t (by simp [ht]))
    have hr : rawResidueAtom (d-2) ∈ finiteSpace n := by
      apply (finiteSpace n).smul_mem
      exact Submodule.subset_span ⟨⟨d-2,by omega⟩,rfl⟩
    refine ⟨(finiteSpace n).add_mem ((finiteSpace n).smul_mem _ hr) hm,?_⟩
    intro k
    rw [synthesis, ← anchoredEvaluationCLM_apply, map_add, map_smul, smul_eq_mul,
      anchoredEvaluationCLM_apply, anchoredEvaluationCLM_apply, rawResidueAtom_sequence, hk]
    simp only [signal, Int.cast_add, Int.cast_mul, Int.cast_natCast, residue,
      show d-2+2=d by omega]

private theorem head_split (K : ℕ) :
    (∑ k ∈ Finset.range (K*128), headUnit k) = ∑ j ∈ Finset.range K, block j := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ block K]
    simp only [Certificate.block]

private def lossTerm (k : ℕ) : ℝ :=
  positiveWeight (k+1) * ((difference (k+1) : ℝ)/1000000)^2

private theorem head_bound (k : ℕ) :
    lossTerm k ≤ (headUnit k : ℝ)/10^12 := by
  let a := (difference (k+1)).natAbs
  let b := (k+1)*(k+2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hi : a^2 ≤ b * headUnit k := (Nat.lt_mul_div_succ (a^2) hb).le
  have hreal : (a:ℝ)^2 ≤ ((k:ℝ)+1)*((k:ℝ)+2)*(headUnit k : ℝ) := by
    exact_mod_cast hi
  have ha : (a:ℝ)^2 = (difference (k+1) : ℝ)^2 := by
    have hz := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (difference (k+1)))
    have hr : (a:ℝ) = |(difference (k+1) : ℝ)| := by
      simpa only [a, Int.cast_natCast, Int.cast_abs] using hz
    rw [hr,sq_abs]
  rw [ha] at hreal
  unfold lossTerm positiveWeight
  push_cast
  have h1 : 0 < (k:ℝ)+1 := by positivity
  have h2 : 0 < (k:ℝ)+1+1 := by positivity
  field_simp [h1.ne',h2.ne']
  nlinarith [hreal]

private theorem complete_trial_upper :
    ‖hilbertOne - (1/1000000 : ℝ) • synthesis rows‖^2 ≤
      (36740218801559 : ℝ)/2979000000000000 := by
  let B : ℝ := (7063991/1000000 : ℝ)^2
  have hb (k : ℕ) : |((difference k : ℝ)/1000000)^2| ≤ B := by
    have hh : |(difference k : ℝ)| ≤ 7063991 := by exact_mod_cast scaled_abs_bound k
    rw [abs_of_nonneg (sq_nonneg _), div_pow]
    dsimp [B]
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hsum : Summable lossTerm :=
    (weighted_summable_of_bounded hb).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have he : ‖hilbertOne - (1/1000000 : ℝ) • synthesis rows‖^2 = ∑' k, lossTerm k := by
    rw [hilbert_norm_weighted_sq]
    have hseq (k : ℕ) : hilbertSequence
        (hilbertOne - (1/1000000 : ℝ) • synthesis rows) (k+1) =
        (difference (k+1) : ℝ)/1000000 := by
      rw [← anchoredEvaluationCLM_apply, map_sub, map_smul, smul_eq_mul,
        anchoredEvaluationCLM_apply, anchoredEvaluationCLM_apply, hilbertOne_sequence,
        (synthesis_spec 123 rows rows_range).2]
      simp only [zeroAnchor, Nat.succ_ne_zero, if_false, difference, Int.cast_sub, Int.cast_ofNat]
      ring
    rw [((hilbertSequence_square_summable _).tsum_eq_zero_add)]
    simp only [positiveWeight, Nat.cast_zero, zero_mul, div_zero, zero_add]
    apply tsum_congr
    intro k
    rw [hseq]
    rfl
  have hhead : (∑ k ∈ Finset.range 32768, lossTerm k) ≤ (10810291372 : ℝ)/10^12 := calc
    _ ≤ ∑ k ∈ Finset.range 32768, (headUnit k : ℝ)/10^12 :=
      Finset.sum_le_sum fun k _ => head_bound k
    _ = _ := by
      rw [← Finset.sum_div, ← Nat.cast_sum,
        show 32768 = 256*128 by decide, head_split, head_units_total]
      norm_num
  have hw : Summable (fun j : ℕ => positiveWeight (j+32769)) :=
    positiveWeight_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have ht : (∑' j, lossTerm (j+32768)) ≤ (1/(32769:ℝ))*B := calc
    _ ≤ ∑' j : ℕ, positiveWeight (j+32769)*B :=
      (hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum
        (fun j => mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (hb _)) (positiveWeight_nonneg _)) (hw.mul_right B)
    _ = _ := by rw [tsum_mul_right,positiveWeight_tsum_tail 32769 (by decide)]; norm_num
  rw [he, ← hsum.sum_add_tsum_nat_add 32768]
  dsimp [B] at ht
  linarith

/-- The canonical mass dominates this complete physical trial at every larger cutoff. -/
theorem packetError_le_conductor_124 (n : ℕ) (hn : 123 ≤ n) :
    1-packetMass n ≤ (36740218801559 : ℝ)/2979000000000000 := by
  let f := (1/1000000 : ℝ) • synthesis rows
  have hm : f ∈ Submodule.span ℝ
      (Set.range (fun i : Fin 123 => ramanujanPacketHilbert (i.val+2))) := by
    rw [finitePacket_span_eq]
    exact (finiteSpace 123).smul_mem _ (synthesis_spec 123 rows rows_range).1
  rw [← Fintype.range_linearCombination] at hm
  obtain ⟨a,ha⟩ := hm
  have he := packet_completion 123 a
  rw [ha] at he
  have hs := sq_nonneg ‖Fintype.linearCombination ℝ
    (fun i : Fin 123 => ramanujanPacketHilbert (i.val+2)) (a-packetCoefficients 123)‖
  have htrial : ‖hilbertOne-f‖^2 ≤ (36740218801559 : ℝ)/2979000000000000 := complete_trial_upper
  linarith [packetMass_monotone hn]

/-- The centered covariance signal-to-noise ratio at every larger cutoff. -/
theorem centered_mass_ratio_ge_conductor_124 (n : ℕ) (hn : 123 ≤ n) :
    (2942259781198441 : ℝ)/36740218801559 ≤ packetMass n / (1-packetMass n) := by
  apply (div_le_div_iff₀ (by norm_num) (sub_pos.mpr (packetMass_bounds n).2)).mpr
  linarith [packetError_le_conductor_124 n hn]

theorem limitEnergy_le_conductor_124 :
    limitEnergy ≤ (36740218801559 : ℝ)/2979000000000000 := by
  have h : (1:ℝ)-36740218801559/2979000000000000 ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto (eventually_atTop.2 ⟨123,fun n hn => by
      linarith [packetError_le_conductor_124 n hn]⟩)
  linarith

end RiemannResearch.RH.RamanujanResidueMass

/--
info: 'RiemannResearch.RH.RamanujanResidueMass.limitEnergy_le_conductor_124' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.RamanujanResidueMass.limitEnergy_le_conductor_124
