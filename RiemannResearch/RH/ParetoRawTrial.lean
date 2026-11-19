import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanResidueMassData
import RiemannResearch.RH.ParetoHiddenNoiseMoments
import Mathlib.Tactic

/-! # Finite certificates for complete Pareto projection error

For signed integer combinations of raw residues with common denominator one
million, an upper bound on the sum of rounded head terms and a global residual
bound control the complete physical error at every larger dictionary stage. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ParetoRawTrial
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RamanujanResidueMass.Certificate (signal)

def difference (rows : List (ℕ × ℤ)) (k : ℕ) : ℤ := 1000000 - signal rows k

def headUnit (rows : List (ℕ × ℤ)) (k : ℕ) : ℕ :=
  (difference rows (k+1)).natAbs^2 / ((k+1)*(k+2)) + 1

def block (rows : List (ℕ × ℤ)) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 128, headUnit rows (j*128+i)

private theorem head_split (rows : List (ℕ × ℤ)) (K : ℕ) :
    (∑ k ∈ Finset.range (K*128), headUnit rows k) = ∑ j ∈ Finset.range K, block rows j := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ (block rows) K]
    simp only [block]

private def lossTerm (rows : List (ℕ × ℤ)) (k : ℕ) : ℝ :=
  positiveWeight (k+1) * ((difference rows (k+1) : ℝ)/1000000)^2

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

private theorem head_bound (rows : List (ℕ × ℤ)) (k : ℕ) :
    lossTerm rows k ≤ (headUnit rows k : ℝ)/10^12 := by
  let a := (difference rows (k+1)).natAbs
  let b := (k+1)*(k+2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hi : a^2 ≤ b * headUnit rows k := (Nat.lt_mul_div_succ (a^2) hb).le
  have hreal : (a:ℝ)^2 ≤ ((k:ℝ)+1)*((k:ℝ)+2)*(headUnit rows k : ℝ) := by
    exact_mod_cast hi
  have ha : (a:ℝ)^2 = (difference rows (k+1) : ℝ)^2 := by
    have hz := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (difference rows (k+1)))
    have hr : (a:ℝ) = |(difference rows (k+1) : ℝ)| := by
      simpa only [a, Int.cast_natCast, Int.cast_abs] using hz
    rw [hr,sq_abs]
  rw [ha] at hreal
  unfold lossTerm positiveWeight
  push_cast
  have h1 : 0 < (k:ℝ)+1 := by positivity
  have h2 : 0 < (k:ℝ)+1+1 := by positivity
  field_simp [h1.ne',h2.ne']
  nlinarith [hreal]


theorem packet_error_le_of_certificate (trialStage n : ℕ) (hstage : trialStage ≤ n)
    (rows : List (ℕ × ℤ)) (K U B : ℕ)
    (hrows : ∀ t ∈ rows, 2 ≤ t.1 ∧ t.1 ≤ trialStage+1)
    (hbound : ∀ k, |difference rows k| ≤ (B : ℤ))
    (hunits : (∑ j ∈ Finset.range K, block rows j) ≤ U) :
    1 - packetMass n ≤ (U : ℝ)/10^12 + (((B : ℝ)/1000000)^2)/((K*128+1 : ℕ) : ℝ) := by
  let T := K * 128
  let C := (((B : ℝ)/1000000)^2)
  have hb (k : ℕ) : |((difference rows k : ℝ)/1000000)^2| ≤ C := by
    have hh : |(difference rows k : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hbound k
    rw [abs_of_nonneg (sq_nonneg _), div_pow]
    dsimp [C]
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hsum : Summable (lossTerm rows) :=
    (weighted_summable_of_bounded hb).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  let f := (1/1000000 : ℝ) • synthesis rows
  have he : ‖hilbertOne - f‖^2 = ∑' k, lossTerm rows k := by
    rw [hilbert_norm_weighted_sq]
    have hseq (k : ℕ) : hilbertSequence
        (hilbertOne - (1/1000000 : ℝ) • synthesis rows) (k+1) =
        (difference rows (k+1) : ℝ)/1000000 := by
      rw [← anchoredEvaluationCLM_apply, map_sub, map_smul, smul_eq_mul,
        anchoredEvaluationCLM_apply, anchoredEvaluationCLM_apply, hilbertOne_sequence,
        (synthesis_spec trialStage rows hrows).2]
      simp only [zeroAnchor, Nat.succ_ne_zero, if_false, difference, Int.cast_sub, Int.cast_ofNat]
      ring
    rw [((hilbertSequence_square_summable _).tsum_eq_zero_add)]
    simp only [positiveWeight, Nat.cast_zero, zero_mul, div_zero, zero_add]
    apply tsum_congr
    intro k
    rw [hseq]
    rfl
  have hhead : (∑ k ∈ Finset.range T, lossTerm rows k) ≤ (U : ℝ)/10^12 := calc
    _ ≤ ∑ k ∈ Finset.range T, (headUnit rows k : ℝ)/10^12 :=
      Finset.sum_le_sum fun k _ => head_bound rows k
    _ = ((∑ j ∈ Finset.range K, block rows j : ℕ) : ℝ)/10^12 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, head_split]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hunits) (by positivity)
  have hw : Summable (fun j : ℕ => positiveWeight (j+(T+1))) :=
    positiveWeight_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have ht : (∑' j, lossTerm rows (j+T)) ≤ C / ((T+1 : ℕ) : ℝ) := calc
    _ ≤ ∑' j : ℕ, positiveWeight (j+(T+1))*C := by
      apply (hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum _ (hw.mul_right C)
      intro j
      change positiveWeight ((j + T) + 1) * _ ≤ positiveWeight (j + (T+1)) * C
      rw [Nat.add_assoc]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb _)) (positiveWeight_nonneg _)
    _ = _ := by rw [tsum_mul_right,positiveWeight_tsum_tail (T+1) (by omega)]; ring
  have htrial := add_le_add hhead ht
  rw [hsum.sum_add_tsum_nat_add T, ← he] at htrial
  have hm : f ∈ Submodule.span ℝ
      (Set.range (fun i : Fin trialStage => ramanujanPacketHilbert (i.val+2))) := by
    rw [finitePacket_span_eq]
    exact (finiteSpace trialStage).smul_mem _ (synthesis_spec trialStage rows hrows).1
  rw [← Fintype.range_linearCombination] at hm
  obtain ⟨a,ha⟩ := hm
  have hfit := packet_completion trialStage a
  rw [ha] at hfit
  have hs := sq_nonneg ‖Fintype.linearCombination ℝ
    (fun i : Fin trialStage => ramanujanPacketHilbert (i.val+2)) (a-packetCoefficients trialStage)‖
  change 1 - packetMass n ≤ (U : ℝ)/10^12 + C / ((T+1 : ℕ) : ℝ)
  linarith [packetMass_monotone hstage]

end RiemannResearch.RH.ParetoRawTrial
