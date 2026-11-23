import RiemannResearch.RH.ParetoPeriodicTailDiscrepancy
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.ParetoHiddenNoiseMoments
import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.Analysis.OrthogonalDistanceBound
import Mathlib.Tactic.FieldSimp

/-! # Complete weighted tail of a signed raw-residue trial

Section 5 of the supplied Pareto parity note gives the tail argument. Each linear term uses its
own conductor as period and each cross term uses the product of its two
conductors. The common-period covariance is the existing CRT theorem.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.RawTrialTail

def centered (d n : ℕ) : ℝ := residue d n - ((d:ℝ)-1)/2

private theorem periodic_centered (d p n : ℕ) (h : d ∣ p) :
    centered d (n+p) = centered d n := by
  simp [centered,residue,Nat.add_mod,Nat.mod_eq_zero_of_dvd h]

private theorem centered_abs (d n : ℕ) (hd : 0 < d) :
    |centered d n| ≤ ((d:ℝ)-1)/2 := by
  have h : (n%d : ℕ)+1 ≤ d := Nat.mod_lt n hd
  have hh : ((n%d : ℕ):ℝ)+1 ≤ (d:ℝ) := by exact_mod_cast h
  have hn : (0:ℝ) ≤ ((n%d : ℕ):ℝ) := Nat.cast_nonneg _
  rw [centered, residue, abs_le]
  constructor <;> linarith

private def prefixSum (a k : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ j ∈ Finset.range k, f (a+j)
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' r f := by simp [Finset.mul_sum]

private theorem centered_prefix_le (d a k : ℕ) (hd : 0 < d) :
    |prefixSum a k (centered d)| ≤ (d:ℝ)*((d:ℝ)-1)/4 := by
  have hm : (∑ j ∈ Finset.range d, centered d j) = (d:ℝ)*0 := by
    rw [← Fin.sum_univ_eq_sum_range (centered d) d, mul_zero]
    simpa only [centered,residue,Nat.mod_eq_of_lt (Fin.isLt _)] using fin_real_centered_sum d
  have he := PeriodicDiscrepancy.prefix_error_le (centered d) d a k hd
    (fun n => periodic_centered d d n (dvd_refl d)) (fun n => centered_abs d n hd) hm
  change |∑ j ∈ Finset.range k, centered d (a+j)| ≤ _
  simp only [mul_zero,sub_zero] at he
  linarith only [he]

private def cross (d e : ℕ) : ℕ → ℝ := fun n =>
  centered d n*centered e n - (((d.gcd e:ℕ):ℝ)^2-1)/12

private theorem cross_prefix_le (d e a k : ℕ) (hd : 0 < d) (he : 0 < e) :
    |prefixSum a k (cross d e)| ≤ (d:ℝ)*(d-1:ℝ)*(e:ℝ)*(e-1:ℝ)/8 := by
  let f (n : ℕ) := centered d n*centered e n
  let μ : ℝ := (((d.gcd e : ℕ):ℝ)^2-1)/12
  have hdp : d ∣ d*e := dvd_mul_right d e
  have hep : e ∣ d*e := dvd_mul_left e d
  have hm : (∑ j ∈ Finset.range (d*e), f j) = ((d*e : ℕ):ℝ)*μ := by
    simpa [f,centered,μ,div_eq_mul_inv,mul_assoc] using
      residue_uniform_covariance_sum d e (d*e) hd he hdp hep
  have hp (n : ℕ) : f (n+d*e) = f n := by
    simp only [f,periodic_centered d (d*e) n hdp,periodic_centered e (d*e) n hep]
  have hmag (n : ℕ) : |f n| ≤ ((d:ℝ)-1)/2 * (((e:ℝ)-1)/2) := by
    change |centered d n * centered e n| ≤ _
    rw [abs_mul]
    exact mul_le_mul (centered_abs d n hd) (centered_abs e n he) (abs_nonneg _)
      ((abs_nonneg _).trans (centered_abs d n hd))
  have h := PeriodicDiscrepancy.prefix_error_le f (d*e) a k (Nat.mul_pos hd he) hp hmag hm
  change |∑ j ∈ Finset.range k, (f (a+j)-μ)| ≤ _
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  push_cast at h
  linarith only [h]

def mean (s : Finset ℕ) (c : ℕ → ℝ) (C : ℝ) : ℝ :=
  C - (∑ d ∈ s, c d*((d:ℝ)-1))/2

def amplitude (s : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s, |c d| *(d:ℝ)*((d:ℝ)-1)

def gcdEnergy (s : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s, ∑ e ∈ s, c d*c e*((((d.gcd e : ℕ):ℝ)^2)-1)

def error (s : Finset ℕ) (c : ℕ → ℝ) (C : ℝ) (n : ℕ) : ℝ :=
  C - ∑ d ∈ s, c d * residue d n

def uniformSquare (s : Finset ℕ) (c : ℕ → ℝ) (C : ℝ) : ℝ :=
  (mean s c C)^2 + gcdEnergy s c/12

def discrepancy (s : Finset ℕ) (c : ℕ → ℝ) (C : ℝ) : ℝ :=
  ((amplitude s c)^2 + 4*|mean s c C| *amplitude s c)/8

private theorem square_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ d ∈ s, x d)^2 = ∑ d ∈ s, ∑ e ∈ s, x d*x e := by
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum]

private theorem expansion (s : Finset ℕ) (c : ℕ → ℝ) (C : ℝ) :
    (fun n => (error s c C n)^2 - uniformSquare s c C) =
      (-2*mean s c C) • (∑ d ∈ s, c d • centered d) +
        ∑ d ∈ s, ∑ e ∈ s, (c d*c e) • cross d e := by
  funext n
  have he : error s c C n = mean s c C - ∑ d ∈ s, c d*centered d n := by
    have hsplit : (∑ d ∈ s, c d * residue d n) =
        (∑ d ∈ s, c d * ((d:ℝ)-1))/2 + ∑ d ∈ s, c d * centered d n := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ => by unfold centered; ring
    unfold error mean
    linarith only [hsplit]
  have hcross : (∑ d ∈ s, ∑ e ∈ s, (c d*c e)*cross d e n) =
      (∑ d ∈ s, c d*centered d n)^2 - gcdEnergy s c/12 := by
    rw [square_sum]
    unfold gcdEnergy
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by unfold cross; ring
  simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  rw [hcross,he,uniformSquare]
  ring

private theorem abs_prefix_linear (s : Finset ℕ) (c : ℕ → ℝ)
    (a k : ℕ) (hs : ∀ d ∈ s, 0 < d) :
    |prefixSum a k (∑ d ∈ s, c d • centered d)| ≤ amplitude s c/4 := by
  simp only [map_sum,map_smul,smul_eq_mul,amplitude,Finset.sum_div]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  convert mul_le_mul_of_nonneg_left (centered_prefix_le d a k (hs d hd))
    (abs_nonneg (c d)) using 1
  ring

private theorem abs_prefix_cross (s : Finset ℕ) (c : ℕ → ℝ)
    (a k : ℕ) (hs : ∀ d ∈ s, 0 < d) :
    |prefixSum a k (∑ d ∈ s, ∑ e ∈ s, (c d*c e) • cross d e)| ≤ (amplitude s c)^2/8 := by
  simp only [map_sum,map_smul,smul_eq_mul,amplitude,square_sum,Finset.sum_div]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e he
  rw [abs_mul, abs_mul]
  convert mul_le_mul_of_nonneg_left (cross_prefix_le d e a k (hs d hd) (hs e he))
      (mul_nonneg (abs_nonneg (c d)) (abs_nonneg (c e))) using 1
  ring

/-- One bound simultaneously controls every shift and every prefix length. -/
theorem residual_prefix_error_le (s : Finset ℕ) (c : ℕ → ℝ) (C : ℝ)
    (a k : ℕ) (hs : ∀ d ∈ s, 0 < d) :
    |∑ j ∈ Finset.range k, ((error s c C (a+j))^2 - uniformSquare s c C)| ≤
      discrepancy s c C := by
  change |prefixSum a k (fun n => (error s c C n)^2-uniformSquare s c C)| ≤ _
  rw [expansion,map_add,map_smul,smul_eq_mul]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ (2:ℝ) by norm_num)]
  unfold discrepancy
  have hl := mul_le_mul_of_nonneg_left (abs_prefix_linear s c a k hs)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (abs_nonneg (mean s c C)))
  linarith only [hl,abs_prefix_cross s c a k hs]

/-- Every finite weighted tail is bounded by its exact uniform part plus one
discrepancy term at the first omitted site. -/
theorem weighted_tail_prefix (s : Finset ℕ) (c : ℕ → ℝ) (C : ℝ)
    (T k : ℕ) (hs : ∀ d ∈ s, 0 < d) :
    (∑ j ∈ Finset.range k, positiveWeight (T+1+j) * (error s c C (T+1+j))^2) ≤
      (∑ j ∈ Finset.range k, positiveWeight (T+1+j)) * uniformSquare s c C +
        positiveWeight (T+1) * discrepancy s c C := by
  let w := fun i => positiveWeight (T+1+i)
  have hw (i : ℕ) : w (i+1) ≤ w i := by
    dsimp [w,positiveWeight]
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) T,Nat.cast_nonneg (α:=ℝ) i]
  have h := PeriodicDiscrepancy.abel_upper
    (fun j => (error s c C (T+1+j))^2 - uniformSquare s c C)
    w (fun j => positiveWeight_nonneg _) hw (discrepancy s c C)
    (fun j => (le_abs_self _).trans (residual_prefix_error_le s c C (T+1) j hs)) k
  simp only [w,Nat.add_zero,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul] at h
  linarith only [h]

open CoefficientStabilization

/-- A checked head and the periodic tail bound the projection error in any
subspace containing the conductors of the trial. -/
theorem projection_error_le_of_head (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] (s : Finset ℕ) (c : ℕ → ℝ) (C H : ℝ)
    (T : ℕ) (hC : 0 < C) (hs : ∀ d ∈ s, 2 ≤ d)
    (hmem : ∀ d ∈ s, rawResidueAtom (d-2) ∈ S)
    (hhead : (∑ j ∈ Finset.range T, positiveWeight (j + 1) * (error s c C (j + 1)) ^ 2) ≤ H) :
    ‖hilbertOne - S.starProjection hilbertOne‖^2 ≤
      (H + uniformSquare s c C / ((T:ℝ)+1) +
        discrepancy s c C / (((T:ℝ)+1)*((T:ℝ)+2))) / C^2 := by
  let v := ∑ d ∈ s, c d • rawResidueAtom (d-2)
  let r := C • hilbertOne - v
  have hv : v ∈ S := S.sum_mem (fun d hd => S.smul_mem _ (hmem d hd))
  have hdist := Metric.infDist_le_dist_of_mem (x := hilbertOne) (S.smul_mem C⁻¹ hv)
  rw [S.infDist_eq_norm_sub_starProjection, dist_eq_norm] at hdist
  have hres : r = C • (hilbertOne-C⁻¹ • v) := by
    simp [r,smul_sub,smul_smul,hC.ne']
  have hmin : ‖hilbertOne - S.starProjection hilbertOne‖^2 * C^2 ≤ ‖r‖^2 := by
    rw [hres,norm_smul,Real.norm_eq_abs,abs_of_pos hC,mul_pow,mul_comm (C^2)]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hdist)
      (sq_nonneg C)
  have hseq (n : ℕ) (hn : 0 < n) : hilbertSequence r n = error s c C n := by
    rw [← anchoredEvaluationCLM_apply]
    simp only [r,v,map_sub,map_smul,map_sum,smul_eq_mul,anchoredEvaluationCLM_apply,
      hilbertOne_sequence,zeroAnchor,if_neg hn.ne',mul_one,rawResidueAtom_sequence,error]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.sub_add_cancel (hs d hd)]
  let L := fun j : ℕ => positiveWeight (j + 1) * (error s c C (j + 1)) ^ 2
  have hL : Summable L := by
    have h := (hilbertSequence_square_summable r).comp_injective
      (fun (x y : ℕ) (he : x+1=y+1) => Nat.add_right_cancel he)
    simpa only [Function.comp_def,hseq _ (Nat.succ_pos _),L] using h
  have hn : ‖r‖^2 = ∑' j, L j := by
    rw [hilbert_norm_weighted_sq,(hilbertSequence_square_summable r).tsum_eq_zero_add]
    rw [show positiveWeight 0 = 0 by norm_num [positiveWeight], zero_mul, zero_add]
    apply tsum_congr
    intro j
    change positiveWeight (j+1) * (hilbertSequence r (j+1))^2 =
      positiveWeight (j + 1) * (error s c C (j + 1)) ^ 2
    rw [hseq (j+1) (Nat.succ_pos j)]
  have hLtail := hL.comp_injective (fun (x y : ℕ) (he : x+T=y+T) => Nat.add_right_cancel he)
  have hw := positiveWeight_summable.comp_injective
    (fun (x y : ℕ) (he : x+(T+1)=y+(T+1)) => Nat.add_right_cancel he)
  have htail : (∑' j, L (j+T)) ≤
      (∑' j : ℕ, positiveWeight (j+(T+1))) * uniformSquare s c C +
        positiveWeight (T+1)*discrepancy s c C := by
    apply le_of_tendsto_of_tendsto' hLtail.hasSum.tendsto_sum_nat
      ((hw.hasSum.tendsto_sum_nat.mul_const _).add_const _)
    intro k
    simpa only [Function.comp_def,L,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      weighted_tail_prefix s c C T k (fun d hd => by have := hs d hd; omega)
  rw [positiveWeight_tsum_tail _ (Nat.succ_pos T)] at htail
  rw [hn, ← hL.sum_add_tsum_nat_add T] at hmin
  apply (le_div_iff₀ (sq_pos_of_pos hC)).mpr
  have h := hmin.trans (add_le_add hhead htail)
  convert h using 1
  simp only [positiveWeight,Nat.cast_succ]
  ring

/-- A finite raw-residue head and the CRT tail together control the true
closed-space distance. The unscaled integer loss is divided by the scale
squared only at the end. -/
theorem limitEnergy_le_of_head (s : Finset ℕ) (c : ℕ → ℝ) (C H : ℝ)
    (T : ℕ) (hC : 0 < C) (hs : ∀ d ∈ s, 2 ≤ d)
    (hhead : (∑ j ∈ Finset.range T, positiveWeight (j + 1) * (error s c C (j + 1)) ^ 2) ≤ H) :
    limitEnergy ≤ (H + uniformSquare s c C / ((T:ℝ)+1) +
      discrepancy s c C / (((T:ℝ)+1)*((T:ℝ)+2))) / C^2 := by
  exact projection_error_le_of_head closedSpace s c C H T hC hs (fun d _ =>
    closedSpace.smul_mem _
      (RiemannResearch.RH.RamanujanMultipleCapacityLimits.residueAtom_mem_closedSpace (d-2))) hhead

end RiemannResearch.RH.Pareto.RawTrialTail
