import RiemannResearch.RH.ParetoInversePolynomial
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact Möbius-harmonic conditioning of the complete physical dictionary

Source: user-provided finite Möbius coefficient-recovery argument, sharpened
by retaining the actual zero values of the Möbius convolution kernel.
Every physical conductor remains present; only the arithmetic transform
kernel has its naturally zero nonsquarefree coefficients retained exactly.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

def cutoffMobiusHarmonic (R : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 R, |(ArithmeticFunction.moebius q : ℝ)| / (q : ℝ)

theorem cutoffMobiusHarmonic_nonneg (R : ℕ) : 0 ≤ cutoffMobiusHarmonic R := by
  unfold cutoffMobiusHarmonic
  exact Finset.sum_nonneg fun q hq => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

theorem cutoffMobiusHarmonic_le_harmonic (R : ℕ) :
    cutoffMobiusHarmonic R ≤ cutoffHarmonic R := by
  unfold cutoffMobiusHarmonic cutoffHarmonic
  apply Finset.sum_le_sum
  intro q hq
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)

private theorem mobius_dilation_energy_le (R q : ℕ) (hq : 0 < q) (a : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, if q ∣ d then a (d / q) ^ 2 else 0) ≤
      ∑ k ∈ Finset.Icc 1 R, a k ^ 2 := by
  classical
  let s := (Finset.Icc 1 R).filter (fun d => q ∣ d)
  have hinj : Set.InjOn (fun d => d / q) (↑s : Set ℕ) := by
    intro d hd e he hde
    change d / q = e / q at hde
    have hqd := (Finset.mem_filter.mp hd).2
    have hqe := (Finset.mem_filter.mp he).2
    calc
      d = (d / q) * q := (Nat.div_mul_cancel hqd).symm
      _ = (e / q) * q := by rw [hde]
      _ = e := Nat.div_mul_cancel hqe
  have hsub : s.image (fun d => d / q) ⊆ Finset.Icc 1 R := by
    intro k hk
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_filter.mp hd with ⟨hdR, hqd⟩
    rcases Finset.mem_Icc.mp hdR with ⟨hd1, hdR⟩
    have hdq : 0 < d / q := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < d) hqd) hq
    exact Finset.mem_Icc.mpr ⟨by omega, (Nat.div_le_self d q).trans hdR⟩
  rw [← Finset.sum_filter]
  change (∑ d ∈ s, a (d / q) ^ 2) ≤ _
  have heq : (∑ d ∈ s, a (d / q) ^ 2) =
      ∑ k ∈ s.image (fun d => d / q), a k ^ 2 :=
    (Finset.sum_image (s := s) (f := fun k : ℕ => a k ^ 2)
      (g := fun d : ℕ => d / q) hinj).symm
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk hki => sq_nonneg _)

private theorem mobius_transform_pointwise (R d : ℕ) (a : ℕ → ℝ) :
    cutoffDivisorTransform R a d ^ 2 ≤ cutoffMobiusHarmonic R *
      ∑ q ∈ Finset.Icc 1 R,
        |(ArithmeticFunction.moebius q : ℝ)| / (q : ℝ) *
          (if q ∣ d then a (d / q) ^ 2 else 0) := by
  let b : ℕ → ℝ := fun q =>
    if q ∣ d then (ArithmeticFunction.moebius q : ℝ) * a (d / q) else 0
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Icc 1 R)
    (r := fun q => b q / (q : ℝ))
    (f := fun q => |(ArithmeticFunction.moebius q : ℝ)| / (q : ℝ))
    (g := fun q => |(ArithmeticFunction.moebius q : ℝ)| / (q : ℝ) *
      (if q ∣ d then a (d / q) ^ 2 else 0))
    (by intro q hq; positivity)
    (by intro q hq; split_ifs <;> positivity)
    (by
      intro q hq
      apply le_of_eq
      by_cases hqd : q ∣ d
      · simp only [b, if_pos hqd, div_pow, mul_pow]
        ring_nf
        rw [sq_abs] <;> ring
      · simp [b, hqd])
  exact hcs

/-- Exact squarefree-support kernel refinement of the harmonic transform bound. -/
theorem cutoffDivisorTransform_energy_le_mobiusHarmonic (R : ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, cutoffDivisorTransform R a d ^ 2) ≤
      cutoffMobiusHarmonic R ^ 2 * ∑ k ∈ Finset.Icc 1 R, a k ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 R, cutoffMobiusHarmonic R *
        ∑ q ∈ Finset.Icc 1 R, |(ArithmeticFunction.moebius q : ℝ)| / (q : ℝ) *
          (if q ∣ d then a (d / q) ^ 2 else 0) :=
      Finset.sum_le_sum fun d hd => mobius_transform_pointwise R d a
    _ = cutoffMobiusHarmonic R * ∑ q ∈ Finset.Icc 1 R,
        |(ArithmeticFunction.moebius q : ℝ)| / (q : ℝ) *
          ∑ d ∈ Finset.Icc 1 R, if q ∣ d then a (d / q) ^ 2 else 0 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ cutoffMobiusHarmonic R * ∑ q ∈ Finset.Icc 1 R,
        |(ArithmeticFunction.moebius q : ℝ)| / (q : ℝ) *
          ∑ k ∈ Finset.Icc 1 R, a k ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (cutoffMobiusHarmonic_nonneg R)
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (mobius_dilation_energy_le R q (by have := (Finset.mem_Icc.mp hq).1; omega) a)
        (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      rw [← Finset.sum_mul]
      change cutoffMobiusHarmonic R * (cutoffMobiusHarmonic R * _) = _
      ring

theorem mobiusDifferenceCLM_weighted_energy_le_mobiusHarmonic
    (R : ℕ) (F : ThresholdHilbert) :
    (∑ d ∈ Finset.Icc 1 R, (mobiusDifferenceCLM d F / (d : ℝ)) ^ 2) ≤
      4 * cutoffMobiusHarmonic R ^ 2 * ‖F‖ ^ 2 := by
  have he :
      (∑ d ∈ Finset.Icc 1 R, (mobiusDifferenceCLM d F / (d : ℝ)) ^ 2) =
        ∑ d ∈ Finset.Icc 1 R, cutoffDivisorTransform R (normalizedDifference F) d ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cutoffDivisorTransform_normalizedDifference R d
      (by have := (Finset.mem_Icc.mp hd).1; omega) (Finset.mem_Icc.mp hd).2]
  rw [he]
  have h1 := cutoffDivisorTransform_energy_le_mobiusHarmonic R (normalizedDifference F)
  have h2 := mul_le_mul_of_nonneg_left (normalizedDifference_energy_le R F)
    (sq_nonneg (cutoffMobiusHarmonic R))
  nlinarith

/-- The improved conditioning holds for every actual subdictionary; a kernel
coefficient vanishing does not remove any physical residue conductor. -/
theorem residueSubdictionary_coefficient_bound_mobiusHarmonic
    {ι : Type*} [Fintype ι] (n : ℕ) (e : ι → Fin n) (he : Function.Injective e)
    (v : ι → ℝ) :
    (∑ i, v i ^ 2) ≤
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffMobiusHarmonic (n + 1) ^ 2 *
        ‖Fintype.linearCombination ℝ (fun i => residueAtom (e i).val) v‖ ^ 2 := by
  classical
  let F := Fintype.linearCombination ℝ (fun i => residueAtom (e i).val) v
  have hex (i : ι) : coefficientCLM ((e i).val + 2) F = v i := by
    have hp (j : ι) : coefficientCLM ((e i).val + 2) (residueAtom (e j).val) =
        if i = j then 1 else 0 := by
      rw [coefficientCLM_biorthogonal]
      have hiff : (e i).val = (e j).val ↔ i = j := by
        constructor
        · intro h
          exact he (Fin.ext h)
        · intro h; rw [h]
      simp only [hiff]
    simp only [F, Fintype.linearCombination_apply, map_sum, map_smul, hp, smul_eq_mul]
    simp
  let s := Finset.univ.image (fun i : ι => (e i).val + 2)
  have hinj : Function.Injective (fun i : ι => (e i).val + 2) := by
    intro i j hij
    change (e i).val + 2 = (e j).val + 2 at hij
    apply he
    apply Fin.ext
    omega
  have hsub : s ⊆ Finset.Icc 1 (n + 1) := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_Icc.mpr ⟨by omega, by have := (e i).isLt; omega⟩
  have hweight :
      (∑ i, (v i / (((e i).val + 2 : ℕ) : ℝ)) ^ 2) ≤
        4 * cutoffMobiusHarmonic (n + 1) ^ 2 * ‖F‖ ^ 2 := by
    have hsum :
        (∑ i, (v i / (((e i).val + 2 : ℕ) : ℝ)) ^ 2) =
          ∑ d ∈ s, (mobiusDifferenceCLM d F / (d : ℝ)) ^ 2 := by
      rw [Finset.sum_image (fun i hi j hj hij => hinj hij)]
      apply Finset.sum_congr rfl
      intro i hi
      have h := hex i
      change -(mobiusDifferenceCLM ((e i).val + 2) F) = v i at h
      rw [← h]
      simp only [neg_div, neg_sq]
    rw [hsum]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d hd hds => sq_nonneg _)).trans
        (mobiusDifferenceCLM_weighted_energy_le_mobiusHarmonic (n + 1) F)
  have hpoint (i : ι) : v i ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) ^ 2 * (v i / (((e i).val + 2 : ℕ) : ℝ)) ^ 2 := by
    have hi0 : (0 : ℝ) < (((e i).val + 2 : ℕ) : ℝ) := by positivity
    have hle : (((e i).val + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (e i).val + 2 ≤ n + 1 by have := (e i).isLt; omega)
    have hsq : (((e i).val + 2 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hi0)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (sq_nonneg (v i))
  have hs : (∑ i, v i ^ 2) ≤
      ∑ i, ((n + 1 : ℕ) : ℝ) ^ 2 * (v i / (((e i).val + 2 : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_le_sum fun i hi => hpoint i
  rw [← Finset.mul_sum] at hs
  have hlast := mul_le_mul_of_nonneg_left hweight (sq_nonneg (((n + 1 : ℕ) : ℝ)))
  change (∑ i, v i ^ 2) ≤ 4 * _ * _ * ‖F‖ ^ 2
  nlinarith

private theorem mobius_inverse_quadratic_of_coercive
    {ι : Type*} [Fintype ι] {v : ι → ThresholdHilbert}
    (hv : LinearIndependent ℝ v) (C : ℝ) (hC : 0 ≤ C)
    (hcoercive : ∀ c : ι → ℝ,
      (∑ i, c i ^ 2) ≤ C * ‖Fintype.linearCombination ℝ v c‖ ^ 2)
    (a : ι → ℝ) :
    (∑ i, (gramEquiv hv).symm a i * a i) ≤ C * ∑ i, a i ^ 2 := by
  let c := (gramEquiv hv).symm a
  let Q := ‖Fintype.linearCombination ℝ v c‖ ^ 2
  have hq : Q = ∑ i, c i * a i := by
    dsimp only [Q]
    rw [gram_quadratic]
    have he : gram v c = a := (gramEquiv hv).apply_symm_apply a
    rw [he]
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  rw [← hq] at hsq
  have hx := hcoercive c
  change (∑ i, c i ^ 2) ≤ C * Q at hx
  have ha0 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hx ha0
  have hQ : 0 ≤ Q := sq_nonneg _
  change (∑ i, c i * a i) ≤ C * ∑ i, a i ^ 2
  rw [← hq]
  by_cases hQ0 : Q = 0
  · rw [hQ0]
    exact mul_nonneg hC ha0
  · have hpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hQ0)
    nlinarith

theorem residueSubdictionary_inverse_mobiusHarmonic_bound
    {ι : Type*} [Fintype ι] (n : ℕ) (e : ι → Fin n) (he : Function.Injective e)
    (a : ι → ℝ) :
    (∑ i, (gramEquiv ((finiteResidue_independent n).comp e he)).symm a i * a i) ≤
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffMobiusHarmonic (n + 1) ^ 2 * ∑ i, a i ^ 2 := by
  apply mobius_inverse_quadratic_of_coercive ((finiteResidue_independent n).comp e he)
    (4 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffMobiusHarmonic (n + 1) ^ 2)
    (by positivity)
  exact residueSubdictionary_coefficient_bound_mobiusHarmonic n e he

theorem completeResidue_inverse_mobiusHarmonic_bound (n : ℕ) (a : Fin n → ℝ) :
    (∑ i, (gramEquiv (finiteResidue_independent n)).symm a i * a i) ≤
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffMobiusHarmonic (n + 1) ^ 2 * ∑ i, a i ^ 2 := by
  simpa only [Function.comp_def, id_eq] using
    residueSubdictionary_inverse_mobiusHarmonic_bound n id Function.injective_id a

theorem completeComposite_inverse_mobiusHarmonic_bound (n : ℕ)
    (a : CompleteCompositeIndex n → ℝ) :
    (∑ i, (gramEquiv (completeComposite_independent n)).symm a i * a i) ≤
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffMobiusHarmonic (n + 1) ^ 2 * ∑ i, a i ^ 2 :=
  residueSubdictionary_inverse_mobiusHarmonic_bound n Subtype.val Subtype.val_injective a

end RiemannResearch.RH.Pareto.CoefficientStabilization
