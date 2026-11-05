/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeWeakLeakage
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
/-!
# Logarithmic multiplier leakage for the actual displacement

Power orbits in the squarefree span give a quantitative obstruction: a nonzero
physical difference forces the norm of the scaled error to grow at least like
`Real.sqrt (Real.log m)`. The liminf-zero hypothesis on the actual displacement
remains an arithmetic condition.

Source: the power-orbit argument in the 4 November 2026 log-leakage continuation.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeMultiplierLeakage
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open SquarefreeRadicalDifference QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.ApproximateSquareTests

theorem closure_difference_power {f : QHilbert} (hf : f ∈ closure)
    (n r : ℕ) (hn : 2 ≤ n) (hr : r ≠ 0) :
    qDifference f (n^r) = qDifference f n := by
  have hnr : 2 ≤ n^r := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    have hp : 0 < n^s := pow_pos (by omega) _
    rw [pow_succ]
    nlinarith
  have hspan : (Submodule.span ℝ (Set.range squarefreeAtom) : Set QHilbert) ⊆
      {x | qDifference x (n^r) = qDifference x n} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        by_cases hk : Squarefree (k+2)
        · simp only [squarefreeAtom, if_pos hk, Set.mem_ofPred_eq,
            qDifference, qSequence_qResidue]
          exact residueFraction_difference_eq_of_dvd_iff (k+2) (n^r) n
            (by omega) (by omega) (by omega) (hk.dvd_pow_iff_dvd hr)
        · simp only [squarefreeAtom, if_neg hk, Set.mem_ofPred_eq, qDifference_zero]
    | zero => simp only [Set.mem_ofPred_eq, qDifference_zero]
    | add x y hx hy ihx ihy =>
        simp only [Set.mem_ofPred_eq] at *
        rw [qDifference_add, qDifference_add, ihx, ihy]
    | smul c x hx ih =>
        simp only [Set.mem_ofPred_eq] at *
        rw [qDifference_smul, qDifference_smul, ih]
  exact (closure_minimal hspan
    (isClosed_eq (continuous_qDifference (n^r)) (continuous_qDifference n))) hf

theorem normalized_square_tsum (f : QHilbert) :
    (∑' n : ℕ, (qSequence f n / (n : ℝ))^2) = zetaTwo * ‖f‖^2 := by
  rw [qNorm_weighted_sq, ← tsum_mul_left]
  congr 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold positiveQWeight
    field_simp [hnR, ne_of_gt zetaTwo_pos]

theorem normalized_sample_sum_le {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (ha : Set.InjOn a s) (f : QHilbert) :
    (∑ j ∈ s, (qSequence f (a j) / (a j : ℝ))^2) ≤ zetaTwo * ‖f‖^2 := by
  classical
  have h := Summable.sum_le_tsum (s.image a)
    (fun n _ => sq_nonneg (qSequence f n / (n : ℝ)))
    (qNormalized_square_summable f)
  rw [normalized_square_tsum] at h
  rw [Finset.sum_image (fun i hi j hj he => ha hi hj he)] at h
  exact h

theorem normalized_coordinate_mono (f : QHilbert) (k n : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    (qSequence f k / (n : ℝ))^2 ≤ (qSequence f k / (k : ℝ))^2 := by
  rw [div_pow, div_pow]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith

theorem fourSite_square_le (f : QHilbert) (n : ℕ) (hn : 2 ≤ n) :
    (fourSite f n / (n : ℝ)^2)^2 ≤ 4 *
      ((qSequence f (n^2) / ((n^2 : ℕ) : ℝ))^2 +
       (qSequence f (n^2-1) / ((n^2-1 : ℕ) : ℝ))^2 +
       (qSequence f n / (n : ℝ))^2 +
       (qSequence f (n-1) / ((n-1 : ℕ) : ℝ))^2) := by
  have hn2 : 4 ≤ n^2 := by nlinarith
  have h1 := normalized_coordinate_mono f (n^2-1) (n^2) (by omega) (by omega)
  have h2 := normalized_coordinate_mono f n (n^2) (by omega) (by nlinarith)
  have hnn : n ≤ n^2 := by nlinarith
  have h3 := normalized_coordinate_mono f (n-1) (n^2) (by omega) (by omega)
  simp only [Nat.cast_pow] at *
  let a := qSequence f (n^2) / (n : ℝ)^2
  let b := qSequence f (n^2-1) / (n : ℝ)^2
  let c := qSequence f n / (n : ℝ)^2
  let d := qSequence f (n-1) / (n : ℝ)^2
  have he : fourSite f n / (n : ℝ)^2 = a-b-c+d := by
    dsimp [fourSite, a,b,c,d]
    ring
  rw [he]
  have hh : (a-b-c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
    nlinarith [sq_nonneg (a+b), sq_nonneg (a+c), sq_nonneg (a-d),
      sq_nonneg (b-c), sq_nonneg (b+d), sq_nonneg (c+d)]
  dsimp [a,b,c,d] at hh ⊢
  nlinarith

theorem fourSite_sample_sum_le {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (ha : Set.InjOn a s) (ha2 : ∀ j ∈ s, 2 ≤ a j) (f : QHilbert) :
    (∑ j ∈ s, (fourSite f (a j) / (a j : ℝ)^2)^2) ≤
      16 * zetaTwo * ‖f‖^2 := by
  have hinj1 : Set.InjOn (fun j => (a j)^2) s := by
    intro i hi j hj h
    apply ha hi hj
    nlinarith [ha2 i hi, ha2 j hj]
  have hinj2 : Set.InjOn (fun j => (a j)^2-1) s := by
    intro i hi j hj h
    dsimp only at h ⊢
    have hi2 : 4 ≤ (a i)^2 := by nlinarith [ha2 i hi]
    have hj2 : 4 ≤ (a j)^2 := by nlinarith [ha2 j hj]
    apply hinj1 hi hj
    dsimp only
    omega
  have hinj3 : Set.InjOn (fun j => a j-1) s := by
    intro i hi j hj h
    dsimp only at h
    apply ha hi hj
    have hi2 := ha2 i hi
    have hj2 := ha2 j hj
    omega
  have h1 := normalized_sample_sum_le s _ hinj1 f
  have h2 := normalized_sample_sum_le s _ hinj2 f
  have h3 := normalized_sample_sum_le s _ ha f
  have h4 := normalized_sample_sum_le s _ hinj3 f
  calc
    _ ≤ ∑ j ∈ s, 4 *
      ((qSequence f ((a j)^2) / (((a j)^2 : ℕ) : ℝ))^2 +
       (qSequence f ((a j)^2-1) / (((a j)^2-1 : ℕ) : ℝ))^2 +
       (qSequence f (a j) / (a j : ℝ))^2 +
       (qSequence f (a j-1) / ((a j-1 : ℕ) : ℝ))^2) :=
      Finset.sum_le_sum (fun j hj => fourSite_square_le f (a j) (ha2 j hj))
    _ ≤ _ := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib]
      nlinarith

theorem normalized_test_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      weightedTest (qSequence displacement) n / (n : ℝ)^2 -
        qDifference displacement n) atTop (𝓝 0) := by
  have hsub := qSequence_div_nat_tendsto_zero displacement
  have hp : Tendsto (fun n : ℕ => n^2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with n hn
    have hb := le_max_left b 1
    have h1 := le_max_right b 1
    nlinarith
  have hinv := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hsq : Tendsto (fun n : ℕ =>
      qSequence displacement (n^2) / (n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using hsub.comp hp
  have hsmall : Tendsto (fun n : ℕ =>
      qSequence displacement n / (n : ℝ)^2) atTop (𝓝 0) := by
    have hh := hsub.mul hinv
    simp only [mul_zero] at hh
    convert hh using 1
    funext n
    ring
  have hd := normalized_difference_tendsto_zero _ hsub
  have hh := (hsq.sub hsmall).sub hd
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have he := weightedTest_eq (qSequence displacement) n
    (QSquarefreeMultiplierRigidity.closure_difference_square displacement_mem n hn)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [he]
  dsimp [qDifference]
  field_simp [hn0]
  ring

theorem normalized_test_power_tendsto (t : ℕ) (ht : 2 ≤ t) :
    Tendsto (fun j : ℕ =>
      weightedTest (qSequence displacement) (t^(j+1)) /
        ((t^(j+1) : ℕ) : ℝ)^2)
      atTop (𝓝 (qDifference displacement t)) := by
  have ha : StrictMono (fun j : ℕ => t^(j+1)) := by
    intro i j hij
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hh := (normalized_test_error_tendsto_zero.comp ha.tendsto_atTop).add
    (tendsto_const_nhds (x := qDifference displacement t))
  have hd (j : ℕ) : qDifference displacement (t^(j+1)) =
      qDifference displacement t :=
    closure_difference_power displacement_mem t (j+1) ht (by omega)
  simpa only [Function.comp_def, hd, zero_add, sub_add_cancel] using hh


theorem log_le_affine_scaledError_of_difference_ne_zero
    (t : ℕ) (ht : 2 ≤ t) (hne : qDifference displacement t ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ᶠ m : ℕ in atTop,
      Real.log (m : ℝ) ≤ A * ‖scaledError m‖^2 + B := by
  have hZ := zetaTwo_pos
  let δ := qDifference displacement t
  let u := fun j : ℕ =>
    weightedTest (qSequence displacement) (t^(j+1)) /
      ((t^(j+1) : ℕ) : ℝ)^2
  have hδ : 0 < δ^2 := sq_pos_of_ne_zero hne
  have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
  have hu : Tendsto (fun j => (u j)^2) atTop (𝓝 (δ^2)) :=
    (normalized_test_power_tendsto t ht).pow 2
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (hu.eventually (eventually_gt_nhds (show δ^2/2 < δ^2 by linarith)))
  refine ⟨64*zetaTwo*Real.log (t : ℝ)/δ^2, by positivity,
    (2*(J : ℝ)+2)*Real.log (t : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (t^(2*J)+1)] with m hm
  have ht0 : 0 < t := by omega
  have hm2 : 2 ≤ m := by
    have hp : 0 < t^(2*J) := pow_pos ht0 _
    omega
  let L := Nat.log t (m-1)
  let N := L/2
  let K := N-J
  have hJL : 2*J ≤ L := (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr (by omega)
  have hJN : J ≤ N := by dsimp [N]; omega
  have hKL : L+1 ≤ 2*K+2*J+2 := by dsimp [K,N]; omega
  have hpL : t^L ≤ m-1 := Nat.pow_log_le_self t (by omega)
  have ha2 (j : ℕ) : 2 ≤ t^(J+j+1) := by
    rw [pow_succ]
    have hpow : 0 < t^(J+j) := pow_pos ht0 _
    nlinarith
  have ham (j : ℕ) (hj : j ∈ Finset.range K) : (t^(J+j+1))^2 < m := by
    have hjK := Finset.mem_range.mp hj
    have he : (J+j+1)*2 ≤ L := by dsimp [K,N] at hjK; omega
    calc
      _ = t^((J+j+1)*2) := (pow_mul t (J+j+1) 2).symm
      _ ≤ t^L := Nat.pow_le_pow_right ht0 he
      _ < m := by omega
  have hainj : Function.Injective (fun j : ℕ => t^(J+j+1)) :=
    (show StrictMono (fun j : ℕ => t^(J+j+1)) from
      fun i j hij => Nat.pow_lt_pow_right (by omega) (by omega)).injective
  have he : (∑ j ∈ Finset.range K, (u (J+j))^2) ≤
      16*zetaTwo*‖scaledError m‖^2 := by
    calc
      _ = ∑ j ∈ Finset.range K,
          (fourSite (scaledError m) (t^(J+j+1)) /
            ((t^(J+j+1) : ℕ) : ℝ)^2)^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [scaledError_fourSite _ m (ha2 j) (ham j hj)]
      _ ≤ _ := fourSite_sample_sum_le _ _ hainj.injOn (fun j _ => ha2 j) _
  have hl : (K : ℝ)*(δ^2/2) ≤
      ∑ j ∈ Finset.range K, (u (J+j))^2 := by
    calc
      _ = ∑ _j ∈ Finset.range K, δ^2/2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => (hJ (J+j) (by omega)).le)
  have hk : (K : ℝ)*δ^2 ≤ 32*zetaTwo*‖scaledError m‖^2 := by
    nlinarith
  have hml : m ≤ t^(L+1) := by
    have hh := Nat.lt_pow_succ_log_self (by omega : 1 < t) (m-1)
    change m-1 < t^(L+1) at hh
    omega
  have hlog : Real.log (m : ℝ) ≤ ((L : ℝ)+1)*Real.log (t : ℝ) := by
    calc
      _ ≤ Real.log ((t^(L+1) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hml)
      _ = _ := by rw [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  have hKLr : (L : ℝ)+1 ≤ 2*(K : ℝ)+2*(J : ℝ)+2 := by exact_mod_cast hKL
  have hb := mul_le_mul_of_nonneg_right hKLr hlogt.le
  have hk' : 2*(K : ℝ)*Real.log (t : ℝ) ≤
      (64*zetaTwo*Real.log (t : ℝ)/δ^2)*‖scaledError m‖^2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_right hk hlogt.le
    nlinarith
  nlinarith

theorem eventually_sqrt_log_lower_of_affine
    (E : ℕ → ℝ) (hE : ∀ m, 0 ≤ E m)
    (A B : ℝ) (hA : 0 < A)
    (hb : ∀ᶠ m : ℕ in atTop, Real.log (m : ℝ) ≤ A * (E m) ^ 2 + B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c ≤ E m / Real.sqrt (Real.log (m : ℝ)) := by
  let c := Real.sqrt (1/(2*A))
  have hC : 0 < 1/(2*A) := by positivity
  refine ⟨c, Real.sqrt_pos.mpr hC, ?_⟩
  have ht := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hb, ht.eventually (eventually_gt_atTop (max (2*B) 0))] with m hm hl
  have hl0 : 0 < Real.log (m : ℝ) := (le_max_right _ _).trans_lt hl
  have hlB : 2*B < Real.log (m : ℝ) := (le_max_left _ _).trans_lt hl
  have hroot : (Real.sqrt (Real.log (m : ℝ)))^2 = Real.log (m : ℝ) :=
    Real.sq_sqrt hl0.le
  have hq : 1/(2*A) ≤ (E m / Real.sqrt (Real.log (m : ℝ)))^2 := by
    rw [div_pow, hroot]
    apply (le_div_iff₀ hl0).mpr
    calc
      (1/(2*A))*Real.log (m : ℝ) = Real.log (m : ℝ)/(2*A) := by ring
      _ ≤ (E m)^2 := (div_le_iff₀ (by positivity : 0 < 2*A)).mpr (by nlinarith)
  have hq0 : 0 ≤ E m / Real.sqrt (Real.log (m : ℝ)) := div_nonneg (hE m) (Real.sqrt_nonneg _)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2 = 1/(2*A) := Real.sq_sqrt hC.le
  nlinarith

theorem positive_log_leakage_lower_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c ≤ (m : ℝ)*leakage m / Real.sqrt (Real.log (m : ℝ)) := by
  have hex : ∃ t : ℕ, 2 ≤ t ∧ qDifference displacement t ≠ 0 := by
    by_contra hh
    apply hRH
    apply QSquarefreePrimeLocalTests.riemannHypothesis_of_difference_tendsto_zero
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with t ht
    have hz : qDifference displacement t = 0 := by
      by_contra hn
      exact hh ⟨t, ht, hn⟩
    exact hz.symm
  obtain ⟨t, ht, hn⟩ := hex
  obtain ⟨A, hA, B, hb⟩ := log_le_affine_scaledError_of_difference_ne_zero t ht hn
  obtain ⟨c, hc, he⟩ := eventually_sqrt_log_lower_of_affine
    (fun m => ‖scaledError m‖) (fun _ => norm_nonneg _) A B hA hb
  exact ⟨c, hc, by simpa only [scaledError_norm] using he⟩

theorem riemannHypothesis_of_log_leakage_liminf_zero
    (h : Filter.liminf (fun m : ℕ => ENNReal.ofReal
      ((m : ℝ)*leakage m / Real.sqrt (Real.log (m : ℝ)))) atTop = 0) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨c, hc, he⟩ := positive_log_leakage_lower_of_not_RH hRH
  have hf : ∃ᶠ m : ℕ in atTop, ENNReal.ofReal
      ((m : ℝ)*leakage m / Real.sqrt (Real.log (m : ℝ))) < ENNReal.ofReal c :=
    Filter.frequently_lt_of_liminf_lt (h := by rw [h]; exact ENNReal.ofReal_pos.mpr hc)
  obtain ⟨m, hm, hmc⟩ := (hf.and_eventually he).exists
  exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal hmc)) hm

open SquarefreeRadicalDifference UniqueFactorizationMonoid
open RiemannResearch.NumberTheory.ApproximateSquareTests

/-- Every sufficiently late set of sites with the same nonzero jump contributes
to the energy of the actual scaled error, even when several primes vary. -/
theorem radical_fiber_card_mul_sq_le_scaledError
    (t : ℕ) (hδ : qDifference displacement t ≠ 0) :
    ∃ N : ℕ, ∀ (m : ℕ) (s : Finset ℕ),
      (∀ n ∈ s, N ≤ n ∧ 2 ≤ n ∧ n^2 < m ∧ radical n = t) →
      (s.card : ℝ) * (qDifference displacement t)^2 ≤
        64 * ZetaTwoProbability.zetaTwo * ‖scaledError m‖^2 := by
  let δ := qDifference displacement t
  have hd : 0 < |δ| := abs_pos.mpr hδ
  have hsmall := (Metric.tendsto_nhds.mp normalized_test_error_tendsto_zero)
    (|δ| / 2) (half_pos hd)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, ?_⟩
  intro m s hs
  have hterm (n : ℕ) (hn : n ∈ s) :
      δ^2 / 4 ≤ (fourSite (scaledError m) n / (n : ℝ)^2)^2 := by
    obtain ⟨hnN, hn2, hnm, hr⟩ := hs n hn
    have hx := hN n hnN
    rw [Real.dist_eq, sub_zero,
      QSquarefreeDisplacementRegularity.displacement_difference_radical n hn2, hr] at hx
    rw [scaledError_fourSite n m hn2 hnm]
    let u := weightedTest (qSequence displacement) n / (n : ℝ)^2
    change |u - δ| < |δ| / 2 at hx
    have hdu : |δ| ≤ |u - δ| + |u| := by
      calc
        |δ| = |(δ-u)+u| := by rw [sub_add_cancel]
        _ ≤ |δ-u| + |u| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm δ u]
    change δ^2 / 4 ≤ u^2
    have hu : |δ| / 2 ≤ |u| := by linarith
    nlinarith [sq_abs δ, sq_abs u,
      mul_self_le_mul_self (by positivity : 0 ≤ |δ| / 2) hu]
  have hsum := Finset.sum_le_sum hterm
  have he := fourSite_sample_sum_le s (fun n : ℕ => n)
    (fun _ _ _ _ heq => heq) (fun n hn => (hs n hn).2.1) (scaledError m)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  change (s.card : ℝ) * δ^2 ≤ _
  linarith

theorem riemannHypothesis_of_squarefree_orbit_leakage
    (h : ∀ t : ℕ, 2 ≤ t → Squarefree t → ∀ ε : ℝ, 0 < ε →
      ∃ᶠ j : ℕ in atTop, ∃ m : ℕ, (t^(j+1))^2 < m ∧
        |fourSite (scaledError m) (t^(j+1)) / ((t^(j+1) : ℕ) : ℝ)^2| < ε) :
    RiemannHypothesis := by
  have hz (t : ℕ) (ht : 2 ≤ t) (hsq : Squarefree t) : qDifference displacement t = 0 := by
    by_contra hn
    have hd : 0 < |qDifference displacement t| := abs_pos.mpr hn
    have hh := (normalized_test_power_tendsto t ht).abs
    have hev := hh.eventually (eventually_gt_nhds
      (show |qDifference displacement t| / 2 < |qDifference displacement t| by linarith))
    obtain ⟨j, ⟨m, hm, he⟩, hj⟩ :=
      ((h t ht hsq _ (half_pos hd)).and_eventually hev).exists
    have hpow : 2 ≤ t^(j+1) := by
      rw [pow_succ]
      have hp : 0 < t^j := pow_pos (by omega) _
      nlinarith
    rw [scaledError_fourSite _ m hpow hm] at he
    exact (not_lt_of_ge hj.le) he
  apply QSquarefreePrimeLocalTests.riemannHypothesis_of_difference_tendsto_zero
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  change 0 = qDifference displacement n
  rw [QSquarefreeDisplacementRegularity.displacement_difference_radical n hn]
  exact (hz _ (Nat.two_le_radical_iff.mpr hn) squarefree_radical).symm

end RiemannResearch.RH.QSquarefreeMultiplierLeakage
