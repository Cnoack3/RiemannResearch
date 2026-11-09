import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Additive rigidity from vanishing dyadic variation

I. Kátai, On additive functions (1978), equations (1.1) and (1.2),
https://doi.org/10.5486/PMD.1978.25.3-4.10, records the additive rigidity
statement and the short-interval refinement due to E. Wirsing.
For the limit over all dyadic starting points, a proof uses the Cesàro
means of two arithmetic progressions. Their difference gives the drift
under integer division, whose logarithmic slope is independent of the base.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory

private def variation (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, |f (i + 1) - f i|

private theorem variation_nonneg (f : ℕ → ℝ) (N : ℕ) : 0 ≤ variation f N :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private theorem variation_mono (f : ℕ → ℝ) : Monotone (variation f) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => abs_nonneg _)

private theorem variation_div_tendsto (f : ℕ → ℝ)
    (h : Tendsto (fun M : ℕ =>
      (∑ i ∈ Finset.range M, |f (M + i + 1) - f (M + i)|) / (M : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => variation f N / (N : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hhalf : 0 < η / 2 := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds hhalf))
  let J : ℕ := 2 * (K + 1)
  let C := variation f J
  have hC : 0 ≤ C := variation_nonneg _ _
  have hwin (m : ℕ) (hm : K + 1 ≤ m) :
      variation f (m + m) ≤ variation f m + (η / 2) * (m : ℝ) := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have he := (div_lt_iff₀ hm').mp (hK m (by omega))
    unfold variation
    rw [Finset.sum_range_add]
    linarith
  have hb (n : ℕ) : variation f n ≤ C + η * (n : ℝ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n ≤ J
      · exact (variation_mono f hn).trans (le_add_of_nonneg_right (by positivity))
      · let m : ℕ := (n + 1) / 2
        have hm : K + 1 ≤ m := by dsimp [m, J] at *; omega
        have hmn : m < n := by dsimp [m, J] at *; omega
        have hlo : n ≤ m + m := by dsimp [m]; omega
        have hhi : 3 * (m : ℝ) ≤ 2 * (n : ℝ) := by
          have hh : 3 * m ≤ 2 * n := by dsimp [m, J] at *; omega
          exact_mod_cast hh
        calc
          _ ≤ variation f (m + m) := variation_mono f hlo
          _ ≤ variation f m + (η / 2) * (m : ℝ) := hwin m hm
          _ ≤ _ := by nlinarith [ih m hmn, mul_le_mul_of_nonneg_left hhi hη.le]
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (C / η))
  refine ⟨L, ?_⟩
  intro n hn
  have hLn : (L : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one
    ((le_max_left (1 : ℝ) (C / η)).trans hL.le)) hLn
  have hlarge : C / η < (n : ℝ) := ((le_max_right _ _).trans_lt hL).trans_le hLn
  have hlarge' := (div_lt_iff₀ hη).mp hlarge
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (variation_nonneg f n) hnpos.le)]
  apply (div_lt_iff₀ hnpos).mpr
  dsimp [η] at *
  nlinarith [hb n]

private theorem abs_sub_le_range_variation (f : ℕ → ℝ) (s t : ℕ) :
    |f (s + t) - f s| ≤ ∑ i ∈ Finset.range t, |f (s + i + 1) - f (s + i)| := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    exact (abs_sub_le (f (s + t + 1)) (f (s + t)) (f s)).trans
      (by linarith)

private theorem abs_le_variation (f : ℕ → ℝ) {i N : ℕ} (hi : i ≤ N) :
    |f i| ≤ |f 0| + variation f N := by
  have h₁ : |f i| ≤ |f i - f 0| + |f 0| := by
    simpa only [sub_zero] using abs_sub_le (f i) (f 0) 0
  have h₂ : |f i - f 0| ≤ variation f i := by
    simpa only [zero_add, variation] using abs_sub_le_range_variation f 0 i
  linarith [variation_mono f hi]

private theorem sum_range_blocks (f : ℕ → ℝ) (a q : ℕ) :
    (∑ i ∈ Finset.range (a * q), f i) =
      ∑ k ∈ Finset.range q, ∑ i ∈ Finset.range a, f (a * k + i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

private def mean (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ Finset.range N, f i) / (N : ℝ)

private def progressionMean (f : ℕ → ℝ) (a j Q : ℕ) : ℝ :=
  mean (fun i => f (a * i + j)) Q

private theorem mean_sub_progressionMean_le (f : ℕ → ℝ) {a j N : ℕ}
    (hj : j < a) (hN : a ≤ N) :
    |mean f N - progressionMean f a j (N / a)| ≤
      (2 * (a : ℝ)) * (variation f N / (N : ℝ)) +
        (2 * (a : ℝ)) * ((|f 0| + variation f N) / (N : ℝ)) := by
  let q := N / a
  let r := N % a
  let B := progressionMean f a j q
  let T := |f 0| + variation f N
  let d := fun i => |f (i + 1) - f i|
  have ha : 0 < a := by omega
  have hq : 0 < q := Nat.div_pos hN ha
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : r < a := Nat.mod_lt _ ha
  have hdiv : a * q + r = N := by dsimp [q, r]; exact Nat.div_add_mod N a
  have hprod : a * q ≤ N := by omega
  have hBT : |B| ≤ T := by
    change |(∑ i ∈ Finset.range q, f (a * i + j)) / (q : ℝ)| ≤ T
    rw [abs_div, abs_of_pos hqr]
    apply (div_le_iff₀ hqr).mpr
    calc
      _ ≤ ∑ i ∈ Finset.range q, |f (a * i + j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range q, T := by
        apply Finset.sum_le_sum
        intro i hi
        have hil : a * (i + 1) ≤ a * q := Nat.mul_le_mul_left a (Finset.mem_range.mp hi)
        apply abs_le_variation f
        rw [Nat.mul_succ] at hil
        omega
      _ = _ := by simp [mul_comm]
  have hsum : (q : ℝ) * B = ∑ k ∈ Finset.range q, f (a * k + j) := by
    change (q : ℝ) * (_ / (q : ℝ)) = _
    field_simp
  have hsplit :
      (∑ i ∈ Finset.range N, f i) =
        (∑ k ∈ Finset.range q, ∑ i ∈ Finset.range a, f (a * k + i)) +
          ∑ i ∈ Finset.range r, f (a * q + i) := by
    calc
      _ = ∑ i ∈ Finset.range (a * q + r), f i :=
        congrArg (fun n => ∑ i ∈ Finset.range n, f i) hdiv.symm
      _ = _ := by rw [Finset.sum_range_add, sum_range_blocks]
  have hsplit' :
      (∑ i ∈ Finset.range N, f i) - (N : ℝ) * B =
        (∑ k ∈ Finset.range q, ∑ i ∈ Finset.range a, (f (a * k + i) - f (a * k + j))) +
          ∑ i ∈ Finset.range r, (f (a * q + i) - B) := by
    have hcast : (a : ℝ) * (q : ℝ) + (r : ℝ) = N := by exact_mod_cast hdiv
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← hsum, hsplit, ← hcast]
    ring
  have hblock (k : ℕ) {i : ℕ} (hi : i < a) :
      |f (a * k + i) - f (a * k + j)| ≤ 2 * ∑ t ∈ Finset.range a, d (a * k + t) := by
    have haux (z : ℕ) (hz : z ≤ a) :
        |f (a * k + z) - f (a * k)| ≤ ∑ t ∈ Finset.range a, d (a * k + t) := by
      exact (abs_sub_le_range_variation f (a * k) z).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hz)
          (fun _ _ _ => abs_nonneg _))
    have ht := abs_sub_le (f (a * k + i)) (f (a * k)) (f (a * k + j))
    rw [abs_sub_comm (f (a * k)) (f (a * k + j))] at ht
    linarith [haux i hi.le, haux j hj.le]
  have hA :
      |∑ k ∈ Finset.range q, ∑ i ∈ Finset.range a, (f (a * k + i) - f (a * k + j))| ≤
        2 * (a : ℝ) * variation f N := by
    calc
      _ ≤ ∑ k ∈ Finset.range q, ∑ i ∈ Finset.range a, 2 * ∑ t ∈ Finset.range a, d (a*k+t) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i hi => hblock k (Finset.mem_range.mp hi))
      _ = 2 * (a : ℝ) * variation f (a * q) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← sum_range_blocks d]
        change (a : ℝ) * (2 * variation f (a * q)) = _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (variation_mono f hprod) (by positivity)
  have hR : |∑ i ∈ Finset.range r, (f (a * q + i) - B)| ≤ 2 * (a : ℝ) * T := by
    have hrr : (r : ℝ) ≤ a := by exact_mod_cast hr.le
    calc
      _ ≤ ∑ i ∈ Finset.range r, 2 * T := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        have hfi : |f (a * q + i)| ≤ T :=
          abs_le_variation f (by have := Finset.mem_range.mp hi; omega)
        have he := abs_sub_le (f (a * q + i)) 0 B
        simp only [sub_zero, zero_sub, abs_neg] at he
        linarith
      _ = (r : ℝ) * (2 * T) := by simp
      _ ≤ _ := by
        have hT : 0 ≤ T := add_nonneg (abs_nonneg _) (variation_nonneg _ _)
        nlinarith [mul_le_mul_of_nonneg_right hrr hT]
  have hb : mean f N - B = ((∑ i ∈ Finset.range N, f i) - (N : ℝ) * B) / (N : ℝ) := by
    unfold mean
    field_simp
  rw [hb, abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  rw [hsplit']
  have ht := abs_add_le (∑ k ∈ Finset.range q, ∑ i ∈ Finset.range a,
    (f (a * k + i) - f (a * k + j))) (∑ i ∈ Finset.range r, (f (a * q + i) - B))
  calc
    _ ≤ 2 * (a : ℝ) * variation f N + 2 * (a : ℝ) * T := by linarith
    _ = _ := by dsimp [T]; field_simp

private theorem mean_sub_progressionMean_tendsto (f : ℕ → ℝ)
    (hv : Tendsto (fun N : ℕ => variation f N / (N : ℝ)) atTop (𝓝 0))
    {a j : ℕ} (hj : j < a) :
    Tendsto (fun N => mean f N - progressionMean f a j (N / a)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun N : ℕ => |f 0| / (N : ℝ)) atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_zero] using ht.const_mul |f 0|
  have hmain : Tendsto (fun N : ℕ => (2 * (a : ℝ)) * (variation f N / (N : ℝ)) +
        (2 * (a : ℝ)) * ((|f 0| + variation f N) / (N : ℝ))) atTop (𝓝 0) := by
    simpa only [add_div, mul_zero, add_zero] using
      (hv.const_mul (2 * (a : ℝ))).add ((hconst.add hv).const_mul (2 * (a : ℝ)))
  apply squeeze_zero_norm' _ hmain
  filter_upwards [eventually_ge_atTop a] with N hN
  simpa only [Real.norm_eq_abs] using mean_sub_progressionMean_le f hj hN

private theorem mean_division_drift (f : ℕ → ℝ)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b)
    (hv : Tendsto (fun N : ℕ => variation f N / (N : ℝ)) atTop (𝓝 0))
    {a : ℕ} (ha : 1 < a) :
    Tendsto (fun N => mean f N - mean f (N / a)) atTop (𝓝 (f a)) := by
  have ha0 : 0 < a := by omega
  have ha2 : a < a * a := by nlinarith
  have hdiv : Tendsto (fun N : ℕ => N / a) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b * a)] with N hN
    exact (Nat.le_div_iff_mul_le ha0).mpr hN
  have hl := mean_sub_progressionMean_tendsto f hv ha2
  have hr := (mean_sub_progressionMean_tendsto f hv ha).comp hdiv
  have hprog (Q : ℕ) (hQ : 0 < Q) :
      progressionMean f (a * a) a Q = progressionMean f a 1 Q + f a := by
    have he (k : ℕ) : f (a * a * k + a) = f (a * k + 1) + f a := by
      rw [show a * a * k + a = a * (a * k + 1) by ring,
        hadd a (a * k + 1) ha0 (by omega) (by simp), add_comm]
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
    unfold progressionMean mean
    simp_rw [he, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have ht := (hl.sub hr).add (tendsto_const_nhds (x := f a))
  rw [zero_sub, neg_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (a * a)] with N hN
  change mean f N - progressionMean f (a * a) a (N / (a * a)) -
      (mean f (N / a) - progressionMean f a 1 (N / a / a)) + f a = _
  rw [Nat.div_div_eq_div_mul, hprog _ (Nat.div_pos hN (Nat.mul_pos ha0 ha0))]
  ring


private theorem logSlope_of_division_drift (A : ℕ → ℝ) {a : ℕ} (ha : 1 < a) {c : ℝ}
    (hd : Tendsto (fun n : ℕ => A n - A (n / a)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 (c / Real.log (a : ℝ))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hla : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hd (η * Real.log (a : ℝ))
    (mul_pos hη hla)
  let L := max K a
  let G : ℕ → ℝ := fun n => A n - c * (Nat.log a n : ℝ)
  let C := ∑ i ∈ Finset.range L, |G i|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hG (n : ℕ) : |G n| ≤ C + η * Real.log (a : ℝ) * (Nat.log a n : ℝ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hL : n < L
      · have hmem : n ∈ Finset.range L := Finset.mem_range.mpr hL
        have hb : |G n| ≤ C := Finset.single_le_sum (f := fun i => |G i|)
          (fun _ _ => abs_nonneg _) hmem
        exact hb.trans (le_add_of_nonneg_right (by positivity))
      · have hL' : L ≤ n := le_of_not_gt hL
        have han : a ≤ n := (le_max_right _ _).trans hL'
        have hn : 0 < n := by omega
        have hnlog : 1 ≤ Nat.log a n := by
          by_contra! h
          have ht := Nat.lt_pow_succ_log_self ha n
          have hz : Nat.log a n = 0 := by omega
          simp only [hz, Nat.zero_add, Nat.succ_eq_add_one, pow_one] at ht
          omega
        have hcast : (Nat.log a (n / a) : ℝ) = (Nat.log a n : ℝ) - 1 := by
          rw [Nat.log_div_base, Nat.cast_sub hnlog, Nat.cast_one]
        have heq : G n = (A n - A (n / a) - c) + G (n / a) := by
          dsimp [G]
          rw [hcast]
          ring
        have hstep := hK n ((le_max_left _ _).trans hL')
        rw [Real.dist_eq] at hstep
        have hprev := ih (n / a) (Nat.div_lt_self hn ha)
        rw [hcast] at hprev
        rw [heq]
        exact (abs_add_le _ _).trans (by linarith)
  have hlogt : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_atTop.1 hlogt ((C + |c|) / η + 1))
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < n by omega))
  have hlo : (Nat.log a n : ℝ) * Real.log (a : ℝ) ≤ Real.log (n : ℝ) := by
    have hp : (a : ℝ) ^ Nat.log a n ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self a (show n ≠ 0 by omega)
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hp
  have hhi : Real.log (n : ℝ) ≤ ((Nat.log a n : ℝ) + 1) * Real.log (a : ℝ) := by
    have hp : (n : ℝ) < (a : ℝ) ^ (Nat.log a n + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self ha n
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using
      Real.log_le_log (by positivity) hp.le
  have hround : |(Nat.log a n : ℝ) * Real.log (a : ℝ) - Real.log (n : ℝ)| ≤
      Real.log (a : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |c * (Nat.log a n : ℝ) - c / Real.log (a : ℝ) * Real.log (n : ℝ)| ≤ |c| := by
    have he : c * (Nat.log a n : ℝ) - c / Real.log (a : ℝ) * Real.log (n : ℝ) =
        (c / Real.log (a : ℝ)) *
          ((Nat.log a n : ℝ) * Real.log (a : ℝ) - Real.log (n : ℝ)) := by
      field_simp [hla.ne']
    rw [he, abs_mul, abs_div, abs_of_pos hla]
    exact (mul_le_mul_of_nonneg_left hround (div_nonneg (abs_nonneg _) hla.le)).trans_eq
      (div_mul_cancel₀ _ hla.ne')
  have hres : |A n - c / Real.log (a : ℝ) * Real.log (n : ℝ)| ≤
      C + |c| + η * Real.log (n : ℝ) := by
    have ht := abs_sub_le (A n) (c * (Nat.log a n : ℝ))
      (c / Real.log (a : ℝ) * Real.log (n : ℝ))
    have hg := hG n
    dsimp [G] at hg
    nlinarith [mul_le_mul_of_nonneg_left hlo hη.le]
  have hbig : C + |c| < η * Real.log (n : ℝ) := by
    have h := hN n ((le_max_left _ _).trans hn)
    have hh : (C + |c|) / η < Real.log (n : ℝ) := by linarith
    simpa only [mul_comm (Real.log (n : ℝ))] using (div_lt_iff₀ hη).mp hh
  have he : A n / Real.log (n : ℝ) - c / Real.log (a : ℝ) =
      (A n - c / Real.log (a : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    field_simp [hln.ne']
  rw [Real.dist_eq, he, abs_div, abs_of_pos hln]
  apply (div_lt_iff₀ hln).mpr
  dsimp [η] at *
  linarith

/-- A real arithmetic function with coprime additivity and vanishing dyadic
mean absolute adjacent differences is a constant multiple of the logarithm. -/
theorem eq_log_of_coprime_additive_of_dyadic_variation (f : ℕ → ℝ)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b)
    (hvar : Tendsto (fun M : ℕ =>
      (∑ i ∈ Finset.range M, |f (M + i + 1) - f (M + i)|) / (M : ℝ)) atTop (𝓝 0)) :
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ) := by
  have hv := variation_div_tendsto f hvar
  have h2 := logSlope_of_division_drift (mean f) (by norm_num : 1 < (2 : ℕ))
    (mean_division_drift f hadd hv (by norm_num : 1 < (2 : ℕ)))
  refine ⟨f 2 / Real.log (2 : ℕ), ?_⟩
  intro n hn
  by_cases h1 : n = 1
  · subst n
    have hh := hadd 1 1 (by norm_num) (by norm_num) (by simp)
    simp only [mul_one] at hh
    simpa only [Nat.cast_one, Real.log_one, mul_zero] using (by linarith : f 1 = 0)
  have hn2 : 1 < n := by omega
  have hs := logSlope_of_division_drift (mean f) hn2 (mean_division_drift f hadd hv hn2)
  exact (div_eq_iff (Real.log_pos (by exact_mod_cast hn2)).ne').mp
    (tendsto_nhds_unique hs h2)

end RiemannResearch.NumberTheory
