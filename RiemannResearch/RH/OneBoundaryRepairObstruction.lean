import RiemannResearch.RH.PositiveSeedCone
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Tactic.FieldSimp

/-!
# A uniform obstruction to concentrating a root-component repair at one endpoint

The construction below is the actual finite floor sum with Möbius coefficients
on a head and arbitrary additional boundary coefficients.  Its bad jump is
derived from divisor arithmetic, not postulated as the construction's conclusion.
The head-support condition is stated explicitly: the Möbius function vanishes on
divisors of the root endpoint above the head cutoff.  The final theorem discharges
that condition for every endpoint `2^A * 3^B` and head cutoff at least 6.
-/

namespace RiemannResearch.RH.OneBoundaryRepair

open scoped BigOperators
open PositiveSeedCone

noncomputable section

/-- The actual integer floor, regarded as a real-valued sequence. -/
def floorBlock (d k : ℕ) : ℝ := (k / d : ℕ)

/-- The finite Möbius interpolation head. -/
def mobiusHead (K k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) * floorBlock d k

/-- A distinguished root endpoint and arbitrary other finite repair endpoints. -/
def repairedHead {ι : Type*} (K T : ℕ) (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) (k : ℕ) : ℝ :=
  mobiusHead K k - (T : ℝ) / 3 * floorBlock T k +
    ∑ i ∈ s, q i * floorBlock (N i) k

/-- Exact extraction from the two adjacent positive coordinates. -/
def adjacentRemainder (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) + 3) * (1 - F (n + 1)) +
    ((n : ℝ) + 1) * (1 - F (n + 2))) ^ 2 /
      (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3))

theorem adjacent_error_completion (F : ℕ → ℝ) (n : ℕ) :
    weightedError F n + weightedError F (n + 1) =
      (F (n + 2) - F (n + 1)) ^ 2 / (2 * ((n : ℝ) + 2) ^ 2) +
        adjacentRemainder F n := by
  unfold weightedError Pareto.positiveWeight adjacentRemainder
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem adjacentRemainder_nonneg (F : ℕ → ℝ) (n : ℕ) :
    0 ≤ adjacentRemainder F n := by
  unfold adjacentRemainder
  positivity

theorem fullError_lower_of_root_jump (F : ℕ → ℝ) (n : ℕ)
    (hsum : Summable (weightedError F))
    (hjump : F (n + 2) - F (n + 1) = -((n : ℝ) + 2) / 3) :
    (1 : ℝ) / 18 ≤ ∑' k : ℕ, weightedError F k := by
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have he : (F (n + 2) - F (n + 1)) ^ 2 /
      (2 * ((n : ℝ) + 2) ^ 2) = (1 : ℝ) / 18 := by
    rw [hjump]
    field_simp
    <;> ring
  have hp : (1 : ℝ) / 18 ≤ weightedError F n + weightedError F (n + 1) := by
    rw [adjacent_error_completion, he]
    exact le_add_of_nonneg_right (adjacentRemainder_nonneg F n)
  calc
    (1 : ℝ) / 18 ≤ weightedError F n + weightedError F (n + 1) := hp
    _ = ∑ k ∈ ({n, n + 1} : Finset ℕ), weightedError F k := by
      simp [show n ≠ n + 1 by omega]
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

theorem floorBlock_mul (d k : ℕ) :
    (d : ℝ) * floorBlock d k = (k : ℝ) - Pareto.residue d k := by
  have h := Nat.mod_add_div k d
  unfold floorBlock Pareto.residue
  have hr : ((k % d : ℕ) : ℝ) + (d : ℝ) * ((k / d : ℕ) : ℝ) = (k : ℝ) :=
    by exact_mod_cast h
  linarith

theorem floorBlock_difference (d T : ℕ) (hd : 0 < d) (hT : 0 < T) :
    floorBlock d T - floorBlock d (T - 1) = if d ∣ T then 1 else 0 := by
  have hTcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    exact_mod_cast (show (T : ℤ) - 1 = ((T - 1 : ℕ) : ℤ) by omega).symm
  have he := Pareto.residue_difference d T hT
  have hx := floorBlock_mul d T
  have hy := floorBlock_mul d (T - 1)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [hTcast] at hy
  apply (mul_left_cancel₀ (ne_of_gt hdR))
  split_ifs at he ⊢ <;> nlinarith

/-- Removing the exact linear part leaves a uniformly bounded finite floor sum. -/
theorem floor_sum_linear_defect_bound {ι : Type*} (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) (hN : ∀ i ∈ s, 0 < N i) (k : ℕ) :
    |(∑ i ∈ s, q i * floorBlock (N i) k) -
      (k : ℝ) * ∑ i ∈ s, q i / (N i : ℝ)| ≤
        ∑ i ∈ s, |q i / (N i : ℝ)| * (N i : ℝ) := by
  have hterm (i : ι) (hi : i ∈ s) :
      |q i * floorBlock (N i) k - (k : ℝ) * (q i / (N i : ℝ))| ≤
        |q i / (N i : ℝ)| * (N i : ℝ) := by
    have hn : (N i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hN i hi))
    have he : q i * floorBlock (N i) k - (k : ℝ) * (q i / (N i : ℝ)) =
        -(q i / (N i : ℝ)) * Pareto.residue (N i) k := by
      have hm := congrArg (fun x : ℝ => q i * x) (floorBlock_mul (N i) k)
      field_simp
      nlinarith
    rw [he, abs_mul, abs_neg]
    have hres : |Pareto.residue (N i) k| ≤ (N i : ℝ) := by
      unfold Pareto.residue
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (Nat.mod_lt k (hN i hi)).le
    exact mul_le_mul_of_nonneg_left hres (abs_nonneg _)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i hi => (abs_le.mp (hterm i hi)).1)
  · exact Finset.sum_le_sum (fun i hi => (abs_le.mp (hterm i hi)).2)

/-- Exact coefficient balance, with the root charge already substituted. -/
def headRepairBalance {ι : Type*} (K : ℕ) (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) : Prop :=
  (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) +
    (∑ i ∈ s, q i / (N i : ℝ)) = (1 : ℝ) / 3

/-- Balanced actual floor repairs have summable full Pareto error. -/
theorem repairedHead_weightedError_summable {ι : Type*} (K T : ℕ) (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) (hT : 0 < T)
    (hN : ∀ i ∈ s, 0 < N i) (hbalance : headRepairBalance K s N q) :
    Summable (weightedError (repairedHead K T s N q)) := by
  let Chead : ℝ := ∑ d ∈ Finset.Icc 1 K,
    |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ)| * (d : ℝ)
  let Cother : ℝ := ∑ i ∈ s, |q i / (N i : ℝ)| * (N i : ℝ)
  apply weightedError_summable_of_bounded _ (Chead + (T : ℝ) / 3 + Cother)
  intro k
  have hh := floor_sum_linear_defect_bound (Finset.Icc 1 K) id
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (fun d hd => (Finset.mem_Icc.mp hd).1) k
  have ho := floor_sum_linear_defect_bound s N q hN k
  have hTcast : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hr0 := floorBlock_mul T k
  have hr : |-(T : ℝ) / 3 * floorBlock T k + (k : ℝ) / 3| ≤ (T : ℝ) / 3 := by
    have he : -(T : ℝ) / 3 * floorBlock T k + (k : ℝ) / 3 =
        Pareto.residue T k / 3 := by linarith
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).mpr
    unfold Pareto.residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.mod_lt k hT).le
  have he : repairedHead K T s N q k =
      (mobiusHead K k - (k : ℝ) *
        (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ))) +
      (-(T : ℝ) / 3 * floorBlock T k + (k : ℝ) / 3) +
      ((∑ i ∈ s, q i * floorBlock (N i) k) -
        (k : ℝ) * ∑ i ∈ s, q i / (N i : ℝ)) := by
    unfold headRepairBalance at hbalance
    unfold repairedHead
    nlinarith [congrArg (fun x : ℝ => (k : ℝ) * x) hbalance]
  rw [he]
  calc
    _ ≤ |mobiusHead K k - (k : ℝ) *
        (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ))| +
        |-(T : ℝ) / 3 * floorBlock T k + (k : ℝ) / 3| +
        |(∑ i ∈ s, q i * floorBlock (N i) k) -
          (k : ℝ) * ∑ i ∈ s, q i / (N i : ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Chead + (T : ℝ) / 3 + Cother := by
      change |mobiusHead K k - _| ≤ Chead at hh
      change |_ - _| ≤ Cother at ho
      exact add_le_add (add_le_add hh hr) ho

/-- The genuine Möbius divisor sum, derived by the project's inversion theorem. -/
theorem moebius_divisor_sum_zero (T : ℕ) (hT : 1 < T) :
    (∑ d ∈ T.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
  have hi := (Pareto.mobius_inversion
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (fun k => (if k = 0 then 0 else 1 : ℝ) -
      (if k - 1 = 0 then 0 else 1 : ℝ))).mpr
      (fun d hd => Pareto.mobiusDifference_one d hd)
  have hh := hi T (by omega)
  simpa [show T ≠ 0 by omega, show T - 1 ≠ 0 by omega] using hh

/-- All nonzero divisor terms are on the finite head; no truncation is dropped. -/
theorem mobius_head_divisor_sum (K T : ℕ) (hT : 0 < T)
    (htail : ∀ d ∈ T.divisors, K < d → ArithmeticFunction.moebius d = 0) :
    (∑ d ∈ Finset.Icc 1 K,
      (ArithmeticFunction.moebius d : ℝ) * (if d ∣ T then 1 else 0)) =
      ∑ d ∈ T.divisors, (ArithmeticFunction.moebius d : ℝ) := by
  classical
  let A := (Finset.Icc 1 K).filter (fun d => d ∣ T)
  have hsub : A ⊆ T.divisors := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    exact Nat.mem_divisors.mpr ⟨hd'.2, ne_of_gt hT⟩
  have hs : (∑ d ∈ A, (ArithmeticFunction.moebius d : ℝ)) =
      ∑ d ∈ T.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hlarge : K < d := by
      by_contra hn
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hd, by omega⟩, (Nat.mem_divisors.mp hd).1⟩
    rw [htail d hd hlarge]
    norm_num
  rw [← hs]
  simp [A, Finset.sum_filter, mul_ite]

theorem mobiusHead_root_difference_zero (K T : ℕ) (hT : 1 < T)
    (htail : ∀ d ∈ T.divisors, K < d → ArithmeticFunction.moebius d = 0) :
    mobiusHead K T - mobiusHead K (T - 1) = 0 := by
  unfold mobiusHead
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hs : (∑ d ∈ Finset.Icc 1 K,
      (ArithmeticFunction.moebius d : ℝ) *
        (floorBlock d T - floorBlock d (T - 1))) =
      ∑ d ∈ Finset.Icc 1 K,
        (ArithmeticFunction.moebius d : ℝ) * (if d ∣ T then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [floorBlock_difference d T (Finset.mem_Icc.mp hd).1 (by omega)]
  rw [hs, mobius_head_divisor_sum K T (by omega) htail,
    moebius_divisor_sum_zero T hT]

/-- The actual concentrated repair has the large root jump. -/
theorem repairedHead_root_jump {ι : Type*} (K T : ℕ) (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) (hT : 1 < T)
    (htail : ∀ d ∈ T.divisors, K < d → ArithmeticFunction.moebius d = 0)
    (hN : ∀ i ∈ s, 0 < N i)
    (hother : ∀ i ∈ s, ¬ N i ∣ T) :
    repairedHead K T s N q T - repairedHead K T s N q (T - 1) = -(T : ℝ) / 3 := by
  have hh := mobiusHead_root_difference_zero K T hT htail
  have hr := floorBlock_difference T T (by omega) (by omega)
  simp only [dvd_refl, ↓reduceIte] at hr
  have hrScaled := congrArg (fun x : ℝ => (T : ℝ) / 3 * x) hr
  have hs : (∑ i ∈ s, q i * floorBlock (N i) T) -
      (∑ i ∈ s, q i * floorBlock (N i) (T - 1)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← mul_sub, floorBlock_difference (N i) T (hN i hi) (by omega)]
    simp [hother i hi]
  unfold repairedHead
  linarith

/-- Uniform full infinite error obstruction for the explicitly defined construction.
The analytic hypothesis is kept explicit; every balanced finite repair satisfies it. -/
theorem repairedHead_fullError_lower {ι : Type*} (K T : ℕ) (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) (hT : 1 < T)
    (htail : ∀ d ∈ T.divisors, K < d → ArithmeticFunction.moebius d = 0)
    (hN : ∀ i ∈ s, 0 < N i)
    (hother : ∀ i ∈ s, ¬ N i ∣ T)
    (hsum : Summable (weightedError (repairedHead K T s N q))) :
    (1 : ℝ) / 18 ≤ ∑' k : ℕ, weightedError (repairedHead K T s N q) k := by
  have ht2 : T - 2 + 2 = T := by omega
  have ht1 : T - 2 + 1 = T - 1 := by omega
  have hc : ((T - 2 : ℕ) : ℝ) + 2 = (T : ℝ) := by exact_mod_cast ht2
  apply fullError_lower_of_root_jump _ (T - 2) hsum
  rw [ht2, ht1, hc]
  exact repairedHead_root_jump K T s N q hT htail hN hother

/-- The whole balanced one-boundary construction has the same positive error floor. -/
theorem balanced_repairedHead_fullError_lower {ι : Type*} (K T : ℕ) (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) (hT : 1 < T)
    (htail : ∀ d ∈ T.divisors, K < d → ArithmeticFunction.moebius d = 0)
    (hN : ∀ i ∈ s, 0 < N i)
    (hother : ∀ i ∈ s, ¬ N i ∣ T)
    (hbalance : headRepairBalance K s N q) :
    (1 : ℝ) / 18 ≤ ∑' k : ℕ, weightedError (repairedHead K T s N q) k := by
  exact repairedHead_fullError_lower K T s N q hT htail hN hother
    (repairedHead_weightedError_summable K T s N q (by omega) hN hbalance)

/-- Every nonzero Möbius divisor of a 2,3-smooth number divides 6. -/
theorem moebius_tail_zero_of_dvd_six_pow (K T L : ℕ) (hK : 6 ≤ K)
    (hsmooth : T ∣ 6 ^ (L + 1)) :
    ∀ d ∈ T.divisors, K < d → ArithmeticFunction.moebius d = 0 := by
  intro d hd hlarge
  by_contra hmu
  have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
  have hd6pow : d ∣ 6 ^ (L + 1) := dvd_trans (Nat.mem_divisors.mp hd).1 hsmooth
  have hd6 : d ∣ 6 := (hsq.dvd_pow_iff_dvd (by omega : L + 1 ≠ 0)).mp hd6pow
  have hsmall : d ≤ 6 := Nat.le_of_dvd (by decide) hd6
  omega

theorem seedPowers_dvd_six_pow (A B : ℕ) :
    2 ^ A * 3 ^ B ∣ 6 ^ (A + B + 1) := by
  refine ⟨6 * 3 ^ A * 2 ^ B, ?_⟩
  rw [pow_add, pow_add, pow_one]
  rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow, mul_pow]
  ring

/-- No moving single root endpoint avoids the positive floor, even when placed
immediately beyond the interpolated head.  All signs are unrestricted. -/
theorem smooth_single_boundary_fullError_lower {ι : Type*} (K A B : ℕ) (s : Finset ι)
    (N : ι → ℕ) (q : ι → ℝ) (hK : 6 ≤ K) (hT : K < 2 ^ A * 3 ^ B)
    (hN : ∀ i ∈ s, 0 < N i)
    (hother : ∀ i ∈ s, ¬ N i ∣ 2 ^ A * 3 ^ B)
    (hbalance : headRepairBalance K s N q) :
    (1 : ℝ) / 18 ≤
      ∑' k : ℕ, weightedError (repairedHead K (2 ^ A * 3 ^ B) s N q) k := by
  apply balanced_repairedHead_fullError_lower K (2 ^ A * 3 ^ B) s N q (by omega)
  · exact moebius_tail_zero_of_dvd_six_pow K (2 ^ A * 3 ^ B) (A + B) hK
      (seedPowers_dvd_six_pow A B)
  · exact hN
  · exact hother
  · exact hbalance

end
end RiemannResearch.RH.OneBoundaryRepair
