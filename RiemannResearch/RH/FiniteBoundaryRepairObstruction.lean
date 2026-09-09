import RiemannResearch.RH.OneBoundaryRepairObstruction
import RiemannResearch.RH.FiniteRepairTriangular

/-!
# A fixed number of root-component repairs cannot converge

These are actual signed floor sums.  Their triangular divisor-jump relation is
derived below.  Smooth-divisor cancellation and exact coefficient balance then
give the complete infinite-error floor for any fixed number of root endpoints.
No location bound on these endpoints is imposed.
-/

namespace RiemannResearch.RH.FiniteBoundaryRepair

open scoped BigOperators
open OneBoundaryRepair PositiveSeedCone

noncomputable section

def repairedHead {ι : Type*} (K N : ℕ) (T : ℕ → ℕ) (a : ℕ → ℝ)
    (s : Finset ι) (M : ι → ℕ) (q : ι → ℝ) (k : ℕ) : ℝ :=
  mobiusHead K k +
    (∑ i ∈ Finset.range N, (T i : ℝ) * a i * floorBlock (T i) k) +
    ∑ i ∈ s, q i * floorBlock (M i) k

def normalizedJump (F : ℕ → ℝ) (T : ℕ) : ℝ :=
  (F T - F (T - 1)) / (T : ℝ)

def divisorCoefficient (T : ℕ → ℕ) (j i : ℕ) : ℝ :=
  if T i ∣ T j then (T i : ℝ) / (T j : ℝ) else 0

theorem proper_divisor_double_le (d n : ℕ) (hdn : d < n) (hdiv : d ∣ n) :
    2 * d ≤ n := by
  obtain ⟨c, hc⟩ := hdiv
  have hc2 : 2 ≤ c := by
    by_contra hn
    have hcases : c = 0 ∨ c = 1 := by omega
    rcases hcases with h | h <;> simp_all
  rw [hc]
  nlinarith

theorem divisorCoefficient_bounds (T : ℕ → ℕ) (hinc : StrictMono T)
    (i j : ℕ) (hij : i < j) (hTj : 0 < T j) :
    0 ≤ divisorCoefficient T j i ∧ divisorCoefficient T j i ≤ (1 / 2 : ℝ) := by
  unfold divisorCoefficient
  split_ifs with hd
  · have hnat := proper_divisor_double_le (T i) (T j) (hinc hij) hd
    have hreal : 2 * (T i : ℝ) ≤ (T j : ℝ) := by exact_mod_cast hnat
    constructor
    · positivity
    · apply (div_le_iff₀ (show 0 < (T j : ℝ) by exact_mod_cast hTj)).mpr
      nlinarith
  · norm_num

/-- Every earlier divisible endpoint is present in the exact jump formula. -/
theorem repairedHead_normalizedJump {ι : Type*}
    (K N : ℕ) (T : ℕ → ℕ) (a : ℕ → ℝ)
    (s : Finset ι) (M : ι → ℕ) (q : ι → ℝ)
    (hinc : StrictMono T) (hT : ∀ i < N, 1 < T i)
    (htail : ∀ j < N, ∀ d ∈ (T j).divisors,
      K < d → ArithmeticFunction.moebius d = 0)
    (hM : ∀ i ∈ s, 0 < M i)
    (hother : ∀ i ∈ s, ∀ j < N, ¬ M i ∣ T j)
    (j : ℕ) (hj : j < N) :
    normalizedJump (repairedHead K N T a s M q) (T j) =
      a j + ∑ i ∈ Finset.range j, divisorCoefficient T j i * a i := by
  classical
  have hTj : 0 < T j := lt_trans Nat.zero_lt_one (hT j hj)
  have hTjR : (T j : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hTj)
  have hh := mobiusHead_root_difference_zero K (T j) (hT j hj) (htail j hj)
  have hroot :
      (∑ i ∈ Finset.range N, (T i : ℝ) * a i * floorBlock (T i) (T j)) -
      (∑ i ∈ Finset.range N, (T i : ℝ) * a i * floorBlock (T i) (T j - 1)) =
      (T j : ℝ) * ∑ i ∈ Finset.range N, divisorCoefficient T j i * a i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_sub, floorBlock_difference (T i) (T j)
      (lt_trans Nat.zero_lt_one (hT i (Finset.mem_range.mp hi))) hTj]
    unfold divisorCoefficient
    split_ifs <;> field_simp <;> ring
  have ho : (∑ i ∈ s, q i * floorBlock (M i) (T j)) -
      (∑ i ∈ s, q i * floorBlock (M i) (T j - 1)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← mul_sub, floorBlock_difference (M i) (T j) (hM i hi) hTj]
    simp [hother i hi j hj]
  have hfull : normalizedJump (repairedHead K N T a s M q) (T j) =
      ∑ i ∈ Finset.range N, divisorCoefficient T j i * a i := by
    unfold normalizedJump repairedHead
    have he :
      (mobiusHead K (T j) +
        (∑ i ∈ Finset.range N, (T i : ℝ) * a i * floorBlock (T i) (T j)) +
        ∑ i ∈ s, q i * floorBlock (M i) (T j)) -
      (mobiusHead K (T j - 1) +
        (∑ i ∈ Finset.range N, (T i : ℝ) * a i * floorBlock (T i) (T j - 1)) +
        ∑ i ∈ s, q i * floorBlock (M i) (T j - 1)) =
      (T j : ℝ) * ∑ i ∈ Finset.range N, divisorCoefficient T j i * a i := by
      linarith
    rw [he]
    field_simp
  have htruncate :
      (∑ i ∈ Finset.range N, divisorCoefficient T j i * a i) =
      ∑ i ∈ Finset.range (j + 1), divisorCoefficient T j i * a i := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ N))
    intro i hi hnot
    have hji : j < i := by
      simp only [Finset.mem_range] at hi hnot
      omega
    have hd : ¬ T i ∣ T j := by
      intro hdiv
      exact not_le_of_gt (hinc hji) (Nat.le_of_dvd hTj hdiv)
    simp [divisorCoefficient, hd]
  rw [hfull, htruncate, Finset.sum_range_succ]
  simp [divisorCoefficient, hTjR, add_comm]

theorem normalizedJump_sq_le_fullError (F : ℕ → ℝ) (T : ℕ)
    (hT : 1 < T) (hsum : Summable (weightedError F)) :
    (normalizedJump F T) ^ 2 ≤ 2 * ∑' k : ℕ, weightedError F k := by
  have ht2 : T - 2 + 2 = T := by omega
  have ht1 : T - 2 + 1 = T - 1 := by omega
  have htc : ((T - 2 : ℕ) : ℝ) + 2 = (T : ℝ) := by exact_mod_cast ht2
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have hcompletion := adjacent_error_completion F (T - 2)
  rw [ht2, ht1, htc] at hcompletion
  have he : (F T - F (T - 1)) ^ 2 / (2 * (T : ℝ) ^ 2) =
      (normalizedJump F T) ^ 2 / 2 := by
    unfold normalizedJump
    field_simp
  rw [he] at hcompletion
  have hpair : weightedError F (T - 2) + weightedError F (T - 2 + 1) ≤
      ∑' k : ℕ, weightedError F k := by
    calc
      _ = ∑ k ∈ ({T - 2, T - 2 + 1} : Finset ℕ), weightedError F k := by
        simp
      _ ≤ ∑' k : ℕ, weightedError F k :=
        hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)
  rw [ht1] at hpair
  nlinarith [adjacentRemainder_nonneg F (T - 2)]

/-- Antichain endpoints remove exactly the off-diagonal divisor terms. -/
theorem repairedHead_antichain_jump {ι : Type*}
    (K N : ℕ) (T : ℕ → ℕ) (a : ℕ → ℝ)
    (s : Finset ι) (M : ι → ℕ) (q : ι → ℝ)
    (hinc : StrictMono T) (hT : ∀ i < N, 1 < T i)
    (htail : ∀ j < N, ∀ d ∈ (T j).divisors,
      K < d → ArithmeticFunction.moebius d = 0)
    (hM : ∀ i ∈ s, 0 < M i)
    (hother : ∀ i ∈ s, ∀ j < N, ¬ M i ∣ T j)
    (hanti : ∀ i < N, ∀ j < N, i ≠ j → ¬ T i ∣ T j)
    (j : ℕ) (hj : j < N) :
    repairedHead K N T a s M q (T j) -
      repairedHead K N T a s M q (T j - 1) = (T j : ℝ) * a j := by
  have h := repairedHead_normalizedJump K N T a s M q
    hinc hT htail hM hother j hj
  have hz : (∑ i ∈ Finset.range j, divisorCoefficient T j i * a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij := Finset.mem_range.mp hi
    simp [divisorCoefficient, hanti i (by omega) j hj (by omega)]
  rw [hz, add_zero] at h
  unfold normalizedJump at h
  have hn : (T j : ℝ) ≠ 0 := by exact_mod_cast (show T j ≠ 0 by have := hT j hj; omega)
  have he := (div_eq_iff hn).mp h
  simpa [mul_comm] using he

theorem repairedHead_fullError_lower {ι : Type*}
    (K N : ℕ) (T : ℕ → ℕ) (a : ℕ → ℝ)
    (s : Finset ι) (M : ι → ℕ) (q : ι → ℝ)
    (hN : 0 < N) (hinc : StrictMono T) (hT : ∀ i < N, 1 < T i)
    (htail : ∀ j < N, ∀ d ∈ (T j).divisors,
      K < d → ArithmeticFunction.moebius d = 0)
    (hM : ∀ i ∈ s, 0 < M i)
    (hother : ∀ i ∈ s, ∀ j < N, ¬ M i ∣ T j)
    (hcharge : (∑ i ∈ Finset.range N, a i) = -(1 / 3 : ℝ))
    (hsum : Summable (weightedError (repairedHead K N T a s M q))) :
    1 / (72 * (((3 / 2 : ℝ) ^ N) - 1) ^ 2) ≤
      ∑' k : ℕ, weightedError (repairedHead K N T a s M q) k := by
  let F := repairedHead K N T a s M q
  let E : ℝ := ∑' k : ℕ, weightedError F k
  have hE : 0 ≤ E := tsum_nonneg (fun k => weightedError_nonneg F k)
  apply FiniteRepairTriangular.energy_floor a N E hN hE hcharge
  intro j hj
  have heq := repairedHead_normalizedJump K N T a s M q
    hinc hT htail hM hother j hj
  have hjump_sq := normalizedJump_sq_le_fullError F (T j) (hT j hj) hsum
  have hjump : |normalizedJump F (T j)| ≤ Real.sqrt (2 * E) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (show 0 ≤ 2 * E by positivity)]
    exact hjump_sq
  have hcoeff : |∑ i ∈ Finset.range j, divisorCoefficient T j i * a i| ≤
      (1 / 2 : ℝ) * ∑ i ∈ Finset.range j, |a i| := by
    calc
      _ ≤ ∑ i ∈ Finset.range j, |divisorCoefficient T j i * a i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range j, (1 / 2 : ℝ) * |a i| := by
        apply Finset.sum_le_sum
        intro i hi
        have hc := divisorCoefficient_bounds T hinc i j
          (Finset.mem_range.mp hi) (lt_trans Nat.zero_lt_one (hT j hj))
        rw [abs_mul, abs_of_nonneg hc.1]
        exact mul_le_mul_of_nonneg_right hc.2 (abs_nonneg _)
      _ = (1 / 2 : ℝ) * ∑ i ∈ Finset.range j, |a i| := by rw [Finset.mul_sum]
  have ha : a j = normalizedJump F (T j) -
      ∑ i ∈ Finset.range j, divisorCoefficient T j i * a i := by
    change normalizedJump F (T j) = _ at heq
    linarith
  calc
    |a j| = |normalizedJump F (T j) -
        ∑ i ∈ Finset.range j, divisorCoefficient T j i * a i| := by rw [ha]
    _ ≤ |normalizedJump F (T j)| +
        |∑ i ∈ Finset.range j, divisorCoefficient T j i * a i| := abs_sub _ _
    _ ≤ Real.sqrt (2 * E) + (1 / 2 : ℝ) * ∑ i ∈ Finset.range j, |a i| :=
      add_le_add hjump hcoeff

/-- The exact total linear coefficient of the actual finite floor sum. -/
def slopeBalance {ι : Type*} (K N : ℕ) (a : ℕ → ℝ)
    (s : Finset ι) (M : ι → ℕ) (q : ι → ℝ) : Prop :=
  (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) +
    (∑ i ∈ Finset.range N, a i) + (∑ i ∈ s, q i / (M i : ℝ)) = 0

theorem repairedHead_weightedError_summable {ι : Type*}
    (K N : ℕ) (T : ℕ → ℕ) (a : ℕ → ℝ)
    (s : Finset ι) (M : ι → ℕ) (q : ι → ℝ)
    (hT : ∀ i < N, 0 < T i) (hM : ∀ i ∈ s, 0 < M i)
    (hbalance : slopeBalance K N a s M q) :
    Summable (weightedError (repairedHead K N T a s M q)) := by
  let Chead : ℝ := ∑ d ∈ Finset.Icc 1 K,
    |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ)| * (d : ℝ)
  let Croot : ℝ := ∑ i ∈ Finset.range N,
    |((T i : ℝ) * a i) / (T i : ℝ)| * (T i : ℝ)
  let Cother : ℝ := ∑ i ∈ s, |q i / (M i : ℝ)| * (M i : ℝ)
  apply weightedError_summable_of_bounded _ (Chead + Croot + Cother)
  intro k
  have hh := floor_sum_linear_defect_bound (Finset.Icc 1 K) id
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (fun d hd => (Finset.mem_Icc.mp hd).1) k
  have hr := floor_sum_linear_defect_bound (Finset.range N) T
    (fun i => (T i : ℝ) * a i) (fun i hi => hT i (Finset.mem_range.mp hi)) k
  have ho := floor_sum_linear_defect_bound s M q hM k
  have hrootSlope : (∑ i ∈ Finset.range N, ((T i : ℝ) * a i) / (T i : ℝ)) =
      ∑ i ∈ Finset.range N, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hTi : (T i : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hT i (Finset.mem_range.mp hi)))
    field_simp
  rw [hrootSlope] at hr
  have he : repairedHead K N T a s M q k =
      (mobiusHead K k - (k : ℝ) *
        ∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) +
      ((∑ i ∈ Finset.range N, (T i : ℝ) * a i * floorBlock (T i) k) -
        (k : ℝ) * ∑ i ∈ Finset.range N, a i) +
      ((∑ i ∈ s, q i * floorBlock (M i) k) -
        (k : ℝ) * ∑ i ∈ s, q i / (M i : ℝ)) := by
    unfold slopeBalance at hbalance
    unfold repairedHead
    nlinarith [congrArg (fun x : ℝ => (k : ℝ) * x) hbalance]
  rw [he]
  calc
    _ ≤ |mobiusHead K k - (k : ℝ) *
          ∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)| +
        |(∑ i ∈ Finset.range N, (T i : ℝ) * a i * floorBlock (T i) k) -
          (k : ℝ) * ∑ i ∈ Finset.range N, a i| +
        |(∑ i ∈ s, q i * floorBlock (M i) k) -
          (k : ℝ) * ∑ i ∈ s, q i / (M i : ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Chead + Croot + Cother := by
      change |mobiusHead K k - _| ≤ Chead at hh
      change |_ - _| ≤ Croot at hr
      change |_ - _| ≤ Cother at ho
      exact add_le_add (add_le_add hh hr) ho

/-- Every balanced actual repair with `N` increasing smooth root endpoints has
this floor, independently of endpoint placement and all coefficient signs. -/
theorem smooth_finite_boundary_fullError_lower {ι : Type*}
    (K N : ℕ) (T : ℕ → ℕ) (a : ℕ → ℝ)
    (s : Finset ι) (M : ι → ℕ) (q : ι → ℝ)
    (hK : 6 ≤ K) (hN : 0 < N) (hinc : StrictMono T)
    (hlarge : ∀ i < N, K < T i)
    (hsmooth : ∀ i < N, ∃ A B : ℕ, T i = 2 ^ A * 3 ^ B)
    (hM : ∀ i ∈ s, 0 < M i)
    (hother : ∀ i ∈ s, ∀ j < N, ¬ M i ∣ T j)
    (hcharge : (∑ i ∈ Finset.range N, a i) = -(1 / 3 : ℝ))
    (hbalance : slopeBalance K N a s M q) :
    1 / (72 * (((3 / 2 : ℝ) ^ N) - 1) ^ 2) ≤
      ∑' k : ℕ, weightedError (repairedHead K N T a s M q) k := by
  have hT : ∀ i < N, 1 < T i := by intro i hi; have := hlarge i hi; omega
  apply repairedHead_fullError_lower K N T a s M q hN hinc hT
    _ hM hother hcharge
    (repairedHead_weightedError_summable K N T a s M q
      (fun i hi => lt_trans Nat.zero_lt_one (hT i hi)) hM hbalance)
  intro j hj
  obtain ⟨A, B, he⟩ := hsmooth j hj
  rw [he]
  exact moebius_tail_zero_of_dvd_six_pow K (2 ^ A * 3 ^ B) (A + B) hK
    (seedPowers_dvd_six_pow A B)

end
end RiemannResearch.RH.FiniteBoundaryRepair
