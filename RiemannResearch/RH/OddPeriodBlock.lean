import RiemannResearch.RH.MixedConductorSeedObstruction
import RiemannResearch.RH.ScreenedPrimePowerTelescope
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Dyadic signed tests of an odd-period correction

Source: the fixed-conductor mixed-projection question. The test pairs the two
halves of each dyadic cell, and tests disjoint positive coordinates at successive
scales. The exact dual weight is evaluated by two geometric series.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.OddPeriodBlock

def block (Q H : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range Q, ∑ u ∈ Finset.range H,
    (f (2*H*(Q+n)+H+u) - f (2*H*(Q+n)+u))

def partialSum (Q K : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, (1/4 : ℝ)^(j+1) * block Q (2^j) f

private theorem periodic_multiple {Q : ℕ} {f : ℕ → ℝ} (hf : ∀ n, f (n + Q) = f n)
    (n k : ℕ) : f (n+k*Q) = f n := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul, ← Nat.add_assoc, hf, ih]

private theorem periodic_sum_shift {Q : ℕ} {f : ℕ → ℝ} (hf : ∀ n, f (n + Q) = f n)
    (k : ℕ) : ∑ n ∈ Finset.range Q, f (n+k) = ∑ n ∈ Finset.range Q, f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have htel (q : ℕ) :
        (∑ n ∈ Finset.range q, f ((n+1)+k)) + f k =
        (∑ n ∈ Finset.range q, f (n+k)) + f (q+k) := by
      induction q with
      | zero => simp
      | succ q ihq => simp only [Finset.sum_range_succ]; linarith
    have hs := htel Q
    rw [show Q+k=k+Q by omega, hf] at hs
    have he : ∑ n ∈ Finset.range Q, f (n+(k+1)) =
        ∑ n ∈ Finset.range Q, f ((n+1)+k) := by
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      omega
    rw [he, ← ih]
    linarith

/-- The two half-blocks have identical mass against every odd-period sequence.
The second half is a cyclic shift of the first by (Q+1)/2 outer cells. -/
theorem block_eq_zero_of_odd_period {Q : ℕ} (hQ : Odd Q) (H : ℕ) {f : ℕ → ℝ}
    (hf : ∀ n, f (n + Q) = f n) : block Q H f = 0 := by
  obtain ⟨a, ha⟩ := hQ
  have hmove (n u : ℕ) : f (2*H*(Q+(n+(a+1)))+u) = f (2*H*(Q+n)+H+u) := by
    convert periodic_multiple hf (2*H*(Q+n)+H+u) H using 1
    congr 1
    rw [ha]
    ring
  unfold block
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro u _
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  calc
    _ = ∑ n ∈ Finset.range Q, f (2*H*(Q+(n+(a+1)))+u) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (hmove n u).symm
    _ = _ := periodic_sum_shift (f := fun n => f (2*H*(Q+n)+u)) (fun n => by
      convert periodic_multiple hf (2*H*(Q+n)+u) (2*H) using 1
      congr 1
      ring) (a+1)

theorem partial_eq_zero_of_odd_period {Q : ℕ} (hQ : Odd Q) (K : ℕ) {f : ℕ → ℝ}
    (hf : ∀ n, f (n + Q) = f n) : partialSum Q K f = 0 := by
  unfold partialSum
  simp [block_eq_zero_of_odd_period hQ _ hf]

/-- Sum of the reciprocal Pareto weights in one full block. -/
theorem block_weight (a : ℕ) :
    ∑ u ∈ Finset.range a, ((a+u : ℕ) : ℝ) * ((a+u : ℕ) + 1 : ℝ) =
      (7*(a:ℝ)^3 - a)/3 := by
  have h (k : ℕ) :
      (∑ u ∈ Finset.range k, ((a+u : ℕ) : ℝ) * ((a+u : ℕ) + 1 : ℝ)) =
       (((a:ℝ)+k)^3-((a:ℝ)+k) - (a:ℝ)^3 + a)/3 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [h]
  ring

def dualWeight (Q : ℕ) : ℝ := (Q:ℝ) * (49*(Q:ℝ)^2-1)/21

/-- Exact squared dual weight over the disjoint infinite sequence of blocks. -/
theorem hasSum_dualWeight (Q : ℕ) :
    HasSum (fun j : ℕ => ((1/4 : ℝ)^(j+1))^2 *
      (∑ u ∈ Finset.range (2^(j+1)*Q),
        ((2^(j+1)*Q+u : ℕ) : ℝ) * ((2^(j+1)*Q+u : ℕ)+1 : ℝ))) (dualWeight Q) := by
  have h₁ := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left (7*(Q:ℝ)^3/6)
  have h₂ := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/8)
    (by norm_num : (1/8 : ℝ) < 1)).mul_left ((Q:ℝ)/24)
  have hd : dualWeight Q = (7*(Q:ℝ)^3/6)*(1-1/2)⁻¹ - ((Q:ℝ)/24)*(1-1/8)⁻¹ := by
    unfold dualWeight
    ring
  rw [hd]
  apply (h₁.sub h₂).congr_fun
  intro j
  symm
  rw [block_weight]
  push_cast
  rw [pow_succ, pow_succ (2 : ℝ)]
  have hpow (a : ℝ) (q r : ℕ) : (a^q)^r = (a^r)^q := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm q r]
  have h₁' (j : ℕ) : ((1/4:ℝ)^j)^2 * ((2:ℝ)^j)^3 = (1/2:ℝ)^j := by
    rw [hpow (1/4) j 2, hpow 2 j 3, ← mul_pow]
    norm_num
  have h₂' (j : ℕ) : ((1/4:ℝ)^j)^2 * (2:ℝ)^j = (1/8:ℝ)^j := by
    rw [hpow (1/4) j 2, ← mul_pow]
    norm_num
  rw [← h₁' j, ← h₂' j]
  ring

private theorem flatten_chunks (Q h A : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.range Q, ∑ u ∈ Finset.range h, g (A+h*n+u)) =
    ∑ v ∈ Finset.range (Q*h), g (A+v) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring

private theorem flatten_halves (Q H : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.range Q, ∑ u ∈ Finset.range H,
      (g (2*H*(Q+n)+H+u) + g (2*H*(Q+n)+u))) =
    ∑ v ∈ Finset.range (2*H*Q), g (2*H*Q+v) := by
  calc
    _ = ∑ n ∈ Finset.range Q, ∑ u ∈ Finset.range (2*H), g (2*H*Q+2*H*n+u) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [show 2*H=H+H by omega, Finset.sum_range_add, Finset.sum_add_distrib, add_comm]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro u _ <;> congr 1 <;> ring
    _ = _ := by
      rw [flatten_chunks, Nat.mul_comm Q]

private theorem flatten_scales (Q K : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range K, ∑ v ∈ Finset.range (2^(j+1)*Q), g (2^(j+1)*Q+v)) =
      ∑ v ∈ Finset.range ((2^(K+1)-2)*Q), g (2*Q+v) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hpos : 2 ≤ 2^(K+1) := by
      rw [pow_succ]
      have : 0 < 2^K := by positivity
      omega
    have hstep : ((2^(K+1+1)-2)*Q) = (2^(K+1)-2)*Q+2^(K+1)*Q := by
      rw [← Nat.add_mul, pow_succ 2 (K+1)]
      congr 1
      omega
    have hstart : 2*Q+(2^(K+1)-2)*Q=2^(K+1)*Q := by
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [Finset.sum_range_succ, ih, hstep, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [← Nat.add_assoc, hstart]

private theorem young_coordinate (x : ThresholdHilbert) (u : ℕ) (hu : 0 < u) (t : ℝ) :
    2*t*hilbertSequence x u ≤ positiveWeight u*(hilbertSequence x u)^2 +
      t^2 * ((u:ℝ)*(u+1)) := by
  have hpos : 0 < (u:ℝ)*((u:ℝ)+1) := by positivity
  unfold positiveWeight
  field_simp [hpos.ne']
  nlinarith [sq_nonneg (hilbertSequence x u-t*((u:ℝ)*(u+1)))]

/-- The complete-Pareto variational bound for every finite block test. -/
theorem partial_variational (Q K : ℕ) (hQ : 0 < Q) (x : ThresholdHilbert) (t : ℝ) :
    2*t*partialSum Q K (hilbertSequence x) ≤ ‖x‖^2 + t^2 * dualWeight Q := by
  let p (m : ℕ) := positiveWeight m * (hilbertSequence x m)^2
  let d (m : ℕ) := (m:ℝ)*(m+1)
  have row (j : ℕ) :
      2*t*((1/4:ℝ)^(j+1)*block Q (2^j) (hilbertSequence x)) ≤
        (∑ v ∈ Finset.range (2^(j+1)*Q), p (2^(j+1)*Q+v)) +
        t^2 * (((1/4:ℝ)^(j+1))^2 * ∑ v ∈ Finset.range (2^(j+1)*Q), d (2^(j+1)*Q+v)) := by
    let a := (1/4:ℝ)^(j+1)
    let H : ℕ := 2^j
    have hHP : 0 < H := by dsimp [H]; positivity
    have hH : 2^(j+1)=2*H := by rw [pow_succ, Nat.mul_comm]
    rw [hH]
    change 2*t*(a*block Q H (hilbertSequence x)) ≤ _ + t^2*(a^2*_ )
    rw [← flatten_halves, ← flatten_halves, ← mul_assoc (t^2),
      Finset.mul_sum, ← Finset.sum_add_distrib]
    unfold block
    rw [← mul_assoc (2*t), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    let lo := 2*H*(Q+n)+u
    let hi := 2*H*(Q+n)+H+u
    have hlow : 0 < lo := by dsimp [lo]; positivity
    have hhigh : 0 < hi := by dsimp [hi]; positivity
    have hl := young_coordinate x lo hlow (-(t*a))
    have hh := young_coordinate x hi hhigh (t*a)
    change 2*t*a*(hilbertSequence x hi - hilbertSequence x lo) ≤
      (p hi+p lo) + t^2*a^2*(d hi+d lo)
    dsimp only [p, d] at *
    nlinarith only [hl, hh]
  have htot := Finset.sum_le_sum (s := Finset.range K) (fun j _ => row j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, flatten_scales] at htot
  have hp : (∑ v ∈ Finset.range ((2^(K+1)-2)*Q), p (2*Q+v)) ≤ ‖x‖^2 := by
    rw [hilbert_norm_weighted_sq]
    let N := (2^(K+1)-2)*Q
    have hinj : Function.Injective (fun n : ℕ => 2*Q+n) := fun _ _ e => Nat.add_left_cancel e
    have h := (hilbertSequence_square_summable x).sum_le_tsum
      ((Finset.range N).image (fun n => 2*Q+n))
      (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
    rwa [Finset.sum_image (fun _ _ _ _ e => hinj e)] at h
  have hd := (hasSum_dualWeight Q).summable.sum_le_tsum (Finset.range K) (fun j _ => by positivity)
  rw [(hasSum_dualWeight Q).tsum_eq] at hd
  exact htot.trans (add_le_add hp (mul_le_mul_of_nonneg_left hd (sq_nonneg t)))

/-- A limiting payoff supplies a lower bound in the complete Pareto norm. -/
theorem squared_error_lower_of_partial_tendsto (Q : ℕ) (hQ : 0 < Q)
    (x : ThresholdHilbert) (p : ℝ)
    (hx : Tendsto (fun K => partialSum Q K (hilbertSequence x)) atTop (𝓝 p)) :
    p^2 / dualWeight Q ≤ ‖x‖^2 := by
  have hQ' : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos : 0 < dualWeight Q := by
    unfold dualWeight
    have hh : 0 < 49*(Q:ℝ)^2-1 := by nlinarith [sq_nonneg ((Q:ℝ)-1)]
    positivity
  let t := p / dualWeight Q
  have h := le_of_tendsto' ((tendsto_const_nhds (x := 2*t)).mul hx)
    (fun K => partial_variational Q K hQ x t)
  dsimp only [t] at h
  field_simp [hpos.ne'] at h ⊢
  nlinarith

/-- The exact witness bound in units of the unnormalized capture deficit. -/
theorem odd_period_floor_of_partial_tendsto (Q : ℕ) (hQ : 0 < Q) (x : ThresholdHilbert)
    (hx : Tendsto (fun K => partialSum Q K (hilbertSequence x)) atTop (𝓝 ((Q : ℝ) / 4))) :
    21*(Q:ℝ)/(16*(49*(Q:ℝ)^2-1)) ≤ ‖x‖^2 := by
  have hQ' : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos : 0 < 49*(Q:ℝ)^2-1 := by nlinarith [sq_nonneg ((Q:ℝ)-1)]
  have hn : (Q:ℝ) ≠ 0 := by positivity
  have he : ((Q:ℝ)/4)^2 / dualWeight Q = 21*(Q:ℝ)/(16*(49*(Q:ℝ)^2-1)) := by
    unfold dualWeight
    field_simp [hn, hpos.ne']
    ring
  have h := squared_error_lower_of_partial_tendsto Q hQ x ((Q:ℝ)/4) hx
  rwa [he] at h

/-- An approximating sequence with vanishing complete deficit must use odd
periods tending to infinity. -/
theorem odd_period_tendsto_atTop_of_vanishing_error (Q : ℕ → ℕ) (e : ℕ → ℝ)
    (hQ : ∀ j, 0 < Q j)
    (hfloor : ∀ j, 21*(Q j:ℝ)/(16*(49*(Q j:ℝ)^2-1)) ≤ e j)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto Q atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let r := 3 / (112*((B:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  filter_upwards [(tendsto_order.1 he).2 r hr] with j hj
  by_contra! h
  have hq : (1:ℝ) ≤ Q j := by exact_mod_cast hQ j
  have hqb : (Q j:ℝ) ≤ (B:ℝ)+1 := by
    exact_mod_cast (show Q j ≤ B+1 by omega)
  have hd : 0 < 49*(Q j:ℝ)^2-1 := by nlinarith [sq_nonneg ((Q j:ℝ)-1)]
  have hc : (3:ℝ) / (112*(Q j:ℝ)) < 21*(Q j:ℝ)/(16*(49*(Q j:ℝ)^2-1)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    norm_num
  have hle : r ≤ 3/(112*(Q j:ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left hqb (by norm_num)
  exact (not_lt_of_ge (hle.trans (hc.le.trans (hfloor j)))) hj

end RiemannResearch.RH.Pareto.OddPeriodBlock
