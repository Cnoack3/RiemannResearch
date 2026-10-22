import RiemannResearch.Analysis.MultiplicativePrefixPrimitive
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.GCongr

/-!
# Recovery from limits of dyadic block averages

Source: the quantitative recovery argument in
`RH_Iff_Two_Seed_Approximation_20260914.md`, Section 4.4, adapted here
to the continuous prefix primitive. The error bound retains the entire
square-summable increment tail before taking the limit.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
open Filter
noncomputable section

def incrementTailEnergy (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' k, sequenceIncrement a (k+N)^2

theorem incrementTailEnergy_nonneg (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ incrementTailEnergy a N := tsum_nonneg (fun _ => sq_nonneg _)

theorem incrementTailEnergy_tendsto (a : ℕ → ℝ)
    (hs : Summable (fun n => sequenceIncrement a n^2)) :
    Tendsto (incrementTailEnergy a) atTop (nhds 0) := by
  have he : incrementTailEnergy a = fun N =>
      (∑' k, sequenceIncrement a k^2) -
        ∑ k ∈ Finset.range N, sequenceIncrement a k^2 := by
    funext N
    have h := hs.sum_add_tsum_nat_add N
    change _ + incrementTailEnergy a N = _ at h
    linarith
  rw [he]
  have hc : Tendsto (fun _ : ℕ => ∑' k, sequenceIncrement a k^2)
      atTop (nhds (∑' k, sequenceIncrement a k^2)) := tendsto_const_nhds
  simpa using hc.sub hs.tendsto_sum_tsum_nat

theorem finite_increment_sq_le_tail (a : ℕ → ℝ)
    (hs : Summable (fun n => sequenceIncrement a n^2))
    (s : Finset ℕ) (N : ℕ) (hN : ∀ k ∈ s, N ≤ k) :
    (∑ k ∈ s, sequenceIncrement a k^2) ≤ incrementTailEnergy a N := by
  classical
  have hinj : Set.InjOn (fun k : ℕ => k-N) (s : Set ℕ) := by
    intro k hk l hl he
    have hNk := hN k hk
    have hNl := hN l hl
    dsimp at he
    omega
  have hshift := (summable_nat_add_iff N).mpr hs
  calc
    _ = ∑ k ∈ s.image (fun k => k-N), sequenceIncrement a (k+N)^2 := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.sub_add_cancel (hN k hk)]
    _ ≤ _ := hshift.sum_le_tsum _ (fun k _ => sq_nonneg _)

def dyadicBlockAverage (a : ℕ → ℝ) (j n : ℕ) : ℝ :=
  (sequencePrefix a (2^j*(n+1)) - sequencePrefix a (2^j*n)) / (2 : ℝ)^j

theorem dyadicBlockAverage_zero (a : ℕ → ℝ) (n : ℕ) :
    dyadicBlockAverage a 0 n = a n := by
  simp [dyadicBlockAverage, sequencePrefix, Finset.sum_range_succ]

theorem dyadicBlockAverage_eq_primitive (a : ℕ → ℝ) (j n : ℕ) :
    dyadicBlockAverage a j n =
      dyadicPrefixPrimitive a j ((n : ℝ)+1) - dyadicPrefixPrimitive a j n := by
  have hf (m : ℕ) : ⌊(2 : ℝ)^j * (m : ℝ)⌋₊ = 2^j*m := by
    have he : (2 : ℝ)^j * (m : ℝ) = ((2^j*m : ℕ) : ℝ) := by push_cast; rfl
    rw [he, Nat.floor_natCast]
  unfold dyadicBlockAverage dyadicPrefixPrimitive
  rw [show (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) by push_cast; rfl, hf, hf]
  ring

theorem dyadicBlockAverage_increment (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n) (j n : ℕ) :
    dyadicBlockAverage a (j+1) n - dyadicBlockAverage a j n =
      (∑ k ∈ Finset.Ico (2^j*n) (2^j*(n+1)), sequenceIncrement a (2*k)) /
        (2 : ℝ)^(j+1) := by
  have hle : 2^j*n ≤ 2^j*(n+1) := Nat.mul_le_mul_left _ (by omega)
  rw [Finset.sum_Ico_eq_sub _ hle]
  unfold dyadicBlockAverage
  simp only [pow_succ', Nat.mul_assoc]
  rw [sequencePrefix_double a h2, sequencePrefix_double a h2]
  field_simp
  <;> ring

theorem dyadicBlockAverage_increment_sq (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hs : Summable (fun k => sequenceIncrement a k^2)) (j n : ℕ) :
    (dyadicBlockAverage a (j+1) n - dyadicBlockAverage a j n)^2 ≤
      incrementTailEnergy a (2*n) / (2 : ℝ)^j := by
  classical
  let s := Finset.Ico (2^j*n) (2^j*(n+1))
  have hcard : s.card = 2^j := by simp [s, Nat.mul_add]
  have hp : 0 < (2 : ℝ)^j := by positivity
  have he : 0 ≤ incrementTailEnergy a (2*n) := incrementTailEnergy_nonneg a _
  have himage : (∑ k ∈ s, sequenceIncrement a (2*k)^2) ≤
      incrementTailEnergy a (2*n) := by
    have hinj : Set.InjOn (fun k : ℕ => 2*k) (s : Set ℕ) := by
      intro k hk l hl h; dsimp at h; omega
    rw [← Finset.sum_image (f := fun k => sequenceIncrement a k^2) hinj]
    apply finite_increment_sq_le_tail a hs
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have hlN : 2^j*n ≤ l := (Finset.mem_Ico.mp hl).1
    have hn : n ≤ 2^j*n := Nat.le_mul_of_pos_left n (pow_pos (by norm_num) j)
    omega
  have hsum := sq_sum_le_card_mul_sum_sq (s := s)
    (f := fun k => sequenceIncrement a (2*k))
  rw [hcard] at hsum
  have hsum' : (∑ k ∈ s, sequenceIncrement a (2*k))^2 ≤
      (2 : ℝ)^j * incrementTailEnergy a (2*n) := by
    exact hsum.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_left himage (Nat.cast_nonneg (2^j)))
  rw [dyadicBlockAverage_increment a h2, div_pow]
  change (∑ k ∈ s, sequenceIncrement a (2*k))^2 / ((2 : ℝ)^(j+1))^2 ≤ _
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < (2 : ℝ)^(j+1)))).mpr
  have heq : incrementTailEnergy a (2*n) / (2 : ℝ)^j * ((2 : ℝ)^(j+1))^2 =
      4 * (2 : ℝ)^j * incrementTailEnergy a (2*n) := by
    rw [pow_succ]
    field_simp
    <;> ring
  rw [heq]
  nlinarith [mul_nonneg hp.le he]

theorem abs_sub_le_of_geometric_increment (u : ℕ → ℝ) (H c : ℝ)
    (hH : 0 ≤ H) (hu : Tendsto u atTop (nhds c))
    (hi : ∀ j, |u (j+1)-u j| ≤ H * (3/4 : ℝ)^j) :
    |c-u 0| ≤ 4*H := by
  have hb (j : ℕ) : |u j-u 0| ≤ 4*H*(1-(3/4 : ℝ)^j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have ht := abs_add_le (u (j+1)-u j) (u j-u 0)
      have hi' := hi j
      rw [pow_succ]
      have hid : u (j+1)-u j+(u j-u 0) = u (j+1)-u 0 := by ring
      rw [hid] at ht
      nlinarith only [ht, hi', ih]
  have hb' (j : ℕ) : |u j-u 0| ≤ 4*H := by
    have hpow : 0 ≤ (3/4 : ℝ)^j := by positivity
    have hprod := mul_nonneg hH hpow
    nlinarith [hb j]
  exact le_of_tendsto (hu.sub tendsto_const_nhds).abs
    (Eventually.of_forall hb')

theorem dyadicBlockAverage_recovery_bound (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hs : Summable (fun k => sequenceIncrement a k^2)) (n : ℕ) (c : ℝ)
    (hc : Tendsto (fun j => dyadicBlockAverage a j n) atTop (nhds c)) :
    |c-a n| ≤ 4*Real.sqrt (incrementTailEnergy a (2*n)) := by
  have hE := incrementTailEnergy_nonneg a (2*n)
  have hsq := Real.sq_sqrt hE
  have h := abs_sub_le_of_geometric_increment (fun j => dyadicBlockAverage a j n)
    (Real.sqrt (incrementTailEnergy a (2*n))) c (Real.sqrt_nonneg _) hc
  rw [dyadicBlockAverage_zero] at h
  apply h
  intro j
  have hpow : (1/2 : ℝ)^j ≤ ((3/4 : ℝ)^j)^2 := by
    calc
      _ ≤ ((3/4 : ℝ)^2)^j := by gcongr <;> norm_num
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 j]
  have hdelta := dyadicBlockAverage_increment_sq a h2 hs j n
  have hratio : incrementTailEnergy a (2*n) / (2 : ℝ)^j =
      incrementTailEnergy a (2*n) * (1/2 : ℝ)^j := by
    simp only [div_eq_mul_inv, one_mul, inv_pow]
  rw [hratio] at hdelta
  have hm := mul_le_mul_of_nonneg_left hpow hE
  have ht : 0 ≤ Real.sqrt (incrementTailEnergy a (2*n)) * (3/4 : ℝ)^j := by positivity
  have ha := sq_abs (dyadicBlockAverage a (j+1) n - dyadicBlockAverage a j n)
  nlinarith [sq_nonneg (Real.sqrt (incrementTailEnergy a (2*n)) * (3/4 : ℝ)^j)]

/-- A linear dyadic prefix limit, together with the actual square-summable
increments and dyadic invariance, forces every positive-index value. -/
theorem sequence_constant_of_linear_prefix_limit (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hs : Summable (fun k => sequenceIncrement a k^2)) (c : ℝ)
    (hc : ∀ n : ℕ, Tendsto (fun j => dyadicBlockAverage a j n) atTop (nhds c)) :
    ∀ n : ℕ, 0 < n → a n = c := by
  intro n hn
  have hpow (s : ℕ) : a (2^s*n) = a n := by
    induction s with
    | zero => simp
    | succ s ih => rw [pow_succ', Nat.mul_assoc, h2, ih]
  have hidx : Tendsto (fun s : ℕ => 2*(2^s*n)) atTop atTop := by
    apply tendsto_atTop_mono (fun s => ?_)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hN := Nat.le_mul_of_pos_right (2^s) hn
    omega
  have hlim : Tendsto (fun s => 4*Real.sqrt (incrementTailEnergy a (2*(2^s*n))))
      atTop (nhds 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((incrementTailEnergy_tendsto a hs).comp hidx)
    simpa using h.const_mul 4
  have hb (s : ℕ) : |c-a n| ≤ 4*Real.sqrt (incrementTailEnergy a (2*(2^s*n))) := by
    have h := dyadicBlockAverage_recovery_bound a h2 hs (2^s*n) c (hc (2^s*n))
    rwa [hpow] at h
  have hz : |c-a n| ≤ 0 := by
    have h := le_of_tendsto (tendsto_const_nhds.sub hlim)
      (Eventually.of_forall (fun s => sub_nonpos.mpr (hb s)))
    simpa using h
  have heq : c-a n = 0 := abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  linarith

end
end RiemannResearch.Analysis
