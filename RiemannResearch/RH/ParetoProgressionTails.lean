import RiemannResearch.RH.ParetoDilation
import Mathlib.Tactic.Linarith

/-!
Source: RH_Two_Seed_Threshold.tex, revised 7 September 2026, Section 10.
Exact progression masses and certified elementary telescoping tail bounds.
The upper enclosure here is slightly stronger than the paper's integral bound.
-/

open scoped BigOperators
open Filter

namespace RiemannResearch.RH.Pareto
noncomputable section

def progressionWeight (N r : ℕ) : ℝ := ∑' j, positiveWeight (r + N*j)

theorem progressionWeight_summable (N r : ℕ) (hN : 0 < N) :
    Summable (fun j => positiveWeight (r + N*j)) := by
  apply positiveWeight_summable.comp_injective
  intro i j hij
  exact Nat.eq_of_mul_eq_mul_left hN (Nat.add_left_cancel hij)

theorem progressionWeight_nonneg (N r : ℕ) : 0 ≤ progressionWeight N r := by
  exact tsum_nonneg (fun _ => positiveWeight_nonneg _)

theorem progressionWeight_split (N r : ℕ) (hN : 0 < N) :
    progressionWeight N r = positiveWeight r + progressionWeight N (r+N) := by
  unfold progressionWeight
  rw [(progressionWeight_summable N r hN).tsum_eq_zero_add]
  simp only [Nat.mul_zero, Nat.add_zero]
  congr 1
  apply tsum_congr
  intro j
  congr 1
  ring

private theorem upper_step (x n : ℝ) (hx : 0 < x) (hn : 1 ≤ n) :
    1 / ((x+n-1)*(x+n)) ≤ 1/(n*x) - 1/(n*(x+n)) := by
  have hn0 : 0 < n := by linarith
  calc
    _ ≤ 1 / (x*(x+n)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith
    _ = _ := by
      field_simp
      <;> ring

private theorem upper_partial (N r J : ℕ) (hN : 0 < N) :
    (∑ j ∈ Finset.range J, positiveWeight (r+N+N*j)) ≤
      1 / ((N:ℝ)*((r:ℝ)+1)) -
        1 / ((N:ℝ)*((r:ℝ)+1+(N:ℝ)*J)) := by
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast hN
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hs := upper_step ((r:ℝ)+1+(N:ℝ)*J) N (by positivity) hNreal
    have he : positiveWeight (r+N+N*J) =
        1 / ((((r:ℝ)+1+(N:ℝ)*J)+N-1)*(((r:ℝ)+1+(N:ℝ)*J)+N)) := by
      unfold positiveWeight
      push_cast
      congr 1 <;> ring
    rw [he]
    push_cast
    have hre : (r:ℝ)+1+(N:ℝ)*(J+1) = ((r:ℝ)+1+(N:ℝ)*J)+N := by ring
    rw [hre]
    linarith

/-- A genuine infinite tail upper bound; all summability is discharged. -/
theorem progressionWeight_tail_upper (N r : ℕ) (hN : 0 < N) :
    progressionWeight N (r+N) ≤ 1 / ((N:ℝ)*((r:ℝ)+1)) := by
  apply (progressionWeight_summable N (r+N) hN).tsum_le_of_sum_range_le
  intro J
  have h := upper_partial N r J hN
  have hp : 0 ≤ 1 / ((N:ℝ)*((r:ℝ)+1+(N:ℝ)*J)) := by positivity
  linarith

/-- Two exact head terms and a certified infinite tail; used by the 36-period witness. -/
theorem progressionWeight_upper_two (N r : ℕ) (hN : 0 < N) :
    progressionWeight N r ≤ positiveWeight r + positiveWeight (r+N) +
      1 / ((N:ℝ)*((r:ℝ)+N+1)) := by
  rw [progressionWeight_split N r hN, progressionWeight_split N (r+N) hN]
  have h := progressionWeight_tail_upper N (r+N) hN
  push_cast at h
  linarith

end
end RiemannResearch.RH.Pareto


/-! Source: RH_Two_Seed_Threshold.tex, revised 7 September 2026, Section 10.
An elementary lower-tail enclosure, stronger than the stated integral bound.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem lower_step (x n : ℝ) (hx : 0 < x) (hn : 1 ≤ n) :
    1/(n*x) - 1/(n*(x+n)) ≤ 1/(x*(x+1)) := by
  have hn0 : 0 < n := by linarith
  calc
    _ = 1 / (x*(x+n)) := by field_simp <;> ring
    _ ≤ _ := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith

private theorem lower_partial (N r J : ℕ) (hN : 0 < N) (hr : 0 < r) :
    1 / ((N:ℝ)*(r:ℝ)) - 1 / ((N:ℝ)*((r:ℝ)+(N:ℝ)*J)) ≤
      ∑ j ∈ Finset.range J, positiveWeight (r+N*j) := by
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast hN
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hs := lower_step ((r:ℝ)+(N:ℝ)*J) N (by positivity) hNreal
    have he : positiveWeight (r+N*J) =
        1 / (((r:ℝ)+(N:ℝ)*J)*(((r:ℝ)+(N:ℝ)*J)+1)) := by
      simp [positiveWeight]
    rw [he]
    push_cast
    have hre : (r:ℝ)+(N:ℝ)*(J+1) = ((r:ℝ)+(N:ℝ)*J)+N := by ring
    rw [hre]
    linarith

/-- Full progression lower bound, requiring only a positive representative and modulus. -/
theorem progressionWeight_lower (N r : ℕ) (hN : 0 < N) (hr : 0 < r) :
    1 / ((N:ℝ)*(r:ℝ)) ≤ progressionWeight N r := by
  have hnat : Tendsto (fun j : ℕ => r+N*j) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    exact le_trans (Nat.le_mul_of_pos_left j hN) (by omega)
  have hinv : Tendsto (fun j : ℕ => 1 / ((r:ℝ)+(N:ℝ)*j)) atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).comp hnat)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, one_div] using h
  have htail : Tendsto (fun j : ℕ => 1 / ((N:ℝ)*((r:ℝ)+(N:ℝ)*j)))
      atTop (nhds 0) := by
    have h := hinv.const_mul (1/(N:ℝ))
    simpa only [mul_zero, one_div_mul_one_div] using h
  have hlim : Tendsto (fun j : ℕ => 1 / ((N:ℝ)*(r:ℝ)) -
      1 / ((N:ℝ)*((r:ℝ)+(N:ℝ)*j))) atTop
      (nhds (1 / ((N:ℝ)*(r:ℝ)))) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub htail
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro J
  exact (lower_partial N r J hN hr).trans
    ((progressionWeight_summable N r hN).sum_le_tsum _
      (fun j _ => positiveWeight_nonneg _))

/-- The complete progression after any finite head, with no tail discarded. -/
theorem progressionWeight_partial_split (N r J : ℕ) (hN : 0 < N) :
    progressionWeight N r =
      (∑ j ∈ Finset.range J, positiveWeight (r+N*j)) +
        progressionWeight N (r+N*J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have he : r+N*(J+1) = r+N*J+N := by ring
    rw [he, ih, progressionWeight_split N (r+N*J) hN]
    ring

/-- The elementary upper enclosure uses one exact head mass. -/
theorem progressionWeight_upper_one (N r : ℕ) (hN : 0 < N) :
    progressionWeight N r ≤ positiveWeight r + 1 / ((N:ℝ)*((r:ℝ)+1)) := by
  rw [progressionWeight_split N r hN]
  exact add_le_add le_rfl (progressionWeight_tail_upper N r hN)

/-- The exact two-sided tail prescription from all Section 10 certificates.
The proof uses elementary telescoping and is independent of integral estimates. -/
theorem progressionWeight_certificate_bounds (N r : ℕ) (hN : 0 < N) (hr : 0 < r) :
    1 / ((N:ℝ)*((r:ℝ)+1)) ≤ progressionWeight N r ∧
      progressionWeight N r ≤ positiveWeight r + 1 / ((N:ℝ)*(r:ℝ)) := by
  have hle : 1 / ((N:ℝ)*((r:ℝ)+1)) ≤ 1 / ((N:ℝ)*(r:ℝ)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact ⟨hle.trans (progressionWeight_lower N r hN hr),
    (progressionWeight_upper_one N r hN).trans (add_le_add le_rfl hle)⟩

end
end RiemannResearch.RH.Pareto
