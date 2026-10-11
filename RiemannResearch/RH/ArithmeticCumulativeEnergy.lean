import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Tactic

/-!
# Arithmetic cumulative energy and balanced divisibility

All sums run over the positive integer arguments of a single arithmetic
function. No independence assumption is used. The energy formula retains the
signed cross terms and the terminal boundary contribution.
-/

namespace RiemannResearch.RH.ArithmeticCumulative
noncomputable section
open scoped BigOperators

/-- Sum on the positive initial interval `1,...,n`. -/
def cumulative (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, f (k + 1)

def divisorIndicator (d n : ℕ) : ℝ := if d ∣ n then 1 else 0

def balancedDivisor (d n : ℕ) : ℝ := divisorIndicator d n - 1 / (d : ℝ)

def residueFraction (d n : ℕ) : ℝ := (n % d : ℕ) / (d : ℝ)

/-- At zero this is zero; at positive `n` it is the NB/Pareto weight. -/
def weight (n : ℕ) : ℝ := 1 / ((n : ℝ) * ((n : ℝ) + 1))

def fullSquaredNorm (F : ℕ → ℝ) : ℝ := ∑' n, weight n * F n ^ 2

def energyPrefix (f : ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ k ∈ Finset.range R, weight (k + 1) * (cumulative f (k + 1)) ^ 2

@[simp] theorem cumulative_zero (f : ℕ → ℝ) : cumulative f 0 = 0 := by
  simp [cumulative]

@[simp] theorem cumulative_succ (f : ℕ → ℝ) (n : ℕ) :
    cumulative f (n + 1) = cumulative f n + f (n + 1) := by
  simp [cumulative, Finset.sum_range_succ]

theorem cumulative_add (f g : ℕ → ℝ) (n : ℕ) :
    cumulative (fun k => f k + g k) n = cumulative f n + cumulative g n := by
  simp [cumulative, Finset.sum_add_distrib]

theorem cumulative_sub (f g : ℕ → ℝ) (n : ℕ) :
    cumulative (fun k => f k - g k) n = cumulative f n - cumulative g n := by
  simp [cumulative, Finset.sum_sub_distrib]

theorem cumulative_const (c : ℝ) (n : ℕ) :
    cumulative (fun _ => c) n = (n : ℝ) * c := by
  simp [cumulative]

theorem cumulative_mul (c : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    cumulative (fun k => c * f k) n = c * cumulative f n := by
  simp [cumulative, Finset.mul_sum]

/-- Exact jump of the integer quotient at a multiple. -/
theorem nat_div_succ (d n : ℕ) (hd : 0 < d) :
    (n + 1) / d = n / d + if d ∣ n + 1 then 1 else 0 := by
  by_cases hdone : d = 1
  · simp [hdone]
  have h1 : 1 < d := by omega
  have hr := Nat.mod_lt n hd
  have hiff : d ≤ n % d + 1 ↔ d ∣ n + 1 := by
    constructor
    · intro h
      have he : n % d + 1 = d := by omega
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, Nat.mod_eq_of_lt h1, he, Nat.mod_self]
    · intro h
      have hm := Nat.mod_eq_zero_of_dvd h
      rw [Nat.add_mod, Nat.mod_eq_of_lt h1] at hm
      by_contra hn
      rw [Nat.mod_eq_of_lt (by omega : n % d + 1 < d)] at hm
      omega
  simpa [Nat.add_div hd, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, hiff]
    using (Nat.add_div (a := n) (b := 1) hd)

theorem real_div_succ (d n : ℕ) (hd : 0 < d) :
    (((n + 1) / d : ℕ) : ℝ) = ((n / d : ℕ) : ℝ) + divisorIndicator d (n + 1) := by
  rw [nat_div_succ d n hd]
  by_cases h : d ∣ n + 1 <;> simp [divisorIndicator, h]

theorem cumulative_divisorIndicator (d n : ℕ) (hd : 0 < d) :
    cumulative (divisorIndicator d) n = (n / d : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [cumulative_succ, ih, ← real_div_succ d n hd]

/-- The legal NB residue is exactly minus the arithmetic primitive. -/
theorem cumulative_balancedDivisor (d n : ℕ) (hd : 0 < d) :
    cumulative (balancedDivisor d) n = -residueFraction d n := by
  change cumulative (fun k => divisorIndicator d k - (1 / (d : ℝ))) n = _
  rw [cumulative_sub, cumulative_divisorIndicator d n hd, cumulative_const]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hdecomp : (d : ℝ) * (n / d : ℕ) + (n % d : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.div_add_mod n d
  unfold residueFraction
  field_simp
  nlinarith

/-- The Pareto weight is a telescoping difference. -/
theorem weight_eq_sub (n : ℕ) (hn : 0 < n) :
    weight n = 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  unfold weight
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

@[simp] theorem energyPrefix_zero (f : ℕ → ℝ) : energyPrefix f 0 = 0 := by
  simp [energyPrefix]

@[simp] theorem energyPrefix_succ (f : ℕ → ℝ) (R : ℕ) :
    energyPrefix f (R + 1) = energyPrefix f R +
      weight (R + 1) * (cumulative f (R + 1)) ^ 2 := by
  simp [energyPrefix, Finset.sum_range_succ]

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

theorem energyPrefix_nonneg (f : ℕ → ℝ) (R : ℕ) : 0 ≤ energyPrefix f R := by
  exact Finset.sum_nonneg fun k _ => mul_nonneg (weight_nonneg _) (sq_nonneg _)

/-- A triangular form of the full signed Green energy, including its boundary.
`2*f(k+1)*cumulative(f,k)` contains every earlier signed cross term. -/
theorem energyPrefix_signed_identity (f : ℕ → ℝ) (R : ℕ) :
    energyPrefix f R =
      (∑ k ∈ Finset.range R,
        (f (k + 1) ^ 2 + 2 * f (k + 1) * cumulative f k) / ((k : ℝ) + 1)) -
      (cumulative f R) ^ 2 / ((R : ℝ) + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [energyPrefix_succ, ih, Finset.sum_range_succ,
      weight_eq_sub (R + 1) (by omega), cumulative_succ]
    push_cast
    ring

/-- The primitive of the point source at 1 is the positive-index constant. -/
theorem cumulative_delta_one (n : ℕ) (hn : 0 < n) :
    cumulative (fun m => if m = 1 then (1 : ℝ) else 0) n = 1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [cumulative, Finset.sum_range_succ']
    simp

/-- Pointwise balance on a repaired head follows from one scalar moment equation. -/
theorem coupled_head_repair (y n : ℕ) (s : Finset ℕ) (t : ℕ → ℝ)
    (R : ℕ → ℝ) (α : ℝ)
    (hn : n ≤ y) (hhead : R n = 1)
    (hs : ∀ d ∈ s, y < d)
    (hbalance : ∑ d ∈ s, t d / (d : ℝ) = -α) :
    R n - α * n - ∑ d ∈ s, t d * residueFraction d n = 1 := by
  have he : (∑ d ∈ s, t d * residueFraction d n) = (n : ℝ) * (-α) := by
    calc
      _ = ∑ d ∈ s, (n : ℝ) * (t d / (d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [residueFraction, Nat.mod_eq_of_lt (lt_of_le_of_lt hn (hs d hd))]
        ring
      _ = (n : ℝ) * ∑ d ∈ s, t d / (d : ℝ) := by rw [Finset.mul_sum]
      _ = _ := by rw [hbalance]
  rw [he, hhead]
  ring

/-- Exact error decomposition for a real inner-product correction. -/
theorem scalar_correction_square (e w c : ℝ) :
    (e - c * w) ^ 2 = e ^ 2 - 2 * c * (e * w) + c ^ 2 * w ^ 2 := by ring

end
end RiemannResearch.RH.ArithmeticCumulative
