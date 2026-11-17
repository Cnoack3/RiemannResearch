import RiemannResearch.RH.ExactHeadAtomMoment
import RiemannResearch.RH.ParetoRationalWeightIntervals
import Mathlib.Tactic

/-!
# Integer verification of complete centered-probe energies

The expansion by first differences preserves every simultaneous jump.
A common integer scale rounds each nonnegative progression term upwards.
The final two terms bound the whole infinite tail.
-/
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadProbeCertificate
open RiemannResearch.RH.ArithmeticCumulative (divisorIndicator real_div_succ)
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.NumberTheory.DivisorIncidence (sum_Icc_one)
open ExactHeadAtomOptimizer

private def ceilingScaled (scale d : ℕ) : ℕ :=
  scale / d + 1

private theorem reciprocal_le_ceilingScaled (scale d : ℕ) (hs : 0 < scale) (hd : 0 < d) :
    (1 : ℝ) / d ≤ (ceilingScaled scale d : ℝ) / scale := by
  have h := Nat.div_add_mod scale d
  rw [Nat.mul_comm d] at h
  have hbound : scale ≤ ceilingScaled scale d * d := by
    unfold ceilingScaled
    rw [Nat.add_mul, one_mul]
    exact h.symm.trans_le (Nat.add_le_add_left (Nat.mod_lt _ hd).le _)
  have hsR : 0 < (scale : ℝ) := by exact_mod_cast hs
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (div_le_div_iff₀ hdR hsR).2
  rw [one_mul]
  exact_mod_cast hbound

private def prefixNumerator (P r scale : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => prefixNumerator P r scale k +
      ceilingScaled scale ((r + P * k) * (r + P * k + 1))

private theorem prefixNumerator_eq_sum (P r scale K : ℕ) :
    prefixNumerator P r scale K =
      ∑ j ∈ Finset.range K, ceilingScaled scale ((r + P * j) * (r + P * j + 1)) := by
  induction K with
  | zero => simp [prefixNumerator]
  | succ k ih => rw [prefixNumerator, Finset.sum_range_succ, ih]

def weightNumerator (P r scale K : ℕ) : ℕ :=
  let t := r + P * K
  prefixNumerator P r scale K +
    ceilingScaled scale (t * (t + 1)) + ceilingScaled scale (P * (t + 1))

private theorem progressionWeight_le_scaled (P r scale K : ℕ)
    (hP : 0 < P) (hr : 0 < r) (hs : 0 < scale) :
    progressionWeight P r ≤ (weightNumerator P r scale K : ℝ) / scale := by
  refine (elementaryProgressionInterval_contains P r K hP hr).2.trans ?_
  simp only [elementaryProgressionInterval, weightNumerator]
  push_cast
  have hp :
      (∑ j ∈ Finset.range K, (1 : ℝ) / ((r + P * j) * (r + P * j + 1))) ≤
        (prefixNumerator P r scale K : ℝ) / scale := by
    rw [prefixNumerator_eq_sum, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
      reciprocal_le_ceilingScaled scale ((r + P * j) * (r + P * j + 1)) hs (by positivity)
  have ht : 0 < r + P * K := by omega
  have ha := reciprocal_le_ceilingScaled scale ((r + P * K) * (r + P * K + 1))
    hs (by positivity)
  have hb := reciprocal_le_ceilingScaled scale (P * (r + P * K + 1)) hs (by positivity)
  push_cast at ha hb
  exact (add_le_add (add_le_add hp ha) hb).trans_eq (by ring)

/-- The two coefficient lists have the common positive denominator `2 * halfDen`.
The first list gives the floor coefficients of the probe. The second gives its
upper gcd-atom correction. -/
structure Witness where
  period : ℕ
  cutoff : ℕ
  halfDen : ℕ
  head : List (ℕ × ℤ)
  upper : List (ℕ × ℤ)

def Witness.den (w : Witness) : ℕ := 2 * w.halfDen

noncomputable def columns : List (ℕ × ℤ) → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | (d, c) :: cs, f => (c : ℝ) * f d + columns cs f

private def hit : List (ℕ × ℤ) → (ℕ → Bool) → ℤ
  | [], _ => 0
  | (d, c) :: cs, test => (if test d then c else 0) + hit cs test

private theorem columns_zero (cs : List (ℕ × ℤ)) (f : ℕ → ℝ) (hf : ∀ d, f d = 0) :
    columns cs f = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [columns, hf, ih]

private theorem columns_add_hits (cs : List (ℕ × ℤ)) (f : ℕ → ℝ) (test : ℕ → Bool) :
    columns cs (fun d => f d + if test d then 1 else 0) =
      columns cs f + (hit cs test : ℝ) := by
  induction cs with
  | nil => simp [columns, hit]
  | cons c cs ih =>
    cases c with
    | mk d a =>
      simp only [columns, hit, ih, Int.cast_add]
      split <;> push_cast <;> ring

noncomputable def Witness.probe (w : Witness) (r : ℕ) : ℝ :=
  columns w.head (fun d => grid d r) / w.den

noncomputable def Witness.correction (w : Witness) (r : ℕ) : ℝ :=
  columns w.upper (fun d => atom w.period d r) / w.den

theorem Witness.correction_mem (w : Witness)
    (hw : w.upper.all (fun z => decide (w.cutoff < z.1 ∧ z.1 ∣ w.period)) = true)
    (hP : 0 < w.period) :
    w.correction ∈ upperSpan w.period w.cutoff (atom w.period) := by
  have hcols (cs : List (ℕ × ℤ))
      (hcs : cs.all (fun z => decide (w.cutoff < z.1 ∧ z.1 ∣ w.period)) = true) :
      (fun r => columns cs (fun d => atom w.period d r)) ∈
        upperSpan w.period w.cutoff (atom w.period) := by
    induction cs with
    | nil => exact Submodule.zero_mem _
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hcs
      have ha : atom w.period c.1 ∈ upperSpan w.period w.cutoff (atom w.period) :=
        Submodule.subset_span ⟨c.1,
          Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hcs.1.2, hP.ne'⟩, hcs.1.1⟩, rfl⟩
      have heq : (fun r => columns (c :: cs) (fun d => atom w.period d r)) =
          (c.2 : ℝ) • atom w.period c.1 +
            (fun r => columns cs (fun d => atom w.period d r)) := by
        funext r
        cases c
        simp only [columns, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ (c.2 : ℝ) ha) (ih hcs.2)
  have heq : w.correction = (↑w.den : ℝ)⁻¹ •
      (fun r => columns w.upper (fun d => atom w.period d r)) := by
    funext r
    simp only [Witness.correction, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact Submodule.smul_mem _ (↑w.den : ℝ)⁻¹ (hcols w.upper hw)

def Witness.jump (w : Witness) (r : ℕ) : ℤ :=
  hit w.head (fun d => decide (d ∣ r)) -
    (if r.gcd w.period = 1 then (w.halfDen : ℤ) else 0) -
    hit w.upper (fun d => decide (r.gcd w.period = d))

def Witness.numerator (w : Witness) : ℕ → ℤ
  | 0 => w.halfDen
  | r + 1 => numerator w r + w.jump (r + 1)

private theorem grid_step (d r : ℕ) :
    grid d (r + 1) = grid d r + if d ∣ r + 1 then 1 else 0 := by
  by_cases hd : 0 < d
  · simpa only [grid, divisorIndicator] using real_div_succ d r hd
  · have hd0 : d = 0 := by omega
    simp [hd0, grid]

private theorem Witness.numerator_cast (w : Witness) (r : ℕ) :
    (w.numerator r : ℝ) =
      columns w.head (fun d => grid d r) - (w.halfDen : ℝ) * target w.period r -
        columns w.upper (fun d => atom w.period d r) := by
  induction r with
  | zero =>
    rw [Witness.numerator,
      columns_zero _ _ (fun d => show grid d 0 = 0 by simp [grid]),
      columns_zero _ _ (fun d => show atom w.period d 0 = 0 by simp [atom])]
    simp [target, atom]
  | succ r ih =>
    rw [Witness.numerator, Int.cast_add, ih]
    have hhead : columns w.head (fun d => grid d (r + 1)) =
        columns w.head (fun d => grid d r) +
          (hit w.head (fun d => decide (d ∣ r + 1)) : ℝ) := by
      simp only [grid_step]
      simpa only [decide_eq_true_eq] using
        columns_add_hits w.head (fun d => grid d r) (fun d => decide (d ∣ r + 1))
    have hupper : columns w.upper (fun d => atom w.period d (r + 1)) =
        columns w.upper (fun d => atom w.period d r) +
          (hit w.upper (fun d => decide ((r + 1).gcd w.period = d)) : ℝ) := by
      simp only [atom_succ]
      simpa only [decide_eq_true_eq] using
        columns_add_hits w.upper (fun d => atom w.period d r)
          (fun d => decide ((r + 1).gcd w.period = d))
    rw [hhead, hupper, Witness.jump, Int.cast_sub, Int.cast_sub]
    simp only [target, atom_succ]
    split_ifs <;> push_cast <;> ring

theorem Witness.centered_eq_numerator (w : Witness) (hd : 0 < w.halfDen)
    (hp : ∀ r, fittedMomentProbe w.cutoff r = w.probe r) (r : ℕ) :
    fittedMomentProbe w.cutoff r - (1 / 2 : ℝ) * target w.period r - w.correction r =
      (w.numerator r : ℝ) / w.den := by
  rw [hp r, Witness.numerator_cast]
  unfold Witness.probe Witness.correction Witness.den
  push_cast
  have hdR : (w.halfDen : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR]

/-- Each step stores the exact numerator at the current residue and the integer
sum of the weighted squares. The accumulator is tail recursive. -/
def scan (w : Witness) (scale K : ℕ) : ℕ → ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, _, n, e => (n, e)
  | k + 1, lo, n, e =>
    let r := lo + 1
    let z := n + w.jump r
    scan w scale K k r z (e + z ^ 2 * (weightNumerator w.period r scale K : ℤ))

def energyNumerator (w : Witness) (scale K : ℕ) (r : ℕ) : ℤ :=
  (w.numerator r) ^ 2 * (weightNumerator w.period r scale K : ℤ)

theorem scan_eq_sum (w : Witness) (scale K len lo : ℕ) (e : ℤ) :
    scan w scale K len lo (w.numerator lo) e =
      (w.numerator (lo + len),
        e + ∑ j ∈ Finset.range len, energyNumerator w scale K (lo + j + 1)) := by
  induction len generalizing lo e with
  | zero => simp [scan]
  | succ len ih =>
    rw [scan]
    change scan w scale K len (lo + 1) (w.numerator (lo + 1))
      (e + energyNumerator w scale K (lo + 1)) = _
    rw [ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have hl : lo + 1 + len = lo + (len + 1) := by omega
    have hs :
        (∑ j ∈ Finset.range len, energyNumerator w scale K (lo + 1 + j + 1)) =
        ∑ j ∈ Finset.range len, energyNumerator w scale K (lo + (j + 1) + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      omega
    rw [hl, hs]
    congr 1
    ring

private theorem scan_add (w : Witness) (scale K a b lo : ℕ) (n e : ℤ) :
    scan w scale K (a + b) lo n e =
      let s := scan w scale K a lo n e
      scan w scale K b (lo + a) s.1 s.2 := by
  induction a generalizing lo n e with
  | zero => simp [scan]
  | succ a ih =>
    rw [Nat.succ_add, scan, scan, ih]
    have h : lo + 1 + a = lo + (a + 1) := by omega
    rw [h]

theorem scan_eq_of_split {w : Witness} {scale K a b lo : ℕ} {n e : ℤ}
    {mid result : ℤ × ℤ} (h₁ : scan w scale K a lo n e = mid)
    (h₂ : scan w scale K b (lo + a) mid.1 mid.2 = result) :
    scan w scale K (a + b) lo n e = result := by
  rw [scan_add, h₁]
  exact h₂

private theorem sum_le_of_energyNumerator (w : Witness) (scale K lo len : ℕ)
    (hP : 0 < w.period)
    (hs : 0 < scale) (hd : 0 < w.halfDen)
    (hp : ∀ r, fittedMomentProbe w.cutoff r = w.probe r) (M : ℚ)
    (h : (↑(∑ j ∈ Finset.range len, energyNumerator w scale K (lo + j + 1)) : ℚ) ≤
      M * (scale : ℚ) * (w.den : ℚ) ^ 2) :
    (∑ j ∈ Finset.range len, progressionWeight w.period (lo + j + 1) *
      (fittedMomentProbe w.cutoff (lo + j + 1) - (1 / 2 : ℝ) * target w.period (lo + j + 1) -
        w.correction (lo + j + 1)) ^ 2) ≤ (M : ℝ) := by
  have hsR : 0 < (scale : ℝ) := by exact_mod_cast hs
  have hdR : 0 < (w.den : ℝ) := by
    exact_mod_cast (show 0 < w.den by unfold Witness.den; positivity)
  calc
    _ ≤ ∑ j ∈ Finset.range len,
        (energyNumerator w scale K (lo + j + 1) : ℝ) / ((scale : ℝ) * (w.den : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hw := progressionWeight_le_scaled w.period (lo + j + 1) scale K hP (by omega) hs
      rw [w.centered_eq_numerator hd hp]
      refine (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_eq ?_
      unfold energyNumerator
      push_cast
      field_simp [hsR.ne', hdR.ne']
    _ ≤ (M : ℝ) := by
      rw [← Finset.sum_div]
      apply (div_le_iff₀ (by positivity)).2
      have hr :
          (∑ j ∈ Finset.range len, (energyNumerator w scale K (lo + j + 1) : ℝ)) ≤
            (M : ℝ) * (scale : ℝ) * (w.den : ℝ) ^ 2 := by
        exact_mod_cast h
      linarith only [hr]

/-- An exact integer check certifies the complete energy. -/
theorem energy_le_of_scan (w : Witness) (scale K : ℕ) (hP : 0 < w.period)
    (hs : 0 < scale) (hd : 0 < w.halfDen)
    (hp : ∀ r, fittedMomentProbe w.cutoff r = w.probe r) (M : ℚ)
    (h : ((scan w scale K (w.period - 1) 0 w.halfDen 0).2 : ℚ) ≤
      M * (scale : ℚ) * (w.den : ℚ) ^ 2) :
    energy (Finset.Icc 1 (w.period - 1)) (progressionWeight w.period)
      (fun r => fittedMomentProbe w.cutoff r -
        (1 / 2 : ℝ) * target w.period r - w.correction r) ≤
      (M : ℝ) := by
  have hn : w.numerator 0 = (w.halfDen : ℤ) := rfl
  rw [← hn, scan_eq_sum, Nat.zero_add, zero_add] at h
  unfold energy
  rw [sum_Icc_one]
  simpa only [Nat.zero_add] using
    sum_le_of_energyNumerator w scale K 0 (w.period - 1) hP hs hd hp M h

/-- Subtracting the exact integer head sum certifies the complementary energy. -/
theorem tail_energy_le_of_scan (w : Witness) (scale K : ℕ)
    (hx : w.cutoff < w.period) (hs : 0 < scale) (hd : 0 < w.halfDen)
    (hp : ∀ r, fittedMomentProbe w.cutoff r = w.probe r) (M : ℚ)
    (h : (((scan w scale K (w.period - 1) 0 w.halfDen 0).2 -
      (scan w scale K w.cutoff 0 w.halfDen 0).2 : ℤ) : ℚ) ≤
      M * (scale : ℚ) * (w.den : ℚ) ^ 2) :
    energy (Finset.Icc 1 (w.period - 1) \ Finset.Icc 1 w.cutoff)
      (progressionWeight w.period)
      (fun r => fittedMomentProbe w.cutoff r -
        (1 / 2 : ℝ) * target w.period r - w.correction r) ≤
      (M : ℝ) := by
  let len := w.period - 1 - w.cutoff
  have hP : 0 < w.period := by omega
  have hn : w.numerator 0 = (w.halfDen : ℤ) := rfl
  simp only [← hn, scan_eq_sum, zero_add] at h
  have hsplit :
      (∑ j ∈ Finset.range (w.period - 1), energyNumerator w scale K (j + 1)) =
        (∑ j ∈ Finset.range w.cutoff, energyNumerator w scale K (j + 1)) +
          ∑ j ∈ Finset.range len, energyNumerator w scale K (w.cutoff + j + 1) := by
    calc
      _ = ∑ j ∈ Finset.range (w.cutoff + len), energyNumerator w scale K (j + 1) := by
        dsimp [len]
        rw [Nat.add_sub_of_le (show w.cutoff ≤ w.period - 1 by omega)]
      _ = _ := by rw [Finset.sum_range_add]
  rw [hsplit, add_sub_cancel_left] at h
  have hset : Finset.Icc 1 (w.period - 1) \ Finset.Icc 1 w.cutoff =
      Finset.Ico (w.cutoff + 1) w.period := by
    ext r
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ico]
    omega
  unfold energy
  rw [hset, Finset.sum_Ico_eq_sum_range, show w.period - (w.cutoff + 1) = len by
    dsimp [len]
    omega]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    sum_le_of_energyNumerator w scale K w.cutoff len hP hs hd hp M h

end RiemannResearch.RH.Pareto.ExactHeadProbeCertificate
