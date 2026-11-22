import RiemannResearch.RH.ParetoLegalStructure
import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-! # Rational certificates for finite dilations of the binary and ternary residues

A row `(p,m,z)` denotes `z / 10^6` times the scaled dilation of the residue
of modulus `p`. Each rounded integer charges the complete positive congruence
class, including the class represented by the period itself. -/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.TwoSeedPeriodicCertificate
noncomputable section

abbrev Row := ℕ × ℕ × ℤ

def value : List Row → ℕ → ℤ
  | [], _ => 0
  | (p, m, z) :: t, k => z * (m : ℤ) * ((k / m % p : ℕ) : ℤ) + value t k

def trial (rows : List Row) (k : ℕ) : ℝ := (value rows k : ℝ) / 1000000

private theorem trial_cons (p m : ℕ) (z : ℤ) (t : List Row) :
    trial ((p, m, z) :: t) = ((z : ℝ) / 1000000) • dilation m (residue p) + trial t := by
  funext k
  simp only [trial, value, Int.cast_add, Int.cast_mul, Int.cast_natCast, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, dilation, residue]
  ring

/-- Every coefficient table with the two seeds and positive dilations is legal. -/
theorem trial_legal (rows : List Row)
    (hr : ∀ t ∈ rows, (t.1 = 2 ∨ t.1 = 3) ∧ 0 < t.2.1) :
    trial rows ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  induction rows with
  | nil =>
    have hz : trial [] = 0 := by funext k; simp [trial, value]
    rw [hz]
    exact (legalSeedSpan _).zero_mem
  | cons t rows ih =>
    obtain ⟨p, m, z⟩ := t
    obtain ⟨hp, hm⟩ := hr (p, m, z) (by simp)
    have hs : p ∈ ({2, 3} : Set ℕ) := by simpa using hp
    rw [trial_cons]
    exact (legalSeedSpan _).add_mem ((legalSeedSpan _).smul_mem _
      (dilation_generator_mem _ hs hm)) (ih (fun t ht => hr t (by simp [ht])))

private theorem trial_period (rows : List Row) (L : ℕ)
    (hL : ∀ t ∈ rows, t.2.1 * t.1 ∣ L) (k : ℕ) :
    trial rows (k + L) = trial rows k := by
  induction rows with
  | nil => rfl
  | cons t rows ih =>
    obtain ⟨p, m, z⟩ := t
    have hd : m * p ∣ L := hL (p, m, z) (by simp)
    have hm : m ∣ L := dvd_trans (dvd_mul_right m p) hd
    rw [trial_cons]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, residue_mul_floor,
      residue_period_of_dvd hd, residue_period_of_dvd hm, ih (fun t ht => hL t (by simp [ht]))]

def classUnits (rows : List Row) (L r : ℕ) : ℕ :=
  let a := (1000000 - value rows r).natAbs
  let d := L * r * (r + 1)
  ((L + r) * a ^ 2) / d + 1

private theorem class_bound (rows : List Row) (L r : ℕ) (hL : 0 < L) (hr : 0 < r) :
    progressionWeight L r * (1 - trial rows r)^2 ≤ (classUnits rows L r : ℝ) / 10^12 := by
  let a := (1000000 - value rows r).natAbs
  let d := L * r * (r + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hu : (L + r) * a^2 ≤ d * classUnits rows L r :=
    (Nat.lt_mul_div_succ _ hd).le
  have hx : ((L : ℝ) + r) * (a : ℝ)^2 ≤
      (L : ℝ) * r * ((r : ℝ) + 1) * (classUnits rows L r : ℝ) := by exact_mod_cast hu
  have ha : (a : ℝ)^2 = (1000000 - (value rows r : ℝ))^2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (1000000 - value rows r))
    have hab : (a : ℝ) = |1000000 - (value rows r : ℝ)| := by
      simpa only [a, Int.cast_natCast, Int.cast_abs, Int.cast_sub, Int.cast_ofNat] using h
    rw [hab, sq_abs]
  rw [ha] at hx
  apply (mul_le_mul_of_nonneg_right (progressionWeight_upper_one L r hL) (sq_nonneg _)).trans
  unfold positiveWeight trial
  have hL' : (L : ℝ) ≠ 0 := by positivity
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hL', hr', hr1]
  nlinarith only [hx]

/-- Kernel-checkable upper bound covering the entire infinite Pareto measure. -/
theorem trial_error_le (rows : List Row) (L : ℕ) (hL : 0 < L)
    (hs : ∀ t ∈ rows, (t.1 = 2 ∨ t.1 = 3) ∧ 0 < t.2.1)
    (hp : ∀ t ∈ rows, t.2.1 * t.1 ∣ L) :
    paretoError (trial rows) ≤
      ((∑ i ∈ Finset.range L, classUnits rows L (i+1) : ℕ) : ℝ) / 10^12 := by
  have hseeds : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    omega
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded _ hseeds (trial_legal rows hs)
  have hb (k : ℕ) : |1 - trial rows k| ≤ 1 + C :=
    (abs_sub _ _).trans (by simpa using add_le_add_left (hC k) (1 : ℝ))
  have he := periodic_paretoInner L hL (fun k => 1 - trial rows k) hb
    (fun k => by rw [trial_period rows L hp k])
  change paretoError (trial rows) = _ at he
  rw [he, Fin.sum_univ_eq_sum_range
    (fun i : ℕ => progressionWeight L (i+1) * (1 - trial rows (i+1))^2) L,
    Nat.cast_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun i _ => class_bound rows L (i+1) hL (Nat.succ_pos _)

def period5040Rows : List Row := [
  (2, 1, 588942), (3, 1, 360550), (2, 2, 166643), (3, 2, -42405),
  (3, 3, 50246), (2, 4, 69475), (3, 4, 43987), (2, 5, -42653),
  (3, 5, -56968), (3, 6, 15882), (2, 7, -21529), (3, 7, -22715),
  (2, 8, 47282), (3, 8, 7922), (2, 10, -2516), (3, 10, 21054),
  (3, 12, -3237), (2, 14, -14505), (3, 14, 7011), (3, 15, -1474),
  (3, 16, 1117), (2, 20, -4958), (3, 20, -917), (3, 21, -7130),
  (3, 24, 7959), (2, 28, -4541), (3, 28, -376), (3, 30, -4092),
  (2, 35, 5586), (3, 35, 9993), (2, 40, -5485), (3, 40, -1784),
  (3, 42, -1269), (3, 48, -839), (2, 56, -3418), (3, 56, 260),
  (3, 60, 1497), (2, 70, 1709), (3, 70, -3814), (3, 80, 772),
  (3, 84, 1696), (3, 105, 565), (3, 112, -892), (3, 120, -336),
  (2, 140, 401), (3, 140, 1067), (3, 168, -1720), (3, 210, 756),
  (3, 240, -436), (2, 280, 660), (3, 280, -60), (3, 336, 402),
  (3, 420, -346), (3, 560, 8), (3, 840, 94), (3, 1680, -20)]

private theorem valid5040 : ∀ t ∈ period5040Rows,
    (t.1 = 2 ∨ t.1 = 3) ∧ 0 < t.2.1 := by decide +kernel

private theorem divides5040 : ∀ t ∈ period5040Rows, t.2.1 * t.1 ∣ 5040 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Evaluate the finite outward-rounded class totals for the 56 coefficients.
private theorem units5040 :
    (∑ i ∈ Finset.range 5040, classUnits period5040Rows 5040 (i+1)) = 39318898889 := by
  decide +kernel

/-- Explicit legal two-seed witness and its complete squared-error bound. -/
theorem period5040_certificate :
    trial period5040Rows ∈ legalSeedSpan ({2, 3} : Set ℕ) ∧
      paretoError (trial period5040Rows) ≤ (39318898889 : ℝ) / 10^12 := by
  refine ⟨trial_legal _ valid5040, ?_⟩
  have h := trial_error_le _ 5040 (by decide) valid5040 divides5040
  simpa only [units5040, Nat.cast_ofNat] using h

end
end RiemannResearch.RH.Pareto.TwoSeedPeriodicCertificate
