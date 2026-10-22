import RiemannResearch.RH.ParetoHiddenNoiseMoments
import RiemannResearch.RH.ParetoRepairCovariance
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# An actual Pareto modulus for nearby binary repair scales

Source: the arithmetic-repair report, §5. The proof works directly with the
complete discrete Pareto law. Exact mismatch intervals, the regular head, and
the infinite tail are retained before obtaining the logarithmic modulus.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The unnormalized binary difference at the two integer scales `n` and `n+h`. -/
def binaryScaleDifference (n h k : ℕ) : ℝ :=
  dilation (n + h) (residue 2) k - dilation n (residue 2) k

theorem binaryScaleDifference_abs_le (n h k : ℕ) :
    |binaryScaleDifference n h k| ≤ (n : ℝ) + h := by
  have hw (a : ℕ) : 0 ≤ squareWave a k ∧ squareWave a k ≤ 1 := by
    constructor
    · unfold squareWave; positivity
    · unfold squareWave
      exact_mod_cast (show (k / a) % 2 ≤ 1 by omega)
  have he : binaryScaleDifference n h k =
      ((n : ℝ) + h) * squareWave (n + h) k - (n : ℝ) * squareWave n k := by
    simp only [binaryScaleDifference, dilation, residue, squareWave, Nat.cast_add]
  rw [he]
  apply abs_le.mpr
  have ha := hw (n + h)
  have hb := hw n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  constructor <;> nlinarith

theorem binaryScaleDifference_head_zero (n h k : ℕ) (hk : k < n) :
    binaryScaleDifference n h k = 0 := by
  have hk' : k < n + h := by omega
  simp [binaryScaleDifference, dilation, residue, Nat.div_eq_of_lt hk, Nat.div_eq_of_lt hk']

theorem binaryScaleDifference_regular_value (n h j k : ℕ)
    (hklo : j * (n + h) ≤ k) (hkhi : k < (j + 1) * n) :
    binaryScaleDifference n h k = (h : ℝ) * (j % 2 : ℕ) := by
  have hl : k / n = j := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · exact hkhi
  have hr : k / (n + h) = j := by
    apply Nat.div_eq_of_lt_le
    · exact hklo
    · nlinarith
  simp only [binaryScaleDifference, dilation, residue, hl, hr, Nat.cast_add]
  ring

theorem binaryScaleDifference_interval_div (n h j k : ℕ) (hj : 0 < j)
    (hjn : j * h ≤ n) (hklo : j * n ≤ k) (hkhi : k < j * (n + h)) :
    k / n = j ∧ k / (n + h) = j - 1 := by
  constructor
  · apply Nat.div_eq_of_lt_le
    · exact hklo
    · have he : j * (n + h) ≤ (j + 1) * n := by nlinarith
      exact lt_of_lt_of_le hkhi he
  · have hj1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
    apply Nat.div_eq_of_lt_le
    · have he : (j - 1) * (n + h) + (n + h) = j * (n + h) := by
        calc
          _ = (j - 1 + 1) * (n + h) := by ring
          _ = _ := by rw [hj1]
      nlinarith
    · simpa only [hj1] using hkhi

theorem binaryScaleDifference_interval_value (n h j k : ℕ) (hj : 0 < j)
    (hjn : j * h ≤ n) (hklo : j * n ≤ k) (hkhi : k < j * (n + h)) :
    binaryScaleDifference n h k = if j % 2 = 1 then -(n : ℝ) else (n : ℝ) + h := by
  have hd := binaryScaleDifference_interval_div n h j k hj hjn hklo hkhi
  by_cases ho : j % 2 = 1
  · have hp : (j - 1) % 2 = 0 := by omega
    simp [binaryScaleDifference, dilation, residue, hd.1, hd.2, ho, hp]
  · have he : j % 2 = 0 := by omega
    have hp : (j - 1) % 2 = 1 := by omega
    simp [binaryScaleDifference, dilation, residue, hd.1, hd.2, ho, he, hp]

/-- Exact Pareto mass of a mismatch interval for an arbitrary integer scale gap. -/
theorem binaryScaleDifference_interval_mass (n h j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    (∑ k ∈ Finset.Ico (j * n) (j * (n + h)), positiveWeight k) =
      (h : ℝ) / ((j : ℝ) * n * ((n : ℝ) + h)) := by
  rw [positiveWeight_interval _ _ (Nat.mul_pos hj hn) (by nlinarith)]
  push_cast
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hnh : (n : ℝ) + h ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The exact mismatch contribution retains its parity-dependent amplitude. -/
def binaryMismatchSquare (n h j : ℕ) : ℝ :=
  if j % 2 = 1 then (h : ℝ) * n / ((j : ℝ) * ((n : ℝ) + h))
  else (h : ℝ) * ((n : ℝ) + h) / ((j : ℝ) * n)

theorem binaryScaleDifference_interval_square (n h j : ℕ) (hn : 0 < n)
    (hj : 0 < j) (hjn : j * h ≤ n) :
    (∑ k ∈ Finset.Ico (j * n) (j * (n + h)),
      positiveWeight k * (binaryScaleDifference n h k)^2) = binaryMismatchSquare n h j := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hnh : (n : ℝ) + h ≠ 0 := by positivity
  by_cases ho : j % 2 = 1
  · calc
      _ = (∑ k ∈ Finset.Ico (j * n) (j * (n + h)), positiveWeight k) * (n : ℝ)^2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [binaryScaleDifference_interval_value n h j k hj hjn
          (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2, if_pos ho]
        ring
      _ = binaryMismatchSquare n h j := by
        rw [binaryScaleDifference_interval_mass n h j hn hj]
        simp only [binaryMismatchSquare, if_pos ho]
        field_simp
        <;> ring
  · calc
      _ = (∑ k ∈ Finset.Ico (j * n) (j * (n + h)), positiveWeight k) * ((n : ℝ) + h)^2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [binaryScaleDifference_interval_value n h j k hj hjn
          (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2, if_neg ho]
      _ = binaryMismatchSquare n h j := by
        rw [binaryScaleDifference_interval_mass n h j hn hj]
        simp only [binaryMismatchSquare, if_neg ho]
        field_simp
        <;> ring

/-- Exact block decomposition, including the regular contribution after both jumps. -/
theorem binaryScaleDifference_block_exact (n h j : ℕ) (hn : 0 < n)
    (hj : 0 < j) (hjn : j * h ≤ n) :
    (∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
      positiveWeight k * (binaryScaleDifference n h k)^2) =
      binaryMismatchSquare n h j +
      ∑ k ∈ Finset.Ico (j * (n + h)) ((j + 1) * n),
        positiveWeight k * ((h : ℝ) * (j % 2 : ℕ))^2 := by
  have hl : j * n ≤ j * (n + h) := by nlinarith
  have hr : j * (n + h) ≤ (j + 1) * n := by nlinarith
  have hm := binaryScaleDifference_interval_square n h j hn hj hjn
  have he : (∑ k ∈ Finset.Ico (j * (n + h)) ((j + 1) * n),
      positiveWeight k * (binaryScaleDifference n h k)^2) =
      ∑ k ∈ Finset.Ico (j * (n + h)) ((j + 1) * n),
        positiveWeight k * ((h : ℝ) * (j % 2 : ℕ))^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [binaryScaleDifference_regular_value n h j k
      (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2]
  rw [← hm, ← he]
  rw [Finset.sum_Ico_eq_sub _ (le_trans hl hr),
    Finset.sum_Ico_eq_sub _ hl, Finset.sum_Ico_eq_sub _ hr]
  ring

/-- Nearby scales give a uniform harmonic bound for the mismatch coefficient. -/
theorem binaryMismatchSquare_le (n h j : ℕ) (hn : 0 < n) (hj : 0 < j) (hh : h ≤ n) :
    binaryMismatchSquare n h j ≤ 2 * h / (j : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hnh : (n : ℝ) + h ≠ 0 := by positivity
  have hnR : (0 : ℝ) < n := by positivity
  have hhR : (h : ℝ) ≤ n := by exact_mod_cast hh
  unfold binaryMismatchSquare
  split_ifs
  · calc
      _ = ((h : ℝ) / j) * ((n : ℝ) / ((n : ℝ) + h)) := by field_simp <;> ring
      _ ≤ ((h : ℝ) / j) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
      _ = _ := by ring
  · calc
      _ = ((h : ℝ) / j) * (((n : ℝ) + h) / (n : ℝ)) := by field_simp <;> ring
      _ ≤ ((h : ℝ) / j) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_iff₀ hnR).mpr
        linarith
      _ = _ := by ring

/-- The full block is bounded by mismatch energy plus a regular head contribution. -/
theorem binaryScaleDifference_block_le (n h j : ℕ) (hn : 0 < n)
    (hj : 0 < j) (hjn : j * h ≤ n) (hh : h ≤ n) :
    (∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
      positiveWeight k * (binaryScaleDifference n h k)^2) ≤
      2 * h / (j : ℝ) + (h : ℝ)^2 *
        ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k := by
  have hp : (0 : ℝ) ≤ (j % 2 : ℕ) := Nat.cast_nonneg _
  have hp1 : ((j % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show j % 2 ≤ 1 by omega)
  have hcoef : ((h : ℝ) * (j % 2 : ℕ))^2 ≤ (h : ℝ)^2 := by
    have hmul : (h : ℝ) * (j % 2 : ℕ) ≤ h := by nlinarith [show (0 : ℝ) ≤ h from Nat.cast_nonneg h]
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ (h : ℝ) * (j % 2 : ℕ)) hmul]
  have hsub : Finset.Ico (j * (n + h)) ((j + 1) * n) ⊆
      Finset.Ico (j * n) ((j + 1) * n) := by
    intro k hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
    apply Finset.mem_Ico.mpr
    constructor
    · nlinarith
    · exact hhi
  have hr : (∑ k ∈ Finset.Ico (j * (n + h)) ((j + 1) * n),
      positiveWeight k * ((h : ℝ) * (j % 2 : ℕ))^2) ≤
      (h : ℝ)^2 * ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
          positiveWeight k * ((h : ℝ) * (j % 2 : ℕ))^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k hk hnk => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
      _ ≤ ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k * (h : ℝ)^2 :=
        Finset.sum_le_sum (fun k hk =>
          mul_le_mul_of_nonneg_left hcoef (positiveWeight_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; ring
  rw [binaryScaleDifference_block_exact n h j hn hj hjn]
  exact add_le_add (binaryMismatchSquare_le n h j hn hj hh) hr

/-- The complete infinite norm, with separate harmonic head and exact Pareto-tail costs. -/
theorem binaryScaleDifference_norm_head_tail_bound (n h L : ℕ) (hn : 0 < n)
    (hh : h ≤ n) (hL : L * h ≤ n) :
    paretoInner (binaryScaleDifference n h) (binaryScaleDifference n h) ≤
      2 * h * (∑ j ∈ Finset.range L, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) +
      (h : ℝ)^2 / n + ((n : ℝ) + h)^2 / (((L + 1) * n : ℕ) : ℝ) := by
  have hf : ∀ k, |(binaryScaleDifference n h k)^2| ≤ ((n : ℝ) + h)^2 := by
    intro k
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [binaryScaleDifference_abs_le n h k,
      sq_abs (binaryScaleDifference n h k), abs_nonneg (binaryScaleDifference n h k)]
  have hb := paretoMean_blocks_exact (fun k => (binaryScaleDifference n h k)^2) hf n L
    (fun k hk => by rw [binaryScaleDifference_head_zero n h k hk]; norm_num)
  have heq : paretoMean (fun k => (binaryScaleDifference n h k)^2) =
      paretoInner (binaryScaleDifference n h) (binaryScaleDifference n h) := by
    simp only [paretoMean, paretoInner, pow_two]
  rw [heq] at hb
  have hw := sum_Ico_mul_blocks positiveWeight n L
  rw [positiveWeight_interval n ((L + 1) * n) hn (by nlinarith)] at hw
  have hs := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range L) =>
    binaryScaleDifference_block_le n h (j + 1) hn (by omega)
      (le_trans (Nat.mul_le_mul_right h (by have hj' := Finset.mem_range.mp hj; omega)) hL) hh)
  have hm : (∑ j ∈ Finset.range L, 2 * (h : ℝ) / ((j + 1 : ℕ) : ℝ)) =
      2 * h * ∑ j ∈ Finset.range L, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [Nat.add_assoc] at hs
  rw [Finset.sum_add_distrib, hm, ← Finset.mul_sum, ← hw] at hs
  have har : (h : ℝ)^2 * (1 / (n : ℝ) - 1 / (((L + 1) * n : ℕ) : ℝ)) =
      (h : ℝ)^2 / n - (h : ℝ)^2 / (((L + 1) * n : ℕ) : ℝ) := by ring
  rw [har] at hs
  have hnon : 0 ≤ (h : ℝ)^2 / (((L + 1) * n : ℕ) : ℝ) := by positivity
  have ht := pareto_nonnegative_tail_bounds (fun k => (binaryScaleDifference n h k)^2)
    hf (fun k => sq_nonneg _) ((L + 1) * n) (Nat.mul_pos (by omega) hn)
  rw [hb]
  linarith

/-- A genuine logarithmic modulus for the unnormalized two-scale binary difference. -/
theorem binaryScaleDifference_norm_log_bound (n h : ℕ) (hh0 : 0 < h) (hh : h ≤ n) :
    paretoInner (binaryScaleDifference n h) (binaryScaleDifference n h) ≤
      8 * h * (1 + Real.log ((n : ℝ) / h)) := by
  have hn : 0 < n := lt_of_lt_of_le hh0 hh
  have hnR : (0 : ℝ) < n := by positivity
  have hhR : (0 : ℝ) < h := by positivity
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast hh
  have hL : (n / h) * h ≤ n := (Nat.le_div_iff_mul_le hh0).mp le_rfl
  have hLpos : 0 < n / h := by
    have he : 1 ≤ n / h := (Nat.le_div_iff_mul_le hh0).mpr (by simpa using hh)
    omega
  have hLreal : ((n / h : ℕ) : ℝ) ≤ (n : ℝ) / h := by
    apply (le_div_iff₀ hhR).mpr
    exact_mod_cast hL
  have hcut : n < (n / h + 1) * h := by
    have hr := Nat.mod_lt n hh0
    have he := Nat.mod_add_div n h
    nlinarith
  have hcutR : (n : ℝ) < (((n / h : ℕ) : ℝ) + 1) * h := by exact_mod_cast hcut
  have he := binaryScaleDifference_norm_head_tail_bound n h (n / h) hn hh hL
  have hcast : (harmonic (n / h) : ℝ) =
      ∑ j ∈ Finset.range (n / h), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
    simp [harmonic, one_div]
  have hharm := harmonic_le_one_add_log (n / h)
  rw [hcast] at hharm
  have hlog : Real.log ((n / h : ℕ) : ℝ) ≤ Real.log ((n : ℝ) / h) :=
    Real.log_le_log (by exact_mod_cast hLpos) hLreal
  have hmain : 2 * h *
      (∑ j ∈ Finset.range (n / h), (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) ≤
      2 * h * (1 + Real.log ((n : ℝ) / h)) := by
    exact mul_le_mul_of_nonneg_left (hharm.trans (by linarith)) (by positivity)
  have hregular : (h : ℝ)^2 / n ≤ h := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhnR (le_of_lt hhR)]
  have htail : ((n : ℝ) + h)^2 /
      (((n / h + 1) * n : ℕ) : ℝ) ≤ 4 * h := by
    push_cast
    apply (div_le_iff₀ (by positivity : 0 < (((n / h : ℕ) : ℝ) + 1) * (n : ℝ))).mpr
    have hp := mul_le_mul_of_nonneg_right (le_of_lt hcutR) (le_of_lt hnR)
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ (n : ℝ) + h)
      (by linarith : (n : ℝ) + h ≤ 2 * n)
    nlinarith
  have hratio : 1 ≤ (n : ℝ) / h := by
    apply (le_div_iff₀ hhR).mpr
    simpa using hhnR
  have hl0 := Real.log_nonneg hratio
  nlinarith [mul_nonneg (le_of_lt hhR) hl0]

/-- The four-residue repair has precisely the normalized full two-scale norm. -/
theorem arithmeticRepair_binary_variance_eq (n h : ℕ) (hn : 0 < n) :
    paretoVariance (arithmeticRepair 2 n (n + h)) =
      paretoInner (binaryScaleDifference n h) (binaryScaleDifference n h) / (n : ℝ)^2 := by
  simp only [paretoVariance, arithmeticRepair_mean_zero 2 n (n + h) (by omega) hn (by omega),
    sub_zero]
  have har : arithmeticRepair 2 n (n + h) =
      fun k => (n : ℝ)⁻¹ * binaryScaleDifference n h k := by
    funext k
    rw [arithmeticRepair_eq_dilation]
    rfl
  rw [har, paretoInner_const_mul_left (binaryScaleDifference_abs_le n h)
      (bounded_const_mul (binaryScaleDifference_abs_le n h) _),
    paretoInner_const_mul_right (binaryScaleDifference_abs_le n h) (binaryScaleDifference_abs_le n h)]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The actual, unconditioned Pareto variance has the required small-gap logarithmic modulus.
No integral representation, smooth-number theorem, or summability hypothesis is assumed. -/
theorem arithmeticRepair_binary_variance_log_bound (n h : ℕ) (hh0 : 0 < h) (hh : h ≤ n) :
    paretoVariance (arithmeticRepair 2 n (n + h)) ≤
      8 * ((h : ℝ) / (n : ℝ)^2) * (1 + Real.log ((n : ℝ) / h)) := by
  rw [arithmeticRepair_binary_variance_eq n h (lt_of_lt_of_le hh0 hh)]
  calc
    _ ≤ (8 * h * (1 + Real.log ((n : ℝ) / h))) / (n : ℝ)^2 :=
      div_le_div_of_nonneg_right (binaryScaleDifference_norm_log_bound n h hh0 hh) (sq_nonneg _)
    _ = _ := by ring

end
end RiemannResearch.RH.Pareto
