/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapStretched
import RiemannResearch.Analysis.FiniteHarmonicBounds
import RiemannResearch.Analysis.OptimizedStretchedBarrier

/-! Uniform arithmetic tail-envelope recurrence for the direct MediumPNT
provider. The subsequent scalar delayed-contraction theorem upgrades this
recurrence to a stretched-exponential Mertens bound. -/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

def mertensTailTerm (T : ℝ) (N : ℕ) : ℝ :=
  if Real.exp T ≤ (N : ℝ) then |M (N : ℝ)| / (N : ℝ) else 0

def mertensTailEnvelope (T : ℝ) : ℝ := sSup (Set.range (mertensTailTerm T))

theorem mertensTailTerm_nonneg (T : ℝ) (N : ℕ) : 0 ≤ mertensTailTerm T N := by
  unfold mertensTailTerm
  split_ifs <;> positivity

theorem mertensTailTerm_le_one (T : ℝ) (N : ℕ) : mertensTailTerm T N ≤ 1 := by
  unfold mertensTailTerm
  split_ifs with hN
  · have hNr : 0 < (N : ℝ) := (Real.exp_pos T).trans_le hN
    exact (div_le_one hNr).mpr (M_nat_abs_le_self N)
  · norm_num

theorem mertensTailEnvelope_bddAbove (T : ℝ) :
    BddAbove (Set.range (mertensTailTerm T)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨N, rfl⟩
  exact mertensTailTerm_le_one T N

theorem mertensTailEnvelope_nonneg (T : ℝ) : 0 ≤ mertensTailEnvelope T := by
  have h := le_csSup (mertensTailEnvelope_bddAbove T)
    (Set.mem_range_self (f := mertensTailTerm T) 0)
  exact (mertensTailTerm_nonneg T 0).trans h

theorem mertensTailEnvelope_le_one (T : ℝ) : mertensTailEnvelope T ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨N, rfl⟩
  exact mertensTailTerm_le_one T N

theorem mertensTailEnvelope_nat_bound (T : ℝ) (N : ℕ)
    (hN : Real.exp T ≤ (N : ℝ)) :
    |M (N : ℝ)| / (N : ℝ) ≤ mertensTailEnvelope T := by
  have h := le_csSup (mertensTailEnvelope_bddAbove T)
    (Set.mem_range_self (f := mertensTailTerm T) N)
  simpa [mertensTailTerm, mertensTailEnvelope, hN] using h

/-- The natural-index supremum controls all real arguments above a natural
cutoff. This is what discharges the whole infinite-tail hypothesis of the
finite reciprocal-cutoff theorem. -/
theorem mertensTailEnvelope_real_bound (T : ℝ) (Y : ℕ) (hY : 0 < Y)
    (hcut : Real.exp T ≤ (Y : ℝ)) (u : ℝ) (hu : (Y : ℝ) ≤ u) :
    |M u| ≤ mertensTailEnvelope T * u := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hu0 : 0 < u := hYr.trans_le hu
  have hfloor : Y ≤ ⌊u⌋₊ := by simpa using Nat.floor_mono hu
  have hfloorR : (Y : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hfloor0 : 0 < (⌊u⌋₊ : ℝ) := hYr.trans_le hfloorR
  have hm := mertensTailEnvelope_nat_bound T ⌊u⌋₊ (hcut.trans hfloorR)
  have hh := (div_le_iff₀ hfloor0).mp hm
  have he : M u = M (⌊u⌋₊ : ℝ) := by simp [M]
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hu0.le)
    (mertensTailEnvelope_nonneg T))

/-- One finite cutoff estimate, uniform over every N above exp T.
The cutoff loss L is held fixed as N varies. -/
theorem mertens_stretched_tail_finite
    (c D : ℝ) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hR : ∀ u : ℝ, 1 ≤ u →
      |R u| ≤ D * u * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) /
        (1 + Real.log u) ^ 2)
    (T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (hTL : Real.log 2 ≤ T - L)
    (N : ℕ) (hNcut : Real.exp T ≤ (N : ℝ)) :
    |M (N : ℝ)| / (N : ℝ) ≤
      ((3 * L + (13 + 7 * Real.log 2)) *
          mertensTailEnvelope (T - L - Real.log 2) +
        3 * Real.exp (-L) +
        3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) / T := by
  have hNr : 0 < (N : ℝ) := (Real.exp_pos T).trans_le hNcut
  have hN : 0 < N := by exact_mod_cast hNr
  have hlogN : T ≤ Real.log (N : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos T) hNcut
    simpa only [Real.log_exp] using hh
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := hT.le.trans hlogN
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  let z : ℝ := (N : ℝ) * Real.exp (-L)
  let Y : ℕ := ⌊z⌋₊
  let J : ℕ := ⌊Real.exp L⌋₊ + 1
  let A : ℝ := mertensTailEnvelope (T - L - Real.log 2)
  have hA : 0 ≤ A := mertensTailEnvelope_nonneg _
  have hz0 : 0 < z := mul_pos hNr (Real.exp_pos _)
  have hzLower : Real.exp (T - L) ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hNcut (Real.exp_pos (-L)).le
    simpa only [← Real.exp_add, sub_eq_add_neg, z] using hh
  have hz2 : 2 ≤ z := by
    have hh := Real.exp_le_exp.mpr hTL
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
    exact hh.trans hzLower
  have hYu : (Y : ℝ) ≤ z := Nat.floor_le hz0.le
  have hYl : z - 1 < (Y : ℝ) := by
    have hh := Nat.lt_floor_add_one z
    dsimp [Y]
    linarith
  have hYhalf : z / 2 ≤ (Y : ℝ) := by linarith
  have hYr : (0 : ℝ) < Y := by linarith
  have hY : 0 < Y := by exact_mod_cast hYr
  have hYone : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hexpMinus : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL)
  have hYNr : (Y : ℝ) ≤ N := by
    exact hYu.trans (by dsimp [z]; exact mul_le_of_le_one_right hNr.le hexpMinus)
  have hYN : Y ≤ N := by exact_mod_cast hYNr
  have hYcut : Real.exp (T - L - Real.log 2) ≤ (Y : ℝ) := by
    calc
      _ = Real.exp (T - L) / 2 := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ z / 2 := div_le_div_of_nonneg_right hzLower (by norm_num)
      _ ≤ _ := hYhalf
  have hlogYu : Real.log (Y : ℝ) ≤ Real.log (N : ℝ) - L := by
    have hh := Real.log_le_log hYr hYu
    simpa only [z, Real.log_mul hNr.ne' (Real.exp_pos (-L)).ne', Real.log_exp, sub_eq_add_neg] using hh
  have hlogYl : Real.log (N : ℝ) - L - Real.log 2 ≤ Real.log (Y : ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < z / 2) hYhalf
    simpa only [Real.log_div hz0.ne' (by norm_num : (2 : ℝ) ≠ 0),
      z, Real.log_mul hNr.ne' (Real.exp_pos (-L)).ne', Real.log_exp, sub_eq_add_neg] using hh
  have hlogQuot : Real.log ((N : ℝ) / Y) = Real.log (N : ℝ) - Real.log (Y : ℝ) :=
    Real.log_div hNr.ne' hYr.ne'
  have hLlo : L ≤ Real.log ((N : ℝ) / Y) := by rw [hlogQuot]; linarith
  have hLhi : Real.log ((N : ℝ) / Y) ≤ L + Real.log 2 := by rw [hlogQuot]; linarith
  have hJ : 0 < J := by dsimp [J]; omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJlower : Real.exp L ≤ (J : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp L)
    simpa [J, Nat.cast_add, Nat.cast_one] using hh.le
  have hJupper : (J : ℝ) ≤ Real.exp L + 1 := by
    have hh := Nat.floor_le (Real.exp_pos L).le
    dsimp [J]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hexpOne : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hJtwo : (J : ℝ) ≤ 2 * Real.exp L := by linarith
  have hlogJ : Real.log (J : ℝ) ≤ L + Real.log 2 := by
    have hh := Real.log_le_log hJr hJtwo
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos L).ne', Real.log_exp] at hh
    linarith
  have hH : (harmonic J : ℝ) + 1 ≤ L + 2 + Real.log 2 := by
    have hh := harmonic_le_one_add_log J
    linarith
  have hRecip : 1 / (J : ℝ) ≤ Real.exp (-L) := by
    apply (div_le_iff₀ hJr).2
    have hh := mul_le_mul_of_nonneg_right hJlower (Real.exp_pos (-L)).le
    have he : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
    rw [he] at hh
    simpa only [mul_comm] using hh
  have hYJ : (J : ℝ) ≤ (Y : ℝ) * J := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hYone) hJr.le]
  have hRecip2 : 1 / ((Y : ℝ) * J) ≤ Real.exp (-L) := by
    exact (one_div_le_one_div_of_le hJr hYJ).trans hRecip
  have hMtail : ∀ u : ℝ, (Y : ℝ) ≤ u → |M u| ≤ A * u := by
    intro u hu
    exact mertensTailEnvelope_real_bound _ Y hY hYcut u hu
  have hPrime : Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ ((1 : ℝ) / 10)) ≤
      Real.exp (-c * L ^ ((1 : ℝ) / 10)) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.rpow_le_rpow hL hLlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
    nlinarith
  have hf := M_log_bootstrap_finite_stretched N Y J hY hYN hJ A c D hA hc hD hMtail hR
  rw [abs_mul, abs_of_nonneg hlogN0, hlog4] at hf
  have hRecipN := mul_le_mul_of_nonneg_left hRecip hNr.le
  have hRecip2N := mul_le_mul_of_nonneg_left hRecip2 hNr.le
  have hHN := mul_le_mul_of_nonneg_left hH (mul_nonneg hA hNr.le)
  have hLN := mul_le_mul_of_nonneg_left hLhi
    (show 0 ≤ 2 * A * (N : ℝ) by positivity)
  have hPN := mul_le_mul_of_nonneg_left hPrime
    (show 0 ≤ 3 * D * (N : ℝ) by positivity)
  have hsum : |M (N : ℝ)| * Real.log (N : ℝ) ≤
      (N : ℝ) * ((3 * L + (13 + 7 * Real.log 2)) * A +
        3 * Real.exp (-L) + 3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) := by
    change (Y : ℝ) ≤ (N : ℝ) * Real.exp (-L) at hYu
    nlinarith only [hf, hYu, hRecipN, hRecip2N, hHN, hLN, hPN]
  apply (div_le_div_iff₀ hNr hT).2
  have hm := mul_le_mul_of_nonneg_left hlogN (abs_nonneg (M (N : ℝ)))
  exact hm.trans (by simpa only [A, mul_comm] using hsum)

/-- Exact uniform tail-envelope recurrence. Holding L fixed while taking
the supremum avoids all regularity assumptions on a future choice L(T). -/
theorem mertensTailEnvelope_stretched_recurrence
    (c D : ℝ) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hR : ∀ u : ℝ, 1 ≤ u →
      |R u| ≤ D * u * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) /
        (1 + Real.log u) ^ 2)
    (T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (hTL : Real.log 2 ≤ T - L) :
    mertensTailEnvelope T ≤
      ((3 * L + (13 + 7 * Real.log 2)) *
          mertensTailEnvelope (T - L - Real.log 2) +
        3 * Real.exp (-L) +
        3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) / T := by
  have hbudget : 0 ≤
      ((3 * L + (13 + 7 * Real.log 2)) *
          mertensTailEnvelope (T - L - Real.log 2) +
        3 * Real.exp (-L) +
        3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) / T := by
    have hh := mertensTailEnvelope_nonneg (T - L - Real.log 2)
    have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨N, rfl⟩
  unfold mertensTailTerm
  split_ifs with hN
  · exact mertens_stretched_tail_finite c D hc hD hR T L hT hL hTL N hN
  · exact hbudget

/-- Passing from natural to real arguments preserves the log-logarithmic
profile after dividing its positive exponential coefficient by four. -/
theorem M_stretched_loglog_real_of_nat
    (β c B : ℝ) (hβ : 0 ≤ β) (hβone : β ≤ 1) (hc : 0 < c) (hB : 0 ≤ B)
    (hNat : ∀ N : ℕ, 1 ≤ N →
      |M (N : ℝ)| ≤ B * N * Real.exp
        (-c * ((6 + Real.log (N : ℝ)) * Real.log (6 + Real.log (N : ℝ))) ^ β)) :
    ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp
        (-(c / 4) * ((6 + Real.log x) * Real.log (6 + Real.log x)) ^ β) := by
  intro x hx
  let N : ℕ := ⌊x⌋₊
  have hN : 1 ≤ N := by simpa [N] using Nat.floor_mono hx
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx0 : 0 < x := by linarith
  have hNu : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hNl : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hx2 : x ≤ 2 * (N : ℝ) := by linarith
  have hlogx : Real.log x ≤ Real.log (N : ℝ) + Real.log 2 := by
    have hh := Real.log_le_log hx0 hx2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hh
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let s : ℝ := 6 + Real.log (N : ℝ)
  let t : ℝ := 6 + Real.log x
  have hs6 : 6 ≤ s := by dsimp [s]; linarith [Real.log_nonneg hN1]
  have ht6 : 6 ≤ t := by dsimp [t]; linarith [Real.log_nonneg hx]
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hts : t ≤ 2 * s := by dsimp [t, s]; linarith [Real.log_nonneg hN1]
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlog2s : Real.log 2 ≤ Real.log s :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogts : Real.log t ≤ 2 * Real.log s := by
    have hh := Real.log_le_log ht0 hts
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs0.ne'] at hh
    linarith
  have hprod : t * Real.log t ≤ 4 * (s * Real.log s) := by
    have hh := mul_le_mul hts hlogts hlogt (show 0 ≤ 2 * s by positivity)
    nlinarith only [hh]
  have hpower : (t * Real.log t) ^ β ≤ 4 * (s * Real.log s) ^ β := by
    calc
      _ ≤ (4 * (s * Real.log s)) ^ β :=
        Real.rpow_le_rpow (mul_nonneg ht0.le hlogt) hprod hβ
      _ = (4 : ℝ) ^ β * (s * Real.log s) ^ β :=
        Real.mul_rpow (by norm_num) (mul_nonneg hs0.le hlogs)
      _ ≤ 4 * (s * Real.log s) ^ β := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (mul_nonneg hs0.le hlogs) _)
        simpa using Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 4) hβone
  have hExp : Real.exp (-c * (s * Real.log s) ^ β) ≤
      Real.exp (-(c / 4) * (t * Real.log t) ^ β) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hpower hc.le]
  have he : M x = M (N : ℝ) := by simp [N, M]
  rw [he]
  calc
    _ ≤ B * N * Real.exp (-c * (s * Real.log s) ^ β) := hNat N hN
    _ ≤ B * x * Real.exp (-(c / 4) * (t * Real.log t) ^ β) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hNu hB) hExp
        (Real.exp_pos _).le (mul_nonneg hB hx0.le)
    _ = _ := rfl

/-- A shifted log-log profile also supplies a shifted plain stretched
profile. The multiplicative coefficient stays strictly positive. -/
theorem M_stretched_shifted_of_loglog
    (β c B : ℝ) (hβ : 0 ≤ β) (hc : 0 < c) (hB : 0 ≤ B)
    (hReal : ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp
        (-c * ((6 + Real.log x) * Real.log (6 + Real.log x)) ^ β)) :
    ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp
        (-(c * (Real.log 6) ^ β) * (6 + Real.log x) ^ β) := by
  intro x hx
  let s : ℝ := 6 + Real.log x
  have hs6 : 6 ≤ s := by dsimp [s]; linarith [Real.log_nonneg hx]
  have hs0 : 0 < s := by linarith
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog : Real.log 6 ≤ Real.log s := Real.log_le_log (by norm_num) hs6
  have hprod : s * Real.log 6 ≤ s * Real.log s := mul_le_mul_of_nonneg_left hlog hs0.le
  have hp : s ^ β * (Real.log 6) ^ β ≤ (s * Real.log s) ^ β := by
    rw [← Real.mul_rpow hs0.le hlog6.le]
    exact Real.rpow_le_rpow (mul_nonneg hs0.le hlog6.le) hprod hβ
  apply (hReal x hx).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (by linarith))
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hp hc.le
  nlinarith only [hh]

/-- Assembly interface for the independent scalar barrier proof. -/
theorem M_stretched_loglog_of_tail_bound
    (d B : ℝ) (hd : 0 < d) (hB : 0 ≤ B)
    (hTail : ∀ T : ℝ, 0 ≤ T → mertensTailEnvelope T ≤ B * Real.exp
      (-d * ((6 + T) * Real.log (6 + T)) ^ ((1 : ℝ) / 11))) :
    ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp
        (-(d / 4) * ((6 + Real.log x) * Real.log (6 + Real.log x)) ^ ((1 : ℝ) / 11)) := by
  apply M_stretched_loglog_real_of_nat ((1 : ℝ) / 11) d B
    (by norm_num) (by norm_num) hd hB
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hE := mertensTailEnvelope_nat_bound (Real.log (N : ℝ)) N
    (by rw [Real.exp_log hN0])
  have hh := hE.trans (hTail (Real.log (N : ℝ)) (Real.log_nonneg hN1))
  have hm := (div_le_iff₀ hN0).mp hh
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hm

/-- The direct MediumPNT provider, the exact finite arithmetic identity,
and uniform delayed contraction give a positive log-logarithmic
stretched-exponential decay coefficient without new arithmetic hypotheses. -/
theorem M_stretched_loglog_bound :
    ∃ d : ℝ, 0 < d ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp
        (-d * ((6 + Real.log x) * Real.log (6 + Real.log x)) ^ ((1 : ℝ) / 11)) := by
  obtain ⟨c, hc, D, hD, hR⟩ := R_stretched_squareLog_bound
  have hK : 0 ≤ 13 + 7 * Real.log 2 := by
    have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hrec := mertensTailEnvelope_stretched_recurrence c D hc.le hD.le hR
  obtain ⟨d, hd, B, hB, hTail⟩ :=
    RiemannResearch.Analysis.optimized_stretched_envelope_bound
      (E := mertensTailEnvelope) (c := c) (D := D) (K := 13 + 7 * Real.log 2)
      (hc := hc) (hD := hD.le) (hK := hK)
      (hE0 := mertensTailEnvelope_nonneg) (hE1 := mertensTailEnvelope_le_one)
      (hrec := hrec)
  refine ⟨d / 4, by positivity, B, hB, ?_⟩
  apply M_stretched_loglog_of_tail_bound d B hd hB
  intro T hT
  simpa only [RiemannResearch.Analysis.optimizedLogProfile, add_comm] using hTail T hT

/-- A plain stretched-exponential corollary, retained for profile consumers
that do not yet use the stronger iterated-logarithm factor. -/
theorem M_stretched_decay_bound :
    ∃ d : ℝ, 0 < d ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp (-d * (Real.log x) ^ ((1 : ℝ) / 11)) := by
  obtain ⟨c, hc, B, hB, hReal⟩ := M_stretched_loglog_bound
  let d : ℝ := c * (Real.log 6) ^ ((1 : ℝ) / 11)
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos hc (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _)
  have hShift := M_stretched_shifted_of_loglog ((1 : ℝ) / 11) c B
    (by norm_num) hc hB hReal
  refine ⟨d, hd, B, hB, ?_⟩
  intro x hx
  apply (hShift x hx).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (by linarith))
  apply Real.exp_le_exp.mpr
  have hp := Real.rpow_le_rpow (Real.log_nonneg hx)
    (show Real.log x ≤ 6 + Real.log x by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 11)
  have hh := mul_le_mul_of_nonneg_left hp hd.le
  change -d * (6 + Real.log x) ^ ((1 : ℝ) / 11) ≤
    -d * (Real.log x) ^ ((1 : ℝ) / 11)
  linarith

end RiemannResearch.NumberTheory.PrimeNumberTheorem
