import RiemannResearch.NumberTheory.FiniteFloorTail
import RiemannResearch.RH.CanonicalMobiusFullEnergy

/-!
# Möbius cancellation on fixed Pareto windows

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`,
Section 3, for the finite tail identity and fixed-window proof strategy.
The finite identities and estimates are unconditional. The limit theorem
takes M(N)/N → 0 and the reciprocal Möbius sum → 0 as explicit hypotheses;
this module does not formalize those prime-number-theorem inputs.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

open RiemannResearch.NumberTheory
/-- The omitted Möbius floor terms are exact differences of ordinary partial sums. -/
theorem finite_mobius_floor_tail_identity (Y n : ℕ) (hn : 0 < n) (hYn : Y ≤ n) :
    1 - (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * ((n/d:ℕ):ℝ)) =
      ∑ k ∈ Finset.Icc 1 (n/(Y+1)),
        ((∑ d ∈ Finset.Icc 1 (n/k), (ArithmeticFunction.moebius d : ℝ)) -
         (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ))) := by
  have hsplit := positive_prefix_split_at
    (fun d => (ArithmeticFunction.moebius d : ℝ) * ((n/d:ℕ):ℝ)) Y n hYn
  rw [finite_mobius_floor_sum n n hn le_rfl] at hsplit
  have he : 1 - (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * ((n/d:ℕ):ℝ)) =
      ∑ d ∈ Finset.Icc (Y+1) n, (ArithmeticFunction.moebius d : ℝ) * ((n/d:ℕ):ℝ) := by linarith
  rw [he, finite_floor_tail_swap]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp : 0 < k := (Finset.mem_Icc.mp hk).1
  have hprod : k*(Y+1) ≤ n :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mp (Finset.mem_Icc.mp hk).2
  have hYk : Y ≤ n/k := by
    have hy1 : Y+1 ≤ n/k := (Nat.le_div_iff_mul_le hkp).mpr (by simpa [Nat.mul_comm] using hprod)
    omega
  have hs := positive_prefix_split_at (fun d => (ArithmeticFunction.moebius d : ℝ)) Y (n/k) hYk
  linarith

/-- A coarse finite-window estimate from ordinary and reciprocal Möbius cancellation. -/
theorem canonicalMobiusHead_window_bound (Y n K : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (hYn : Y < n) (hnK : n ≤ K * (Y + 1))
    (hM : ∀ t : ℕ, Y ≤ t →
      |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ))
    (hm : |mobiusReciprocalSum Y| ≤ ε) :
    |canonicalMobiusHead Y n| ≤
      1 + ε * (K : ℝ) * ((K : ℝ) + 2) * ((Y+1 : ℕ) : ℝ) := by
  classical
  let M : ℕ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)
  let q : ℕ := n / (Y+1)
  let T : ℝ := ∑ k ∈ Finset.Icc 1 q, (M (n/k) - M Y)
  have hq : q ≤ K := by
    have hh : q * (Y+1) ≤ n := Nat.div_mul_le_self n (Y+1)
    nlinarith
  have hqR : (q : ℝ) ≤ (K : ℝ) := by exact_mod_cast hq
  have hnR : (n : ℝ) ≤ (K : ℝ) * ((Y+1 : ℕ) : ℝ) := by exact_mod_cast hnK
  have hYR : (Y : ℝ) ≤ ((Y+1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ Y)
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 q) :
      |M (n/k) - M Y| ≤ ε * ((K : ℝ)+1) * ((Y+1 : ℕ) : ℝ) := by
    have hkp : 0 < k := (Finset.mem_Icc.mp hk).1
    have hprod : k*(Y+1) ≤ n :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mp (Finset.mem_Icc.mp hk).2
    have hYk : Y ≤ n/k := by
      have hy1 : Y+1 ≤ n/k :=
        (Nat.le_div_iff_mul_le hkp).mpr (by simpa [Nat.mul_comm] using hprod)
      omega
    have hnkR : ((n/k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.div_le_self n k)
    have hsumR : ((n/k : ℕ) : ℝ) + (Y : ℝ) ≤
        ((K : ℝ)+1) * ((Y+1 : ℕ) : ℝ) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsumR hε
    calc
      _ ≤ |M (n/k)| + |M Y| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (M (n/k)) (-(M Y))
      _ ≤ ε * ((n/k : ℕ) : ℝ) + ε * (Y : ℝ) := add_le_add (hM _ hYk) (hM Y le_rfl)
      _ ≤ _ := by nlinarith
  have htail : |T| ≤ ε * (K : ℝ) * ((K : ℝ)+1) * ((Y+1 : ℕ) : ℝ) := by
    calc
      |T| ≤ ∑ k ∈ Finset.Icc 1 q, |M (n/k)-M Y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 q,
          ε * ((K : ℝ)+1) * ((Y+1 : ℕ) : ℝ) := Finset.sum_le_sum hterm
      _ = (q : ℝ) * (ε * ((K : ℝ)+1) * ((Y+1 : ℕ) : ℝ)) := by simp [Nat.card_Icc]
      _ ≤ (K : ℝ) * (ε * ((K : ℝ)+1) * ((Y+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hqR (by positivity)
      _ = _ := by ring
  have hcorr : |((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y * (q : ℝ)| ≤
      ε * (K : ℝ) * ((Y+1 : ℕ) : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (Y+1)),
      (show |(q : ℝ)| = (q : ℝ) from abs_of_nonneg (Nat.cast_nonneg q))]
    have hh := mul_le_mul hm hqR (Nat.cast_nonneg q) hε
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (Y+1) : (0 : ℝ) ≤ _)
    nlinarith
  have hrep : canonicalMobiusHead Y n =
      1 - T - ((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y * (q : ℝ) := by
    have hi := finite_mobius_floor_tail_identity Y n (by omega) hYn.le
    rw [canonicalMobiusHead_floor_expansion]
    change 1 - (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) * ((n/d : ℕ) : ℝ)) = T at hi
    change (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) * ((n/d : ℕ) : ℝ)) -
        ((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y * (q : ℝ) = _
    linarith
  have hone : |1 - T| ≤ 1 + |T| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_one] using abs_add_le (1 : ℝ) (-T)
  rw [hrep]
  calc
    _ ≤ |1-T| + |((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y * (q : ℝ)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (1-T) (-(((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y * (q : ℝ)))
    _ ≤ (1 + ε * (K : ℝ) * ((K : ℝ)+1) * ((Y+1 : ℕ) : ℝ)) +
        ε * (K : ℝ) * ((Y+1 : ℕ) : ℝ) :=
      add_le_add (hone.trans (add_le_add le_rfl htail)) hcorr
    _ = _ := by ring

/-- The two explicit PNT cancellation inputs give a uniformly sublinear fixed window. -/
theorem canonicalMobiusHead_windows_of_mobius_cancellation
    (hM : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) / (N : ℝ))
      atTop (𝓝 0))
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0))
    (K : ℕ) (hK : 2 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ j, N < j → j ≤ K * N →
      |canonicalMobiusHead N j| ≤ ε * (N : ℝ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  let a : ℝ := ε / (4 * (K : ℝ) * ((K : ℝ) + 2))
  have ha : 0 < a := by dsimp [a]; positivity
  have haeq : 2 * a * (K : ℝ) * ((K : ℝ) + 2) = ε / 2 := by
    dsimp [a]
    field_simp
    ring
  have hMsmall : ∀ᶠ t : ℕ in atTop,
      |(∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)) / (t : ℝ)| < a := by
    simpa only [abs_zero] using hM.abs.eventually (gt_mem_nhds (by simpa only [abs_zero] using ha))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hMsmall
  have hmsmall : ∀ᶠ N in atTop, |mobiusReciprocalSum N| < a := by
    simpa only [abs_zero] using hm.abs.eventually (gt_mem_nhds (by simpa only [abs_zero] using ha))
  have hinv : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) < ε / 2 :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1, hmsmall, hinv]
    with N hN₀N hN1 hmN hiN
  intro j hNj hjK
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlocal : ∀ t : ℕ, N ≤ t →
      |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ a * (t : ℝ) := by
    intro t hNt
    have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    have h := hN₀ t (hN₀N.trans hNt)
    rw [abs_div, (show |(t : ℝ)| = (t : ℝ) from abs_of_nonneg (Nat.cast_nonneg t))] at h
    exact ((div_lt_iff₀ htR).1 h).le
  have hb := canonicalMobiusHead_window_bound N j K a ha.le hNj
    (hjK.trans (by nlinarith : K * N ≤ K * (N + 1))) hlocal hmN.le
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by push_cast; linarith
  have hcoef : 0 ≤ a * (K : ℝ) * ((K : ℝ) + 2) := by positivity
  have hb' := mul_le_mul_of_nonneg_left hNp hcoef
  have hi : 1 < (ε / 2) * (N : ℝ) := (div_lt_iff₀ hNR).1 hiN
  have heq : a * (K : ℝ) * ((K : ℝ) + 2) * (2 * (N : ℝ)) =
      (ε / 2) * (N : ℝ) := by nlinarith [haeq]
  calc
    _ ≤ 1 + a * (K : ℝ) * ((K : ℝ) + 2) * ((N + 1 : ℕ) : ℝ) := hb
    _ ≤ 1 + a * (K : ℝ) * ((K : ℝ) + 2) * (2 * (N : ℝ)) := by linarith
    _ ≤ ε * (N : ℝ) := by rw [heq]; linarith

end RiemannResearch.RH.Pareto
