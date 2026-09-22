import RiemannResearch.RH.CanonicalMobiusWindowCancellation

/-!
# Sublinear full Pareto energy of the canonical Möbius family

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`,
Section 3, for the head/window/far-tail argument.
The final theorem proves the full energy limit from two explicit Möbius
cancellation inputs. It neither supplies those PNT inputs nor asserts
vanishing approximation error.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- Head, middle window, and complete far tail, with no omitted coordinates. -/
theorem canonicalMobiusHilbert_cutoff_bound (N K : ℕ) (hN : 0 < N) (hK : 2 ≤ K)
    (a : ℝ) (hmid : ∀ j, N < j → j ≤ K * N →
      |canonicalMobiusHead N j| ≤ a * (N : ℝ)) :
    ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ) ≤
      1 / (N : ℝ) + a ^ 2 + 4 / (K : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  let L := K * N - N
  have hNL : N ≤ K * N := by nlinarith
  have hL : L + N = K * N := Nat.sub_add_cancel hNL
  have hidx (k : ℕ) : (k + L) + (N + 1) = k + (K * N + 1) := by omega
  have hs : Summable (fun j : ℕ => positiveWeight j * canonicalMobiusHead N j ^ 2) := by
    simpa only [canonicalMobiusHilbert_sequence] using
      hilbertSequence_square_summable (canonicalMobiusHilbert N)
  have ht := (summable_nat_add_iff (N + 1)).mpr hs
  have hw := (summable_nat_add_iff (N + 1)).mpr positiveWeight_summable
  have hweights : (∑ k ∈ Finset.range L, positiveWeight (k + (N + 1))) ≤
      1 / ((N : ℝ) + 1) := by
    calc
      _ ≤ ∑' k : ℕ, positiveWeight (k + (N + 1)) :=
        Summable.sum_le_tsum _ (fun k _ => positiveWeight_nonneg _) hw
      _ = _ := by rw [positiveWeight_tail_tsum (N + 1) (Nat.succ_pos _)]; norm_cast
  have hmiddle : (∑ k ∈ Finset.range L,
      positiveWeight (k + (N + 1)) * canonicalMobiusHead N (k + (N + 1)) ^ 2) ≤
      a ^ 2 * (N : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range L, positiveWeight (k + (N + 1)) * (a * (N : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
        have hk' := Finset.mem_range.mp hk
        have hh := mul_self_le_mul_self
          (abs_nonneg (canonicalMobiusHead N (k + (N + 1))))
          (hmid _ (by omega) (by omega))
        simpa only [← pow_two, sq_abs] using hh
      _ = (∑ k ∈ Finset.range L, positiveWeight (k + (N + 1))) *
          (a * (N : ℝ)) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (1 / ((N : ℝ) + 1)) * (a * (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hweights (sq_nonneg _)
      _ ≤ a ^ 2 * (N : ℝ) := by
        rw [one_div, mul_comm, ← div_eq_mul_inv]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).2
        nlinarith [sq_nonneg a]
  have hfar : (∑' k : ℕ, positiveWeight (k + (K * N + 1)) *
      canonicalMobiusHead N (k + (K * N + 1)) ^ 2) ≤ 4 * (N : ℝ) / (K : ℝ) := by
    have hf := (summable_nat_add_iff (K * N + 1)).mpr hs
    have hwf := (summable_nat_add_iff (K * N + 1)).mpr positiveWeight_summable
    calc
      _ ≤ ∑' k : ℕ, positiveWeight (k + (K * N + 1)) * (2 * (N : ℝ)) ^ 2 := by
        apply Summable.tsum_le_tsum _ hf (hwf.mul_right _)
        intro k
        apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
        have hh := mul_self_le_mul_self (abs_nonneg _)
          (canonicalMobiusHead_abs_le_two_mul N hN (k + (K * N + 1)))
        simpa only [← pow_two, sq_abs] using hh
      _ = (2 * (N : ℝ)) ^ 2 / ((K : ℝ) * (N : ℝ) + 1) := by
        rw [tsum_mul_right, positiveWeight_tail_tsum (K * N + 1) (Nat.succ_pos _)]
        push_cast
        ring
      _ ≤ (2 * (N : ℝ)) ^ 2 / ((K : ℝ) * (N : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hKR hNR) (by linarith)
      _ = _ := by field_simp; ring
  have htotal : ‖canonicalMobiusHilbert N‖ ^ 2 ≤
      1 + a ^ 2 * (N : ℝ) + 4 * (N : ℝ) / (K : ℝ) := by
    rw [canonicalMobiusHilbert_norm_sq_split, ← ht.sum_add_tsum_nat_add L]
    simp_rw [hidx]
    have hhead : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).2
      linarith
    linarith
  apply (div_le_iff₀ hNR).2
  calc
    _ ≤ 1 + a ^ 2 * (N : ℝ) + 4 * (N : ℝ) / (K : ℝ) := htotal
    _ = _ := by field_simp

/-- First fix the window multiplier, then let it grow after taking the cutoff limit. -/
theorem canonicalMobiusHilbert_sublinear_of_windows
    (hwindow : ∀ K : ℕ, 2 ≤ K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N in atTop, ∀ j, N < j → j ≤ K * N →
        |canonicalMobiusHead N j| ≤ ε * (N : ℝ)) :
    Tendsto (fun N => ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro x hx
    exact Eventually.of_forall (fun N =>
      lt_of_lt_of_le hx (div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)))
  · intro ε hε
    have hthird : 0 < ε / 3 := by linarith
    have hKlim : Tendsto (fun K : ℕ => 4 / (K : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
    obtain ⟨K, hK2, hKs⟩ := ((eventually_ge_atTop 2).and
      (hKlim.eventually (gt_mem_nhds hthird))).exists
    let a : ℝ := min 1 (ε / 6)
    have ha : 0 < a := lt_min zero_lt_one (by linarith)
    have ha1 : a ≤ 1 := min_le_left _ _
    have haε : a ≤ ε / 6 := min_le_right _ _
    have hasq : a ^ 2 < ε / 3 := by nlinarith
    have hinv := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hthird)
    filter_upwards [hwindow K hK2 a ha, hinv, eventually_gt_atTop 0] with N hm hn hN
    have he := canonicalMobiusHilbert_cutoff_bound N K hN hK2 a hm
    linarith

/-- The complete canonical energy is sublinear under the two stated PNT inputs. -/
theorem canonicalMobiusHilbert_sublinear_of_mobius_cancellation
    (hM : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) / (N : ℝ))
      atTop (𝓝 0))
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0)) :
    Tendsto (fun N => ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) :=
  canonicalMobiusHilbert_sublinear_of_windows
    (canonicalMobiusHead_windows_of_mobius_cancellation hM hm)

end RiemannResearch.RH.Pareto
