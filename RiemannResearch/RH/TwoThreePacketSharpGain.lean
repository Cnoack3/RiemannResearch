/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResonanceLeadingGram
import RiemannResearch.RH.CrossResonanceCovarianceBounds
import RiemannResearch.RH.OldNewCovarianceBounds
import RiemannResearch.RH.SameScaleCovarianceBounds
import RiemannResearch.RH.TwoThreePacketLogGain
import Mathlib.Tactic.FinCases

/-!
# The sharp logarithmic cell gain in the ordinary two-seed budget

Source: Christian Noack's resonance-cell continuation, 15 September 2026.
Every entry of the actual seven-column Gram matrix is bounded here using the
full signed digit covariance and its exact packet transfer. The resulting
coefficient `7/3` has no remaining covariance hypothesis. The source is still
the actual projection residual; no source lower bound or RH conclusion is
asserted.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket

open RiemannResearch.Analysis
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ResonanceCellRefit
open RiemannResearch.Analysis.ResonanceLeadingGram
open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
open AdjacentDigit

noncomputable section

/-- A single uniform bound for every entry of the raw seven-column Gram matrix. -/
def packetGramConstant : ℝ := twoSeedCovarianceError+2000

/-- The explicit scale-independent constant in the sharp logarithmic bound. -/
def packetSharpConstant : ℝ := (21:ℝ)/2*packetGramConstant+7/3

theorem packetGramConstant_pos : 0 < packetGramConstant := by
  unfold packetGramConstant twoSeedCovarianceError twoSeedPacketLinear
    twoSeedPacketError twoSeedEnergy
  positivity

theorem packetSharpConstant_pos : 0 < packetSharpConstant := by
  unfold packetSharpConstant
  linarith [packetGramConstant_pos]

private theorem actual_entry_of_scaled (p q m n k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hn : 0 < n)
    (hps : p=2 ∨ p=3) (hqs : q=2 ∨ q=3) (hk : 0 < k)
    (hkm : k ≤ m) (hkn : k ≤ n) (hmhi : m ≤ 5*k) (hnhi : n ≤ 5*k)
    (c : ℝ)
    (hs : |(m:ℝ)*(n:ℝ)*crossCovariance p q m n-(harmonic k:ℝ)*c| ≤ 500) :
    |inner ℝ (packet p m hp hm) (packet q n hq hn)-(harmonic k:ℝ)*c| ≤
      packetGramConstant := by
  have ht := packet_cross_covariance_transfer p q m n k hp hq hm hn
    hps hqs hk hkm hkn hmhi hnhi
  have ha := abs_add_le
    (inner ℝ (packet p m hp hm) (packet q n hq hn)-
      (m:ℝ)*(n:ℝ)*crossCovariance p q m n)
    ((m:ℝ)*(n:ℝ)*crossCovariance p q m n-(harmonic k:ℝ)*c)
  simp only [sub_add_sub_cancel] at ha
  unfold packetGramConstant
  linarith

private theorem actual_cross_entry (k r s : ℕ) (hk : 24 ≤ k)
    (hr : r ≤ 2) (hs : s ≤ 1) :
    |inner ℝ (packet 2 (3*k+r) (by omega) (by omega))
      (packet 3 (2*k+s) (by omega) (by omega))-
        (harmonic k:ℝ)*crossLeading r s| ≤ packetGramConstant := by
  apply actual_entry_of_scaled 2 3 (3*k+r) (2*k+s) k
    (by omega) (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr rfl)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  simpa only [mul_comm (crossLeading r s) (harmonic k:ℝ)] using
    cross_cell_harmonic_bound k r s hk hr hs

private theorem actual_old_binary_entry (k r : ℕ) (hk : 24 ≤ k) (hr : r < 3) :
    |inner ℝ (packet 2 (3*k+r) (by omega) (by omega))
      (packet 2 k (by omega) (by omega))-(harmonic k:ℝ)*(1/3:ℝ)| ≤
      packetGramConstant := by
  apply actual_entry_of_scaled 2 2 (3*k+r) k k
    (by omega) (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inl rfl)
    (by omega) (by omega) le_rfl (by omega) (by omega)
  simpa only [mul_comm (1/3:ℝ) (harmonic k:ℝ)] using
    old_new_binary_covariance_bound k r hk hr

private theorem actual_old_ternary_entry (k r : ℕ) (hk : 24 ≤ k) (hr : r < 2) :
    |inner ℝ (packet 3 (2*k+r) (by omega) (by omega))
      (packet 3 k (by omega) (by omega))-(harmonic k:ℝ)| ≤
      packetGramConstant := by
  have h := actual_entry_of_scaled 3 3 (2*k+r) k k
    (by omega) (by omega) (by omega) (by omega) (Or.inr rfl) (Or.inr rfl)
    (by omega) (by omega) le_rfl (by omega) (by omega) 1
    (by simpa only [mul_one] using old_new_ternary_covariance_bound k r hk hr)
  simpa only [mul_one] using h

private theorem actual_binary_old_ternary_entry (k r : ℕ) (hk : 24 ≤ k) (hr : r < 3) :
    |inner ℝ (packet 2 (3*k+r) (by omega) (by omega))
      (packet 3 k (by omega) (by omega))| ≤ packetGramConstant := by
  have h := actual_entry_of_scaled 2 3 (3*k+r) k k
    (by omega) (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr rfl)
    (by omega) (by omega) le_rfl (by omega) (by omega) 0
    (by simpa only [mul_zero, sub_zero] using old_new_binary_ternary_covariance_bound k r hk hr)
  simpa only [mul_zero, sub_zero] using h

private theorem actual_ternary_old_binary_entry (k r : ℕ) (hk : 24 ≤ k) (hr : r < 2) :
    |inner ℝ (packet 3 (2*k+r) (by omega) (by omega))
      (packet 2 k (by omega) (by omega))| ≤ packetGramConstant := by
  have h := actual_entry_of_scaled 3 2 (2*k+r) k k
    (by omega) (by omega) (by omega) (by omega) (Or.inr rfl) (Or.inl rfl)
    (by omega) (by omega) le_rfl (by omega) (by omega) 0
    (by simpa only [mul_zero, sub_zero] using old_new_ternary_binary_covariance_bound k r hk hr)
  simpa only [mul_zero, sub_zero] using h

/-- The actual seven Hilbert columns to which the arithmetic bounds apply. -/
def packetRawColumns (k : ℕ) (hk : 0 < k) : Fin 7 → ThresholdHilbert :=
  rawColumns (packetColumns k hk)
    (packet 2 k (by omega) hk) (packet 3 k (by omega) hk)

/-- Every raw signed Gram entry has its required leading harmonic coefficient. -/
theorem packet_raw_gram_bound (k : ℕ) (hk : 24 ≤ k) (i j : Fin 7) :
    |inner ℝ (packetRawColumns k (by omega) i) (packetRawColumns k (by omega) j)-
      (harmonic k:ℝ)*leadingGram i j| ≤ packetGramConstant := by
  have hdiag2 (m : ℕ) (hkm : k ≤ m) (hmhi : m ≤ 5*k) :
      |‖packet 2 m (by omega) (by omega)‖^2-(harmonic k:ℝ)| ≤ packetGramConstant := by
    have h := packet_diagonal_harmonic_bound 2 m k
      (by omega) (Or.inl rfl) (by omega) hkm hmhi
    norm_num [packetGramConstant] at h ⊢
    exact h
  have hdiag3 (m : ℕ) (hkm : k ≤ m) (hmhi : m ≤ 5*k) :
      |‖packet 3 m (by omega) (by omega)‖^2-(harmonic k:ℝ)*2| ≤ packetGramConstant := by
    have h := packet_diagonal_harmonic_bound 3 m k
      (by omega) (Or.inr rfl) (by omega) hkm hmhi
    norm_num [packetGramConstant] at h ⊢
    simpa only [mul_comm (2:ℝ) (harmonic k:ℝ)] using h
  have hb (r s : ℕ) (hr : r ≤ 2) (hs : s ≤ 2) (hrs : r ≠ s) :
      |inner ℝ (packet 2 (3*k+r) (by omega) (by omega))
        (packet 2 (3*k+s) (by omega) (by omega))| ≤ packetGramConstant := by
    have h := same_scale_packet_covariance_bound 2 2 3 k r s
      (by omega) (by omega) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) hk hr hs hrs
    unfold packetGramConstant
    linarith
  have ht : |inner ℝ (packet 3 (2*k) (by omega) (by omega))
      (packet 3 (2*k+1) (by omega) (by omega))| ≤ packetGramConstant := by
    have h := same_scale_packet_covariance_bound 3 3 2 k 0 1
      (by omega) (by omega) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) hk
      (by omega) (by omega) (by omega)
    simp only [add_zero] at h
    unfold packetGramConstant
    linarith
  have h00 := hdiag2 (3*k) (by omega) (by omega)
  have h11 := hdiag2 (3*k+1) (by omega) (by omega)
  have h22 := hdiag2 (3*k+2) (by omega) (by omega)
  have h33 := hdiag3 (2*k) (by omega) (by omega)
  have h44 := hdiag3 (2*k+1) (by omega) (by omega)
  have h55 := hdiag2 k le_rfl (by omega)
  have h66 := hdiag3 k le_rfl (by omega)
  have h01 := hb 0 1 (by omega) (by omega) (by omega)
  have h02 := hb 0 2 (by omega) (by omega) (by omega)
  have h12 := hb 1 2 (by omega) (by omega) (by omega)
  have h03 := actual_cross_entry k 0 0 hk (by omega) (by omega)
  have h04 := actual_cross_entry k 0 1 hk (by omega) (by omega)
  have h13 := actual_cross_entry k 1 0 hk (by omega) (by omega)
  have h14 := actual_cross_entry k 1 1 hk (by omega) (by omega)
  have h23 := actual_cross_entry k 2 0 hk (by omega) (by omega)
  have h24 := actual_cross_entry k 2 1 hk (by omega) (by omega)
  have h05 := actual_old_binary_entry k 0 hk (by omega)
  have h15 := actual_old_binary_entry k 1 hk (by omega)
  have h25 := actual_old_binary_entry k 2 hk (by omega)
  have h06 := actual_binary_old_ternary_entry k 0 hk (by omega)
  have h16 := actual_binary_old_ternary_entry k 1 hk (by omega)
  have h26 := actual_binary_old_ternary_entry k 2 hk (by omega)
  have h35 := actual_ternary_old_binary_entry k 0 hk (by omega)
  have h45 := actual_ternary_old_binary_entry k 1 hk (by omega)
  have h36 := actual_old_ternary_entry k 0 hk (by omega)
  have h46 := actual_old_ternary_entry k 1 hk (by omega)
  have h56 : |inner ℝ (packet 2 k (by omega) (by omega))
      (packet 3 k (by omega) (by omega))| ≤ packetGramConstant := by
    have h := old_mixed_packet_covariance_bound k (by omega)
    unfold packetGramConstant
    linarith
  norm_num only [add_zero, crossLeading, if_true, if_false, zero_mul, mul_zero,
    mul_one, sub_zero] at h01 h02 h03 h04 h13 h14 h23 h24 h05 h15 h25 h06 h16 h26 h35 h45 h36 h46
  have hupper (a b : Fin 7) (hab : a ≤ b) :
      |inner ℝ (packetRawColumns k (by omega) a) (packetRawColumns k (by omega) b)-
        (harmonic k:ℝ)*leadingGram a b| ≤ packetGramConstant := by
    fin_cases a <;> fin_cases b
    all_goals try (norm_num [Fin.le_def] at hab)
    all_goals norm_num [packetRawColumns, rawColumns, packetColumns, leadingGram,
      real_inner_self_eq_norm_sq]
    all_goals assumption
  by_cases hij : i ≤ j
  · exact hupper i j hij
  · have hsym : leadingGram i j = leadingGram j i := by
      fin_cases i <;> fin_cases j <;> norm_num [leadingGram]
    have hi : inner ℝ (packetRawColumns k (by omega) i) (packetRawColumns k (by omega) j) =
        inner ℝ (packetRawColumns k (by omega) j) (packetRawColumns k (by omega) i) :=
      real_inner_comm _ _
    rw [hi, hsym]
    exact hupper j i (le_of_lt (lt_of_not_ge hij))

/-- The actual fully screened synthesis has the sharp leading energy bound. -/
theorem packet_screened_harmonic_bound (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (k : ℕ) (hk : 24 ≤ k)
    (h2 : packet 2 k (by omega) (by omega) ∈ P)
    (h3 : packet 3 k (by omega) (by omega) ∈ P) (a : CellVector) :
    ‖residual P (synthesis (packetColumns k (by omega)) a)‖^2 ≤
      (harmonic k:ℝ)*energy a+(21:ℝ)/2*packetGramConstant*sizeSq a := by
  exact screened_synthesis_leading_bound P (packetColumns k (by omega))
    (packet 2 k (by omega) (by omega)) (packet 3 k (by omega) (by omega))
    h2 h3 (le_of_lt packetGramConstant_pos) (packet_raw_gram_bound k hk) a

/-- The arithmetic harmonic bound yields the exact printed logarithmic coefficient. -/
theorem packet_screened_sharp_log_bound (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (k : ℕ) (hk : 24 ≤ k)
    (h2 : packet 2 k (by omega) (by omega) ∈ P)
    (h3 : packet 3 k (by omega) (by omega) ∈ P) (a : CellVector) :
    ‖residual P (synthesis (packetColumns k (by omega)) a)‖^2 ≤
      Real.log (k:ℝ)*energy a+packetSharpConstant*sizeSq a := by
  have hh := harmonic_le_one_add_log k
  have hm := mul_le_mul_of_nonneg_right hh (energy_nonneg a)
  have hs := packet_screened_harmonic_bound P k hk h2 h3 a
  have he := energy_le a
  unfold packetSharpConstant
  nlinarith

/-- All covariance providers discharged: actual cell gain with harmonic denominator. -/
theorem packet_cell_sharp_harmonic_gain (P W : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPW : P ≤ W) (k : ℕ) (hk : 24 ≤ k)
    (h2 : packet 2 k (by omega) (by omega) ∈ P)
    (h3 : packet 3 k (by omega) (by omega) ∈ P)
    (hu : ColumnsIn W (packetColumns k (by omega))) :
    sizeSq (cellSource (residual P hilbertOne) k (by omega)) /
        ((7:ℝ)/3*(harmonic k:ℝ)+(21:ℝ)/2*packetGramConstant) ≤
      ‖residual P hilbertOne‖^2-‖residual W hilbertOne‖^2 := by
  have hC : 0 < (7:ℝ)/3*(harmonic k:ℝ)+(21:ℝ)/2*packetGramConstant := by
    nlinarith [harmonic_nonnegative k, packetGramConstant_pos]
  change sizeSq (source P hilbertOne (packetColumns k (by omega))) /
    ((7:ℝ)/3*(harmonic k:ℝ)+(21:ℝ)/2*packetGramConstant) ≤
      ‖residual P hilbertOne‖^2-‖residual W hilbertOne‖^2
  exact enlarged_gain_of_raw_gram P W hPW hilbertOne (packetColumns k (by omega)) hu
      (packetColumns_source_compatible P k (by omega) h2 h3)
      (packet 2 k (by omega) (by omega)) (packet 3 k (by omega) (by omega))
      h2 h3 (harmonic_nonnegative k) (le_of_lt packetGramConstant_pos) hC
      (packet_raw_gram_bound k hk)

/-- The sharp logarithmic gain now has only genuine space-membership assumptions. -/
theorem packet_cell_sharp_log_gain (P W : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPW : P ≤ W) (k : ℕ) (hk : 24 ≤ k)
    (h2 : packet 2 k (by omega) (by omega) ∈ P)
    (h3 : packet 3 k (by omega) (by omega) ∈ P)
    (hu : ColumnsIn W (packetColumns k (by omega))) :
    sizeSq (cellSource (residual P hilbertOne) k (by omega)) /
        ((7:ℝ)/3*Real.log (k:ℝ)+packetSharpConstant) ≤
      ‖residual P hilbertOne‖^2-‖residual W hilbertOne‖^2 := by
  have hlog : 0 ≤ Real.log (k:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hC : 0 < (7:ℝ)/3*Real.log (k:ℝ)+packetSharpConstant := by
    linarith [packetSharpConstant_pos]
  apply packet_cell_log_gain_lower P W hPW k (by omega) h2 h3 hu hC
  intro a ha
  exact packet_screened_sharp_log_bound P k hk h2 h3 a

/-- The four actual compatible source charges retain their exact leading optimum.
Only the already proved bounded covariance error is absorbed into the denominator. -/
theorem packet_cell_four_charge_harmonic_gain (P W : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPW : P ≤ W) (k : ℕ) (hk : 24 ≤ k)
    (h2 : packet 2 k (by omega) (by omega) ∈ P)
    (h3 : packet 3 k (by omega) (by omega) ∈ P)
    (hu : ColumnsIn W (packetColumns k (by omega))) :
    sourceEnergy (cellSource (residual P hilbertOne) k (by omega)) /
        ((harmonic k:ℝ)+(63:ℝ)/4*packetGramConstant) ≤
      ‖residual P hilbertOne‖^2-‖residual W hilbertOne‖^2 := by
  have hL : 0 < (harmonic k:ℝ)+(63:ℝ)/4*packetGramConstant := by
    nlinarith [harmonic_nonnegative k, packetGramConstant_pos]
  change sourceEnergy (source P hilbertOne (packetColumns k (by omega))) /
    ((harmonic k:ℝ)+(63:ℝ)/4*packetGramConstant) ≤
      ‖residual P hilbertOne‖^2-‖residual W hilbertOne‖^2
  apply enlarged_gain_four_charges P W hPW hilbertOne (packetColumns k (by omega)) hu
    (packetColumns_source_compatible P k (by omega) h2 h3) hL
  intro a ha
  have hs := packet_screened_harmonic_bound P k hk h2 h3 a
  have hc := mul_le_mul_of_nonneg_left (compatible_coercivity a ha)
    (show 0 ≤ (63:ℝ)/4*packetGramConstant by
      exact mul_nonneg (by norm_num) (le_of_lt packetGramConstant_pos))
  nlinarith

end
end RiemannResearch.RH.Pareto.AdjacentPacket

namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
open AdjacentPacket RamanujanLaguerre
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ResonanceCellRefit
open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
noncomputable section

/-- The sharp `7/3` logarithmic gain in the original ordinary-dilation problem. -/
theorem ordinary_budget_sharp_log_gain (M k : ℕ) (hk : 24 ≤ k)
    (hcell : 3*k+3 ≤ 2*M) :
    sizeSq (cellSource (residual (budgetHilbert M) hilbertOne) k (by omega)) /
        ((7:ℝ)/3*Real.log (k:ℝ)+packetSharpConstant) ≤
      ‖residual (budgetHilbert M) hilbertOne‖^2-
        ‖residual (budgetHilbert (2*M)) hilbertOne‖^2 := by
  have hk0 : 0 < k := by omega
  have hkM : k+1 ≤ M := by omega
  obtain ⟨h2, h3⟩ := old_cell_packets_mem M k hk0 hkM
  exact packet_cell_sharp_log_gain (budgetHilbert M) (budgetHilbert (2*M))
    (budgetHilbert_mono (by omega)) k hk h2 h3
    (packetColumns_mem_doubled_budget M k hk0 hcell)

/-- The four-charge bound also applies to the original ordinary finite budgets. -/
theorem ordinary_budget_four_charge_gain (M k : ℕ) (hk : 24 ≤ k)
    (hcell : 3*k+3 ≤ 2*M) :
    sourceEnergy (cellSource (residual (budgetHilbert M) hilbertOne) k (by omega)) /
        ((harmonic k:ℝ)+(63:ℝ)/4*packetGramConstant) ≤
      ‖residual (budgetHilbert M) hilbertOne‖^2-
        ‖residual (budgetHilbert (2*M)) hilbertOne‖^2 := by
  have hk0 : 0 < k := by omega
  have hkM : k+1 ≤ M := by omega
  obtain ⟨h2, h3⟩ := old_cell_packets_mem M k hk0 hkM
  exact packet_cell_four_charge_harmonic_gain (budgetHilbert M) (budgetHilbert (2*M))
    (budgetHilbert_mono (by omega)) k hk h2 h3
    (packetColumns_mem_doubled_budget M k hk0 hcell)

end
end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
