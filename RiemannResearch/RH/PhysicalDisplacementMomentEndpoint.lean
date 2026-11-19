/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.ZeroFreeMertensDisplacement
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Critical physical displacement moments

Truncating a summable weighted moment upgrades the existing prefix bound
to little-o at its precise exponent. This discharges the critical-prefix
condition if an actual Mertens bound is available at its stated exponent.
The strict-exponent Gerhold transfer is discussed in the companion module.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QAnnihilatorTailEscape QSquarefreeResidualTail ZetaTwoOptimizerStage

private theorem hasSum_prefix (f : ℕ → ℝ) (M : ℕ) :
    HasSum (fun n : ℕ => if n < M then f n else 0) (∑ n ∈ Finset.range M, f n) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    apply (ih.add (hasSum_ite_eq M (f M))).congr_fun
    intro n
    by_cases hm : n < M
    · simp [hm, show n < M+1 by omega, show n ≠ M by omega]
    · by_cases he : n = M
      · subst n
        simp
      · simp [hm,he, show ¬ n < M+1 by omega]

/-- A finite weighted p-moment makes the absolute prefix little-o of the
critical power, for every real p at least one. -/
theorem critical_prefix_of_weighted_moment (d : ℕ → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hm : Summable fun n : ℕ => |d n| ^ p / ((n : ℝ) + 1) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∑ n ∈ Finset.range k, |d n| ≤ ε * (k : ℝ) ^ (1 + 1/p) := by
  let f (n : ℕ) := |d n| ^ p / ((n : ℝ) + 1) ^ 2
  let b := ε / 3
  have hb : 0 < b := by dsimp [b]; positivity
  have hbp := Real.rpow_pos_of_pos hb p
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hmf : Summable f := hm
  have hlim : Tendsto (fun k : ℕ => (∑' n, f n) - ∑ n ∈ Finset.range k, f n)
      atTop (𝓝 0) := by simpa using (tendsto_const_nhds (x := ∑' n, f n)).sub hmf.hasSum.tendsto_sum_nat
  obtain ⟨M,hM⟩ := eventually_atTop.1 (hlim.eventually_lt_const hbp)
  let t (n : ℕ) := if n < M then 0 else d n / b
  have ht : HasSum (fun n : ℕ => |t n|^p / ((n : ℝ)+1)^2)
      (((∑' n, f n) - ∑ n ∈ Finset.range M, f n) / b^p) := by
    apply ((hm.hasSum.sub (hasSum_prefix f M)).div_const (b^p)).congr_fun
    intro n
    by_cases hn : n < M
    · simp [t, hn, f, Real.zero_rpow hp0.ne']
    · simp [t, hn, f, abs_div, abs_of_pos hb, Real.div_rpow (abs_nonneg _) hb.le]
      <;> ring
  have htail : (∑' n : ℕ, |t n|^p / ((n : ℝ)+1)^2) ≤ 1 := by
    rw [ht.tsum_eq]
    exact (div_le_one hbp).mpr (hM M le_rfl).le
  let A := ∑ n ∈ Finset.range M, |d n|
  have hpow : Tendsto (fun k : ℕ => (k:ℝ)^(1+1/p)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1+1/p)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop M, eventually_gt_atTop (0:ℕ),
    hpow.eventually (eventually_ge_atTop (A/b))] with k hk hk0 hh
  have hhead : (∑ n ∈ Finset.range k, if n < M then |d n| else 0) = A := by
    calc
      _ = ∑ n ∈ Finset.range M, if n < M then |d n| else 0 :=
        (Finset.sum_subset (Finset.range_mono hk) (fun n _ h => by simp [show ¬ n < M from fun hn => h (Finset.mem_range.mpr hn)])).symm
      _ = A := Finset.sum_congr rfl fun n hn => by simp [Finset.mem_range.mp hn]
  have he (n : ℕ) : |d n| = (if n < M then |d n| else 0) + b*|t n| := by
    by_cases hn : n < M
    · simp [t,hn]
    · simp [t,hn,abs_div,abs_of_pos hb]; field_simp
  have hP := prefix_of_quadratically_weighted_moment t hp ht.summable k hk0
  have hk' := Real.rpow_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (1+1/p)
  calc
    _ = ∑ n ∈ Finset.range k, ((if n < M then |d n| else 0) + b*|t n|) :=
      Finset.sum_congr rfl fun n _ => he n
    _ = A + b * ∑ n ∈ Finset.range k, |t n| := by
      rw [Finset.sum_add_distrib, hhead, Finset.mul_sum]
    _ ≤ b * (k:ℝ)^(1+1/p) + b * (2 * (k:ℝ)^(1+1/p)) := by
      apply add_le_add
      · simpa only [mul_comm] using (div_le_iff₀ hb).mp hh
      · exact mul_le_mul_of_nonneg_left (hP.trans (mul_le_mul_of_nonneg_right (by linarith only [htail]) hk')) hb.le
    _ = _ := by dsimp [b]; ring

/-- The exact critical physical moment suffices if the Mertens exponent is
attained. Gerhold's source alone supplies only exponents strictly to the
right of the zero-free boundary. -/
theorem riemannHypothesis_of_mertens_power_and_critical_moment
    {s C p : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n → |M (n : ℝ)| ≤ C*(n : ℝ)^s)
    (hp : 1 ≤ p) (heq : 1/p = (1-s)/(2-s)) (hd : PhysicalDisplacementMoment p) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertens_power_and_critical_prefix s C hs hs1 hC hM
  intro ε hε
  rw [← heq]
  exact critical_prefix_of_weighted_moment (fun n => qSequence displacement (n+1)) hp hd hε

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
