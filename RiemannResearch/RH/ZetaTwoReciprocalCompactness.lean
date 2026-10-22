import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Compact weak-to-strong behavior of the actual reciprocal diagonal

Source: the user-provided exact optimizer cancellation manuscript, for the
reciprocal multiplier. The proof is the standard finite-head/full-tail
argument for a diagonal whose entries tend to zero. Its full coordinate tail
and its exact cutoff bound are retained before passing to the limit.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoHilbert

def qPointSequence (n k : ℕ) : ℝ := if k = n+1 then 1 else 0

private theorem qPoint_square_summable (n : ℕ) :
    Summable (fun k => positiveQWeight k*(qPointSequence n k)^2) :=
  boundedQ_square_summable _ 1 zero_le_one (by
    intro k
    by_cases hk : k = n+1 <;> simp [qPointSequence, hk])

def qPoint (n : ℕ) : QHilbert := encodeQ (qPointSequence n) (qPoint_square_summable n)

@[simp] theorem qSequence_qPoint (n : ℕ) : qSequence (qPoint n) = qPointSequence n :=
  qSequence_encodeQ _ _ (by simp [qPointSequence])

theorem qPoint_inner (n : ℕ) (f : QHilbert) :
    inner ℝ (qPoint n) f = qWeight n*qSequence f (n+1) := by
  rw [qInner_weighted, qSequence_qPoint]
  simp only [qPointSequence, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [qWeight]

/-- Weak convergence against every actual Hilbert vector implies convergence
of each literal ℓ² coordinate. -/
theorem qCoordinate_tendsto_zero_of_weak (u : ℕ → QHilbert)
    (hweak : ∀ y : QHilbert,
      Tendsto (fun j => inner ℝ y (u j)) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun j => u j n) atTop (𝓝 0) := by
  have hphys : Tendsto (fun j => qSequence (u j) (n+1)) atTop (𝓝 0) := by
    have h := (hweak (qPoint n)).div_const (qWeight n)
    simp only [qPoint_inner, zero_div] at h
    convert h using 1
    funext j
    field_simp [ne_of_gt (qWeight_pos n)]
  have h := hphys.mul_const (Real.sqrt (qWeight n))
  simp only [zero_mul] at h
  convert h using 1
  funext j
  rw [qSequence_succ]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))]

/-- Literal finite head and the full infinite tail, with an exact reciprocal
cutoff estimate. No coordinates after the cutoff are discarded. -/
theorem reciprocalD_head_tail_bound (f : QHilbert) (K : ℕ) :
    ‖reciprocalD f‖^2 ≤
      (∑ n ∈ Finset.range K, (reciprocalD f n)^2) + ‖f‖^2/((K:ℝ)+1)^2 := by
  have hsD := qCoordinate_square_summable (reciprocalD f)
  have hsF := qCoordinate_square_summable f
  have hsDtail := (summable_nat_add_iff K).mpr hsD
  have hsFtail := (summable_nat_add_iff K).mpr hsF
  have hrawtail : (∑' n : ℕ, (f (n+K))^2) ≤ ‖f‖^2 := by
    have he := hsF.sum_add_tsum_nat_add K
    rw [← qNorm_sq f] at he
    have hh : 0 ≤ ∑ n ∈ Finset.range K, (f n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  have htail : (∑' n : ℕ, (reciprocalD f (n+K))^2) ≤ ‖f‖^2/((K:ℝ)+1)^2 := by
    calc
      _ ≤ ∑' n : ℕ, (f (n+K))^2/((K:ℝ)+1)^2 := by
        apply Summable.tsum_le_tsum _ hsDtail (hsFtail.div_const _)
        intro n
        rw [reciprocalD_apply, div_pow]
        have hd : ((K:ℝ)+1)^2 ≤ (((n+K:ℕ):ℝ)+1)^2 := by
          push_cast
          nlinarith [Nat.cast_nonneg (α:=ℝ) n, Nat.cast_nonneg (α:=ℝ) K]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd
      _ = (∑' n : ℕ, (f (n+K))^2)/((K:ℝ)+1)^2 := by rw [tsum_div_const]
      _ ≤ _ := div_le_div_of_nonneg_right hrawtail (by positivity)
  have he := hsD.sum_add_tsum_nat_add K
  rw [← qNorm_sq (reciprocalD f)] at he
  linarith

private theorem reciprocal_cutoff_square_tendsto_zero (C : ℝ) :
    Tendsto (fun K : ℕ => C^2/((K:ℝ)+1)^2) atTop (𝓝 0) := by
  have h : Tendsto (fun K : ℕ => 1/((K:ℝ)+1)) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hh
  have hh := (h.pow 2).const_mul (C^2)
  simpa only [div_pow, one_pow, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    mul_one_div] using hh

/-- Actual reciprocal weak-to-strong convergence from any fixed norm bound.
In particular, it applies to unit-normalized residuals with C=1. -/
theorem reciprocalD_norm_tendsto_zero_of_weak (u : ℕ → QHilbert) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ j, ‖u j‖ ≤ C)
    (hweak : ∀ y : QHilbert,
      Tendsto (fun j => inner ℝ y (u j)) atTop (𝓝 0)) :
    Tendsto (fun j => ‖reciprocalD (u j)‖) atTop (𝓝 0) := by
  have hcoord := qCoordinate_tendsto_zero_of_weak u hweak
  have hhead (K : ℕ) : Tendsto
      (fun j => ∑ n ∈ Finset.range K, (reciprocalD (u j) n)^2) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.range K) (fun n _ =>
      ((hcoord n).div_const ((n:ℝ)+1)).pow 2)
    simpa only [reciprocalD_apply, zero_div, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero] using h
  have hsquare : Tendsto (fun j => ‖reciprocalD (u j)‖^2) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro x hx
      exact Filter.Eventually.of_forall (fun j => hx.trans_le (sq_nonneg _))
    · intro ε hε
      have hhalf : 0 < ε/2 := by linarith
      obtain ⟨K, hK⟩ := ((reciprocal_cutoff_square_tendsto_zero C).eventually
        (gt_mem_nhds hhalf)).exists
      filter_upwards [(hhead K).eventually (gt_mem_nhds hhalf)] with j hj
      have he := reciprocalD_head_tail_bound (u j) K
      have hb2 : ‖u j‖^2 ≤ C^2 := by
        simpa only [← pow_two] using mul_le_mul (hb j) (hb j) (norm_nonneg _) hC
      have hbquot : ‖u j‖^2/((K:ℝ)+1)^2 ≤ C^2/((K:ℝ)+1)^2 :=
        div_le_div_of_nonneg_right hb2 (by positivity)
      linarith
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end RiemannResearch.RH.ZetaTwoHilbert
