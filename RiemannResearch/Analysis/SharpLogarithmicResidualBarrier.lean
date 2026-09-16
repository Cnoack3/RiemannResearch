import RiemannResearch.Analysis.LogarithmicResidualBarrier
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Sharp logarithmic obstruction conditional on the distance envelope

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 7. The analytic comparison with the classical Nyman--Beurling
distance and Burnol's lower bound are NOT assumed established: the
positive distance envelope is an explicit hypothesis throughout.

The main conclusion is the quantified sharp liminf statement: for each
`a > 1`, every tail contains an index with `(j+1)*relativeGain d j < a`.
This contains the sharp constant without requiring any convention for
liminf of an unbounded sequence or division by a zero improvement.
-/
noncomputable section
namespace RiemannResearch.Analysis.LogarithmicResidualBarrier

theorem relativeGain_le_log_loss (d : ℕ → ℝ) (hd : ∀ j, 0 < d j) (j : ℕ) :
    relativeGain d j ≤ -Real.log (1-relativeGain d j) := by
  have hp : 0 < 1-relativeGain d j := by
    rw [one_sub_relativeGain d j (ne_of_gt (hd j))]
    exact div_pos (hd (j+1)) (hd j)
  have h := Real.log_le_sub_one_of_pos hp
  linarith

theorem log_successor_difference_le (x : ℝ) (hx : 0 < x) :
    Real.log (x+1)-Real.log x ≤ 1/x := by
  calc
    _ = Real.log ((x+1)/x) :=
      (Real.log_div (by positivity) (ne_of_gt hx)).symm
    _ ≤ (x+1)/x-1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 1/x := by field_simp; ring

theorem scaled_log_step_le_log_drop (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (j : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hgain : a/((j : ℝ)+1) ≤ relativeGain d j) :
    a*(Real.log ((j : ℝ)+2)-Real.log ((j : ℝ)+1)) ≤
      Real.log (d j)-Real.log (d (j+1)) := by
  calc
    _ ≤ a*(1/((j : ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_left _ ha
      simpa only [add_assoc, one_add_one_eq_two] using
        log_successor_difference_le ((j : ℝ)+1) (by positivity)
    _ = a/((j : ℝ)+1) := by ring
    _ ≤ relativeGain d j := hgain
    _ ≤ -Real.log (1-relativeGain d j) := relativeGain_le_log_loss d hd j
    _ = Real.log (d j)-Real.log (d (j+1)) := by
      rw [one_sub_relativeGain d j (ne_of_gt (hd j)),
        Real.log_div (ne_of_gt (hd (j+1))) (ne_of_gt (hd j))]
      ring

/-- Lower logarithmic growth obtained from a hypothesized eventual
gain at least `a/(j+1)`. This is a finite telescope. -/
theorem scaled_log_growth_le_log_drop (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (J N : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hgain : ∀ j, J ≤ j → a/((j : ℝ)+1) ≤ relativeGain d j) :
    a*(Real.log (((J+N : ℕ) : ℝ)+1)-Real.log ((J : ℝ)+1)) ≤
      Real.log (d J)-Real.log (d (J+N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep := scaled_log_step_le_log_drop d hd (J+N) a ha
      (hgain (J+N) (by omega))
    have hc : (((J+(N+1) : ℕ) : ℝ)+1) = (((J+N : ℕ) : ℝ)+2) := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    have hi : J+(N+1) = (J+N)+1 := by omega
    change a*(Real.log (((J+(N+1) : ℕ) : ℝ)+1)-Real.log ((J : ℝ)+1)) ≤ _
    rw [hc, hi]
    nlinarith

theorem log_drop_le_of_distance_lower {u v c x : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hc : 0 < c) (hx : 0 < x)
    (hlower : c/x ≤ v) :
    Real.log u-Real.log v ≤ Real.log (u/c)+Real.log x := by
  have hb : u/v ≤ (u/c)*x := by
    have hl := (div_le_iff₀ hx).mp hlower
    apply (div_le_iff₀ hv).mpr
    apply le_of_mul_le_mul_right ?_ hc
    calc
      u*c ≤ u*(v*x) := mul_le_mul_of_nonneg_left hl hu.le
      _ = ((u/c)*x*v)*c := by field_simp [ne_of_gt hc]
  calc
    _ = Real.log (u/v) := (Real.log_div (ne_of_gt hu) (ne_of_gt hv)).symm
    _ ≤ Real.log ((u/c)*x) := Real.log_le_log (div_pos hu hv) hb
    _ = _ := Real.log_mul (ne_of_gt (div_pos hu hc)) (ne_of_gt hx)

/-- The sharp asymptotic obstruction in quantified form. The domain
specific distance lower envelope is explicitly a hypothesis. Equivalently,
the liminf of `(j+1)*relativeGain d j` is at most one whenever that liminf
is interpreted in the extended real line. -/
theorem exists_late_scaled_gain_lt_of_distance_lower
    (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (c : ℝ) (hc : 0 < c) (N₀ : ℕ)
    (hlower : ∀ n, N₀ ≤ n → c/((n : ℝ)+1) ≤ d n)
    (a : ℝ) (ha : 1 < a) (J : ℕ) :
    ∃ j, J ≤ j ∧ ((j : ℝ)+1)*relativeGain d j < a := by
  by_contra hcontra
  have hgain : ∀ j, J ≤ j → a/((j : ℝ)+1) ≤ relativeGain d j := by
    intro j hj
    have hnot : ¬ ((j : ℝ)+1)*relativeGain d j < a := by
      intro hlt
      exact hcontra ⟨j, hj, hlt⟩
    apply (div_le_iff₀ (show 0 < (j : ℝ)+1 by positivity)).mpr
    nlinarith [le_of_not_gt hnot]
  let K : ℕ := max J N₀
  let B : ℝ :=
    (a*Real.log ((K : ℝ)+1)+Real.log (d K/c))/(a-1)
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (B+1))
  have hX : Real.exp (B+1) < (((K+N : ℕ) : ℝ)+1) := by
    simp only [Nat.cast_add] at *
    have hK : 0 ≤ (K : ℝ) := by positivity
    linarith
  have hlog : B+1 < Real.log (((K+N : ℕ) : ℝ)+1) := by
    calc
      _ = Real.log (Real.exp (B+1)) := (Real.log_exp _).symm
      _ < _ := Real.log_lt_log (Real.exp_pos _) hX
  have hg := scaled_log_growth_le_log_drop d hd K N a (by linarith)
    (fun j hj => hgain j (le_trans (le_max_left J N₀) hj))
  have hu := log_drop_le_of_distance_lower (hd K) (hd (K+N)) hc
    (show 0 < (((K+N : ℕ) : ℝ)+1) by positivity)
    (hlower (K+N) (by dsimp [K]; omega))
  have heq : B*(a-1) = a*Real.log ((K : ℝ)+1)+Real.log (d K/c) := by
    dsimp [B]
    exact div_mul_cancel₀ _ (by linarith)
  nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hlog)]

/-- Any eventual logarithmic reconstruction-cost upper bound has
constant at least `1 / log 2`, conditional on the stated distance
envelope. Positivity of each gain is explicit because zero gains have
infinite constrained reconstruction cost, not real-valued quotient zero. -/
theorem eventual_cost_constant_ge_inv_log_two
    (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (c : ℝ) (hc : 0 < c) (N₀ : ℕ)
    (hlower : ∀ n, N₀ ≤ n → c/((n : ℝ)+1) ≤ d n)
    (C : ℝ) (hC : 0 < C) (J : ℕ)
    (hcost : ∀ j, J ≤ j →
      0 < d j-d (j+1) ∧
      (d j)^2/(d j-d (j+1)) ≤
        C*d j*(((j : ℝ)+1)*Real.log 2)) :
    1/Real.log 2 ≤ C := by
  by_contra hcontra
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCL : 0 < C*Real.log 2 := mul_pos hC hlog
  have hlt : C*Real.log 2 < 1 :=
    (lt_div_iff₀ hlog).mp (lt_of_not_ge hcontra)
  have ha : 1 < 1/(C*Real.log 2) :=
    (lt_div_iff₀ hCL).mpr (by simpa using hlt)
  obtain ⟨j, hj, hsmall⟩ := exists_late_scaled_gain_lt_of_distance_lower
    d hd c hc N₀ hlower (1/(C*Real.log 2)) ha J
  obtain ⟨hgain, hupper⟩ := hcost j hj
  have hu := (div_le_iff₀ hgain).mp hupper
  have hcanc : d j ≤ C*((j : ℝ)+1)*Real.log 2*(d j-d (j+1)) := by
    apply le_of_mul_le_mul_left ?_ (hd j)
    convert hu using 1 <;> ring
  have hlarge : 1/(C*Real.log 2) ≤
      (((j : ℝ)+1)*(d j-d (j+1)))/d j := by
    apply (div_le_div_iff₀ hCL (hd j)).mpr
    simpa only [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hcanc
  have heq : (((j : ℝ)+1)*(d j-d (j+1)))/d j =
      ((j : ℝ)+1)*relativeGain d j := by
    unfold relativeGain
    ring
  rw [heq] at hlarge
  exact (not_lt_of_ge hlarge) hsmall

end RiemannResearch.Analysis.LogarithmicResidualBarrier
