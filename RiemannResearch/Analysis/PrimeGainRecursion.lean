import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Aggregate prime and block gain budgets

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


These scalar lemmas do not assume a primewise source margin. A nonnegative lower
bound `q n` on the actual optimizer gain gives an inverse-energy budget. The
unboundedness provider is explicitly a hypothesis; no RH assertion is hidden
in the scalar algebra.

Signed-window consumers and exact actual-budget equivalences are added below.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeGainRecursion

/-- Exact reciprocal increment. -/
theorem inverse_energy_difference (E E' : ℝ) (hE : E ≠ 0) (hE' : E' ≠ 0) :
    1 / E' - 1 / E = (E - E') / (E * E') := by
  field_simp [hE, hE']

/-- A lower bound on the actual gain produces a normalized reciprocal gain. -/
theorem inverse_energy_step (E E' q : ℝ) (hE : 0 < E) (hE' : 0 < E')
    (hq : 0 ≤ q) (hstep : E' ≤ E - q) :
    q / E ^ 2 ≤ 1 / E' - 1 / E := by
  have hmon : E' ≤ E := by linarith
  have hqstep : q ≤ E - E' := by linarith
  have hmul : q * E' ≤ (E - E') * E := by
    calc
      q * E' ≤ q * E := mul_le_mul_of_nonneg_left hmon hq
      _ ≤ (E - E') * E := mul_le_mul_of_nonneg_right hqstep hE.le
  rw [inverse_energy_difference E E' (ne_of_gt hE) (ne_of_gt hE')]
  apply (div_le_div_iff₀ (sq_pos_of_pos hE) (mul_pos hE hE')).2
  have hscaled := mul_le_mul_of_nonneg_left hmul hE.le
  convert hscaled using 1 <;> ring

/-- The sharper normalized lower gain uses both adjacent errors. -/
theorem inverse_energy_step_sharp (E E' q : ℝ) (hE : 0 < E) (hE' : 0 < E')
    (hstep : E' ≤ E - q) :
    q / (E * E') ≤ 1 / E' - 1 / E := by
  rw [inverse_energy_difference E E' (ne_of_gt hE) (ne_of_gt hE')]
  apply div_le_div_of_nonneg_right
  · linarith
  · exact (mul_pos hE hE').le

/-- Exact finite telescope for the complete block gain. No gain sign is needed. -/
theorem inverse_energy_telescope (E : ℕ → ℝ) (hE : ∀ n, 0 < E n) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (E n - E (n + 1)) / (E n * E (n + 1))) = 1 / E N - 1 / E 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [← inverse_energy_difference (E N) (E (N + 1))
        (ne_of_gt (hE N)) (ne_of_gt (hE (N + 1)))]
      ring

/-- The entire normalized lower-gain sum controls the inverse error. -/
theorem reciprocal_gain_sum (E q : ℕ → ℝ) (hE : ∀ n, 0 < E n)
    (hq : ∀ n, 0 ≤ q n) (hstep : ∀ n, E (n + 1) ≤ E n - q n) (N : ℕ) :
    1 / E 0 + (∑ n ∈ Finset.range N, q n / (E n) ^ 2) ≤ 1 / E N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hincr := inverse_energy_step (E N) (E (N + 1)) (q N)
        (hE N) (hE (N + 1)) (hq N) (hstep N)
      linarith

/-- Sharper finite lower-gain telescope. For the actual gain this is equality. -/
theorem reciprocal_gain_sum_sharp (E q : ℕ → ℝ) (hE : ∀ n, 0 < E n)
    (hstep : ∀ n, E (n + 1) ≤ E n - q n) (N : ℕ) :
    1 / E 0 + (∑ n ∈ Finset.range N, q n / (E n * E (n + 1))) ≤ 1 / E N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hincr := inverse_energy_step_sharp (E N) (E (N + 1)) (q N)
        (hE N) (hE (N + 1)) (hstep N)
      linarith

/-- A finite quantitative error bound from all usable signed-source gains. -/
theorem energy_le_inverse_budget (E q : ℕ → ℝ) (hE : ∀ n, 0 < E n)
    (hq : ∀ n, 0 ≤ q n) (hstep : ∀ n, E (n + 1) ≤ E n - q n) (N : ℕ) :
    E N ≤ 1 / (1 / E 0 + ∑ n ∈ Finset.range N, q n / (E n) ^ 2) := by
  have hrec := reciprocal_gain_sum E q hE hq hstep N
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, q n / (E n) ^ 2 := by
    exact Finset.sum_nonneg (fun n _ => div_nonneg (hq n) (sq_nonneg (E n)))
  have hden : 0 < 1 / E 0 + ∑ n ∈ Finset.range N, q n / (E n) ^ 2 :=
    add_pos_of_pos_of_nonneg (div_pos zero_lt_one (hE 0)) hsum
  have hprod := (le_div_iff₀ (hE N)).mp hrec
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_comm] using hprod

/-- Gain lower bounds preserve monotonicity of the optimizer errors. -/
theorem energy_antitone (E q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hstep : ∀ n, E (n + 1) ≤ E n - q n) : Antitone E := by
  apply antitone_nat_of_succ_le
  intro n
  have hn := hstep n
  have hqn := hq n
  linarith

/-- Divergence of the aggregate normalized gain budget forces the error to zero.

The conclusion is the epsilon definition of convergence, avoiding any topology
imports. The provider may aggregate an arbitrary set of primes or block trials;
it requires no pointwise source margin and no reciprocal-prime subset.
-/
theorem eventual_small_of_unbounded_gain_budget (E q : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hq : ∀ n, 0 ≤ q n)
    (hstep : ∀ n, E (n + 1) ≤ E n - q n)
    (hbudget : ∀ M : ℝ, ∃ N : ℕ,
      M ≤ ∑ n ∈ Finset.range N, q n / (E n) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hbudget (1 / ε + 1)
  have hrec := reciprocal_gain_sum E q hE hq hstep N
  have hinitial : 0 < 1 / E 0 := div_pos zero_lt_one (hE 0)
  have hinv : 1 / ε < 1 / E N := by linarith
  have hsmall : E N < ε := by
    have hp := (div_lt_div_iff₀ hε (hE N)).mp hinv
    simpa only [one_mul] using hp
  refine ⟨N, ?_⟩
  intro n hn
  exact lt_of_le_of_lt ((energy_antitone E q hq hstep) hn) hsmall

/-- Aggregate source criterion with arbitrary nonnegative source weights.

Using the paper-level bound `‖g_p‖² ≤ 4 / (3p)`, a single prime innovation permits
`w n = p n * 3 / 4`. For a legal block
trial direction one can take `w n = 1 / (v_nᵀ S_n v_n)` and
`eta n = v_nᵀ η_n`, when that denominator is positive.
-/
theorem eventual_small_of_weighted_source_budget (E w eta : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hw : ∀ n, 0 ≤ w n)
    (hstep : ∀ n, E (n + 1) ≤ E n - w n * (eta n) ^ 2)
    (hbudget : ∀ M : ℝ, ∃ N : ℕ,
      M ≤ ∑ n ∈ Finset.range N, w n * (eta n) ^ 2 / (E n) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε := by
  exact eventual_small_of_unbounded_gain_budget E (fun n => w n * (eta n) ^ 2)
    hE (fun n => mul_nonneg (hw n) (sq_nonneg (eta n))) hstep hbudget

/-- Actual nested-space monotonicity removes the sign condition on a gain
certificate. Negative arithmetic contributions may be retained in a prefix sum. -/
theorem inverse_energy_step_signed (E E' q : ℝ) (hE : 0 < E) (hE' : 0 < E')
    (hmon : E' ≤ E) (hstep : E' ≤ E - q) :
    q / E ^ 2 ≤ 1 / E' - 1 / E := by
  by_cases hq : 0 ≤ q
  · exact inverse_energy_step E E' q hE hE' hq hstep
  · have hqneg : q ≤ 0 := (lt_of_not_ge hq).le
    have hleft : q / E ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hqneg (sq_nonneg E)
    have hright : 0 ≤ 1 / E' - 1 / E := by
      rw [inverse_energy_difference E E' (ne_of_gt hE) (ne_of_gt hE')]
      exact div_nonneg (sub_nonneg.mpr hmon) (mul_pos hE hE').le
    exact hleft.trans hright

/-- A signed lower certificate needs only actual error monotonicity; its
individual terms and its partial sums may be negative. -/
theorem reciprocal_signed_gain_sum (E q : ℕ → ℝ) (hE : ∀ n, 0 < E n)
    (hmon : Antitone E) (hstep : ∀ n, E (n + 1) ≤ E n - q n) (N : ℕ) :
    1 / E 0 + (∑ n ∈ Finset.range N, q n / (E n) ^ 2) ≤ 1 / E N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hincr := inverse_energy_step_signed (E N) (E (N + 1)) (q N)
        (hE N) (hE (N + 1)) (hmon (Nat.le_succ N)) (hstep N)
      linarith

/-- Prefix-level certification suffices. No local gain inequality or sign
restriction on the arithmetic budget is required. -/
theorem eventual_small_of_unbounded_prefix_budget (E B : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hmon : Antitone E)
    (hprefix : ∀ N, 1 / E 0 + B N ≤ 1 / E N)
    (hbudget : ∀ M : ℝ, ∃ N : ℕ, M ≤ B N) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hbudget (1 / ε + 1)
  have hrec := hprefix N
  have hinitial : 0 < 1 / E 0 := div_pos zero_lt_one (hE 0)
  have hinv : 1 / ε < 1 / E N := by linarith
  have hsmall : E N < ε := by
    have hp := (div_lt_div_iff₀ hε (hE N)).mp hinv
    simpa only [one_mul] using hp
  exact ⟨N, fun n hn => lt_of_le_of_lt (hmon hn) hsmall⟩

/-- Signed arithmetic gains can cancel across arbitrarily long prime windows.
Only cofinal unboundedness of the normalized complete signed sum is needed. -/
theorem eventual_small_of_unbounded_signed_gain_budget (E q : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hmon : Antitone E)
    (hstep : ∀ n, E (n + 1) ≤ E n - q n)
    (hbudget : ∀ M : ℝ, ∃ N : ℕ,
      M ≤ ∑ n ∈ Finset.range N, q n / (E n) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε := by
  exact eventual_small_of_unbounded_prefix_budget E
    (fun N => ∑ n ∈ Finset.range N, q n / (E n) ^ 2)
    hE hmon (reciprocal_signed_gain_sum E q hE hmon hstep) hbudget

/-- The sharper signed product budget uses the literal adjacent errors and has
no positivity requirement for its arithmetic certificates. -/
theorem eventual_small_of_unbounded_sharp_gain_budget (E q : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hmon : Antitone E)
    (hstep : ∀ n, E (n + 1) ≤ E n - q n)
    (hbudget : ∀ M : ℝ, ∃ N : ℕ,
      M ≤ ∑ n ∈ Finset.range N, q n / (E n * E (n + 1))) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε := by
  exact eventual_small_of_unbounded_prefix_budget E
    (fun N => ∑ n ∈ Finset.range N, q n / (E n * E (n + 1)))
    hE hmon (reciprocal_gain_sum_sharp E q hE hstep) hbudget

/-- Actual complete gains give an exact equivalence, not only a sufficient
condition. It makes explicit that budget divergence for the actual gains is
precisely the unresolved density question. -/
theorem eventual_small_iff_unbounded_exact_gain_budget (E : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hmon : Antitone E) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε) ↔
    (∀ M : ℝ, ∃ N : ℕ,
      M ≤ ∑ n ∈ Finset.range N,
        (E n - E (n + 1)) / (E n * E (n + 1))) := by
  constructor
  · intro hsmall M
    let T : ℝ := max M 0 + 1 / E 0 + 1
    have hT : 0 < T := by
      dsimp [T]
      have hmax : 0 ≤ max M 0 := le_max_right M 0
      have hinitial : 0 < 1 / E 0 := div_pos zero_lt_one (hE 0)
      linarith
    obtain ⟨N, hN⟩ := hsmall (1 / T) (div_pos zero_lt_one hT)
    have hEN : E N < 1 / T := hN N le_rfl
    have hprod : E N * T < 1 := (lt_div_iff₀ hT).mp hEN
    have hinv : T < 1 / E N := by
      apply (lt_div_iff₀ (hE N)).2
      simpa only [mul_comm] using hprod
    refine ⟨N, ?_⟩
    rw [inverse_energy_telescope E hE N]
    have hM : M ≤ max M 0 := le_max_left M 0
    dsimp [T] at hinv
    linarith
  · intro hbudget
    apply eventual_small_of_unbounded_sharp_gain_budget E
      (fun n => E n - E (n + 1)) hE hmon
      (fun n => by linarith) hbudget

/-- A tail drop is paid for by the complete square-normalized budget.
This remains true even after discarding the initial stages in the telescoping
energy difference. -/
theorem tail_drop_le_scaled_actual_square_budget (E : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hmon : Antitone E) (m k : ℕ) :
    E m - E (m + k) ≤ (E m) ^ 2 *
      (∑ n ∈ Finset.range (m + k),
        (E n - E (n + 1)) / (E n) ^ 2) := by
  have hq : ∀ n, 0 ≤ E n - E (n + 1) := fun n =>
    sub_nonneg.mpr (hmon (Nat.le_succ n))
  induction k with
  | zero =>
      have hsum : 0 ≤ ∑ n ∈ Finset.range m,
          (E n - E (n + 1)) / (E n) ^ 2 := by
        exact Finset.sum_nonneg (fun n _ => div_nonneg (hq n) (sq_nonneg (E n)))
      simpa using mul_nonneg (sq_nonneg (E m)) hsum
  | succ k ih =>
      have hmk : m ≤ m + k := Nat.le_add_right m k
      have hsq : (E (m + k)) ^ 2 ≤ (E m) ^ 2 := by
        have hprod := mul_nonneg (sub_nonneg.mpr (hmon hmk))
          (add_nonneg (hE m).le (hE (m + k)).le)
        nlinarith
      have hratio : 0 ≤ (E (m + k) - E (m + k + 1)) / (E (m + k)) ^ 2 :=
        div_nonneg (hq (m + k)) (sq_nonneg (E (m + k)))
      have hscaled := mul_le_mul_of_nonneg_right hsq hratio
      have hcancel : (E (m + k)) ^ 2 *
          ((E (m + k) - E (m + k + 1)) / (E (m + k)) ^ 2) =
          E (m + k) - E (m + k + 1) := by
        field_simp [ne_of_gt (hE (m + k))]
      rw [hcancel] at hscaled
      rw [Nat.add_succ, Finset.sum_range_succ]
      simp only [Nat.succ_eq_add_one]
      nlinarith

/-- Square normalization loses no qualitative information for the actual full
optimizer gains. It is an exact criterion under positive monotone errors,
although its finite reciprocal bound is generally not an equality. -/
theorem eventual_small_iff_unbounded_actual_square_gain_budget (E : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hmon : Antitone E) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε) ↔
    (∀ M : ℝ, ∃ N : ℕ,
      M ≤ ∑ n ∈ Finset.range N,
        (E n - E (n + 1)) / (E n) ^ 2) := by
  constructor
  · intro hsmall M
    let C : ℝ := max M 0 + 1
    have hC : 0 < C := by
      dsimp [C]
      have hmax : 0 ≤ max M 0 := le_max_right M 0
      linarith
    obtain ⟨m, hm⟩ := hsmall (1 / (2 * C)) (div_pos zero_lt_one (by linarith))
    have hm_small : E m < 1 / (2 * C) := hm m le_rfl
    have hm_prod : E m * C < 1 / 2 := by
      have hp := (lt_div_iff₀ (by linarith : 0 < 2 * C)).mp hm_small
      nlinarith
    obtain ⟨n₀, hn₀⟩ := hsmall (E m / 2) (by linarith [hE m])
    let N : ℕ := max m n₀
    have hmN : m ≤ N := le_max_left m n₀
    have hnN : n₀ ≤ N := le_max_right m n₀
    have hNsmall : E N < E m / 2 := hn₀ N hnN
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmN
    have hdrop := tail_drop_le_scaled_actual_square_budget E hE hmon m k
    rw [← hk] at hdrop
    refine ⟨N, ?_⟩
    by_contra hnot
    have hbudget : (∑ n ∈ Finset.range N,
        (E n - E (n + 1)) / (E n) ^ 2) < M := lt_of_not_ge hnot
    have hMC : M ≤ C := by
      have hmax : M ≤ max M 0 := le_max_left M 0
      dsimp [C]
      linarith
    have hscaled_budget := mul_le_mul_of_nonneg_left
      (le_trans hbudget.le hMC) (sq_nonneg (E m))
    have hscaled_small := mul_lt_mul_of_pos_left hm_prod (hE m)
    nlinarith
  · intro hbudget
    apply eventual_small_of_unbounded_signed_gain_budget E
      (fun n => E n - E (n + 1)) hE hmon
      (fun n => by linarith) hbudget

/-- Cumulative signed cancellation over arbitrary prime windows can be paid for
by a strict fraction of an independently diverging reference budget. There is
no source margin on individual primes and no sign assumption on q. -/
theorem eventual_small_of_signed_window_budget
    (E q A : ℕ → ℝ) (t : ℕ → ℕ) (θ C : ℝ)
    (hE : ∀ n, 0 < E n) (hmon : Antitone E)
    (hstep : ∀ n, E (n + 1) ≤ E n - q n) (hθ : θ < 1)
    (hwindow : ∀ k, (1 - θ) * A k - C ≤
      ∑ n ∈ Finset.range (t k), q n / (E n) ^ 2)
    (hA : ∀ M : ℝ, ∃ k : ℕ, M ≤ A k) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E n < ε := by
  apply eventual_small_of_unbounded_signed_gain_budget E q hE hmon hstep
  intro M
  have hfactor : 0 < 1 - θ := sub_pos.mpr hθ
  obtain ⟨k, hk⟩ := hA ((M + C) / (1 - θ))
  refine ⟨t k, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hk hfactor.le
  have hcancel : (1 - θ) * ((M + C) / (1 - θ)) = M + C := by
    field_simp [ne_of_gt hfactor]
  rw [hcancel] at hscaled
  have hwin := hwindow k
  linarith

/-- Square normalization discards an explicit quadratic reciprocal gain.
This is an exact identity for every pair of nonzero adjacent errors. -/
theorem inverse_energy_square_completion (E E' : ℝ)
    (hE : E ≠ 0) (hE' : E' ≠ 0) :
    1 / E' - 1 / E = (E - E') / E ^ 2 +
      (E - E') ^ 2 / (E ^ 2 * E') := by
  field_simp [hE, hE']
  <;> ring

/-- The complete positive quadratic remainder restores equality to the finite
square-normalized budget. No monotonicity is needed for the identity. -/
theorem inverse_energy_square_telescope (E : ℕ → ℝ)
    (hE : ∀ n, E n ≠ 0) (N : ℕ) :
    1 / E 0 +
      (∑ n ∈ Finset.range N, (E n - E (n + 1)) / (E n) ^ 2) +
      (∑ n ∈ Finset.range N,
        (E n - E (n + 1)) ^ 2 / ((E n) ^ 2 * E (n + 1))) =
      1 / E N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hincr := inverse_energy_square_completion (E N) (E (N + 1))
        (hE N) (hE (N + 1))
      linarith

/-- A nonnegative lower gain also has a quadratic reciprocal bonus, with the
actual adjacent error retained in its denominator. -/
theorem inverse_energy_step_quadratic (E E' q : ℝ)
    (hE : 0 < E) (hE' : 0 < E') (hq : 0 ≤ q) (hstep : E' ≤ E - q) :
    q / E ^ 2 + q ^ 2 / (E ^ 2 * E') ≤ 1 / E' - 1 / E := by
  have hdrop : q ≤ E - E' := by linarith
  have hdrop0 : 0 ≤ E - E' := le_trans hq hdrop
  have hsq : q ^ 2 ≤ (E - E') ^ 2 := by nlinarith
  rw [inverse_energy_square_completion E E' (ne_of_gt hE) (ne_of_gt hE')]
  apply add_le_add
  · exact div_le_div_of_nonneg_right hdrop (sq_nonneg E)
  · exact div_le_div_of_nonneg_right hsq (mul_nonneg (sq_nonneg E) hE'.le)

/-- The sharper finite quantitative certificate retains all quadratic lower
gain bonuses instead of summing only the first-order reciprocal terms. -/
theorem reciprocal_gain_sum_quadratic (E q : ℕ → ℝ)
    (hE : ∀ n, 0 < E n) (hq : ∀ n, 0 ≤ q n)
    (hstep : ∀ n, E (n + 1) ≤ E n - q n) (N : ℕ) :
    1 / E 0 +
      (∑ n ∈ Finset.range N, q n / (E n) ^ 2) +
      (∑ n ∈ Finset.range N, (q n) ^ 2 / ((E n) ^ 2 * E (n + 1))) ≤
      1 / E N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hincr := inverse_energy_step_quadratic (E N) (E (N + 1)) (q N)
        (hE N) (hE (N + 1)) (hq N) (hstep N)
      linarith

end RiemannResearch.Analysis.PrimeGainRecursion
