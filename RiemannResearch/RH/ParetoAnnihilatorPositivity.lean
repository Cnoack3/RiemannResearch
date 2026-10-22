import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Tactic.Linarith

/-!
# Positivity and the legal Pareto annihilator

Source: user-provided argument and the ensuing discussion of indicator reduction,
September 11, 2026. This formalizes the nonnegative uniqueness argument and the
conditional absolute-value reduction, in the actual Pareto weights and legal span.

The square-summability hypothesis covers unbounded weighted L2 sequences.
Index zero has weight zero; conclusions there require a separate anchor.
Absolute-value closure of the annihilator is an unresolved substantive hypothesis.
The general indicator counterexample is in Analysis/IndicatorAnnihilator.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The weighted L2 annihilator of the actual finite legal span. -/
def LegalAnnihilator (A : Set ℕ) (h : ℕ → ℝ) : Prop :=
  Summable (fun k => positiveWeight k * h k ^ 2) ∧
  ∀ g ∈ legalSeedSpan A, paretoInner h g = 0

theorem weighted_abs_summable_of_square {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Summable (fun k => positiveWeight k * |h k|) := by
  apply (positiveWeight_summable.add hs).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_abs,
    abs_of_nonneg (positiveWeight_nonneg k)]
  have hb : |h k| ≤ 1 + h k ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (h k - 1), sq_nonneg (h k + 1)]
  simpa only [mul_add, mul_one] using
    mul_le_mul_of_nonneg_left hb (positiveWeight_nonneg k)

theorem weighted_product_summable_of_square_of_bounded {h g : ℕ → ℝ} {C : ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hg : ∀ k, |g k| ≤ C) :
    Summable (fun k => positiveWeight k * (h k * g k)) := by
  apply ((weighted_abs_summable_of_square hs).mul_right C).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (positiveWeight_nonneg k)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hg k) (mul_nonneg (positiveWeight_nonneg k) (abs_nonneg _))

theorem dyadic_dilation_nonneg (m k : ℕ) : 0 ≤ dilation m (residue 2) k := by
  unfold dilation residue
  positivity

theorem dyadic_dilation_abs_le (m k : ℕ) :
    |dilation m (residue 2) k| ≤ (m : ℝ) * 2 := by
  apply dilation_abs_le
  intro j
  simp only [residue]
  rw [abs_of_nonneg (Nat.cast_nonneg (j % 2) : (0 : ℝ) ≤ (j % 2 : ℕ))]
  exact_mod_cast (Nat.mod_lt j (by decide : 0 < 2)).le

theorem dyadic_dilation_self {m : ℕ} (hm : 0 < m) :
    dilation m (residue 2) m = (m : ℝ) := by
  simp [dilation, residue, Nat.div_self hm]

/-- Each nonnegative dyadic test detects its own positive index. -/
theorem nonnegative_dyadic_annihilator_eq_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hn : ∀ k, 0 ≤ h k)
    (ho : ∀ m, 0 < m → paretoInner h (dilation m (residue 2)) = 0)
    {n : ℕ} (hnpos : 0 < n) : h n = 0 := by
  have hsum := weighted_product_summable_of_square_of_bounded hs
    (dyadic_dilation_abs_le n)
  have ht := hsum.le_tsum n (fun k _ =>
    mul_nonneg (positiveWeight_nonneg k)
      (mul_nonneg (hn k) (dyadic_dilation_nonneg n k)))
  change positiveWeight n * (h n * dilation n (residue 2) n) ≤
    paretoInner h (dilation n (residue 2)) at ht
  rw [ho n hnpos, dyadic_dilation_self hnpos] at ht
  have hw : 0 < positiveWeight n := by
    unfold positiveWeight
    positivity
  have hp : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hz : positiveWeight n * (h n * (n : ℝ)) = 0 :=
    le_antisymm ht (mul_nonneg hw.le (mul_nonneg (hn n) hp.le))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hw))).resolve_right
    (ne_of_gt hp)

theorem legalAnnihilator_nonnegative_eq_zero {A : Set ℕ} (hA : 2 ∈ A)
    {h : ℕ → ℝ} (hh : LegalAnnihilator A h) (hn : ∀ k, 0 ≤ h k)
    {n : ℕ} (hnpos : 0 < n) : h n = 0 :=
  nonnegative_dyadic_annihilator_eq_zero hh.1 hn
    (fun _m hm => hh.2 _ (dilation_generator_mem A hA hm)) hnpos

theorem legalAnnihilator_indicator_no_positive_member {A : Set ℕ} (hA : 2 ∈ A)
    (s : Set ℕ)
    (hs : LegalAnnihilator A (s.indicator (fun _ => (1 : ℝ)))) :
    ∀ n, 0 < n → n ∉ s := by
  classical
  intro n hn hns
  have hz := legalAnnihilator_nonnegative_eq_zero hA hs
    (fun k => by by_cases hk : k ∈ s <;> simp [hk]) hn
  simp [hns] at hz

/-- Conditional research reduction. The hypothesis `habs` is not proved here. -/
theorem legalAnnihilator_eq_zero_of_abs_closed {A : Set ℕ} (hA : 2 ∈ A)
    (habs : ∀ h, LegalAnnihilator A h →
      LegalAnnihilator A (fun k => |h k|))
    {h : ℕ → ℝ} (hh : LegalAnnihilator A h) {n : ℕ} (hn : 0 < n) :
    h n = 0 := by
  exact abs_eq_zero.mp
    (legalAnnihilator_nonnegative_eq_zero hA (habs h hh) (fun k => abs_nonneg _) hn)

theorem legalAnnihilator_anchored_eq_zero_of_abs_closed {A : Set ℕ} (hA : 2 ∈ A)
    (habs : ∀ h, LegalAnnihilator A h →
      LegalAnnihilator A (fun k => |h k|))
    {h : ℕ → ℝ} (hh : LegalAnnihilator A h) (hzero : h 0 = 0) :
    h = 0 := by
  funext n
  cases n with
  | zero => exact hzero
  | succ n => exact legalAnnihilator_eq_zero_of_abs_closed hA habs hh (Nat.succ_pos n)

/-- Dyadic tests have no support strictly before their dilation index. -/
theorem dyadic_dilation_eq_zero_of_lt {m k : ℕ} (hk : k < m) :
    dilation m (residue 2) k = 0 := by
  simp [dilation, residue, Nat.div_eq_of_lt hk]

/-- A tail of fixed sign already vanishes on that tail. -/
theorem nonnegative_tail_dyadic_annihilator_eq_zero {h : ℕ → ℝ} {N : ℕ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hn : ∀ k, N ≤ k → 0 ≤ h k)
    (ho : ∀ m, 0 < m → paretoInner h (dilation m (residue 2)) = 0)
    {n : ℕ} (hnpos : 0 < n) (hN : N ≤ n) : h n = 0 := by
  have hsum := weighted_product_summable_of_square_of_bounded hs
    (dyadic_dilation_abs_le n)
  have ht := hsum.le_tsum n (fun k _ => show
      0 ≤ positiveWeight k * (h k * dilation n (residue 2) k) from by
    by_cases hk : k < n
    · simp [dyadic_dilation_eq_zero_of_lt hk]
    · exact mul_nonneg (positiveWeight_nonneg k)
        (mul_nonneg (hn k (le_trans hN (Nat.le_of_not_gt hk)))
          (dyadic_dilation_nonneg n k)))
  change positiveWeight n * (h n * dilation n (residue 2) n) ≤
    paretoInner h (dilation n (residue 2)) at ht
  rw [ho n hnpos, dyadic_dilation_self hnpos] at ht
  have hw : 0 < positiveWeight n := by
    unfold positiveWeight
    positivity
  have hp : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hz : positiveWeight n * (h n * (n : ℝ)) = 0 :=
    le_antisymm ht (mul_nonneg hw.le (mul_nonneg (hn n hN) hp.le))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hw))).resolve_right
    (ne_of_gt hp)

/-- Descending elimination removes every finite head of a dyadic annihilator.
No summability assumption is necessary once the tail is identically zero. -/
theorem finite_support_dyadic_annihilator_eq_zero {h : ℕ → ℝ}
    (ho : ∀ m, 0 < m → paretoInner h (dilation m (residue 2)) = 0)
    (N : ℕ) (htail : ∀ k, N ≤ k → h k = 0)
    {n : ℕ} (hn : 0 < n) : h n = 0 := by
  have hall : ∀ M, (∀ k, M ≤ k → h k = 0) → ∀ k, 0 < k → h k = 0 := by
    intro M
    induction M with
    | zero =>
        intro hz k _
        exact hz k (Nat.zero_le k)
    | succ M ih =>
        intro hz k hk
        by_cases hM : M = 0
        · exact hz k (by omega)
        · have hMp : 0 < M := Nat.pos_of_ne_zero hM
          have hpair : paretoInner h (dilation M (residue 2)) =
              positiveWeight M * (h M * dilation M (residue 2) M) := by
            apply tsum_eq_single M
            intro j hj
            by_cases hjM : j < M
            · simp [dyadic_dilation_eq_zero_of_lt hjM]
            · rw [hz j (by omega)]
              simp
          rw [ho M hMp, dyadic_dilation_self hMp] at hpair
          have hw : 0 < positiveWeight M := by
            unfold positiveWeight
            positivity
          have hMr : (0 : ℝ) < M := by exact_mod_cast hMp
          have hzM : h M = 0 :=
            (mul_eq_zero.mp ((mul_eq_zero.mp hpair.symm).resolve_left
              (ne_of_gt hw))).resolve_right (ne_of_gt hMr)
          apply ih _ k hk
          intro j hj
          by_cases hjeq : j = M
          · simpa [hjeq] using hzM
          · exact hz j (by omega)
  exact hall N htail n hn

/-- An eventually nonnegative weighted L2 dyadic annihilator is zero. -/
theorem eventually_nonnegative_dyadic_annihilator_eq_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (ho : ∀ m, 0 < m → paretoInner h (dilation m (residue 2)) = 0)
    (hn : ∃ N, ∀ k, N ≤ k → 0 ≤ h k)
    {n : ℕ} (hnpos : 0 < n) : h n = 0 := by
  obtain ⟨N, hN⟩ := hn
  apply finite_support_dyadic_annihilator_eq_zero ho (N + 1) _ hnpos
  intro k hk
  exact nonnegative_tail_dyadic_annihilator_eq_zero hs hN ho (by omega) (by omega)

/-- A signed annihilator cannot be eventually of either sign, unless it is zero
at every positive index. Source: user-provided analytic research argument. -/
theorem legalAnnihilator_eventually_one_sign_eq_zero {A : Set ℕ} (hA : 2 ∈ A)
    {h : ℕ → ℝ} (hh : LegalAnnihilator A h)
    (hsign : (∃ N, ∀ k, N ≤ k → 0 ≤ h k) ∨
      (∃ N, ∀ k, N ≤ k → h k ≤ 0))
    {n : ℕ} (hnpos : 0 < n) : h n = 0 := by
  have ho : ∀ m, 0 < m → paretoInner h (dilation m (residue 2)) = 0 :=
    fun _m hm => hh.2 _ (dilation_generator_mem A hA hm)
  rcases hsign with hpos | hneg
  · exact eventually_nonnegative_dyadic_annihilator_eq_zero hh.1 ho hpos hnpos
  · have hsneg : Summable (fun k => positiveWeight k * (-h k) ^ 2) := by
      simpa only [neg_sq] using hh.1
    have honeg : ∀ m, 0 < m →
        paretoInner (fun k => -h k) (dilation m (residue 2)) = 0 := by
      intro m hm
      change (∑' k, positiveWeight k * ((-h k) * dilation m (residue 2) k)) = 0
      simp_rw [neg_mul, mul_neg]
      rw [tsum_neg]
      change -paretoInner h (dilation m (residue 2)) = 0
      rw [ho m hm, neg_zero]
    have hnneg : ∃ N, ∀ k, N ≤ k → 0 ≤ -h k := by
      obtain ⟨N, hN⟩ := hneg
      exact ⟨N, fun k hk => neg_nonneg.mpr (hN k hk)⟩
    exact neg_eq_zero.mp
      (eventually_nonnegative_dyadic_annihilator_eq_zero hsneg honeg hnneg hnpos)

theorem legalAnnihilator_anchored_eq_zero_of_eventually_one_sign
    {A : Set ℕ} (hA : 2 ∈ A) {h : ℕ → ℝ} (hh : LegalAnnihilator A h)
    (hsign : (∃ N, ∀ k, N ≤ k → 0 ≤ h k) ∨
      (∃ N, ∀ k, N ≤ k → h k ≤ 0)) (hzero : h 0 = 0) : h = 0 := by
  funext n
  cases n with
  | zero => exact hzero
  | succ n =>
      exact legalAnnihilator_eventually_one_sign_eq_zero hA hh hsign (Nat.succ_pos n)

/-- Every nonzero positive coordinate forces both signs arbitrarily far out. -/
theorem legalAnnihilator_both_signs_arbitrarily_far {A : Set ℕ} (hA : 2 ∈ A)
    {h : ℕ → ℝ} (hh : LegalAnnihilator A h)
    {n : ℕ} (hn : 0 < n) (hne : h n ≠ 0) (N : ℕ) :
    (∃ k, N ≤ k ∧ 0 < h k) ∧ (∃ k, N ≤ k ∧ h k < 0) := by
  constructor
  · by_contra hp
    push Not at hp
    exact hne (legalAnnihilator_eventually_one_sign_eq_zero hA hh
      (Or.inr ⟨N, hp⟩) hn)
  · by_contra hn'
    push Not at hn'
    exact hne (legalAnnihilator_eventually_one_sign_eq_zero hA hh
      (Or.inl ⟨N, hn'⟩) hn)

end
end RiemannResearch.RH.Pareto
