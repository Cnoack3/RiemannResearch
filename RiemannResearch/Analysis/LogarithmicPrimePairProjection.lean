import RiemannResearch.Analysis.LogarithmicPrimePairFMZ
import RiemannResearch.Probability.DeterminantalPairTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# An explicit projection comparison on the arithmetic sites

Use counting measure on {0,...,N-1} and the orthogonal complement of the
constant vector. This projection process deletes one uniformly chosen site.
The two-point vacancy can be computed exactly for every arithmetic weight.
The reference for determinantal inclusion probabilities is Lyons,
*Determinantal probability measures*, https://arxiv.org/abs/math/0204325.
-/
noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.LogarithmicPrimePairs

def deletionEntry {ι : Type*} [DecidableEq ι] (N : ℕ) (i j : ι) : ℝ :=
  (if i=j then 1 else 0) - 1/(N:ℝ)

theorem deletionEntry_symmetric {ι : Type*} [DecidableEq ι] (N : ℕ) (i j : ι) :
    deletionEntry N i j = deletionEntry N j i := by simp [deletionEntry,eq_comm]

/-- Matrix entries of the square of the projection on the finite counting space. -/
theorem deletionEntry_idempotent {N : ℕ} (i j : Fin N) :
    ∑ k : Fin N, deletionEntry N i k * deletionEntry N k j = deletionEntry N i j := by
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by have := i.isLt; omega)
  have hex (k : Fin N) : deletionEntry N i k * deletionEntry N k j =
      (if i=k then (if k=j then 1 else 0) else 0) -
      (if i=k then 1/(N:ℝ) else 0) - (if k=j then 1/(N:ℝ) else 0) + (1/(N:ℝ))^2 := by
    unfold deletionEntry
    split_ifs <;> ring
  simp_rw [hex]
  simp only [sum_add_distrib,sum_sub_distrib,sum_ite_eq,sum_ite_eq',mem_univ,if_true,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold deletionEntry
  field_simp [hN]
  <;> ring

theorem deletion_twoPoint {ι : Type*} [DecidableEq ι] (N : ℕ) {i j : ι} (hij : i ≠ j) :
    deletionEntry N i i * deletionEntry N j j - deletionEntry N i j * deletionEntry N j i =
      1-2/(N:ℝ) := by
  simp [deletionEntry,hij,hij.symm]
  ring

/-- The determinant equals the probability that a uniform deleted index
misses both labels. The formula also covers a ground set of size two. -/
theorem uniform_deletion_inclusion {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (∑ k : Fin N, if k ≠ i ∧ k ≠ j then (1:ℝ) else 0)/(N:ℝ) =
      deletionEntry N i i * deletionEntry N j j - deletionEntry N i j * deletionEntry N j i := by
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by have := i.isLt; omega)
  have hex (k : Fin N) : (if k ≠ i ∧ k ≠ j then (1:ℝ) else 0) =
      1 - (if k=i then 1 else 0) - (if k=j then 1 else 0) := by
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all
  simp_rw [hex]
  rw [deletion_twoPoint N hij]
  simp only [sum_sub_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp [hN]
  <;> ring

/-- Count through the greatest possible shifted second site, inclusive. -/
def deletionSize (B u X : ℝ) : ℕ := ⌊B*X⌋₊ + shiftWidth u X + 1

def deletionExpected (A B u X : ℝ) : ℝ :=
  let N := deletionSize B u X
  (pairModeTest A B u X (fun m n =>
    ((deletionEntry N m m * deletionEntry N n n - deletionEntry N m n * deletionEntry N n m : ℝ) : ℂ))).re

/-- Exact signed vacancy transfer for the actual arithmetic coefficients. -/
theorem triangle_sub_deletionExpected (A B u X : ℝ) :
    trianglePairAverage A B u X-deletionExpected A B u X =
      (2/(deletionSize B u X:ℝ))*trianglePairAverage A B u X := by
  let N := deletionSize B u X
  have h : ∀ h ∈ Ioc 0 (shiftWidth u X), ∀ n ∈ Ioc ⌊A*X⌋₊ ⌊B*X⌋₊,
      deletionEntry N (n+h) (n+h) * deletionEntry N n n -
        deletionEntry N (n+h) n * deletionEntry N n (n+h) = 1-2/(N:ℝ) := by
    intro h hh n _
    exact deletion_twoPoint N (by have := (mem_Ioc.mp hh).1; omega)
  have hmass := pairModeTest_at_identity A B u X
  simp only [pairModeTest,mul_one] at hmass
  have he : deletionExpected A B u X = (1-2/(N:ℝ))*trianglePairAverage A B u X := by
    unfold deletionExpected pairModeTest
    have hsum :
        (∑ h ∈ Ioc 0 (shiftWidth u X), ∑ n ∈ Ioc ⌊A*X⌋₊ ⌊B*X⌋₊,
          (pairCoefficient u X n h : ℂ) *
            (↑(deletionEntry N (n+h) (n+h) * deletionEntry N n n -
                deletionEntry N (n+h) n * deletionEntry N n (n+h)) : ℂ)) =
        ((trianglePairAverage A B u X:ℝ):ℂ) * ((1-2/(N:ℝ):ℝ):ℂ) := by
      rw [← hmass, sum_mul]
      apply sum_congr rfl
      intro h' hh
      rw [sum_mul]
      apply sum_congr rfl
      intro n hn
      rw [h h' hh n hn]
    exact (congrArg Complex.re hsum).trans (by
      rw [← Complex.ofReal_mul, Complex.ofReal_re, mul_comm])
  rw [he]
  change _ = (2/(N:ℝ))*_
  ring

theorem tendsto_deletion_vacancy (A : ℝ) {B u : ℝ} (hB : 0 < B) (hu : 0 < u) :
    Tendsto (fun X : ℝ => trianglePairAverage A B u X-deletionExpected A B u X)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℝ => (Real.log X)^3/X) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_pow_atTop (1:ℝ) 3 (by norm_num)
  have lim := hlog.const_mul (200*u^2)
  rw [mul_zero] at lim
  apply squeeze_zero_norm' _ lim
  filter_upwards [eventually_pairModeMass_le A hB hu,eventually_gt_atTop (1:ℝ)] with X hmass hX
  have hx : 0 < X := by linarith
  have hN : B*X ≤ (deletionSize B u X:ℝ) := by
    have h := Nat.lt_floor_add_one (B*X)
    dsimp [deletionSize]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (shiftWidth u X)]
  have hNX := (mul_pos hB hx).trans_le hN
  rw [Real.norm_eq_abs,triangle_sub_deletionExpected,abs_mul,abs_of_pos (div_pos (by norm_num) hNX)]
  calc
    _ ≤ (2/(B*X))*((100*B*u^2)*(Real.log X)^3) :=
      mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (mul_pos hB hx) hN)
        ((abs_triangle_le_pairModeMass A B u X).trans hmass) (abs_nonneg _) (by positivity)
    _ = _ := by field_simp [hB.ne',hx.ne']; ring

end RiemannResearch.Analysis.LogarithmicPrimePairs
