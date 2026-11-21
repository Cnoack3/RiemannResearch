import RiemannResearch.Analysis.LogarithmicPrimePairOddAnnulus
import RiemannResearch.Analysis.LogarithmicPrimePairTriangle
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Restoring all prime powers in the logarithmic two-point upper sieve

Goldston, Pintz and Yıldırım, *Primes in tuples IV*, Acta Arith. 160
(2013), equations (5.3)–(5.5), https://doi.org/10.4064/aa160-1-3,
use an unconditional upper sieve for pairs of primes. Their sum in (5.5)
uses a dyadic interval for both primes:
    #{Y < p < q ≤ 2Y : q-p ≤ h} ≪ hY/(log Y)².
For a fixed positive annulus, cover it by finitely many dyadic intervals.
Crossings of the right end of each interval add at most H² pairs. With
H = floor(u log X), weighting each prime pair by O((log X)²) yields the
prime-only bound below. The literature input has no prime powers in it.
The transfer to von Mangoldt weights is proved here.
-/
noncomputable section
open Finset Filter
open scoped BigOperators Topology ArithmeticFunction
namespace RiemannResearch.Analysis.LogarithmicPrimePairs

def primeOnlyBlock (a b h : ℕ) : ℝ :=
  ∑ n ∈ Ioc a b, if n.Prime ∧ (n+h).Prime then Λ n * Λ (n+h) else 0

def primeOnlySharp (A B u X : ℝ) : ℝ :=
  (∑ h ∈ Ioc 0 (shiftWidth u X), primeOnlyBlock ⌊A*X⌋₊ ⌊B*X⌋₊ h) / (X*Real.log X)

/-- Fixed-annulus, logarithmic-width consequence of GPY (5.5). -/
def GPYPrimePairSieve : Prop :=
  ∀ A B : ℝ, 0 < A → A < B → ∃ C > (0 : ℝ), ∀ u : ℝ, 0 < u →
    ∀ᶠ X : ℝ in atTop, primeOnlySharp A B u X ≤ C * u

private theorem nonprime_shift_le (a b j : ℕ) {Y : ℝ} (hb : b + j ≤ ⌊Y⌋₊) :
    (∑ n ∈ Ioc a b, if (n+j).Prime then 0 else Λ (n+j)) ≤ Chebyshev.psi Y - Chebyshev.theta Y := by
  let J := (Ioc a b).filter (fun n => ¬(n+j).Prime)
  have he : (∑ n ∈ Ioc a b, if (n+j).Prime then 0 else Λ (n+j)) = ∑ n ∈ J, Λ (n+j) := by
    simp only [J,sum_filter,ite_not]
  rw [he,Chebyshev.psi_sub_theta_eq_sum_not_prime]
  let f := fun n : ℕ => n+j
  have hi : Set.InjOn f (J:Set ℕ) := fun _ _ _ _ e => Nat.add_right_cancel e
  have hs : J.image f ⊆ (Ioc 0 ⌊Y⌋₊).filter (fun m => ¬m.Prime) := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
    obtain ⟨hn,hp⟩ := mem_filter.mp hn
    have hn' := mem_Ioc.mp hn
    simpa only [mem_filter,mem_Ioc,f] using
      (show (0 < n+j ∧ n+j ≤ ⌊Y⌋₊) ∧ ¬(n+j).Prime from ⟨⟨by omega,by omega⟩,hp⟩)
  calc
    _ = ∑ m ∈ J.image f, Λ m := (sum_image hi).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem pairBlock_sub_primeOnly_bound {a b h : ℕ} {Y K : ℝ}
    (hb : b + h ≤ ⌊Y⌋₊) (hK : 0 ≤ K) (hΛ : ∀ n : ℕ, n ≤ b+h → Λ n ≤ K) :
    0 ≤ (∑ n ∈ Ioc a b, Λ n * Λ (n+h)) - primeOnlyBlock a b h ∧
    (∑ n ∈ Ioc a b, Λ n * Λ (n+h)) - primeOnlyBlock a b h ≤
      2*K*(Chebyshev.psi Y-Chebyshev.theta Y) := by
  unfold primeOnlyBlock
  rw [← sum_sub_distrib]
  have hn0 (n : ℕ) : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  constructor
  · apply sum_nonneg
    intro n _
    split_ifs <;> simp [mul_nonneg (hn0 _) (hn0 _)]
  · have hs (n : ℕ) (hn : n ∈ Ioc a b) :
        Λ n*Λ (n+h) - (if n.Prime ∧ (n+h).Prime then Λ n*Λ (n+h) else 0) ≤
        K*((if n.Prime then 0 else Λ n) + (if (n+h).Prime then 0 else Λ (n+h))) := by
      have hc := (mem_Ioc.mp hn).2
      have h1 := hΛ n (by omega)
      have h2 := hΛ (n+h) (by omega)
      by_cases hp : n.Prime <;> by_cases hq : (n+h).Prime <;> simp [hp,hq] <;>
        nlinarith [mul_le_mul_of_nonneg_right h1 (hn0 (n+h)),
          mul_le_mul_of_nonneg_left h2 (hn0 n), mul_nonneg hK (hn0 n)]
    refine (sum_le_sum hs).trans ?_
    rw [← mul_sum, sum_add_distrib]
    have h1 := nonprime_shift_le a b 0 (Y := Y) (by omega)
    have h2 := nonprime_shift_le a b h hb
    simp only [Nat.add_zero] at h1
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK]

/-- The whole contribution of pairs with at least one proper prime power is
O(log X / sqrt X) in the normalized sharp statistic. -/
theorem properPower_sharp_rate (A : ℝ) {B u : ℝ} (hB : 0 < B) (hu : 0 < u) :
    ∃ C > (0:ℝ), ∀ᶠ X : ℝ in atTop,
      |sharpPairAverage A B u X-primeOnlySharp A B u X| ≤ C*Real.log X/Real.sqrt X := by
  obtain ⟨c,hc⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := B+u
  let K := max 1 c
  have hD : 0 < D := add_pos hB hu
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨4*u*K*Real.sqrt D,by positivity, ?_⟩
  filter_upwards [eventually_window_mangoldt hB hu, eventually_gt_atTop (1:ℝ)] with X hm hX
  let H := shiftWidth u X
  let a := ⌊A*X⌋₊
  let b := ⌊B*X⌋₊
  let L := Real.log X
  have hx : 0 < X := by linarith
  have hl : 0 < L := Real.log_pos hX
  have hw : (H:ℝ) ≤ u*L := Nat.floor_le (mul_pos hu hl).le
  have hy : b+H ≤ ⌊D*X⌋₊ := by
    apply Nat.le_floor
    push_cast
    have hb : (b:ℝ) ≤ B*X := Nat.floor_le (mul_pos hB hx).le
    have hlog : L ≤ X := Real.log_le_self hx.le
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_left hlog hu.le]
  have hrow (h : ℕ) (hh : h ∈ Ioc 0 H) := pairBlock_sub_primeOnly_bound (a := a)
    (b := b) (h := h) (Y := D*X) (K := 2*L)
    (by have := (mem_Ioc.mp hh).2; omega) (by positivity)
    (fun n hn => hm n (by have := (mem_Ioc.mp hh).2; omega))
  let R := ∑ h ∈ Ioc 0 H, (pairBlock A B X h-primeOnlyBlock a b h)
  have h0 : 0 ≤ R := sum_nonneg (fun h hh => (hrow h hh).1)
  have hraw : R ≤ (H:ℝ) * (2*(2*L)*(K*Real.sqrt (D*X))) := by
    have hs := (hc (D*X)).trans (mul_le_mul_of_nonneg_right (le_max_right 1 c) (Real.sqrt_nonneg _))
    have hi (h : ℕ) (hh : h ∈ Ioc 0 H) := (hrow h hh).2.trans
      (mul_le_mul_of_nonneg_left hs (by positivity))
    simpa [R, pairBlock, K, a, b] using sum_le_sum hi
  have heq : sharpPairAverage A B u X-primeOnlySharp A B u X = R/(X*L) := by
    unfold sharpPairAverage primeOnlySharp
    rw [sum_comm, ← sub_div]
    simp only [R,pairBlock,a,b,H,L,sum_sub_distrib]
  rw [heq,abs_of_nonneg (div_nonneg h0 (mul_pos hx hl).le)]
  apply (div_le_iff₀ (mul_pos hx hl)).mpr
  calc
    _ ≤ (H:ℝ)*(2*(2*L)*(K*Real.sqrt (D*X))) := hraw
    _ ≤ (u*L)*(2*(2*L)*(K*Real.sqrt (D*X))) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul hD.le]
      dsimp only [L]
      field_simp [(Real.sqrt_pos.mpr hx).ne']
      <;> ring_nf <;> rw [Real.sq_sqrt hx.le] <;> ring

theorem tendsto_sharp_sub_primeOnly (A : ℝ) {B u : ℝ} (hB : 0 < B) (hu : 0 < u) :
    Tendsto (fun X : ℝ => sharpPairAverage A B u X - primeOnlySharp A B u X) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := properPower_sharp_rate A hB hu
  have ht : Tendsto (fun X : ℝ => Real.log X / Real.sqrt X) atTop (𝓝 0) := by
    simpa [Real.sqrt_eq_rpow] using Real.tendsto_pow_log_div_pow_atTop ((1 : ℝ) / 2) 1 (by norm_num)
  have hlim := ht.const_mul K
  rw [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hK] with X hX
  rw [Real.norm_eq_abs, ← mul_div_assoc]
  exact hX

/-- One annular constant controls every fixed logarithmic width. The threshold in X
may depend on the width. -/
theorem eventually_sharp_le_width_of_sieve (published : GPYPrimePairSieve)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C > (0 : ℝ), ∀ u : ℝ, 0 < u → ∀ᶠ X : ℝ in atTop, sharpPairAverage A B u X ≤ C * u := by
  obtain ⟨M, hM, hm⟩ := published A B hA hAB
  refine ⟨M + 1, by positivity, ?_⟩
  intro u hu
  have he := tendsto_sharp_sub_primeOnly A (hA.trans hAB) hu
  filter_upwards [hm u hu, he.eventually (eventually_lt_nhds hu)] with X hp hsmall
  change sharpPairAverage A B u X - primeOnlySharp A B u X < u at hsmall
  linarith

/-- The prime-only upper sieve therefore controls actual positive von Mangoldt pairs. -/
theorem eventually_sharp_bounded_of_sieve (published : GPYPrimePairSieve)
    {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop, sharpPairAverage A B u X ≤ C := by
  obtain ⟨C, hC, hbound⟩ := eventually_sharp_le_width_of_sieve published hA hAB
  exact ⟨C * u, mul_pos hC hu, hbound u hu⟩

end RiemannResearch.Analysis.LogarithmicPrimePairs
