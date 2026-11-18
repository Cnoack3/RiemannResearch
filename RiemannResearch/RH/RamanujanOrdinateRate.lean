import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroCauchyDensity
import RiemannResearch.RH.RamanujanOrdinateFMZ
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.ParetoPacketGreenGram
import Mathlib.Algebra.Order.Round
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# Unconditional error in Ramanujan synthesis from zeta ordinates

Ford and Zaharescu, *On the distribution of imaginary parts of zeros of the
Riemann zeta function*, Corollary 2, https://arxiv.org/abs/math/0405459,
identify the prime-root Fourier coefficients. Here the actual contour remainder
and the Cauchy-density bound give a rate for the full signed Möbius synthesis
and its integrated packets. Each evaluation uses one height for all modes.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- A prime-root divisor probe recovers its indicator with a quantitative
remainder, whether or not the root is an integer. -/
theorem ordinateDivisorProbe_error_isBigO {p d n : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hn : 0 < n) :
    Asymptotics.IsBigO atTop
      (fun T : ℝ => ordinateDivisorProbe p d n T - (if d ∣ n then (1 : ℂ) else 0))
      horizontalLogRate := by
  let u := primeRootFrequency p d n
  let A : ℂ := (((-(2 * Real.pi * Real.sqrt (Real.exp u)) / Real.log p) : ℝ) : ℂ)
  have hu : 0 < u := mul_pos (div_pos (by exact_mod_cast hn) (by exact_mod_cast hd))
    (Real.log_pos (by exact_mod_cast hp.one_lt))
  have he := tendsto_nhds_unique
    ((tendsto_primeRoot_ordinate hp hd hn sublinearHorizontalEnergy).const_mul A)
    (tendsto_ordinateDivisorProbe hp hd hn sublinearHorizontalEnergy)
  have hf := (fixed_ordinate_remainder_isBigO_horizontalLogRate hu
    (tendsto_primeRoot_landau hp hd hn)).const_mul_left A
  apply hf.congr' _ Filter.EventuallyEq.rfl
  filter_upwards with T
  change A * (ordinateSum T u / (T : ℂ) - (primeRootMain p d n : ℂ)) =
    A * (ordinateSum T u / (T : ℂ)) - _
  rw [mul_sub,he]

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.ActualZeroOrdinate

/-- The full signed Möbius synthesis at one actual height. -/
def ramanujanOrdinateApprox (p q n : ℕ) (T : ℝ) : ℂ :=
  ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q/d) : ℂ) * (d : ℂ)) *
    ordinateDivisorProbe p d n T

/-- Exact finite-height signed error before taking absolute values. -/
theorem ramanujanOrdinateApprox_sub_eq (p q n : ℕ) (T : ℝ) :
    ramanujanOrdinateApprox p q n T - (ramanujanSum q n : ℂ) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q/d) : ℂ) * (d : ℂ)) *
        (ordinateDivisorProbe p d n T - (if d ∣ n then (1 : ℂ) else 0)) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ramanujanOrdinateApprox]
  congr 1
  unfold ramanujanSum
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ n <;> simp [h]

/-- Quantitative recovery for every conductor, including nonsquarefree ones. -/
theorem ramanujanOrdinateApprox_error_isBigO {p n : ℕ} (q : ℕ)
    (hp : p.Prime) (hn : 0 < n) :
    Asymptotics.IsBigO atTop
      (fun T : ℝ => ramanujanOrdinateApprox p q n T - (ramanujanSum q n : ℂ))
      horizontalLogRate := by
  simp_rw [ramanujanOrdinateApprox_sub_eq]
  apply Asymptotics.IsBigO.sum
  intro d hd
  exact (ordinateDivisorProbe_error_isBigO hp (Nat.pos_of_mem_divisors hd) hn).const_mul_left _

/-- The same quantitative scale holds for the signed integrated physical
packet at any fixed cutoff, with one common zero height for the entire prefix. -/
theorem ramanujanPacket_ordinate_error_isBigO {p q : ℕ} (k : ℕ)
    (hp : p.Prime) (hq : 1 < q) :
    Asymptotics.IsBigO atTop
      (fun T : ℝ => -(∑ n ∈ Finset.Ico 1 (k+1), ramanujanOrdinateApprox p q n T) -
        (ramanujanPacket q k : ℂ)) horizontalLogRate := by
  have h : Asymptotics.IsBigO atTop (fun T : ℝ => ∑ n ∈ Finset.Ico 1 (k+1),
      (ramanujanOrdinateApprox p q n T - (ramanujanSum q n : ℂ))) horizontalLogRate := by
    apply Asymptotics.IsBigO.sum
    intro n hn
    exact ramanujanOrdinateApprox_error_isBigO q hp (Finset.mem_Ico.mp hn).1
  apply h.neg_left.congr' _ Filter.EventuallyEq.rfl
  filter_upwards with T
  rw [ramanujanPacket_prefix q k hq, Complex.ofReal_neg, Complex.ofReal_sum, Finset.sum_sub_distrib]
  ring

/-- Reconstruct the integrated packet from the first q-1 positive harmonics
at height T. The physical coordinate is reduced before taking the prefix. -/
def periodicOrdinatePacket (p q : ℕ) (T : ℝ) (k : ℕ) : ℂ :=
  -(∑ n ∈ Finset.Ico 1 (k % q + 1), ramanujanOrdinateApprox p q n T)

@[simp] theorem periodicOrdinatePacket_add_period (p q : ℕ) (T : ℝ) (k : ℕ) :
    periodicOrdinatePacket p q T (k+q) = periodicOrdinatePacket p q T k := by
  simp [periodicOrdinatePacket]

/-- At every height a single finite budget bounds the error on the entire
infinite physical space. No summability or limiting interchange is required. -/
theorem periodicOrdinatePacket_error_le_one_period (p q : ℕ) (hq : 1 < q) (T : ℝ) (k : ℕ) :
    ‖periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ)‖ ≤
      ∑ n ∈ Finset.Ico 1 q, ‖ramanujanOrdinateApprox p q n T - (ramanujanSum q n : ℂ)‖ := by
  have hper : ramanujanPacket q k = ramanujanPacket q (k % q) := by
    simpa only [Nat.mod_add_div] using
      ramanujanPacket_period_of_dvd q (q*(k/q)) (dvd_mul_right q _) (k%q)
  rw [hper, ramanujanPacket_prefix q (k%q) hq, Complex.ofReal_neg, Complex.ofReal_sum]
  unfold periodicOrdinatePacket
  have he : -(∑ n ∈ Finset.Ico 1 (k%q+1), ramanujanOrdinateApprox p q n T) -
      -(∑ n ∈ Finset.Ico 1 (k%q+1), (ramanujanSum q n : ℂ)) =
      -(∑ n ∈ Finset.Ico 1 (k%q+1),
        (ramanujanOrdinateApprox p q n T - (ramanujanSum q n : ℂ))) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [he,norm_neg]
  refine (_root_.norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro n hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨hlo,by have := Nat.mod_lt k (by omega : 0 < q); omega⟩
  · exact fun n _ _ => norm_nonneg _

/-- One height threshold works for every physical coordinate. Successive
differences recover the classical Ramanujan sum, including across a period end. -/
theorem eventually_periodicOrdinatePacket_uniform {p q : ℕ} (hp : p.Prime) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (∀ k, ‖periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ)‖ ≤
        C * horizontalLogRate T) ∧
      ∀ k, ‖(periodicOrdinatePacket p q T k - periodicOrdinatePacket p q T (k+1)) -
        (ramanujanSum q (k+1) : ℂ)‖ ≤ 2 * (C * horizontalLogRate T) := by
  let B (T : ℝ) := ∑ n ∈ Finset.Ico 1 q,
    ‖ramanujanOrdinateApprox p q n T - (ramanujanSum q n : ℂ)‖
  have hB : Asymptotics.IsBigO atTop B horizontalLogRate := by
    apply Asymptotics.IsBigO.sum
    intro n hn
    exact (ramanujanOrdinateApprox_error_isBigO q hp (Finset.mem_Ico.mp hn).1).norm_left
  obtain ⟨C,hC⟩ := hB.bound
  refine ⟨|C|+1,by positivity,?_⟩
  filter_upwards [hC,eventually_gt_atTop (1:ℝ)] with T ht hT
  have hR : 0 ≤ horizontalLogRate T := by
    unfold horizontalLogRate
    exact div_nonneg (sq_nonneg _) (Real.log_pos hT).le
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ B T from Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_eq_abs,abs_of_nonneg hR] at ht
  have hall (k : ℕ) : ‖periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ)‖ ≤
      (|C|+1) * horizontalLogRate T :=
    (periodicOrdinatePacket_error_le_one_period p q hq T k).trans
      (ht.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hR))
  refine ⟨hall,?_⟩
  intro k
  have hi := ramanujanPacket_increment q (k+1) hq (by omega)
  simp only [Nat.add_sub_cancel] at hi
  have he : ramanujanSum q (k+1) = ramanujanPacket q k - ramanujanPacket q (k+1) := by linarith
  rw [he,Complex.ofReal_sub]
  calc
    _ = ‖(periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ)) -
        (periodicOrdinatePacket p q T (k+1) - (ramanujanPacket q (k+1) : ℂ))‖ := by
          congr 1
          ring
    _ ≤ _ := (norm_sub_le _ _).trans (by linarith [hall k, hall (k+1)])

/-- Simultaneous full squared-error estimate for every nonnegative summable
physical weight, in particular the P and Q weights. The constant and height
threshold are independent of the weight. -/
theorem eventually_periodicOrdinatePacket_weighted_sq {p q : ℕ} (hp : p.Prime) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ w : ℕ → ℝ, (∀ k, 0 ≤ w k) → Summable w →
      Summable (fun k => w k * ‖periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ)‖^2) ∧
      (∑' k, w k * ‖periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ)‖^2) ≤
        (∑' k, w k) * (C * horizontalLogRate T)^2 := by
  obtain ⟨C,hC,h⟩ := eventually_periodicOrdinatePacket_uniform hp hq
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T hT
  intro w hw hs
  let M := (C*horizontalLogRate T)^2
  have hmajor := hs.mul_right M
  have hdom (k : ℕ) : w k * ‖periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ)‖^2 ≤
      w k * M := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hT.1 k) 2) (hw k)
  have hsum := Summable.of_nonneg_of_le (fun k => mul_nonneg (hw k) (sq_nonneg _)) hdom hmajor
  refine ⟨hsum,(hsum.tsum_le_tsum hdom hmajor).trans_eq ?_⟩
  exact tsum_mul_right

private theorem ramanujanSum_int_witness (q n : ℕ) :
    ∃ z : ℤ, (z : ℝ) = ramanujanSum q n := by
  refine ⟨∑ d ∈ q.divisors,
    ArithmeticFunction.moebius (q/d) * (if d ∣ n then (d : ℤ) else 0),?_⟩
  simp only [ramanujanSum, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ n <;> simp [h]

private theorem round_real_part_of_close {v : ℂ} {x : ℝ}
    (hx : ∃ z : ℤ, (z : ℝ) = x) (hv : ‖v - (x : ℂ)‖ < 1 / 2) :
    (round v.re : ℝ) = x := by
  obtain ⟨z,rfl⟩ := hx
  have h := (Complex.abs_re_le_norm (v - ((z : ℝ) : ℂ))).trans_lt hv
  simp only [Complex.sub_re,Complex.ofReal_re,abs_lt] at h
  have hz : round v.re = z := round_eq_iff.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
  rw [hz]

/-- For every sufficiently large height, a single period reconstructed from
the ordinates recovers all integer packet values and all positive harmonic
Ramanujan sums exactly by nearest-integer rounding of real parts. -/
theorem eventually_round_periodicOrdinatePacket {p q : ℕ} (hp : p.Prime) (hq : 1 < q) :
    ∀ᶠ T : ℝ in atTop, ∀ k : ℕ,
      (round (periodicOrdinatePacket p q T k).re : ℝ) = ramanujanPacket q k ∧
      (round (periodicOrdinatePacket p q T k - periodicOrdinatePacket p q T (k+1)).re : ℝ) =
        ramanujanSum q (k+1) := by
  obtain ⟨C,hC,hu⟩ := eventually_periodicOrdinatePacket_uniform hp hq
  have hz : Tendsto (fun T => C * horizontalLogRate T) atTop (𝓝 0) := by
    simpa using horizontalLogRate_tendsto_zero.const_mul C
  choose a ha using ramanujanSum_int_witness q
  filter_upwards [hu,hz.eventually_lt_const (by norm_num : (0:ℝ) < 1/4)] with T hT hsmall
  intro k
  have hint : ∃ z : ℤ, (z : ℝ) = ramanujanPacket q k := by
    refine ⟨-(∑ n ∈ Finset.Ico 1 (k+1), a n),?_⟩
    simp only [Int.cast_neg,Int.cast_sum,ha,ramanujanPacket_prefix q k hq]
  exact ⟨round_real_part_of_close hint ((hT.1 k).trans_lt (by linarith)),
    round_real_part_of_close ⟨_,ha (k+1)⟩ ((hT.2 k).trans_lt (by linarith))⟩


/-- Cofinal simultaneous reconstruction. A single height works at stage N for
every prime and conductor up to N and for every physical coordinate. -/
theorem exists_cofinal_round_periodicOrdinatePacket :
    ∃ H : ℕ → ℝ, StrictMono H ∧ Tendsto H atTop atTop ∧
      ∀ N T, H N ≤ T → ∀ p ≤ N, p.Prime → ∀ q ≤ N, 1 < q → ∀ k : ℕ,
        (round (periodicOrdinatePacket p q T k).re : ℝ) = ramanujanPacket q k ∧
        (round (periodicOrdinatePacket p q T k - periodicOrdinatePacket p q T (k+1)).re : ℝ) =
          ramanujanSum q (k+1) := by
  classical
  let P (p q : ℕ) (T : ℝ) := ∀ k : ℕ,
    (round (periodicOrdinatePacket p q T k).re : ℝ) = ramanujanPacket q k ∧
    (round (periodicOrdinatePacket p q T k - periodicOrdinatePacket p q T (k+1)).re : ℝ) =
      ramanujanSum q (k+1)
  have hs (N : ℕ) : ∀ᶠ T : ℝ in atTop, ∀ p q : Fin (N+1),
      (p : ℕ).Prime → 1 < (q : ℕ) → P p q T := by
    apply Filter.eventually_all.mpr
    intro p
    apply Filter.eventually_all.mpr
    intro q
    by_cases hp : (p : ℕ).Prime
    · by_cases hq : 1 < (q : ℕ)
      · exact (eventually_round_periodicOrdinatePacket hp hq).mono (fun _ h _ _ => h)
      · exact Eventually.of_forall (fun _ _ h => (hq h).elim)
    · exact Eventually.of_forall (fun _ h => (hp h).elim)
  choose b hb using fun N => eventually_atTop.mp (hs N)
  let H (n : ℕ) := (n : ℝ) + ∑ i ∈ Finset.range (n+1), |b i|
  have hstep (n : ℕ) : H n < H (n+1) := by
    dsimp only [H]
    rw [Finset.sum_range_succ (fun i => |b i|) (n+1)]
    push_cast
    linarith [abs_nonneg (b (n+1))]
  have hmajor (n : ℕ) : b n ≤ H n := by
    have hterm := Finset.single_le_sum (s := Finset.range (n+1))
      (f := fun i => |b i|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact (le_abs_self _).trans (hterm.trans (le_add_of_nonneg_left (Nat.cast_nonneg n)))
  have hnat (n : ℕ) : (n : ℝ) ≤ H n :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine ⟨H,strictMono_nat_of_lt_succ hstep,tendsto_atTop_mono hnat tendsto_natCast_atTop_atTop,?_⟩
  intro N T hT p hpN hp q hqN hq
  exact hb N T ((hmajor N).trans hT) ⟨p,by omega⟩ ⟨q,by omega⟩ hp hq

end RiemannResearch.RH.Pareto

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_ordinate_landau_of_moving_loglog' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_ordinate_landau_of_moving_loglog

/--
info: 'RiemannResearch.RH.Pareto.ramanujanOrdinateApprox_error_isBigO' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.ramanujanOrdinateApprox_error_isBigO

/--
info: 'RiemannResearch.RH.Pareto.eventually_periodicOrdinatePacket_weighted_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.eventually_periodicOrdinatePacket_weighted_sq

/--
info: 'RiemannResearch.RH.Pareto.exists_cofinal_round_periodicOrdinatePacket' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.exists_cofinal_round_periodicOrdinatePacket
