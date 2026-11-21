import RiemannResearch.Analysis.LogarithmicPrimePairs
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-! # Uniform odd-shift savings on a fixed macroscopic annulus

At an odd shift every surviving pair contains a power of two. In an interval
of endpoint ratio at most 2^k there are at most k candidate powers on either
side of the pair, uniformly in the shift. Counting only these powers saves a
factor of log X over the bound obtained from the entire prefix through BX.
-/
noncomputable section
open Finset Filter
open scoped BigOperators Topology ArithmeticFunction
namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open OddGapPrimeCorrelation

private theorem powers_on_annulus (a b j L k : ℕ) (hk : 0 < k)
    (hb : b < 2 ^ k * (a + 1)) :
    ((Ioc a b).filter (fun n => n+j ∈ powersTwo L)).card ≤ k := by
  let S := (Ioc a b).filter (fun n => n+j ∈ powersTwo L)
  let e := fun n => Nat.log 2 (n+j)
  have hx (n : ℕ) (hn : n ∈ S) : n+j = 2^(e n) := by
    obtain ⟨z,_,hz⟩ := mem_image.mp (mem_filter.mp hn).2
    dsimp [e]
    rw [← hz, Nat.log_pow (by decide : 1 < 2)]
  have sep (n m : ℕ) (hn : n ∈ S) (hm : m ∈ S) (he : e n < e m)
      (heq : e n % k = e m % k) : False := by
    have hd : k ∣ e m-e n := (Nat.modEq_iff_dvd' he.le).mp heq
    have hgap : k ≤ e m-e n := Nat.le_of_dvd (by omega) hd
    have hpow : 2^k*(n+j) ≤ m+j := by
      rw [hx n hn,hx m hm, ← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hn' := (mem_Ioc.mp (mem_filter.mp hn).1).1
    have hm' := (mem_Ioc.mp (mem_filter.mp hm).1).2
    have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide)
    have hadd := Nat.mul_le_mul_right j hp
    have hbase := Nat.mul_le_mul_left (2^k) (show a+1 ≤ n by omega)
    rw [Nat.mul_add] at hpow
    omega
  calc
    S.card ≤ (range k).card := by
      apply card_le_card_of_injOn (fun n => e n % k)
      · intro n _
        exact mem_range.mpr (Nat.mod_lt _ hk)
      · intro n hn m hm heq
        rcases lt_trichotomy (e n) (e m) with h | h | h
        · exact (sep n m hn hm h heq).elim
        · have hn' := hx n hn
          rw [h, ← hx m hm] at hn'
          omega
        · exact (sep m n hm hn h heq.symm).elim
    _ = k := card_range _

/-- A finite uniform odd-shift estimate, including the shifted right endpoint. -/
theorem odd_pair_annular_bound {a b h k : ℕ} (hk : 0 < k)
    (hb : b < 2 ^ k * (a + 1)) (hodd : h % 2 = 1) {K : ℝ} (hK : 0 ≤ K)
    (hΛ : ∀ n : ℕ, n ≤ b+h → Λ n ≤ K) :
    (∑ n ∈ Ioc a b, Λ n * Λ (n+h)) ≤ 2*k*Real.log 2*K := by
  let L := b+h
  have hs (j : ℕ) (f : ℕ → ℝ) (hf : ∀ n ∈ Ioc a b, f n ≤ K) :
      (∑ n ∈ Ioc a b, if n+j ∈ powersTwo L then f n else 0) ≤ k*K := by
    rw [← sum_filter]
    calc
      _ ≤ ∑ _n ∈ (Ioc a b).filter (fun n => n+j ∈ powersTwo L), K :=
        sum_le_sum (fun n hn => hf n (mem_filter.mp hn).1)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast powers_on_annulus a b j L k hk hb) hK
  have h1 := hs 0 (fun n => Λ (n+h)) (fun n hn => hΛ _ (Nat.add_le_add_right (mem_Ioc.mp hn).2 _))
  have h2 := hs h (fun n => Λ n) (fun n hn => hΛ _ (by have := (mem_Ioc.mp hn).2; omega))
  simp only [Nat.add_zero] at h1
  have hid (n : ℕ) (hn : n ∈ Ioc a b) := odd_gap_product_exact n h L hodd
    (by dsimp [L]; have := (mem_Ioc.mp hn).2; omega) (Nat.add_le_add_right (mem_Ioc.mp hn).2 _)
  rw [sum_congr rfl hid, ← mul_sum, sum_add_distrib]
  have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  linarith

/-- The entire normalized odd mass is O(log X / X), for every fixed annulus. -/
theorem oddMass_annular_rate {A B d : ℝ} (hA : 0 < A) (hAB : A < B) (hd : 0 < d) :
    ∃ k : ℕ, 0 < k ∧ B < (2:ℝ)^k*A ∧ ∀ᶠ X : ℝ in atTop,
      |oddMass A B d X/(X*Real.log X)| ≤
        (4*(k:ℝ)*Real.log 2*d)*(Real.log X/X) := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (B/A) (by norm_num : (1:ℝ) < 2)
  have hkB : B < (2:ℝ)^k*A := (div_lt_iff₀ hA).mp hk
  have hk0 : 0 < k := by
    by_contra! he
    have hkz : k = 0 := Nat.le_zero.mp he
    rw [hkz, pow_zero, one_mul] at hkB
    exact (not_lt_of_ge hAB.le) hkB
  refine ⟨k,hk0,hkB, ?_⟩
  filter_upwards [eventually_window_mangoldt (hA.trans hAB) hd,
    eventually_gt_atTop (1:ℝ)] with X hΛ hX
  have hx : 0 < X := by linarith
  have hL := Real.log_pos hX
  let a := ⌊A*X⌋₊
  let b := ⌊B*X⌋₊
  let H := shiftWidth d X
  have hscale : b < 2 ^ k * (a + 1) := by
    have hab := Nat.floor_le (mul_pos (hA.trans hAB) hx).le
    have ha := Nat.lt_floor_add_one (A*X)
    have he : (b:ℝ) < (2:ℝ)^k*((a:ℝ)+1) := calc
      _ ≤ B*X := hab
      _ < (2:ℝ)^k*(A*X) := by linarith [mul_lt_mul_of_pos_right hkB hx]
      _ < _ := mul_lt_mul_of_pos_left ha (by positivity)
    exact_mod_cast he
  have hrow (h : ℕ) (hh : h ∈ Ioc 0 H) :
      (if h % 2=0 then 0 else pairBlock A B X h) ≤ 2*k*Real.log 2*(2*Real.log X) := by
    split_ifs with he
    · positivity
    · exact odd_pair_annular_bound hk0 hscale (by omega) (by positivity)
        (fun n hn => hΛ n (hn.trans (Nat.add_le_add_left (mem_Ioc.mp hh).2 _)))
  have hs : oddMass A B d X ≤ H*(2*k*Real.log 2*(2*Real.log X)) := by
    simpa [oddMass,H] using sum_le_sum hrow
  have hpos : 0 ≤ oddMass A B d X := by
    apply sum_nonneg
    intro h _
    split_ifs <;> first | rfl | exact pairBlock_nonneg _ _ _ _
  have hwidth : (H:ℝ) ≤ d*Real.log X := Nat.floor_le (mul_pos hd hL).le
  rw [abs_of_nonneg (div_nonneg hpos (mul_pos hx hL).le)]
  apply (div_le_iff₀ (mul_pos hx hL)).mpr
  calc
    _ ≤ H*(2*k*Real.log 2*(2*Real.log X)) := hs
    _ ≤ (d*Real.log X)*(2*k*Real.log 2*(2*Real.log X)) :=
      mul_le_mul_of_nonneg_right hwidth (by positivity)
    _ = _ := by field_simp [hx.ne']; ring

end RiemannResearch.Analysis.LogarithmicPrimePairs
