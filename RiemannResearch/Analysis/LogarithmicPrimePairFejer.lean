import RiemannResearch.Analysis.LogarithmicFejerKernel
import RiemannResearch.Analysis.LogarithmicPrimePairTriangle
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The additive Fourier energy for actual logarithmic prime pairs

Both cutoffs are on the first site in the prime-pair statistic. The Fourier
polynomial cuts off both sites. The discrepancy occurs at the right endpoint.
Centering also introduces a left endpoint. All sums include prime powers.
-/
noncomputable section
open Finset Filter
open scoped BigOperators ArithmeticFunction Topology
namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open FractionalFejer

def rightSites (a b h : ℕ) : Finset ℕ := (Ioc a b).filter (fun n => b < n+h)
def leftSites (a b h : ℕ) : Finset ℕ := (Ioc a b).filter (fun n => n ≤ a+h)

private theorem right_card (a b h : ℕ) : (rightSites a b h).card ≤ h := by
  have hs : rightSites a b h ⊆ Ioc (b-h) b := by
    intro n hn
    simp only [rightSites, mem_filter, mem_Ioc] at hn
    exact mem_Ioc.mpr ⟨by omega, hn.1.2⟩
  have hc := card_le_card hs
  rw [Nat.card_Ioc] at hc
  omega

private theorem left_card (a b h : ℕ) : (leftSites a b h).card ≤ h := by
  have hs : leftSites a b h ⊆ Ioc a (a+h) := by
    intro n hn
    simp only [leftSites, mem_filter, mem_Ioc] at hn
    exact mem_Ioc.mpr ⟨hn.1.1,hn.2⟩
  simpa [Nat.card_Ioc] using card_le_card hs

def edgePair (a b h : ℕ) : ℝ := ∑ n ∈ rightSites a b h, Λ n * Λ (n+h)

def edgeMean (a b h : ℕ) : ℝ :=
  (∑ n ∈ rightSites a b h, (Λ n-1)) + ∑ n ∈ leftSites a b h, Λ n

def rightEndpoint (a b H : ℕ) (s : ℝ) : ℝ := ∑ h ∈ Ioc 0 H, (s-h) * edgePair a b h
def meanEndpoint (a b H : ℕ) (s : ℝ) : ℝ := ∑ h ∈ Ioc 0 H, (s-h) * edgeMean a b h

def annularEnergy (A B u X : ℝ) (w : ℕ → ℝ) : ℝ :=
  energy (shiftWidth u X) (u * Real.log X - shiftWidth u X)
    (Ioc ⌊A*X⌋₊ ⌊B*X⌋₊) w

private theorem pair_split (a b h : ℕ) :
    (∑ n ∈ Ioc a b, Λ n * Λ (n+h)) =
      correlation (Ioc a b) (fun n => Λ n) h + edgePair a b h := by
  unfold correlation edgePair rightSites
  rw [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  obtain ⟨hlo,_⟩ := mem_Ioc.mp hn
  have hlo' : a < n+h := by omega
  by_cases he : n+h ≤ b <;> simp [hlo', he, not_lt.mpr, Nat.lt_of_not_ge]

private theorem translate_interior (a b h : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ (Ioc a b).filter (fun n => n+h ≤ b), w (n+h)) =
    ∑ m ∈ (Ioc a b).filter (fun m => a+h < m), w m := by
  apply sum_bij' (fun n _ => n+h) (fun m _ => m-h)
  all_goals intro n hn
  all_goals simp only [mem_filter, mem_Ioc] at hn ⊢
  all_goals first | rfl | omega

private theorem centered_lag (a b h : ℕ) :
    correlation (Ioc a b) (fun n => Λ n) h -
        correlation (Ioc a b) (fun n => Λ n-1) h =
      (∑ n ∈ Ioc a b, (2*Λ n-1)) - edgeMean a b h := by
  let J := (Ioc a b).filter (fun n => n+h ≤ b)
  have he : correlation (Ioc a b) (fun n => Λ n) h -
      correlation (Ioc a b) (fun n => Λ n-1) h =
      (∑ n ∈ J, (Λ n-1)) + ∑ n ∈ J, Λ (n+h) := by
    simp only [correlation, J, sum_filter, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hn' := (mem_Ioc.mp hn).1
    have hlo : a < n+h := by omega
    by_cases hh : n+h ≤ b <;> simp [hlo, hh] <;> ring
  rw [he]
  dsimp only [J]
  rw [translate_interior]
  unfold edgeMean rightSites leftSites
  simp only [sum_filter]
  have h (n : ℕ) : (if n+h ≤ b then Λ n-1 else 0) + (if a+h < n then Λ n else 0) =
      (2*Λ n-1) - ((if b < n+h then Λ n-1 else 0) + (if n ≤ a+h then Λ n else 0)) := by
    by_cases hr : n+h ≤ b <;> by_cases hl : n ≤ a+h <;>
      simp [hr,hl, Nat.lt_of_not_ge, not_lt.mpr] <;> ring
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl (fun n _ => h n)

theorem width_weight_sum (H : ℕ) (s : ℝ) :
    (∑ h ∈ Ioc 0 H, (s - h)) = H*s - (H:ℝ)*(H+1)/2 := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le H), ih]
    push_cast
    ring

theorem edge_weight_sum (H : ℕ) (r : ℝ) :
    (∑ h ∈ Ioc 0 H, (h:ℝ) * (H+r-h)) = H*(H+1)*(H-1+3*r)/6 := by
  have gen (m : ℕ) (s : ℝ) : (∑ h ∈ Ioc 0 m, (h:ℝ)*(s-h)) =
      (m:ℝ)*(m+1)*(3*s-2*m-1)/6 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le m), ih]
      push_cast
      ring
  rw [gen]
  ring

/-- Exact missing-right-endpoint form of the finite Plancherel identity. -/
theorem triangle_fejer_exact (A B u : ℝ) {X : ℝ} (hX : 1 < X) :
    2*X*(Real.log X)^2*trianglePairAverage A B u X =
      annularEnergy A B u X (fun n => Λ n) -
        (u*Real.log X)*(∑ n ∈ Ioc ⌊A*X⌋₊ ⌊B*X⌋₊, (Λ n)^2) +
        2*rightEndpoint ⌊A*X⌋₊ ⌊B*X⌋₊ (shiftWidth u X) (u*Real.log X) := by
  let H := shiftWidth u X
  let s := u*Real.log X
  let a := ⌊A*X⌋₊
  let b := ⌊B*X⌋₊
  have hc : (H:ℝ) + (s-H) = s := by ring
  have hw : X*(Real.log X)^2*trianglePairAverage A B u X =
      ∑ h ∈ Ioc 0 H, (s-h)*pairBlock A B X h := by
    unfold trianglePairAverage
    rw [show X*(Real.log X)^2 = Real.log X*(X*Real.log X) by ring, mul_assoc,
      mul_div_cancel₀ _ (mul_ne_zero (by linarith : X ≠ 0) (Real.log_pos hX).ne'), mul_sum]
    apply sum_congr rfl
    intro h _
    dsimp [s]
    field_simp [(Real.log_pos hX).ne']
    <;> ring
  have he := energy_eq H (s-H) (Ioc a b) (fun n => Λ n)
  rw [hc] at he
  change 2*X*(Real.log X)^2*trianglePairAverage A B u X =
    energy H (s-H) (Ioc a b) (fun n => Λ n) - s*_ + 2*rightEndpoint a b H s
  rw [show 2*X*(Real.log X)^2*trianglePairAverage A B u X =
    2*(X*(Real.log X)^2*trianglePairAverage A B u X) by ring, hw, he]
  have hs : (∑ h ∈ Ioc 0 H, (s-h)*pairBlock A B X h) =
      (∑ h ∈ Ioc 0 H, (s-h)*correlation (Ioc a b) (fun n => Λ n) h) + rightEndpoint a b H s := by
    unfold rightEndpoint
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro h _
    change (s-h)*(∑ n ∈ Ioc a b, Λ n*Λ (n+h)) = _
    rw [pair_split, mul_add]
  rw [hs]
  ring

/-- Centering subtracts the full zero-frequency value times the one-site
mass, with two translated endpoint sums restored exactly. -/
theorem centered_fejer_exact (a b H : ℕ) (s : ℝ) :
    energy H (s-H) (Ioc a b) (fun n => Λ n) -
      energy H (s-H) (Ioc a b) (fun n => Λ n-1) =
    (s^2 + (s-H)*(1-(s-H))) * (∑ n ∈ Ioc a b, (2*Λ n-1)) -
      2*meanEndpoint a b H s := by
  rw [energy_eq, energy_eq, show (H:ℝ)+(s-H) = s by ring]
  have hdiag : (∑ n ∈ Ioc a b, (Λ n)^2) - (∑ n ∈ Ioc a b, (Λ n-1)^2) =
      ∑ n ∈ Ioc a b, (2*Λ n-1) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  let D := ∑ n ∈ Ioc a b, (2*Λ n-1)
  have hoff : (∑ h ∈ Ioc 0 H, (s-h)*correlation (Ioc a b) (fun n => Λ n) h) -
      (∑ h ∈ Ioc 0 H, (s-h)*correlation (Ioc a b) (fun n => Λ n-1) h) =
      (∑ h ∈ Ioc 0 H, (s-h))*D - meanEndpoint a b H s := by
    unfold meanEndpoint
    rw [sum_mul, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro h _
    rw [← mul_sub, centered_lag]
    dsimp [D]
    ring
  rw [width_weight_sum] at hoff
  dsimp [D] at hoff
  linear_combination s*hdiag + 2*hoff

private theorem boundary_sum_le (J : Finset ℕ) (f : ℕ → ℝ) {M : ℝ} {h : ℕ}
    (hc : J.card ≤ h) (hM : 0 ≤ M) (hf : ∀ n ∈ J, |f n| ≤ M) :
    |∑ n ∈ J, f n| ≤ h*M := by
  calc
    _ ≤ ∑ n ∈ J, |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ J, M := sum_le_sum hf
    _ = (J.card:ℝ)*M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hM

/-- Both arithmetic endpoints bounded by the same exact cubic weight. -/
theorem fejer_endpoint_bounds {a b H : ℕ} {s K : ℝ} (hH : (H:ℝ) ≤ s)
    (hK : 0 ≤ K) (hΛ : ∀ n : ℕ, n ≤ b+H → Λ n ≤ K) :
    |rightEndpoint a b H s| ≤ K^2 * (∑ h ∈ Ioc 0 H, (h:ℝ)*(s-h)) ∧
    |meanEndpoint a b H s| ≤ (2*K+1) * (∑ h ∈ Ioc 0 H, (h:ℝ)*(s-h)) := by
  have hrow (h : ℕ) (hh : h ∈ Ioc 0 H) :
      |edgePair a b h| ≤ h*K^2 ∧ |edgeMean a b h| ≤ h*(2*K+1) := by
    have hh' := (mem_Ioc.mp hh).2
    have hr (n : ℕ) (hn : n ∈ rightSites a b h) := (mem_Ioc.mp (mem_filter.mp hn).1).2
    have hl (n : ℕ) (hn : n ∈ leftSites a b h) := (mem_Ioc.mp (mem_filter.mp hn).1).2
    have hn0 (n : ℕ) : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    constructor
    · apply boundary_sum_le _ _ (right_card a b h) (sq_nonneg K)
      intro n hn
      rw [abs_of_nonneg (mul_nonneg (hn0 _) (hn0 _)), sq]
      exact mul_le_mul (hΛ n (by have := hr n hn; omega))
        (hΛ (n+h) (by have := hr n hn; omega)) (hn0 _) hK
    · have hright := boundary_sum_le _ (fun n => Λ n-1) (right_card a b h)
          (by linarith : 0 ≤ K+1) (fun n hn => (abs_sub _ _).trans (by
            rw [abs_of_nonneg (hn0 _), abs_one]
            linarith [hΛ n (by have := hr n hn; omega)]))
      have hleft := boundary_sum_le _ (fun n => Λ n) (left_card a b h) hK
        (fun n hn => by rw [abs_of_nonneg (hn0 _)]; exact hΛ n (by have := hl n hn; omega))
      exact (abs_add_le _ _).trans (by linarith [hright,hleft])
  have sumBound (f : ℕ → ℝ) (C : ℝ) (hf : ∀ h ∈ Ioc 0 H, |f h| ≤ h*C) :
      |∑ h ∈ Ioc 0 H, (s-h)*f h| ≤ C*(∑ h ∈ Ioc 0 H, (h:ℝ)*(s-h)) := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
    intro h hh
    have hcast : (h:ℝ) ≤ H := by exact_mod_cast (mem_Ioc.mp hh).2
    have hw := sub_nonneg.mpr (hcast.trans hH)
    rw [abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ (s-h)*(h*C) := mul_le_mul_of_nonneg_left (hf h hh) hw
      _ = _ := by ring
  exact ⟨sumBound _ _ (fun h hh => (hrow h hh).1), sumBound _ _ (fun h hh => (hrow h hh).2)⟩

end RiemannResearch.Analysis.LogarithmicPrimePairs
