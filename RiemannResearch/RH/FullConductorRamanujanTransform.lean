/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.DivisorIncidence
import RiemannResearch.RH.ExactHeadRamanujanPlancherel
import RiemannResearch.RH.RamanujanFiniteIdentities
import RiemannResearch.RH.ResidueJumpCovariance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# The finite Ramanujan transform for every positive conductor

P. Haukkanen, *Discrete Ramanujan-Fourier transform of even functions (mod r)*,
Theorems 3.1–3.2, https://arxiv.org/abs/1210.0295, gives the finite basis and
inversion for even functions. Here the input is total mass in a gcd class,
with no class-cardinality factor in the forward transform. The two factors
in the inverse come from the class size and the squared norm of the primitive
row. We obtain primitive orthogonality from the integer divisor Gram matrix
and obtain its dual identity by reversing a finite matrix inverse.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.FullConductorRamanujan

open RiemannResearch.NumberTheory.DivisorIncidence
open RiemannResearch.RH.Pareto.RamanujanFinitePlancherel (transform)

/-- Divisor sums determine their summands on a downward-closed divisor set. -/
private theorem divisor_sum_injective (L : ℕ) (hL : 0 < L) (f g : ℕ → ℝ)
    (hs : ∀ n, n ∣ L → (∑ j ∈ n.divisors, f j) = ∑ j ∈ n.divisors, g j) :
    ∀ n, n ∣ L → f n = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnL
    have hn := Nat.pos_of_dvd_of_pos hnL hL
    have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
    have he : (∑ j ∈ n.divisors.erase n, f j) = ∑ j ∈ n.divisors.erase n, g j := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hjn, hjm⟩ := Finset.mem_erase.mp hj
      have hd := Nat.dvd_of_mem_divisors hjm
      exact ih j (lt_of_le_of_ne (Nat.le_of_dvd hn hd) hjn) (hd.trans hnL)
    have hf := Finset.sum_erase_add n.divisors f hmem
    have hg := Finset.sum_erase_add n.divisors g hmem
    linarith [hs n hnL]

private theorem divisor_indicator_gram (L d e : ℕ) (hd : d ∣ L) (he : e ∣ L) :
    (∑ n ∈ Finset.Icc 1 L,
      (if d ∣ n then (d : ℝ) else 0) * (if e ∣ n then (e : ℝ) else 0)) =
      (L : ℝ) * (Nat.gcd d e : ℝ) := by
  rw [sum_Icc_one L (fun n =>
    (if d ∣ n then (d : ℝ) else 0) * (if e ∣ n then (e : ℝ) else 0))]
  calc
    _ = ∑ n ∈ Finset.range L, (Nat.gcd d e : ℝ) *
        (if Nat.lcm d e ∣ n+1 then (Nat.lcm d e : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n _
      have hmul : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * e := by
        exact_mod_cast Nat.gcd_mul_lcm d e
      by_cases hdn : d ∣ n+1 <;> by_cases hen : e ∣ n+1 <;>
        simp [Nat.lcm_dvd_iff, hdn, hen, hmul]
    _ = _ := by
      rw [← Finset.mul_sum, sum_dvd_weight_of_period _ _ (Nat.lcm_dvd hd he), mul_comm]

private theorem totient_diagonal_divisor_sum (L d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (∑ q ∈ d.divisors, ∑ r ∈ e.divisors,
      if q = r then (L : ℝ) * (q.totient : ℝ) else 0) =
      (L : ℝ) * (Nat.gcd d e : ℝ) := by
  classical
  have hset : d.divisors.filter (fun q => q ∈ e.divisors) = (Nat.gcd d e).divisors := by
    ext q
    simp [Nat.mem_divisors, hd.ne', he.ne', (Nat.gcd_pos_of_pos_left e hd).ne', Nat.dvd_gcd_iff]
  calc
    _ = ∑ q ∈ d.divisors.filter (fun q => q ∈ e.divisors), (L : ℝ) * (q.totient : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : q ∈ e.divisors <;> simp [hq]
    _ = _ := by
      rw [hset, ← Finset.mul_sum]
      congr 1
      exact_mod_cast Nat.sum_totient (Nat.gcd d e)

/-- Unnormalized uniform Gram matrix of the primitive Ramanujan sums.
The last representative is L, so the zero residue is included exactly once. -/
theorem primitive_period_orthogonality (L q r : ℕ) (hL : 0 < L)
    (hq : q ∣ L) (hr : r ∣ L) :
    (∑ n ∈ Finset.Icc 1 L, ramanujanSum q n * ramanujanSum r n) =
      if q = r then (L : ℝ) * (q.totient : ℝ) else 0 := by
  let gram (i j : ℕ) := ∑ n ∈ Finset.Icc 1 L, ramanujanSum i n * ramanujanSum j n
  let diag (i j : ℕ) := if i = j then (L : ℝ) * (i.totient : ℝ) else 0
  have hsum (d e : ℕ) (hd : d ∣ L) (he : e ∣ L) :
      (∑ i ∈ d.divisors, ∑ j ∈ e.divisors, gram i j) =
      ∑ i ∈ d.divisors, ∑ j ∈ e.divisors, diag i j := by
    have hdpos := Nat.pos_of_dvd_of_pos hd hL
    have hepos := Nat.pos_of_dvd_of_pos he hL
    calc
      _ = ∑ n ∈ Finset.Icc 1 L, (∑ i ∈ d.divisors, ramanujanSum i n) *
          (∑ j ∈ e.divisors, ramanujanSum j n) := by
        unfold gram
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm (s := Finset.Icc 1 L) (t := d.divisors)]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = (L : ℝ) * (Nat.gcd d e : ℝ) := by
        simp_rw [ramanujanSum_divisor_sum d _ hdpos, ramanujanSum_divisor_sum e _ hepos]
        exact divisor_indicator_gram L d e hd he
      _ = _ := (totient_diagonal_divisor_sum L d e hdpos hepos).symm
  refine divisor_sum_injective L hL (gram q) (diag q) ?_ r hr
  intro e he
  exact divisor_sum_injective L hL (fun i => ∑ j ∈ e.divisors, gram i j)
    (fun i => ∑ j ∈ e.divisors, diag i j) (fun d hd => hsum d e hd he) q hq

/-- The same primitive Gram matrix summed over gcd classes with their exact cardinalities. -/
theorem primitive_gcd_orthogonality (L q r : ℕ) (hL : 0 < L) (hq : q ∣ L) (hr : r ∣ L) :
    (∑ g ∈ L.divisors, (Nat.totient (L/g) : ℝ) * (ramanujanSum q g * ramanujanSum r g)) =
      if q = r then (L : ℝ) * (q.totient : ℝ) else 0 := by
  classical
  rw [← primitive_period_orthogonality L q r hL hq hr]
  let F (g : ℕ) := ramanujanSum q g * ramanujanSum r g
  calc
    _ = ∑ g ∈ L.divisors, ∑ n ∈ Finset.Icc 1 L,
        if Nat.gcd n L = g then F g else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← gcd_class_card L g hg]
      change ((gcdClass L g).card : ℝ) * F g = _
      calc
        _ = ∑ _n ∈ gcdClass L g, F g := by simp [nsmul_eq_mul]
        _ = _ := by rw [gcdClass, Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      have hg : Nat.gcd n L ∈ L.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n L, hL.ne'⟩
      simp [hg, F, RiemannResearch.RH.ExactHeadRamanujanPlancherel.ramanujanSum_gcd_period L q n hq,
        RiemannResearch.RH.ExactHeadRamanujanPlancherel.ramanujanSum_gcd_period L r n hr]

/-- Dual Ramanujan Gram identity, with the actual gcd-cell weight for every modulus. -/
theorem conductor_kernel (L g h : ℕ) (hL : 0 < L) (hg : g ∣ L) (hh : h ∣ L) :
    (∑ q ∈ L.divisors, ramanujanSum q g * ramanujanSum q h / (q.totient : ℝ)) =
      if g = h then (L : ℝ) / (Nat.totient (L/g) : ℝ) else 0 := by
  classical
  let A : Matrix L.divisors L.divisors ℝ := fun q g => ramanujanSum q g
  let B : Matrix L.divisors L.divisors ℝ := fun g q =>
    (Nat.totient (L/(g : ℕ)) : ℝ) * ramanujanSum q g / ((L : ℝ) * (Nat.totient q : ℝ))
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have ht (q : L.divisors) : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors q.property)).ne'
  have hAB : A * B = 1 := by
    ext q r
    change (∑ g : L.divisors, A q g * B g r) = if q = r then 1 else 0
    calc
      _ = (∑ g : L.divisors, (Nat.totient (L/(g : ℕ)) : ℝ) *
          (ramanujanSum q g * ramanujanSum r g)) / ((L : ℝ) * (Nat.totient r : ℝ)) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro g _
        dsimp [A, B]
        ring
      _ = _ := by
        rw [Finset.sum_coe_sort L.divisors (fun g => (Nat.totient (L/g) : ℝ) *
          (ramanujanSum q g * ramanujanSum r g)), primitive_gcd_orthogonality L q r hL
            (Nat.dvd_of_mem_divisors q.property) (Nat.dvd_of_mem_divisors r.property)]
        by_cases heq : q = r
        · subst r
          simp [hL0, ht q]
        · have hn : (q : ℕ) ≠ (r : ℕ) := fun he => heq (Subtype.ext he)
          simp [heq, hn]
  have hBA : B * A = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (A := A) (B := B) (Equiv.refl L.divisors)).mp hAB
  let G : L.divisors := ⟨g, Nat.mem_divisors.mpr ⟨hg, hL.ne'⟩⟩
  let H : L.divisors := ⟨h, Nat.mem_divisors.mpr ⟨hh, hL.ne'⟩⟩
  have hentry := congrArg (fun M : Matrix L.divisors L.divisors ℝ => M G H) hBA
  change (∑ q : L.divisors, B G q * A q H) = if G = H then 1 else 0 at hentry
  have hnorm : (Nat.totient (L/g) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd hL hg)
      (Nat.pos_of_dvd_of_pos hg hL))).ne'
  have scaled : (Nat.totient (L/g) : ℝ) / L *
      (∑ q ∈ L.divisors, ramanujanSum q g * ramanujanSum q h / (q.totient : ℝ)) =
        if g = h then 1 else 0 := by
    calc
      _ = ∑ q : L.divisors, B G q * A q H := by
        rw [← Finset.sum_coe_sort L.divisors (fun q =>
          ramanujanSum q g * ramanujanSum q h / (q.totient : ℝ)), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        dsimp [B, G, A, H]
        field_simp [hL0, ht q] <;> ring
      _ = _ := by simpa only [G, H, Subtype.ext_iff] using hentry
  by_cases heq : g = h
  · rw [if_pos heq] at scaled ⊢
    field_simp [hL0, hnorm] at scaled ⊢
    linarith
  · rw [if_neg heq] at scaled ⊢
    exact (mul_eq_zero.mp scaled).resolve_left (div_ne_zero hnorm hL0)

private theorem dual_pairing (L g : ℕ) (hL : 0 < L) (hg : g ∈ L.divisors) (V : ℕ → ℝ) :
    (∑ q ∈ L.divisors, ramanujanSum q g * transform L V q / (q.totient : ℝ)) =
      V g * ((L : ℝ) / (Nat.totient (L/g) : ℝ)) := by
  unfold transform
  simp_rw [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  calc
    _ = ∑ h ∈ L.divisors, V h * (∑ q ∈ L.divisors,
        ramanujanSum q g * ramanujanSum q h / (q.totient : ℝ)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      calc
        _ = ∑ h ∈ L.divisors, V h * (if g = h then
            (L : ℝ) / (Nat.totient (L/g) : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [conductor_kernel L g h hL (Nat.dvd_of_mem_divisors hg) (Nat.dvd_of_mem_divisors hh)]
        _ = _ := by simp [hg]

theorem polarized_plancherel (L : ℕ) (hL : 0 < L) (W V : ℕ → ℝ) :
    (∑ q ∈ L.divisors, transform L W q * transform L V q / (q.totient : ℝ)) =
      ∑ g ∈ L.divisors, ((L : ℝ) / (Nat.totient (L/g) : ℝ)) * W g * V g := by
  calc
    _ = ∑ q ∈ L.divisors, ∑ g ∈ L.divisors, W g *
        (ramanujanSum q g * transform L V q / (q.totient : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [transform, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      rw [← Finset.mul_sum, dual_pairing L g hL hg]
      ring

theorem plancherel (L : ℕ) (hL : 0 < L) (W : ℕ → ℝ) :
    (∑ q ∈ L.divisors, transform L W q ^ 2 / (q.totient : ℝ)) =
      ∑ g ∈ L.divisors, ((L : ℝ) / (Nat.totient (L/g) : ℝ)) * W g ^ 2 := by
  simpa only [pow_two, mul_assoc] using polarized_plancherel L hL W W

theorem transform_inverse (L g : ℕ) (hL : 0 < L) (hg : g ∈ L.divisors) (W : ℕ → ℝ) :
    W g = (Nat.totient (L/g) : ℝ) / L *
      ∑ q ∈ L.divisors, ramanujanSum q g * transform L W q / (q.totient : ℝ) := by
  rw [dual_pairing L g hL hg]
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have ht : (Nat.totient (L/g) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd hL (Nat.dvd_of_mem_divisors hg))
      (Nat.pos_of_mem_divisors hg))).ne'
  field_simp [hL0, ht] <;> ring

end RiemannResearch.RH.Pareto.FullConductorRamanujan
