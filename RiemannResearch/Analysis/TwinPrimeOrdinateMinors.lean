/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.PrimeOrdinateMinors
import Mathlib.Data.Nat.Prime.Basic

/-!
# Summing consecutive-ordinate determinants over the twin-prime columns

The indices in each finite block enumerate all pairs (p,p+2) with both
entries prime and lower entry in the stated interval. The elementary
residue restriction and a telescoping reciprocal-square majorant give an
explicit uniform tail. No counting asymptotic for twin primes is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeOrdinateMinors

/-- Uniform bound for every positive starting column and additive shift. -/
theorem shifted_tripleMinor_le {p : ℕ} (k : ℕ) (hp : 0 < p) (s : ℝ)
    {g h : ℝ} (hg : 0 ≤ g) (hh : 0 ≤ h) :
    ‖tripleMinor p (p+k) s (s+g) (s+g+h)‖ ≤ ((k : ℝ)/p)^3 * (g*h*(g+h)) := by
  have h₀ := (tripleMinor_defect p (p+k) s hg hh).1
  calc
    _ ≤ logDistance p (p+k)^3 * (g*h*(g+h)) := by linarith only [h₀]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (logDistance_nonneg p (p+k)) (logDistance_add_le p k hp) 3)
      (mul_nonneg (mul_nonneg hg hh) (add_nonneg hg hh))

theorem twin_lower_mod_six {p : ℕ} (hp : p.Prime) (hq : (p+2).Prime) (hp3 : 3 < p) :
    p % 6 = 5 := by
  have h₂ : ¬ 2 ∣ p := by
    intro hd; rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  have h₃ : ¬ 3 ∣ p := by
    intro hd; rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  have hq₃ : ¬ 3 ∣ p+2 := by
    intro hd; rcases (Nat.dvd_prime hq).mp hd with h | h <;> omega
  have he := Nat.mod_add_div p 6
  by_contra hbad
  have hr : p%6=0 ∨ p%6=1 ∨ p%6=2 ∨ p%6=3 ∨ p%6=4 := by omega
  rcases hr with h | h | h | h | h
  · exact h₂ ⟨3*(p/6), by omega⟩
  · exact hq₃ ⟨2*(p/6)+1, by omega⟩
  · exact h₂ ⟨3*(p/6)+1, by omega⟩
  · exact h₃ ⟨2*(p/6)+1, by omega⟩
  · exact h₂ ⟨3*(p/6)+2, by omega⟩

/-- The residue class of all lower twin primes larger than three. -/
def sixBase (K j : ℕ) : ℕ := 6*(K+j)+5

/-- The candidate at index j is sixBase K (j+1). Both primality tests are exact. -/
def twinIndices (K L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun j => (sixBase K (j+1)).Prime ∧ (sixBase K (j+1)+2).Prime)

theorem twinIndices_exact {K L p : ℕ} :
    (∃ j ∈ twinIndices K L, sixBase K (j+1) = p) ↔
      sixBase K 0 < p ∧ p ≤ sixBase K L ∧ p.Prime ∧ (p+2).Prime := by
  simp only [twinIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨j, ⟨hj, hp, hq⟩, rfl⟩
    exact ⟨by unfold sixBase; omega, by unfold sixBase; omega, hp, hq⟩
  · rintro ⟨hlo, hhi, hp, hq⟩
    unfold sixBase at hlo hhi
    have hr := twin_lower_mod_six hp hq (by omega)
    let j := p / 6 - K - 1
    have hej : sixBase K (j+1) = p := by unfold sixBase; dsimp [j]; omega
    exact ⟨j, ⟨by dsimp [j]; omega, by rwa [hej], by rwa [hej]⟩, hej⟩

/-- Exact slack in the reciprocal-square majorant on the residue class. -/
theorem twin_mesh_remainder {x : ℝ} (hx : 0 < x) :
    (2/3 : ℝ) * (1/x^2 - 1/(x+6)^2) - (2/(x+6))^3 =
      72*(2+x)/(x^2*(x+6)^3) := by
  have hx₆ : 0 < x+6 := by linarith
  field_simp [hx.ne', hx₆.ne']
  ring

/-- Every twin prime with lower entry in (6K+5,6(K+L)+5] contributes once.
The right side stays bounded as L grows and decreases quadratically in K. -/
theorem twin_block_triple_bound (K L : ℕ) (s : ℝ) {g h : ℝ} (hg : 0 ≤ g) (hh : 0 ≤ h) :
    (∑ j ∈ twinIndices K L, ‖tripleMinor (sixBase K (j+1)) (sixBase K (j+1)+2)
      s (s+g) (s+g+h)‖) ≤
      (2/3 : ℝ) * (1/(sixBase K 0 : ℝ)^2 - 1/(sixBase K L : ℝ)^2) * (g*h*(g+h)) := by
  let F (j : ℕ) : ℝ := 1/(sixBase K j : ℝ)^2
  let v (j : ℕ) := ‖tripleMinor (sixBase K (j+1)) (sixBase K (j+1)+2) s (s+g) (s+g+h)‖
  let A := g*h*(g+h)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hg hh) (add_nonneg hg hh)
  have step (j : ℕ) : v j ≤ ((2/3 : ℝ) * (F j - F (j+1))) * A := by
    have hx : 0 < sixBase K j := by unfold sixBase; omega
    have hn : sixBase K (j+1) = sixBase K j + 6 := by unfold sixBase; omega
    have hn' : (sixBase K (j+1) : ℝ) = (sixBase K j : ℝ) + 6 := by exact_mod_cast hn
    have hx' : (0 : ℝ) < sixBase K j := by exact_mod_cast hx
    have hr := twin_mesh_remainder hx'
    have hpos : 0 ≤ 72*(2+(sixBase K j : ℝ)) /
        ((sixBase K j : ℝ)^2*((sixBase K j : ℝ)+6)^3) := by positivity
    have h₁ := shifted_tripleMinor_le 2 (p := sixBase K (j+1)) (by omega) s hg hh
    apply h₁.trans
    apply mul_le_mul_of_nonneg_right _ hA
    dsimp only [F]
    rw [hn']
    norm_num only [Nat.cast_ofNat]
    linarith only [hr, hpos]
  have htel : (∑ j ∈ Finset.range L, (F j - F (j+1))) = F 0 - F L := by
    rw [Finset.sum_sub_distrib]
    linarith only [Finset.sum_range_succ F L, Finset.sum_range_succ' F L]
  calc
    (∑ j ∈ twinIndices K L, v j) ≤ ∑ j ∈ Finset.range L, v j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ j ∈ Finset.range L, ((2/3 : ℝ) * (F j - F (j+1))) * A :=
      Finset.sum_le_sum (fun j _ => step j)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, htel]

end RiemannResearch.Analysis.PrimeOrdinateMinors
