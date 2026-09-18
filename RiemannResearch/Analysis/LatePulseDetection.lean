import RiemannResearch.Analysis.SummableMultiples
import RiemannResearch.Analysis.DyadicTailRigidity

set_option autoImplicit false

/-!
Qualitative pulse detection from absolute summability and faster-than-1/n
decay. Source: user-provided three-generator strict-improvement argument;
this proof reuses the project's summable-multiples inversion and dyadic
rigidity in place of explicit Dirichlet inverse coefficients.
-/

open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis
noncomputable section

/-- Vanishing of every sufficiently late binary pulse transform forces the
underlying sequence to vanish on the same tail. The weighted limit is the
strict decay hypothesis; ordinary summability alone is insufficient. -/
theorem eq_zero_on_tail_of_binary_grouped
    {A : ℕ → ℝ} (hA : Summable A) (hA0 : A 0 = 0)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * A n) atTop (𝓝 0))
    (Y : ℕ)
    (hQ : ∀ d : ℕ, Y < d →
      (∑' j : ℕ, (A (d*(2*j+1)) - A (d*(2*(j+1))))) = 0)
    (d : ℕ) (hd : Y < d) : A d = 0 := by
  have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le Y) hd
  have hdinj : Function.Injective (fun n : ℕ => d*n) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hdpos hij
  have hs : Summable (fun n : ℕ => A (d*n)) := hA.comp_injective hdinj
  have hscale : ∀ n : ℕ, A (d*(2*n)) = A (d*n) / 2 := by
    apply dyadic_scaling_of_summable_binary_grouped hs
    · simpa using hA0
    · intro m hm
      have hdm : Y < d*m := hd.trans_le (by
        simpa using Nat.mul_le_mul_left d hm)
      change (∑' j : ℕ, (A (d*(m*(2*j+1))) - A (d*(m*(2*(j+1)))))) = 0
      simpa only [Nat.mul_assoc] using hQ (d*m) hdm
  have hidx : Tendsto (fun n : ℕ => d*n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (by simpa using Nat.mul_le_mul_right n hdpos)
  have hdreal : (d : ℝ) ≠ 0 := by positivity
  have hscaled : Tendsto (fun n : ℕ => (n : ℝ) * A (d*n)) atTop (𝓝 0) := by
    have ht := (hlim.comp hidx).const_mul ((d : ℝ)⁻¹)
    convert ht using 1
    · funext n
      simp only [Function.comp_apply, Nat.cast_mul]
      field_simp [hdreal]
    · simp
  have hz := DyadicTailRigidity.eq_zero_of_dyadic_scaling_of_weighted_tendsto
    (fun n : ℕ => A (d*n)) (fun n _ => hscale n) hscaled 1 (by decide)
  simpa using hz

/-- A nonzero tail value is detected by a sufficiently late binary pulse. -/
theorem exists_binary_grouped_ne_zero
    {A : ℕ → ℝ} (hA : Summable A) (hA0 : A 0 = 0)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * A n) atTop (𝓝 0))
    (Y : ℕ) (hne : ∃ d : ℕ, Y < d ∧ A d ≠ 0) :
    ∃ d : ℕ, Y < d ∧
      (∑' j : ℕ, (A (d*(2*j+1)) - A (d*(2*(j+1))))) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨d, hd, hne⟩ := hne
  exact hne (eq_zero_on_tail_of_binary_grouped hA hA0 hlim Y h d hd)

/-- A pulse correlation tending to zero cannot be dyadically constant on
the whole late tail unless it vanishes there. This selects the three-term
direction `H_d - H_(2*d)` directly. -/
theorem exists_ne_double_on_tail_of_tendsto_zero
    {P : ℕ → ℝ} (hlim : Tendsto P atTop (𝓝 0))
    (Y : ℕ) (hne : ∃ d : ℕ, Y < d ∧ P d ≠ 0) :
    ∃ d : ℕ, Y < d ∧ P d - P (2*d) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨d, hd, hPd⟩ := hne
  have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le Y) hd
  have hidx : Tendsto (fun n : ℕ => d*n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (by simpa using Nat.mul_le_mul_right n hdpos)
  have hscale : ∀ n : ℕ, 0 < n → P (d*(2*n)) = P (d*n) := by
    intro n hn
    have hdn : Y < d*n := hd.trans_le (by
      simpa using Nat.mul_le_mul_left d hn)
    have he := h (d*n) hdn
    have hid : 2*(d*n) = d*(2*n) := by ring
    rw [hid] at he
    linarith
  have hz := DyadicTailRigidity.eq_zero_of_dyadic_invariant_of_tendsto
    (fun n : ℕ => P (d*n)) hscale (hlim.comp hidx) 1 (by decide)
  exact hPd (by simpa using hz)

end
end RiemannResearch.Analysis
