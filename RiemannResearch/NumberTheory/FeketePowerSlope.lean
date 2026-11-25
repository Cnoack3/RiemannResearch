import Mathlib.Analysis.Subadditive
import RiemannResearch.NumberTheory.DyadicAdditiveRigidity

/-! # Fekete slopes along multiplicative powers

The additive index is the exponent. Mathlib's Fekete lemma gives the infimum
formula. Coprime additivity and vanishing dyadic variation supply logarithmic
rigidity by the Kátai–Wirsing argument in `DyadicAdditiveRigidity`.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory

/-- Upper envelope of the increments of length `n` of a real sequence. -/
def upperIncrement (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup (range fun k : ℕ => b (k + n) - b k)

theorem upperIncrement_subadditive (b : ℕ → ℝ)
    (hb : ∀ n, BddAbove (range fun k : ℕ => b (k + n) - b k)) :
    Subadditive (upperIncrement b) := by
  intro m n
  apply csSup_le (range_nonempty _)
  rintro _ ⟨k, rfl⟩
  have hm : b (k + m) - b k ≤ upperIncrement b m :=
    le_csSup (hb m) (mem_range_self k)
  have hn : b (k + m + n) - b (k + m) ≤ upperIncrement b n :=
    le_csSup (hb n) (mem_range_self (k + m))
  change b (k + (m + n)) - b k ≤ upperIncrement b m + upperIncrement b n
  rw [← Nat.add_assoc]
  linarith

/-- Fekete's upper-envelope limit. Applying it to the negative sequence
gives the corresponding lower-envelope limit. -/
theorem upperIncrement_fekete (b : ℕ → ℝ)
    (hb : ∀ n, BddAbove (range fun k : ℕ => b (k + n) - b k))
    (hl : BddBelow (range fun n : ℕ => upperIncrement b n / n)) :
    Tendsto (fun n : ℕ => upperIncrement b n / n) atTop
      (𝓝 ((upperIncrement_subadditive b hb).lim)) :=
  (upperIncrement_subadditive b hb).tendsto_lim hl

/-- Fekete's infimum restricted to the nonzero exponents of a single base. -/
def powerRate (f : ℕ → ℝ) (a : ℕ) : ℝ :=
  sInf ((fun n : ℕ => f (a ^ n) / n) '' Ici 1)

/-- On a logarithmically rigid function the Fekete slope recovers the
one-step value, including its sign. -/
theorem powerRate_eq_of_log {f : ℕ → ℝ} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) {a : ℕ} (ha : 0 < a) :
    powerRate f a = f a := by
  have hr (n : ℕ) : f (a ^ n) = (n : ℝ) * f a := by
    rw [hlog _ (pow_pos ha n), hlog _ ha, Nat.cast_pow, Real.log_pow]
    ring
  have hs : Subadditive (fun n : ℕ => f (a ^ n)) := by
    intro m n
    simp only [hr, Nat.cast_add, add_mul, le_refl]
  have hd (n : ℕ) (hn : n ≠ 0) : f (a ^ n) / n = f a := by
    rw [hr]
    field_simp [Nat.cast_ne_zero.mpr hn] <;> ring
  have hb : BddBelow (range fun n : ℕ => f (a ^ n) / n) := by
    refine ⟨min 0 (f a), ?_⟩
    rintro _ ⟨n, rfl⟩
    change min 0 (f a) ≤ f (a ^ n) / (n : ℝ)
    by_cases hn : n = 0
    · subst n
      simp
    · rw [hd n hn]
      exact min_le_right _ _
  have hlim : Tendsto (fun n : ℕ => f (a ^ n) / n) atTop (𝓝 (f a)) := by
    apply (tendsto_const_nhds (x := f a)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hd n hn.ne').symm
  simpa only [powerRate, Subadditive.lim] using tendsto_nhds_unique (hs.tendsto_lim hb) hlim

theorem log_normalization_by_powerRate {f : ℕ → ℝ}
    (hlog : ∃ c : ℝ, ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) :
    ∀ n : ℕ, 0 < n → f n = (powerRate f 2 / Real.log 2) * Real.log (n : ℝ) := by
  obtain ⟨c, hc⟩ := hlog
  have htwo : powerRate f 2 = c * Real.log 2 :=
    (powerRate_eq_of_log hc (by decide : 0 < 2)).trans (hc 2 (by decide))
  have hs : powerRate f 2 / Real.log 2 = c :=
    (div_eq_iff (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne').2 htwo
  simpa only [hs] using hc

/-- Coprime additivity is sufficient under the dyadic variation hypothesis,
even though successive powers of the same integer need not be coprime. -/
theorem powerRate_of_coprime_additive_of_dyadic_variation (f : ℕ → ℝ)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a*b) = f a + f b)
    (hv : Tendsto (fun M : ℕ =>
      (∑ i ∈ Finset.range M, |f (M+i+1) - f (M+i)|) / (M : ℝ)) atTop (𝓝 0)) :
    ∀ a : ℕ, 0 < a → powerRate f a = f a := by
  obtain ⟨c, hc⟩ := eq_log_of_coprime_additive_of_dyadic_variation f hadd hv
  exact fun _ ha => powerRate_eq_of_log hc ha

end RiemannResearch.NumberTheory
