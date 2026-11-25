import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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

open scoped Pointwise

/-- Lower envelope of all increments of a fixed length. -/
def lowerIncrement (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  sInf (range fun k : ℕ => b (k + n) - b k)

/-- Negation exchanges the upper and lower increment envelopes. -/
theorem upperIncrement_neg_eq_neg_lowerIncrement (b : ℕ → ℝ) (n : ℕ) :
    upperIncrement (fun k => -b k) n = -lowerIncrement b n := by
  have hset : (range fun k : ℕ => -b (k + n) - -b k) =
      -(range fun k : ℕ => b (k + n) - b k) := by
    ext x
    rw [Set.mem_neg]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ring⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      change b (k + n) - b k = -x at hk
      linarith
  change sSup (range fun k : ℕ => -b (k + n) - -b k) =
    -sInf (range fun k : ℕ => b (k + n) - b k)
  rw [hset, Real.sSup_neg]

/-- The infimum of an increment over every starting point is superadditive. -/
theorem lowerIncrement_superadditive (b : ℕ → ℝ)
    (hb : ∀ n, BddBelow (range fun k : ℕ => b (k + n) - b k)) (m n : ℕ) :
    lowerIncrement b m + lowerIncrement b n ≤ lowerIncrement b (m + n) := by
  apply le_csInf (range_nonempty _)
  rintro _ ⟨k, rfl⟩
  have hm : lowerIncrement b m ≤ b (k + m) - b k :=
    csInf_le (hb m) (mem_range_self k)
  have hn : lowerIncrement b n ≤ b (k + m + n) - b (k + m) :=
    csInf_le (hb n) (mem_range_self (k + m))
  change lowerIncrement b m + lowerIncrement b n ≤ b (k + (m + n)) - b k
  rw [← Nat.add_assoc]
  linarith

/-- The normalized lower envelope converges to the supremum over positive lengths. -/
theorem lowerIncrement_fekete (b : ℕ → ℝ)
    (hb : ∀ n, BddBelow (range fun k : ℕ => b (k + n) - b k))
    (hu : BddAbove (range fun n : ℕ => lowerIncrement b n / n)) :
    Tendsto (fun n : ℕ => lowerIncrement b n / n) atTop
      (𝓝 (sSup ((fun n : ℕ => lowerIncrement b n / n) '' Ici 1))) := by
  let u : ℕ → ℝ := fun n => -lowerIncrement b n
  have hsub : Subadditive u := by
    intro m n
    change -lowerIncrement b (m + n) ≤ -lowerIncrement b m + -lowerIncrement b n
    linarith [lowerIncrement_superadditive b hb m n]
  obtain ⟨C, hC⟩ := hu
  have hbound : BddBelow (range fun n : ℕ => u n / n) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨n, rfl⟩
    change -C ≤ -lowerIncrement b n / (n : ℝ)
    rw [neg_div]
    exact neg_le_neg (hC (mem_range_self n))
  have hset : (fun n : ℕ => u n / n) '' Ici 1 =
      -((fun n : ℕ => lowerIncrement b n / n) '' Ici 1) := by
    ext x
    rw [Set.mem_neg]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, by simp only [u, neg_div, neg_neg]⟩
    · rintro ⟨n, hn, h⟩
      refine ⟨n, hn, ?_⟩
      change lowerIncrement b n / (n : ℝ) = -x at h
      change -lowerIncrement b n / (n : ℝ) = x
      rw [neg_div, h, neg_neg]
  have he : hsub.lim = -sSup ((fun n : ℕ => lowerIncrement b n / n) '' Ici 1) := by
    rw [Subadditive.lim, hset, Real.sInf_neg]
  have hlim := (hsub.tendsto_lim hbound).neg
  change Tendsto (fun n : ℕ => -(u n / (n : ℝ))) atTop (𝓝 (-hsub.lim)) at hlim
  rw [he, neg_neg] at hlim
  simpa only [u, neg_div, neg_neg] using hlim

/-- Fekete's infimum restricted to the nonzero exponents of a single base. -/
def powerRate (f : ℕ → ℝ) (a : ℕ) : ℝ :=
  sInf ((fun n : ℕ => f (a ^ n) / n) '' Ici 1)

/-- Fekete's lemma on the exponent sequence of a fixed base. -/
theorem tendsto_powerRate {f : ℕ → ℝ} {a : ℕ}
    (hs : Subadditive (fun n : ℕ => f (a ^ n)))
    (hb : BddBelow (range fun n : ℕ => f (a ^ n) / n)) :
    Tendsto (fun n : ℕ => f (a ^ n) / n) atTop (𝓝 (powerRate f a)) := by
  simpa only [powerRate, Subadditive.lim] using hs.tendsto_lim hb

/-- Fekete slopes add across a coprime product. The two exponent sequences
need only be subadditive with normalized values bounded below. -/
theorem powerRate_mul_of_coprime {f : ℕ → ℝ}
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (hsa : Subadditive (fun n : ℕ => f (a ^ n)))
    (hsb : Subadditive (fun n : ℕ => f (b ^ n)))
    (hla : BddBelow (range fun n : ℕ => f (a ^ n) / n))
    (hlb : BddBelow (range fun n : ℕ => f (b ^ n) / n)) :
    powerRate f (a * b) = powerRate f a + powerRate f b := by
  have hsplit (n : ℕ) : f ((a * b) ^ n) = f (a ^ n) + f (b ^ n) := by
    rw [mul_pow]
    exact hadd _ _ (pow_pos ha n) (pow_pos hb n) ((hc.pow_left n).pow_right n)
  have hs : Subadditive (fun n : ℕ => f ((a * b) ^ n)) := by
    intro i j
    change f ((a * b) ^ (i + j)) ≤ f ((a * b) ^ i) + f ((a * b) ^ j)
    rw [hsplit (i + j), hsplit i, hsplit j]
    calc
      f (a ^ (i + j)) + f (b ^ (i + j))
          ≤ (f (a ^ i) + f (a ^ j)) + (f (b ^ i) + f (b ^ j)) :=
        add_le_add (hsa i j) (hsb i j)
      _ = _ := by ring
  have hl : BddBelow (range fun n : ℕ => f ((a * b) ^ n) / n) := by
    obtain ⟨A, hA⟩ := hla
    obtain ⟨B, hB⟩ := hlb
    refine ⟨A + B, ?_⟩
    rintro _ ⟨n, rfl⟩
    change A + B ≤ f ((a * b) ^ n) / (n : ℝ)
    rw [hsplit n, add_div]
    exact add_le_add (hA (mem_range_self n)) (hB (mem_range_self n))
  have hab : Tendsto (fun n : ℕ => f ((a * b) ^ n) / n) atTop
      (𝓝 (powerRate f a + powerRate f b)) := by
    apply ((tendsto_powerRate hsa hla).add (tendsto_powerRate hsb hlb)).congr
    intro n
    rw [hsplit n, add_div]
  exact tendsto_nhds_unique (tendsto_powerRate hs hl) hab

/-- Reindexing a base by a positive power multiplies its Fekete slope
by the exponent. -/
theorem powerRate_pow {f : ℕ → ℝ} {a m : ℕ} (hm : 0 < m)
    (hs : Subadditive (fun n : ℕ => f (a ^ n)))
    (hb : BddBelow (range fun n : ℕ => f (a ^ n) / n)) :
    powerRate f (a ^ m) = (m : ℝ) * powerRate f a := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hscale (n : ℕ) :
      f ((a ^ m) ^ n) / (n : ℝ) = (m : ℝ) * (f (a ^ (m * n)) / (m * n : ℕ)) := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [← pow_mul, Nat.cast_mul]
      field_simp [hmR, Nat.cast_ne_zero.mpr hn]
  have hs' : Subadditive (fun n : ℕ => f ((a ^ m) ^ n)) := by
    intro i j
    change f ((a ^ m) ^ (i + j)) ≤ f ((a ^ m) ^ i) + f ((a ^ m) ^ j)
    simpa only [← pow_mul, Nat.mul_add] using hs (m * i) (m * j)
  have hb' : BddBelow (range fun n : ℕ => f ((a ^ m) ^ n) / n) := by
    obtain ⟨L, hL⟩ := hb
    refine ⟨(m : ℝ) * L, ?_⟩
    rintro _ ⟨n, rfl⟩
    change (m : ℝ) * L ≤ f ((a ^ m) ^ n) / n
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hL (mem_range_self (m * n))) (Nat.cast_nonneg m)
  have hmnat : 1 ≤ m := hm
  have hidx : Tendsto (fun n : ℕ => m * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      change n ≤ m * n
      simpa only [one_mul] using Nat.mul_le_mul_right n hmnat) tendsto_id
  have hlim : Tendsto (fun n : ℕ => f ((a ^ m) ^ n) / n) atTop
      (𝓝 ((m : ℝ) * powerRate f a)) := by
    apply (((tendsto_powerRate hs hb).comp hidx).const_mul (m : ℝ)).congr
    intro n
    exact (hscale n).symm
  exact tendsto_nhds_unique (tendsto_powerRate hs' hb') hlim

/-- On a logarithmically rigid function the exponent law holds already at zero. -/
theorem pow_value_of_log {f : ℕ → ℝ} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) {a : ℕ} (ha : 0 < a)
    (n : ℕ) : f (a ^ n) = (n : ℝ) * f a := by
  rw [hlog _ (pow_pos ha n), hlog _ ha, Nat.cast_pow, Real.log_pow]
  ring

/-- At every positive exponent the normalized value already equals its limit. -/
theorem pow_div_exponent_of_log {f : ℕ → ℝ} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) {a n : ℕ}
    (ha : 0 < a) (hn : 0 < n) : f (a ^ n) / n = f a := by
  rw [pow_value_of_log hlog ha]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

theorem tendsto_pow_div_exponent_of_log {f : ℕ → ℝ} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) {a : ℕ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => f (a ^ n) / n) atTop (𝓝 (f a)) := by
  apply (tendsto_const_nhds (x := f a)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (pow_div_exponent_of_log hlog ha hn).symm

/-- On a logarithmically rigid function the Fekete slope recovers the
one-step value, including its sign. -/
theorem powerRate_eq_of_log {f : ℕ → ℝ} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) {a : ℕ} (ha : 0 < a) :
    powerRate f a = f a := by
  have hs : Subadditive (fun n : ℕ => f (a ^ n)) := by
    intro m n
    simp only [pow_value_of_log hlog ha, Nat.cast_add, add_mul, le_refl]
  have hb : BddBelow (range fun n : ℕ => f (a ^ n) / n) := by
    refine ⟨min 0 (f a), ?_⟩
    rintro _ ⟨n, rfl⟩
    change min 0 (f a) ≤ f (a ^ n) / (n : ℝ)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [pow_div_exponent_of_log hlog ha hn]
      exact min_le_right _ _
  exact tendsto_nhds_unique (tendsto_powerRate hs hb) (tendsto_pow_div_exponent_of_log hlog ha)

/-- Every base greater than one gives the same logarithmic coefficient. -/
theorem powerRate_div_log_eq_of_log {f : ℕ → ℝ} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) {a : ℕ} (ha : 1 < a) :
    powerRate f a / Real.log (a : ℝ) = c := by
  have ha' : 0 < a := Nat.zero_lt_of_lt ha
  apply (div_eq_iff (Real.log_pos (by exact_mod_cast ha)).ne').2
  exact (powerRate_eq_of_log hlog ha').trans (hlog a ha')

theorem log_normalization_by_powerRate {f : ℕ → ℝ}
    (hlog : ∃ c : ℝ, ∀ n : ℕ, 0 < n → f n = c * Real.log (n : ℝ)) :
    ∀ n : ℕ, 0 < n → f n = (powerRate f 2 / Real.log 2) * Real.log (n : ℝ) := by
  obtain ⟨c, hc⟩ := hlog
  have hs : powerRate f 2 / Real.log 2 = c :=
    powerRate_div_log_eq_of_log hc (by decide : 1 < 2)
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
