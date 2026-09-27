import RiemannResearch.Analysis.IncreasingAbelConvergence

/-! Finite head/tail splitting of the centered increasing Abel error.
This allows arbitrarily large fixed logarithmic amplification exponents
without requiring an integrable derivative envelope with exponent below one. -/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Split the *centered prefix errors*, not the absolute series terms.
The first J weight increments cost only B (w J - 1); the remaining
increments and the terminal term cost at most 2 w N R. -/
theorem signedVector_increasing_weight_split_le
    (u : ℕ → E) (w : ℕ → ℝ) (f : E)
    (hw : Monotone w) (hwn : ∀ n, 0 ≤ w n) (hwzero : w 0 = 1)
    (N J : ℕ) (hJN : J ≤ N) (B R : ℝ) (hR : 0 ≤ R)
    (hglobal : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ B)
    (htail : ∀ n, J ≤ n → ‖signedVectorPrefix u (n + 1) - f‖ ≤ R) :
    ‖(∑ n ∈ Finset.range (N + 1), w n • u n) - f‖ ≤
      B * (w J - 1) + 2 * w N * R := by
  let Q : ℕ → ℝ := fun n => if n ≤ J then B else R
  have hQ : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ Q (n + 1) := by
    intro n
    by_cases hn : n + 1 ≤ J
    · simpa [Q, hn] using hglobal n
    · simpa [Q, hn] using htail n (by omega)
  have hterminal : Q (N + 1) = R := by
    simp [Q, show ¬N + 1 ≤ J by omega]
  have hhead :
      (∑ n ∈ Finset.range J, (w (n + 1) - w n) * Q (n + 1)) =
        B * (w J - w 0) := by
    calc
      _ = ∑ n ∈ Finset.range J, (w (n + 1) - w n) * B := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' : n + 1 ≤ J := by have := Finset.mem_range.mp hn; omega
        simp [Q, hn']
      _ = (∑ n ∈ Finset.range J, (w (n + 1) - w n)) * B :=
        (Finset.sum_mul _ _ _).symm
      _ = (w J - w 0) * B := by rw [Finset.sum_range_sub]
      _ = _ := by ring
  have hNsum : J + (N - J) = N := by omega
  have htailSum :
      (∑ n ∈ Finset.range (N - J),
        (w (J + n + 1) - w (J + n)) * Q (J + n + 1)) =
        R * (w N - w J) := by
    calc
      _ = ∑ n ∈ Finset.range (N - J),
          (w (J + n + 1) - w (J + n)) * R := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [Q, show ¬J + n + 1 ≤ J by omega]
      _ = (∑ n ∈ Finset.range (N - J),
          (w (J + n + 1) - w (J + n))) * R :=
        (Finset.sum_mul _ _ _).symm
      _ = (w (J + (N - J)) - w J) * R := by
        have he := Finset.sum_range_sub (fun n => w (J + n)) (N - J)
        simpa only [Nat.add_assoc, Nat.add_zero] using congrArg (fun x : ℝ => x * R) he
      _ = R * (w N - w J) := by rw [hNsum]; ring
  have hsum :
      (∑ n ∈ Finset.range N, (w (n + 1) - w n) * Q (n + 1)) =
        B * (w J - w 0) + R * (w N - w J) := by
    have he := Finset.sum_range_add
      (fun n => (w (n + 1) - w n) * Q (n + 1)) J (N - J)
    rw [hNsum] at he
    rw [he, hhead, htailSum]
  have hb := signedVector_increasing_weight_residual_le u w f Q hw hwn hQ N
  rw [hwzero, one_smul, hterminal, hsum, hwzero] at hb
  have hnonneg : 0 ≤ w J * R := mul_nonneg (hwn J) hR
  nlinarith only [hb, hnonneg]

/-- A moving cutoff can make the early weights close to one while the
endpoint tail error absorbs an unbounded terminal weight. Neither absolute
summability nor a fixed upper bound on the terminal weights is assumed. -/
theorem signedVector_increasing_weights_split_tendsto
    (u : ℕ → E) (f : E) (B : ℝ) (R : ℕ → ℝ)
    (hR : ∀ J, 0 ≤ R J)
    (hglobal : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ B)
    (htail : ∀ J n, J ≤ n → ‖signedVectorPrefix u (n + 1) - f‖ ≤ R J)
    (w : ℕ → ℕ → ℝ) (hw : ∀ j, Monotone (w j))
    (hwn : ∀ j n, 0 ≤ w j n) (hwzero : ∀ j, w j 0 = 1)
    (M J : ℕ → ℕ) (hJM : ∀ᶠ j in atTop, J j ≤ M j)
    (hhead : Tendsto (fun j => w j (J j)) atTop (𝓝 1))
    (htailWeight : Tendsto (fun j => w j (M j) * R (J j)) atTop (𝓝 0)) :
    Tendsto (fun j => ∑ n ∈ Finset.range (M j + 1), w j n • u n)
      atTop (𝓝 f) := by
  have hbudget : Tendsto
      (fun j => B * (w j (J j) - 1) + 2 * w j (M j) * R (J j))
      atTop (𝓝 0) := by
    have h := ((hhead.sub_const 1).const_mul B).add (htailWeight.const_mul 2)
    simpa only [sub_self, mul_zero, zero_add, mul_assoc] using h
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp hbudget η hη
  obtain ⟨K₂, hK₂⟩ := Filter.eventually_atTop.mp hJM
  refine ⟨max K₁ K₂, fun j hj => ?_⟩
  rw [dist_eq_norm]
  have hbound := signedVector_increasing_weight_split_le u (w j) f
    (hw j) (hwn j) (hwzero j) (M j) (J j)
    (hK₂ j ((le_max_right _ _).trans hj)) B (R (J j)) (hR (J j))
    hglobal (htail (J j))
  apply hbound.trans_lt
  have hsmall := hK₁ j ((le_max_left _ _).trans hj)
  rw [dist_zero_right, Real.norm_eq_abs] at hsmall
  exact lt_of_le_of_lt (le_abs_self _) hsmall

end RiemannResearch.Analysis
