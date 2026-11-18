import RiemannResearch.Analysis.ActualInghamGabrielSharp
import Mathlib.Tactic

/-!
# The undamped, comparable-cutoff Gabriel moment

Use physical damping `b = T⁻²`. The left and right Gaussian scales are
bounded by one, the observation factor is bounded below uniformly for
`H ≥ 2`, and fixed cutoff comparability bounds the right-edge Gamma term.
The one-log sharp edge then gives the undamped height and logarithmic powers.
-/
noncomputable section
open Set MeasureTheory
open RiemannResearch.Analysis.InghamInterpolation
namespace RiemannResearch.Analysis.InghamMollifier

private theorem undamped_profile {Q L R k A N l θ : ℝ} (hQ : 0 ≤ Q)
    (hL0 : 0 ≤ L) (hR0 : 0 ≤ R) (hk : 0 < k) (hA : 0 < A) (hN : 0 < N)
    (hl : 0 < l) (hθ : θ ∈ Icc (0:ℝ) 1)
    (hs : k * Q ^ ((3-θ)/4) ≤ (L ^ (3/4:ℝ))^(1-θ)*(R^(1/2:ℝ))^θ)
    (hL : L ≤ A*N*l^2) (hR : R ≤ A*l) :
    Q ≤ Real.exp (Real.log A + 2*|Real.log k|) *
      N^(3*(1-θ)/(3-θ)) * l^((6-4*θ)/(3-θ)) := by
  rcases hQ.eq_or_lt with hQ | hQ
  · subst Q
    positivity
  have hd : 0 < 3-θ := by linarith [hθ.2]
  have hL' := Real.rpow_le_rpow hL0 hL (by norm_num : 0≤(3/4:ℝ))
  have hR' := Real.rpow_le_rpow hR0 hR (by norm_num : 0≤(1/2:ℝ))
  have h := hs.trans (mul_le_mul
    (Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hL' (sub_nonneg.mpr hθ.2))
    (Real.rpow_le_rpow (Real.rpow_nonneg hR0 _) hR' hθ.1)
    (Real.rpow_nonneg (Real.rpow_nonneg hR0 _) _)
    (Real.rpow_nonneg (Real.rpow_nonneg (hL0.trans hL) _) _))
  have hAN : 0 < A*N*l^2 := by positivity
  have hAl : 0 < A*l := mul_pos hA hl
  have eL : Real.log (A*N*l^2) = Real.log A + Real.log N + 2*Real.log l := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hN.ne', Real.log_pow]
    norm_num
  have eR := Real.log_mul hA.ne' hl.ne'
  have hlog := Real.log_le_log (mul_pos hk (Real.rpow_pos_of_pos hQ _)) h
  rw [Real.log_mul hk.ne' (by positivity), Real.log_rpow hQ,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (Real.rpow_pos_of_pos hAN _),
    Real.log_rpow (Real.rpow_pos_of_pos hAl _), Real.log_rpow hAN, Real.log_rpow hAl,
    eL,eR] at hlog
  apply (Real.log_le_log_iff hQ (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp,Real.log_rpow hN,Real.log_rpow hl]
  apply (mul_le_mul_iff_right₀ (show 0 < (3-θ)/4 by positivity)).mp
  have heq : (3-θ)/4 * ((Real.log A + 2*|Real.log k| +
      (3*(1-θ)/(3-θ))*Real.log N) + ((6-4*θ)/(3-θ))*Real.log l) =
      (3-θ)/4*Real.log A + (3-θ)/2*|Real.log k| +
      3*(1-θ)/4*Real.log N + (6-4*θ)/4*Real.log l := by
    field_simp [hd.ne']
    ring
  rw [heq]
  have habs := abs_nonneg (Real.log k)
  have hmul := mul_nonneg (sub_nonneg.mpr hθ.2) habs
  nlinarith only [hlog, neg_abs_le (Real.log k), hmul]

private theorem normalized_scale_bounds {T p : ℝ} (hT : 0 < T) (hp : 1 ≤ p) :
    0 ≤ gabrielGaussianScale T (1/T^2) p ∧ gabrielGaussianScale T (1/T^2) p ≤ 1 := by
  have hp0 : 0 ≤ p := by linarith
  have hsq : (T*Real.sqrt (p*(1/T^2)))^2 = p := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hbase : 1 ≤ T*Real.sqrt (p*(1/T^2)) :=
    (sq_le_sq₀ zero_le_one (mul_nonneg hT.le (Real.sqrt_nonneg _))).mp (by rwa [one_pow, hsq])
  refine ⟨inv_nonneg.mpr (by linarith), ?_⟩
  simpa only [gabrielGaussianScale, ← one_div, div_one] using
    one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hbase

/-- Unconditional undamped moment for every comparable cutoff and every
observation interval `[H,T]`. The constant depends only on the two parameters
`δ,D` and is uniform in the observation line, height, and cutoff. -/
theorem exists_actual_gabriel_comparable_moment {δ D : ℝ} (hδ : 0 < δ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 2 ≤ X → ∀ {T H σ : ℝ},
      2 ≤ T → (X:ℝ) ≤ T → T ≤ D*(X:ℝ) → 2 ≤ H → H ≤ T → σ ∈ Icc (1/2:ℝ) 1 →
      let β := 1 + δ/Real.log (X:ℝ)
      let θ := (σ-1/2)/(β-1/2)
      let p := 4/(3-θ)
      (∫ t in H..T, stripMomentDensity (mollifiedError X) σ p t) ≤
        C*T^(3*(1-θ)/(3-θ))*(Real.log T)^((6-4*θ)/(3-θ)) := by
  obtain ⟨Cl,Cr,hCl,hCr,hsharp⟩ := exists_actual_gabriel_sharp_window hδ
  let B := 1 + δ/Real.log 2
  let M := 1 + (Real.log 2)⁻¹
  let G := Real.Gamma (3/2)
  let Al := Real.exp 1 * Cl * M^2 * 8
  let Ar := Real.exp (2*B^2) * Cr * (1+D*G)
  let A := max Al Ar
  let k := Real.exp (-1)/2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 0 < M := by dsimp [M]; positivity
  have hG : 0 < G := Real.Gamma_pos_of_pos (by norm_num)
  have hD0 : 0 ≤ D := by linarith
  have hAl : 0 < Al := by dsimp [Al]; positivity
  have hA : 0 < A := hAl.trans_le (le_max_left _ _)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨Real.exp (Real.log A + 2*|Real.log k|), Real.exp_pos _, ?_⟩
  intro X hX T H σ hT hXT hTX hH hHT hσ
  let β := 1 + δ/Real.log (X:ℝ)
  let θ := (σ-1/2)/(β-1/2)
  let p := 4/(3-θ)
  let b := 1/T^2
  let Q := ∫ t in H..T, stripMomentDensity (mollifiedError X) σ p t
  let aₗ := gabrielGaussianScale T b (4/3)
  let aᵣ := gabrielGaussianScale T b 2
  let L := Real.exp ((4/3)*b*(1/2)^2) * (Cl*T*(1+Real.log T)^2*(1+aₗ)^3)
  let R := Real.exp (2*b*β^2) * (Cr*Real.log X*(1+(T*aᵣ/(X:ℝ))*G))
  have ht : 0 < T := by linarith
  have hx2 : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hx : 0 < (X:ℝ) := by linarith
  have hlx := Real.log_pos (show 1 < (X:ℝ) by linarith)
  have hlt := Real.log_pos (show 1 < T by linarith)
  have hT2 := Real.log_le_log (by norm_num : 0<(2:ℝ)) hT
  have hX2 := Real.log_le_log (by norm_num : 0<(2:ℝ)) hx2
  have hXl := Real.log_le_log hx hXT
  have hβ : 1 < β := by dsimp [β]; linarith [div_pos hδ hlx]
  have hB : β ≤ B := by
    dsimp [β,B]
    exact add_le_add_right (div_le_div_of_nonneg_left hδ.le hlog2 hX2) 1
  have hd : 0 < β-1/2 := by linarith
  have hθ : θ ∈ Icc (0:ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr hσ.1) hd.le,
    (div_le_one hd).mpr (by linarith [hσ.2])⟩
  have hσe : 1/2+(β-1/2)*θ = σ := by
    calc 1/2+(β-1/2)*θ = 1/2+((σ-1/2)/(β-1/2))*(β-1/2) := by dsimp only [θ]; ring
         _ = _ := by rw [div_mul_cancel₀ _ hd.ne']; ring
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos ht)).mpr
    nlinarith
  have hLgamma := normalized_scale_bounds ht (by norm_num : (1:ℝ)≤4/3)
  have hRgamma := normalized_scale_bounds ht (by norm_num : (1:ℝ)≤2)
  have hal : 0 ≤ aₗ := hLgamma.1
  have har : 0 ≤ aᵣ := hRgamma.1
  have hal1 : aₗ ≤ 1 := hLgamma.2
  have har1 : aᵣ ≤ 1 := hRgamma.2
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hHT (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have h := hsharp hX hT hXT (by linarith : 1≤H) hHT hb hθ
  change Real.exp (b*((1/2+(β-1/2)*θ)^2-T^2))*(1-1/H)*
    (∫ t in H..T, stripMomentDensity (mollifiedError X) (1/2+(β-1/2)*θ) p t)^((3-θ)/4) ≤
    (L^(3/4:ℝ))^(1-θ)*(R^(1/2:ℝ))^θ at h
  rw [hσe] at h
  have hexplo : -1 ≤ b*(σ^2-T^2) := by
    have he : b*T^2=1 := by dsimp [b]; field_simp
    nlinarith [mul_nonneg hb.le (sq_nonneg σ)]
  have hhalf : (1/2:ℝ) ≤ 1-1/H := by
    linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hH]
  have hlow : k ≤ Real.exp (b*(σ^2-T^2))*(1-1/H) := by
    calc k = Real.exp (-1)*(1/2) := by dsimp [k]; ring
         _ ≤ _ := mul_le_mul (Real.exp_le_exp.mpr hexplo) hhalf (by norm_num) (Real.exp_pos _).le
  have hlscale : 1+Real.log T ≤ M*Real.log T := by
    have hm : 1 ≤ (Real.log 2)⁻¹ * Real.log T := by
      calc 1 = (Real.log 2)⁻¹ * Real.log 2 := (inv_mul_cancel₀ hlog2.ne').symm
           _ ≤ _ := mul_le_mul_of_nonneg_left hT2 (inv_nonneg.mpr hlog2.le)
    dsimp [M]
    linarith
  have hΓ : T*aᵣ/(X:ℝ) ≤ D := by
    apply (div_le_iff₀ hx).mpr
    exact (mul_le_of_le_one_right ht.le har1).trans hTX
  have hLB : L ≤ A*T*(Real.log T)^2 := by
    have he : (4/3)*b*(1/2)^2 ≤ (1:ℝ) := by linarith
    calc L ≤ Real.exp 1 * (Cl*T*(M*Real.log T)^2*(1+1)^3) := by
            dsimp [L]
            gcongr
          _ = Al*T*(Real.log T)^2 := by dsimp [Al]; ring
          _ ≤ _ := by gcongr; exact le_max_left _ _
  have hRB : R ≤ A*Real.log T := by
    have he : 2*b*β^2 ≤ 2*B^2 := by
      calc 2*b*β^2 ≤ 2*1*B^2 := by gcongr <;> linarith
           _ = _ := by ring
    calc R ≤ Real.exp (2*B^2) * (Cr*Real.log T*(1+D*G)) := by
            dsimp [R]
            gcongr
          _ = Ar*Real.log T := by dsimp [Ar]; ring
          _ ≤ _ := by gcongr; exact le_max_right _ _
  exact undamped_profile hQ hL0 hR0 hk hA ht hlt hθ
    ((mul_le_mul_of_nonneg_right hlow (Real.rpow_nonneg hQ _)).trans h) hLB hRB

/--
info: 'RiemannResearch.Analysis.InghamMollifier.exists_actual_gabriel_comparable_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_actual_gabriel_comparable_moment

end RiemannResearch.Analysis.InghamMollifier
