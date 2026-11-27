import RiemannResearch.CategoryTheory.ObservedModeFibre
import RiemannResearch.RH.QHilbertConvergence

/-! # The observed Gram of shifted Dirichlet characters

Equation (6) of the supplied CRT character note.  The complex coordinate
uses the physical real Hilbert projections on real and imaginary parts.
All positive shifts split into smooth and rough factors at each cutoff. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.ObservedCharacterGram
open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoProbability
open ObservedModeFibre PrimeValuationCovariance ValuationCharacterGram DivisibilityCharacterGram

/-- Smooth shifts have all their prime factors in the revealed set. -/
def Smooth (b a : ℕ) := ∃ e : ℕ, a ∣ (primorial b)^e

private theorem smooth_site (b : ℕ) (n : ℕ+) : Smooth b (smoothSite b n) := by
  apply (Nat.exists_dvd_pow_iff (smoothSite b n).pos.ne' (primorial_ne_zero _)).mpr
  intro p hp
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
    (primorial_covers b p (Nat.prime_of_mem_primeFactors hp)).2 ((smoothSite_fibre b n).1 p hp),
    primorial_ne_zero b⟩

/-- The hypotheses for the explicit Gram apply to every positive shift. -/
theorem exists_cutoff_split (b : ℕ) (g : ℕ+) :
    ∃ a d : ℕ+, (g : ℕ) = (a : ℕ)*(d : ℕ) ∧ Smooth b a ∧ (d : ℕ).Coprime (primorial b) := by
  obtain ⟨d, he, hr⟩ := (sameFibre_iff_rough_multiple b (smoothSite b g) g
    (smoothSite_fibre b g).1).mp (smoothSite_fibre b g).2
  refine ⟨smoothSite b g,d,he,smooth_site b g,?_⟩
  by_contra h
  obtain ⟨p,hp,hpd,hpR⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hr p hp ((primorial_covers b p hp).1 hpR) hpd

private theorem lcm_smooth {b a h : ℕ} (ha : Smooth b a) (hh : Smooth b h) :
    Smooth b (Nat.lcm a h) := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨d, hd⟩ := hh
  refine ⟨e+d,?_⟩
  rw [pow_add]
  exact Nat.lcm_dvd (he.trans (dvd_mul_right _ _)) (hd.trans (dvd_mul_left _ _))

private def component {q : ℕ} (g : ℕ) (χ : DirichletCharacter ℂ q) (L : ℂ →L[ℝ] ℝ) : QHilbert :=
  (exists_mode_component g χ L).choose

private theorem component_apply {q : ℕ} (g : ℕ) (χ : DirichletCharacter ℂ q) (L : ℂ →L[ℝ] ℝ)
    (n : ℕ) (hn : 0 < n) : qSequence (component g χ L) n = L (mode g χ n) :=
  (exists_mode_component g χ L).choose_spec n hn

private def value (x y : QHilbert) (n : ℕ) : ℂ :=
  (qSequence x n : ℂ) + (qSequence y n : ℂ) * Complex.I

/-- Projection of both components onto the actual closed valuation-fibre space. -/
def observedValue {q : ℕ} (b g : ℕ) (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  value ((observed b).starProjection (component g χ Complex.reCLM))
    ((observed b).starProjection (component g χ Complex.imCLM))

private theorem split_component {q : ℕ} (b : ℕ) (n : ℕ+) (a d : ℕ+) (ha : Smooth b a)
    (hd : (d : ℕ).Coprime (primorial b)) (χ : DirichletCharacter ℂ q) (L : ℂ →L[ℝ] ℝ) :
    qSequence ((observed b).starProjection (component ((a : ℕ)*d) χ L)) n =
      L (mode a χ (smoothSite b n) / (d : ℂ)^2 * tailCharacterProduct b χ) := by
  let s := smoothSite b n
  let R := primorial b
  have hs := smoothSite_fibre b n
  have hz : (d : ℕ).Coprime (s : ℕ) := by
    obtain ⟨e, he⟩ := smooth_site b n
    exact (hd.pow_right e).coprime_dvd_right he
  have he := (mem_observed b _).mp ((observed b).starProjection_apply_mem
    (component ((a : ℕ)*d) χ L)) s n hs.2
  rw [← he, observed_mode_component (primorial_covers b) s hs.1 _ (Nat.mul_pos a.pos d.pos) χ L _
    (component_apply _ χ L), ← arbitrary_mode_rough_ratio R ((a : ℕ)*d) (s : ℕ)
    (Nat.mul_pos a.pos d.pos) χ]
  rw [rough_mode_split R a d s 2 a.pos d.pos ha hz hd χ, mul_div_assoc]
  simp only [tailCharacterProduct, primeCharacterFactor, primorial_roughRatio_tprod, R, s]

theorem observedValue_split {q : ℕ} (b : ℕ) (n : ℕ+) (a d : ℕ+) (ha : Smooth b a)
    (hd : (d : ℕ).Coprime (primorial b)) (χ : DirichletCharacter ℂ q) :
    observedValue b ((a : ℕ)*d) χ n =
      mode a χ (smoothSite b n) / (d : ℂ)^2 * tailCharacterProduct b χ := by
  simp only [observedValue, value, split_component b n a d ha hd,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.re_add_im]

private theorem value_mean (x y : QHilbert) :
    (∑' n : ℕ, (positiveQWeight n : ℂ) * value x y n) =
      (inner ℝ qOne x : ℂ) + (inner ℝ qOne y : ℂ) * Complex.I := by
  simp only [qOne_inner_weighted, Complex.ofReal_tsum, ← tsum_mul_right]
  rw [← Summable.tsum_add (Complex.summable_ofReal.mpr (qFirstMoment_summable x))
    ((Complex.summable_ofReal.mpr (qFirstMoment_summable y)).mul_right Complex.I)]
  apply tsum_congr
  intro n
  simp [value, mul_add, mul_assoc]

private theorem observed_preserves_mean (b : ℕ) (x : QHilbert) :
    inner ℝ qOne ((observed b).starProjection x) = inner ℝ qOne x := by
  have h : qOne ∈ observed b := (mem_observed b _).2 fun i j _ => by
    simp [qSequence_qOne, qOneSequence, i.pos.ne', j.pos.ne']
  have he := (observed b).sub_starProjection_mem_orthogonal x qOne h
  rw [inner_sub_right] at he
  linarith

private theorem mode_mean {q : ℕ} (l : ℕ+) (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, (positiveQWeight n : ℂ) * mode l χ n) =
      (tailCharacterProduct 0 χ) / (l : ℂ)^2 := by
  have hi : Function.Injective (fun k : ℕ => (l : ℕ)*k) := fun _ _ h => Nat.eq_of_mul_eq_mul_left l.pos h
  have hs : Function.support (fun n : ℕ => (positiveQWeight n : ℂ)*mode l χ n) ⊆
      Set.range (fun k : ℕ => (l : ℕ)*k) := by
    intro n hn
    by_cases h : (l : ℕ) ∣ n
    · obtain ⟨k,rfl⟩ := h
      exact ⟨k,rfl⟩
    · exact (hn (by simp [mode,h])).elim
  rw [← hi.tsum_eq hs, ← qCharacterMean_eq_fullProduct χ, ← tsum_div_const]
  apply tsum_congr
  intro k
  simp [positiveQWeight, mode,
    mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem observedValue_mean {q : ℕ} (b : ℕ) (l : ℕ+) (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, (positiveQWeight n : ℂ) * observedValue b l χ n) =
      tailCharacterProduct 0 χ / (l : ℂ)^2 := by
  unfold observedValue
  rw [value_mean, observed_preserves_mean, observed_preserves_mean, ← value_mean, ← mode_mean l χ]
  apply tsum_congr
  intro n
  by_cases h : n = 0
  · simp [h, positiveQWeight]
  · simp [value,component_apply _ _ _ n (Nat.pos_of_ne_zero h),Complex.re_add_im]

/-- The genuine product character at the least common multiple of the levels. -/
def joint {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    DirichletCharacter ℂ (Nat.lcm q r) :=
  χ.changeLevel (Nat.dvd_lcm_left q r) * star (ψ.changeLevel (Nat.dvd_lcm_right q r))

theorem joint_apply {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    joint χ ψ n = χ n * star (ψ n) := by
  by_cases hu : n.Coprime (Nat.lcm q r)
  · let hv := ZMod.unitOfCoprime n hu
    have h1 := χ.changeLevel_eq_cast_of_dvd (Nat.dvd_lcm_left q r) hv
    have h2 := ψ.changeLevel_eq_cast_of_dvd (Nat.dvd_lcm_right q r) hv
    simp only [hv,ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_left q r)] at h1
    simp only [hv,ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_right q r)] at h2
    rw [joint,MulChar.mul_apply,MulChar.star_apply,h1,h2]
  · rw [MulChar.map_nonunit _ (fun h => hu ((ZMod.isUnit_iff_coprime n _).1 h))]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hu ((hq.mul_right hr).coprime_dvd_right (Nat.lcm_dvd_mul q r))
      simp [MulChar.map_nonunit ψ (fun h => hr ((ZMod.isUnit_iff_coprime n r).1 h))]
    · simp [MulChar.map_nonunit χ (fun h => hq ((ZMod.isUnit_iff_coprime n q).1 h))]

private theorem site_product {q r : ℕ} (a h : ℕ+) (n : ℕ) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    mode a χ n * star (mode h ψ n) =
      (χ ((Nat.lcm a h/a : ℕ) : ZMod q) * star (ψ ((Nat.lcm a h/h : ℕ) : ZMod r))) *
      mode (Nat.lcm a h) (joint χ ψ) n := by
  by_cases hn : Nat.lcm a h ∣ n
  · obtain ⟨k,rfl⟩ := hn
    let s := Nat.lcm (a : ℕ) (h : ℕ)
    have hmul (d : ℕ) (hd : d ∣ s) : s*k/d = (s/d)*k := by
      rw [Nat.mul_comm s k, Nat.mul_div_assoc _ hd, Nat.mul_comm k]
    have ha : (a : ℕ) ∣ s := Nat.dvd_lcm_left _ _
    have hh : (h : ℕ) ∣ s := Nat.dvd_lcm_right _ _
    have hs : 0 < s := Nat.lcm_pos a.pos h.pos
    change mode a χ (s*k) * star (mode h ψ (s*k)) = _ * mode s (joint χ ψ) (s*k)
    simp only [mode, if_pos (ha.trans (dvd_mul_right s k)), if_pos (hh.trans (dvd_mul_right s k)),
      if_pos (dvd_mul_right s k), Nat.mul_div_cancel_left _ hs, hmul a ha, hmul h hh,
      Nat.cast_mul, map_mul, joint_apply, star_mul']
    ring
  · rw [mode, mode, mode, if_neg hn, mul_zero]
    by_cases ha : (a : ℕ) ∣ n
    · simp [show ¬ (h : ℕ) ∣ n from fun h => hn (Nat.lcm_dvd ha h)]
    · simp [ha]

/-- The full physical Gram, expressed with the very same joint character
and with both parts of the Euler product retained at the specified cutoff. -/
theorem full_mode_gram {q r : ℕ} (b : ℕ) (g h : ℕ+) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    let l := Nat.lcm (g : ℕ) (h : ℕ)
    (∑' n : ℕ, (positiveQWeight n : ℂ) * mode g χ n * star (mode h ψ n)) =
      (χ ((l/g : ℕ) : ZMod q) * star (ψ ((l/h : ℕ) : ZMod r)) / (l : ℂ)^2) *
        (∏ p ∈ revealedPrimeSet b, primeCharacterFactor (joint χ ψ) p) *
          tailCharacterProduct b (joint χ ψ) := by
  let l : ℕ+ := ⟨Nat.lcm (g : ℕ) (h : ℕ), Nat.lcm_pos g.pos h.pos⟩
  let phase := χ (((l : ℕ)/g : ℕ) : ZMod q) * star (ψ (((l : ℕ)/h : ℕ) : ZMod r))
  have hterm (n : ℕ) : (positiveQWeight n : ℂ) * mode g χ n * star (mode h ψ n) =
      phase * ((positiveQWeight n : ℂ) * mode l (joint χ ψ) n) := by
    rw [mul_assoc,site_product]
    change _ * (phase * mode (l : ℕ) (joint χ ψ) n) = _
    ring
  simp_rw [hterm]
  rw [tsum_mul_left,mode_mean,fullProduct_eq_head_mul_tail b (joint χ ψ)]
  change phase * (_ * _ / (l : ℂ)^2) = (phase / (l : ℂ)^2) * _ * _
  ring

/-- The observed Gram at every cutoff. a and h are the smooth parts of the
shifts and d and e are their rough parts. The joint character retains both
Dirichlet zero extensions at unequal levels. -/
theorem observed_mode_gram {q r : ℕ} (b : ℕ) (a d h e : ℕ+)
    (ha : Smooth b a) (hh : Smooth b h)
    (hd : (d : ℕ).Coprime (primorial b)) (he : (e : ℕ).Coprime (primorial b))
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    let s := Nat.lcm (a : ℕ) (h : ℕ)
    (∑' n : ℕ, (positiveQWeight n : ℂ) * observedValue b ((a : ℕ)*d) χ n *
      star (observedValue b ((h : ℕ)*e) ψ n)) =
      (χ ((s/a : ℕ) : ZMod q) * star (ψ ((s/h : ℕ) : ZMod r))) /
        ((s : ℂ)^2 * (d : ℂ)^2 * (e : ℂ)^2) *
      (∏ p ∈ revealedPrimeSet b, primeCharacterFactor (joint χ ψ) p) *
        tailCharacterProduct b χ * star (tailCharacterProduct b ψ) := by
  let s : ℕ+ := ⟨Nat.lcm (a : ℕ) (h : ℕ), Nat.lcm_pos a.pos h.pos⟩
  let ξ := joint χ ψ
  let phase := χ (((s : ℕ)/a : ℕ) : ZMod q) * star (ψ (((s : ℕ)/h : ℕ) : ZMod r))
  let C := phase * tailCharacterProduct b χ * star (tailCharacterProduct b ψ) /
    ((d : ℂ)^2*(e : ℂ)^2*tailCharacterProduct b ξ)
  have ht := tailCharacterProduct_ne_zero b ξ
  have term (n : ℕ) :
      (positiveQWeight n : ℂ) * observedValue b ((a : ℕ)*d) χ n *
      star (observedValue b ((h : ℕ)*e) ψ n) =
      C * ((positiveQWeight n : ℂ)*observedValue b s ξ n) := by
    by_cases h0 : n = 0
    · simp [h0,positiveQWeight]
    let n' : ℕ+ := ⟨n,Nat.pos_of_ne_zero h0⟩
    have one : (1 : ℕ).Coprime (primorial b) := Nat.coprime_one_left _
    have hs := observedValue_split b n' s (1 : ℕ+) (lcm_smooth ha hh) one ξ
    simp only [PNat.val_ofNat, mul_one, Nat.cast_one, one_pow, div_one] at hs
    change (positiveQWeight (n' : ℕ) : ℂ) * observedValue b ((a : ℕ)*d) χ n' *
      star (observedValue b ((h : ℕ)*e) ψ n') = C * ((positiveQWeight (n' : ℕ) : ℂ)*observedValue b s ξ n')
    rw [observedValue_split b n' a d ha hd χ, observedValue_split b n' h e hh he ψ, hs]
    have hf := site_product a h (smoothSite b n') χ ψ
    change mode a χ _ * star (mode h ψ _) = phase * mode s ξ _ at hf
    simp only [star_mul',star_div₀, star_pow, star_natCast]
    calc
      _ = (positiveQWeight (n' : ℕ) : ℂ) * (mode a χ (smoothSite b n') * star (mode h ψ (smoothSite b n'))) *
          (tailCharacterProduct b χ * star (tailCharacterProduct b ψ)) / ((d : ℂ)^2*(e : ℂ)^2) := by ring
      _ = _ := by
        rw [hf]
        dsimp only [C]
        field_simp [ht]
  simp_rw [term]
  rw [tsum_mul_left, observedValue_mean, fullProduct_eq_head_mul_tail b ξ]
  change C * ((∏ p ∈ revealedPrimeSet b, primeCharacterFactor ξ p) * tailCharacterProduct b ξ / (s : ℂ)^2) =
    phase / ((s : ℂ)^2 * (d : ℂ)^2 * (e : ℂ)^2) * (∏ p ∈ revealedPrimeSet b, primeCharacterFactor ξ p) * tailCharacterProduct b χ * star (tailCharacterProduct b ψ)
  dsimp only [C]
  field_simp [ht]

end RiemannResearch.CategoryTheory.ObservedCharacterGram
#print axioms RiemannResearch.CategoryTheory.ObservedCharacterGram.observed_mode_gram
