import RiemannResearch.Analysis.MontgomeryResolventWeilTest
import RiemannResearch.RH.ActualIntegratedZeroTruncation

/-! # Incoming actual zeros at the finite ordinate cutoff

The omitted all-zero resolvent on [0,T] has two boundary layers. Multiplicity
counts control the unit cells up to twice the cutoff. The proved
reciprocal-square tail estimate controls every more distant zero.
-/

noncomputable section
open MeasureTheory Complex Set Filter Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryIncomingResolvent
open MontgomeryFiniteResolventSignal MontgomeryResolventWeilTest ActualZeroOrdinate MarkedFourierTail
open RiemannResearch.RH.ActualIntegratedZeroSeries RiemannResearch.RH.ActualIntegratedZeroTruncation

def allSignal (u t : ℝ) : ℂ := ∑' ρ : ActualZero, fullZeroTerm u t ρ

private theorem term_norm_le {u : ℝ} (hu : 0 ≤ u) (t : ℝ) (ρ : ActualZero) :
    ‖fullZeroTerm u t ρ‖ ≤
      8*Real.exp (u/2) * ((zeroMult ρ:ℝ)/(1+((ρ:ℂ).im-t)^2)) := by
  have h := zetaZeroConfig.strip (ρ:ℂ) ρ.property
  have hre : |(((ρ:ℂ)-1/2):ℂ).re| ≤ 1/2 := by
    have he : (((ρ:ℂ)-1/2):ℂ).re = (ρ:ℂ).re-1/2 := by norm_num
    rw [he,abs_le]; constructor <;> linarith [h.1,h.2]
  have he : ‖Complex.exp ((u:ℂ)*((ρ:ℂ)-1/2))‖ ≤ Real.exp (u/2) := by
    rw [Complex.norm_exp,Complex.re_ofReal_mul]
    exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (abs_le.mp hre).2 hu).trans_eq (by ring))
  have hq := norm_rationalTerm_le ((ρ:ℂ)-1/2) hre t
  rw [show (((ρ:ℂ)-1/2):ℂ).im = (ρ:ℂ).im by norm_num] at hq
  rw [fullZeroTerm,norm_mul,Complex.norm_natCast,norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul he hq (norm_nonneg _) (Real.exp_pos _).le) (Nat.cast_nonneg _)).trans_eq (by ring)

private def key (ρ : ActualZero) := WeilEF.key (ρ:ℂ).im

private theorem finite_rank_sum (s : Finset ℤ) (rank : ℤ → ℕ)
    (hinj : Set.InjOn rank (s : Set ℤ)) {R : ℝ} (hR : 1 ≤ R) :
    ∑ a ∈ s, 1/(R + (rank a : ℝ))^2 ≤ 2/R := by
  classical
  have hs := summable_window_tail (fun _ => (1:ℝ)) hR (by norm_num)
    (fun _ => by norm_num) (fun _ => le_rfl)
  calc
    _ = ∑ n ∈ s.image rank, 1/(R+(n:ℝ))^2 := by rw [Finset.sum_image hinj]
    _ ≤ ∑' n : ℕ, 1/(R+(n:ℝ))^2 := hs.sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ _ := by simpa using window_tsum_tail_le (fun _ => (1:ℝ)) hR (by norm_num) (fun _ => by norm_num) (fun _ => le_rfl)

private theorem near_sum {A : ℝ} (hA : 1 ≤ A)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t+1):ℝ) ≤ A*Real.log (|t|+3))
    (s : Finset ActualZero) {T u t R : ℝ} (hT : 0 ≤ T) (hu : 0 ≤ u) (hR : 1 ≤ R)
    (hnear : ∀ ρ ∈ s, |(ρ:ℂ).im| ≤ 2*T) (rank : ℤ → ℕ)
    (hinj : Set.InjOn rank ((s.image key : Finset ℤ) : Set ℤ))
    (hd : ∀ ρ ∈ s, R+(rank (key ρ):ℝ) ≤ 2+|(ρ:ℂ).im-t|) :
    ∑ ρ ∈ s, ‖fullZeroTerm u t ρ‖ ≤ 80*Real.exp (u/2)*A*Real.log (2*T+4)/R := by
  classical
  let B := Real.exp (u/2)
  let lc := Tail.LocalCount.ofWindowCount zetaZeroConfig hA hloc
  have hcell (n : ℤ) (hn : n ∈ s.image key) :
      ∑ ρ ∈ s with key ρ=n, ‖fullZeroTerm u t ρ‖ ≤
        (40*B*A*Real.log (2*T+4))*(1/(R+(rank n:ℝ))^2) := by
    have hwin := lc.window n (s.filter fun ρ => key ρ=n) (fun ρ h => by
      rw [← (Finset.mem_filter.mp h).2]
      exact ⟨WeilEF.key_lt _,WeilEF.le_key_add_one _⟩)
    have hnB : |(n:ℝ)|+3 ≤ 2*T+4 := by
      obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hn
      have hl := WeilEF.key_lt (ρ:ℂ).im
      have hr := WeilEF.le_key_add_one (ρ:ℂ).im
      have ⟨h₁,h₂⟩ := abs_le.mp (hnear ρ hρ)
      dsimp [key]
      have hab : |((WeilEF.key (ρ:ℂ).im : ℤ):ℝ)| ≤ 2*T+1 := abs_le.mpr ⟨by linarith,by linarith⟩
      linarith
    have hmass := hwin.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hnB) (by linarith))
    have hpt (ρ : ActualZero) (hρ : ρ ∈ s.filter fun ρ => key ρ=n) :
        ‖fullZeroTerm u t ρ‖ ≤ (40*B/(R+(rank n:ℝ))^2)*(zeroMult ρ:ℝ) := by
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hρ
      have hd' := hd ρ hm; rw [he] at hd'
      let d := (ρ:ℂ).im-t
      have hp : 0 < R+(rank n:ℝ) := by linarith [Nat.cast_nonneg (rank n) (α := ℝ)]
      have htemp := pow_le_pow_left₀ hp.le hd' 2
      have hden : (R+(rank n:ℝ))^2 ≤ 5*(1+d^2) := by
        dsimp [d] at *; nlinarith only [htemp,sq_abs ((ρ:ℂ).im-t),sq_nonneg (2*|(ρ:ℂ).im-t|-1)]
      have hi : 1/(1+d^2) ≤ 5/(R+(rank n:ℝ))^2 :=
        (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hp)).mpr (by linarith only [hden])
      calc
        _ ≤ 8*B*((zeroMult ρ:ℝ)/(1+d^2)) := term_norm_le hu t ρ
        _ = (8*B*(zeroMult ρ:ℝ))*(1/(1+d^2)) := by ring
        _ ≤ (8*B*(zeroMult ρ:ℝ))*(5/(R+(rank n:ℝ))^2) :=
          mul_le_mul_of_nonneg_left hi (by dsimp [B]; positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ ρ ∈ s with key ρ=n, (40*B/(R+(rank n:ℝ))^2)*(zeroMult ρ:ℝ) :=
        Finset.sum_le_sum hpt
      _ ≤ (40*B/(R+(rank n:ℝ))^2)*(A*Real.log (2*T+4)) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hmass (by dsimp [B]; positivity)
      _ = _ := by ring
  calc
    _ = ∑ n ∈ s.image key, ∑ ρ ∈ s with key ρ=n, ‖fullZeroTerm u t ρ‖ :=
      (Finset.sum_fiberwise_of_maps_to (g := key) (t := s.image key)
        (fun ρ hρ => Finset.mem_image_of_mem key hρ) _).symm
    _ ≤ ∑ n ∈ s.image key, (40*B*A*Real.log (2*T+4))*(1/(R+(rank n:ℝ))^2) := Finset.sum_le_sum hcell
    _ ≤ (40*B*A*Real.log (2*T+4))*(2/R) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left (finite_rank_sum _ _ hinj hR)
      have hlog := Real.log_nonneg (show 1 ≤ 2*T+4 by linarith)
      dsimp [B]; positivity
    _ = _ := by dsimp [B]; ring

private theorem near_lower {A : ℝ} (hA : 1 ≤ A)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t+1):ℝ) ≤ A*Real.log (|t|+3))
    (s : Finset ActualZero) {T u t : ℝ} (hT : 0 ≤ T) (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hnear : ∀ ρ ∈ s, |(ρ:ℂ).im| ≤ 2*T) (hlo : ∀ ρ ∈ s, (ρ:ℂ).im ≤ 0) :
    ∑ ρ ∈ s, ‖fullZeroTerm u t ρ‖ ≤ 80*Real.exp (u/2)*A*Real.log (2*T+4)/(1+t) := by
  classical
  let rank := fun n : ℤ => (-n-1).toNat
  have hn (n : ℤ) (h : n ∈ s.image key) : n ≤ -1 := by
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp h
    have hr := (WeilEF.key_lt (ρ:ℂ).im).trans_le (hlo ρ hρ)
    have hh : key ρ < (0:ℤ) := by exact_mod_cast hr
    omega
  apply near_sum hA hloc s hT hu (by linarith) hnear rank
  · intro a ha b hb he
    have h₁ := hn a ha; have h₂ := hn b hb
    dsimp [rank] at he; omega
  intro ρ hρ
  have ha := hn (key ρ) (Finset.mem_image_of_mem key hρ)
  have he : (rank (key ρ):ℝ) = -(key ρ:ℝ)-1 := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ -key ρ-1))
  rw [he,abs_of_nonpos (sub_nonpos.mpr ((hlo ρ hρ).trans ht))]
  have hi := WeilEF.le_key_add_one (ρ:ℂ).im
  dsimp [key]; linarith

private theorem near_upper {A : ℝ} (hA : 1 ≤ A)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t+1):ℝ) ≤ A*Real.log (|t|+3))
    (s : Finset ActualZero) {T u t : ℝ} (hT : 0 ≤ T) (hu : 0 ≤ u) (ht : t ≤ T)
    (hnear : ∀ ρ ∈ s, |(ρ:ℂ).im| ≤ 2*T) (hhi : ∀ ρ ∈ s, T < (ρ:ℂ).im) :
    ∑ ρ ∈ s, ‖fullZeroTerm u t ρ‖ ≤ 80*Real.exp (u/2)*A*Real.log (2*T+4)/(1+(T-t)) := by
  classical
  let L := Int.floor T
  let rank := fun n : ℤ => (n-L).toNat
  have hn (n : ℤ) (h : n ∈ s.image key) : L ≤ n := by
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp h
    have h := (hhi ρ hρ).trans_le (WeilEF.le_key_add_one (ρ:ℂ).im)
    have h' : L < key ρ + 1 := Int.floor_lt.mpr (by exact_mod_cast h)
    omega
  apply near_sum hA hloc s hT hu (by linarith) hnear rank
  · intro a ha b hb he
    have h₁ := hn a ha; have h₂ := hn b hb
    dsimp [rank] at he; omega
  intro ρ hρ
  have ha := hn (key ρ) (Finset.mem_image_of_mem key hρ)
  have he : (rank (key ρ):ℝ) = (key ρ:ℝ)-(L:ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ key ρ-L))
  rw [he,abs_of_nonneg (sub_nonneg.mpr (ht.trans (hhi ρ hρ).le))]
  have hi := WeilEF.key_lt (ρ:ℂ).im
  have hfloor := Int.lt_floor_add_one T
  dsimp [key,L]; linarith

private theorem far_sum {A : ℝ} (hA : 1 ≤ A)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t+1):ℝ) ≤ A*Real.log (|t|+3))
    (s : Finset ActualZero) {T u t : ℝ} (hT : 5 ≤ T) (hu : 0 ≤ u) (ht : t ∈ Icc 0 T)
    (hfar : ∀ ρ ∈ s, 2*T < |(ρ:ℂ).im|) :
    ∑ ρ ∈ s, ‖fullZeroTerm u t ρ‖ ≤
      2048*Real.exp (u/2)*A*Real.log (2*T+4)/(1+t) := by
  let K := Nat.floor (2*T)
  have hKle : (K:ℝ) ≤ 2*T := Nat.floor_le (by linarith)
  have hKlt : 2*T < (K:ℝ)+1 := Nat.lt_floor_add_one _
  have hK : 5 ≤ K := by exact_mod_cast (by linarith : (5:ℝ) ≤ K)
  have hW := weight_partial_tail_le hA hloc K hK s (fun ρ hρ => hKle.trans_lt (hfar ρ hρ))
  have hm (ρ : ActualZero) (hρ : ρ ∈ s) : ‖fullZeroTerm u t ρ‖ ≤ 64*Real.exp (u/2)*weight ρ := by
    let g := (ρ:ℂ).im
    have hg : |g| ≤ 2*|g-t| := by
      have hf := hfar ρ hρ
      have h := abs_sub_abs_le_abs_sub g t
      rw [abs_of_nonneg ht.1] at h
      change 2*T < |g| at hf
      linarith [ht.2]
    have hsqr := pow_le_pow_left₀ (abs_nonneg _) hg 2
    rw [mul_pow,sq_abs,sq_abs] at hsqr
    have hm := WeilEF.abs_gammaOf_im_le (zetaZeroConfig.strip (ρ:ℂ) ρ.property)
    have hm' := (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) hm 2)
    have hden : 1+Complex.normSq (gammaOf ρ) ≤ 8*(1+(g-t)^2) := by
      rw [Complex.normSq_apply,WeilEF.gammaOf_re]
      change 1+(g*g+_ * _) ≤ _
      nlinarith only [hsqr,hm',sq_nonneg (g-t)]
    have hi : 1/(1+(g-t)^2) ≤ 8/(1+Complex.normSq (gammaOf ρ)) :=
      (div_le_div_iff₀ (by positivity) (by linarith [Complex.normSq_nonneg (gammaOf (ρ:ℂ))])).mpr (by linarith)
    calc
      _ ≤ 8*Real.exp (u/2)*((zeroMult ρ:ℝ)/(1+(g-t)^2)) := term_norm_le hu t ρ
      _ = (8*Real.exp (u/2)*(zeroMult ρ:ℝ))*(1/(1+(g-t)^2)) := by ring
      _ ≤ (8*Real.exp (u/2)*(zeroMult ρ:ℝ))*(8/(1+Complex.normSq (gammaOf ρ))) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by unfold weight; ring
  have hlog := Real.log_le_log (show 0 < (K:ℝ)+3 by positivity) (show (K:ℝ)+3 ≤ 2*T+4 by linarith)
  have hb : Real.log ((K:ℝ)+3)/K ≤ Real.log (2*T+4)/(1+t) :=
    div_le_div₀ (Real.log_nonneg (by linarith)) hlog (by linarith [ht.1]) (by linarith [ht.2])
  calc
    _ ≤ ∑ ρ ∈ s, 64*Real.exp (u/2)*weight ρ := Finset.sum_le_sum hm
    _ ≤ (64*Real.exp (u/2))*(32*A*Real.log ((K:ℝ)+3)/K) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (2048*Real.exp (u/2)*A)*(Real.log ((K:ℝ)+3)/K) := by ring
    _ ≤ (2048*Real.exp (u/2)*A)*(Real.log (2*T+4)/(1+t)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private def inside (T : ℝ) : Set ActualZero := {ρ | 0 < (ρ:ℂ).im ∧ (ρ:ℂ).im ≤ T}

private theorem finite_head_eq (T u t : ℝ) :
    (∑' ρ : inside T, fullZeroTerm u t ρ.1) = actualSignal T u t := by
  classical
  let e : inside T ≃ {z // z ∈ cutoff T} := {
    toFun := fun ρ => ⟨ρ.1.1,mem_cutoff.mpr ⟨ρ.1.2,ρ.2⟩⟩
    invFun := fun z => ⟨⟨z.1,(mem_cutoff.mp z.2).1⟩,(mem_cutoff.mp z.2).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let f := fun z : ℂ => Complex.exp ((u:ℂ)*(z-1/2))*rationalTerm (z-1/2) t
  calc
    _ = ∑' z : {z // z ∈ cutoff T}, (zeroMult z.1:ℂ)*f z.1 :=
      e.tsum_eq (fun z => (zeroMult z.1:ℂ)*f z.1)
    _ = ActualZeroOrdinate.sum T f := by
      simp only [tsum_fintype,ActualZeroOrdinate.sum]
      exact Finset.sum_attach (cutoff T) (fun z => (zeroMult z:ℂ)*f z)
    _ = _ := sum_eq_copies T f

/-- Pointwise size of all the incoming spectral mass on the physical interval. -/
theorem exists_incoming_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T u t : ℝ, 5 ≤ T → 0 ≤ u → t ∈ Icc 0 T →
      ‖allSignal u t-actualSignal T u t‖ ≤
        C*Real.exp (u/2)*Real.log (2*T+4)*(1/(1+t)+1/(1+(T-t))) := by
  classical
  obtain ⟨A,hA,hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨2128*A, by linarith,fun T u t hT hu ht => ?_⟩
  let G := fun ρ : ActualZero => fullZeroTerm u t ρ
  let H := (inside T)ᶜ
  let B := Real.exp (u/2)*A*Real.log (2*T+4)
  have hb : 0 ≤ B := by
    have := Real.log_nonneg (show 1 ≤ 2*T+4 by linarith)
    dsimp [B]; positivity
  have hh := (summable_norm_iff.mp (summable_norm_fullZeroTerm u t)).tsum_subtype_add_tsum_subtype_compl (inside T)
  rw [finite_head_eq] at hh
  have he : allSignal u t-actualSignal T u t = ∑' ρ : H, G ρ.1 := by
    change _ + _ = allSignal u t at hh
    exact sub_eq_iff_eq_add.mpr (hh.symm.trans (add_comm _ _))
  rw [he]
  have hpart (s : Finset H) :
      ∑ ρ ∈ s, ‖G ρ.1‖ ≤ 2128*B*(1/(1+t)+1/(1+(T-t))) := by
    let f := s.map (Function.Embedding.subtype _)
    let near := f.filter (fun ρ : ActualZero => |(ρ:ℂ).im| ≤ 2*T)
    let far := f.filter (fun ρ : ActualZero => ¬ |(ρ:ℂ).im| ≤ 2*T)
    let lo := near.filter (fun ρ : ActualZero => (ρ:ℂ).im ≤ 0)
    let hi := near.filter (fun ρ : ActualZero => ¬ (ρ:ℂ).im ≤ 0)
    have hnear (ρ : ActualZero) (hm : ρ ∈ near) : |(ρ:ℂ).im| ≤ 2*T := (Finset.mem_filter.mp hm).2
    have hhi (ρ : ActualZero) (hρ : ρ ∈ hi) : T < (ρ:ℂ).im := by
      obtain ⟨hN,hP⟩ := Finset.mem_filter.mp hρ
      have hf := (Finset.mem_filter.mp hN).1
      obtain ⟨η,hη,rfl⟩ := Finset.mem_map.mp hf
      have hη' := η.2
      change ¬ (0 < (η.1:ℂ).im ∧ (η.1:ℂ).im ≤ T) at hη'
      exact lt_of_not_ge (fun h => hη' ⟨lt_of_not_ge hP,h⟩)
    have hl := near_lower hA hloc lo (by linarith : 0 ≤ T) hu ht.1
      (fun ρ hm => hnear ρ (Finset.mem_filter.mp hm).1) (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    have hu' := near_upper hA hloc hi (by linarith : 0 ≤ T) hu ht.2
      (fun ρ hm => hnear ρ (Finset.mem_filter.mp hm).1) hhi
    have hf := far_sum hA hloc far hT hu ht (fun ρ hρ => lt_of_not_ge (Finset.mem_filter.mp hρ).2)
    let F := fun ρ : ActualZero => ‖G ρ‖
    have hsplit : (∑ ρ ∈ lo, F ρ)+(∑ ρ ∈ hi, F ρ)= ∑ ρ ∈ near, F ρ :=
      Finset.sum_filter_add_sum_filter_not near _ F
    have hsplit' : (∑ ρ ∈ near, F ρ)+(∑ ρ ∈ far, F ρ)= ∑ ρ ∈ f, F ρ :=
      Finset.sum_filter_add_sum_filter_not f _ F
    have hs : (∑ ρ ∈ s, ‖G ρ.1‖) = ∑ ρ ∈ f, F ρ := by
      simp only [f,F,Finset.sum_map,Function.Embedding.coe_subtype]
    rw [hs,← hsplit',← hsplit]
    apply (add_le_add (add_le_add hl hu') hf).trans
    have hr : 0 ≤ B/(1+(T-t)) := div_nonneg hb (by linarith [ht.2])
    change 80*Real.exp (u/2)*A*Real.log (2*T+4)/(1+t) + _ + _ ≤ _
    dsimp only [B] at hr ⊢
    ring_nf at hr ⊢
    linarith only [hr]
  have hsNorm := (summable_norm_fullZeroTerm u t).subtype H
  calc
    _ ≤ ∑' ρ : H, ‖G ρ.1‖ := norm_tsum_le_tsum_norm hsNorm
    _ ≤ 2128*B*(1/(1+t)+1/(1+(T-t))) := Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hpart
    _ = _ := by dsimp [B]; ring

end RiemannResearch.Analysis.MontgomeryIncomingResolvent

namespace RiemannResearch.Analysis.MontgomeryIncomingResolvent

/--
info: 'RiemannResearch.Analysis.MontgomeryIncomingResolvent.exists_incoming_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_incoming_bound

end RiemannResearch.Analysis.MontgomeryIncomingResolvent
