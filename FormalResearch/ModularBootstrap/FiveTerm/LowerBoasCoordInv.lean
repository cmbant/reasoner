module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasCoord

/-!
# Inverse Conformal Phase Coordinate `b(ζ)` (`cts:boas` Step 1)

Completes Step 1 of Lemma C8 (`cts:boas`) on top of `LowerBoasCoord.lean`:

* `re_zetaRight_sub_cumulN_le`: `0 ≤ c' * cumulN b.re - (zetaRight c' b).re ≤ (c' / 3) * |b.im|`
  for all `b ∈ lowerBoasRightDom`.
* `zetaRight_injOn`: Noshiro–Warschawski injectivity of `zetaRight c'` on `lowerBoasRightDom`.
* `zetaStrip_subset_zetaRight_image`: surjectivity of `zetaRight c'` from `lowerBoasRightDom` onto
  `zetaStrip c' = {ζ : ℂ | 0 < ζ.re ∧ |ζ.im| < (c' / 3) * xiStar}`.
* `bOfZeta`: the holomorphic inverse `b(ζ)` on `zetaStrip c'`, satisfying
  `zetaRight c' (bOfZeta c' ζ) = ζ`, `bOfZeta_conj`, `bOfZeta_ofReal`, `differentiableOn_bOfZeta`,
  and `majorantUExt_bOfZeta`:
  `c' * (majorantUExt (bOfZeta c' ζ) + (2 * π / 3) * (bOfZeta c' ζ).re) = 2 * π * |ζ.im|`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. Quantitative Real-Part Bound `0 ≤ c' N(Re b) - Re ζ(b) ≤ (c'/3) |Im b|` -/

theorem re_zetaRight_sub_cumulN_le {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    0 ≤ c' * cumulN b.re - (zetaRight c' b).re ∧
      c' * cumulN b.re - (zetaRight c' b).re ≤ (c' / 3) * |b.im| := by
  have hpos_case : ∀ {z : ℂ}, z ∈ lowerBoasRightDom → 0 < z.im →
      0 ≤ c' * cumulN z.re - (zetaRight c' z).re ∧
      c' * cumulN z.re - (zetaRight c' z).re ≤ (c' / 3) * z.im := by
    intro z hz hzim
    have hzim_lt : z.im < 1 / 2 := (abs_lt.mp hz.2).2
    let γ : ℝ → ℂ := fun s => (z.re : ℂ) + (s : ℂ) * Complex.I
    let f : ℝ → ℝ := fun s => (zetaRight c' (γ s)).re
    let g : ℝ → ℝ := fun s => (deriv (zetaRight c') (γ s) * Complex.I).re
    have hmem_s : ∀ {s : ℝ}, 0 ≤ s → s ≤ z.im → γ s ∈ lowerBoasRightDom := fun {s} hs0 hsz =>
      ⟨by simpa [γ] using hz.1, by
        change |(γ s).im| < 1 / 2
        have him_s : (γ s).im = s := by simp [γ]
        rw [him_s, abs_of_nonneg hs0]; linarith⟩
    have hg_bd : ∀ {s : ℝ}, 0 < s → s ≤ z.im → -(c' / 3) ≤ g s ∧ g s ≤ 0 := by
      intro s hs0 hsz
      have hms := hmem_s hs0.le hsz
      have hbs : γ s ∈ slitStrip := mem_slitStrip_of_im_ne_zero hms.2 (by simp [γ]; exact hs0.ne')
      have hev : zetaRight c' =ᶠ[𝓝 (γ s)] zetaPlus c' := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds
          (by simp [γ]; exact hs0)] with w hw
        unfold zetaRight; rw [ite_eq_left hw]
      have hd := (hasDerivAt_zetaPlus (c' := c') hbs).congr_of_eventuallyEq hev
      have hgs : g s = -(2 * c' / 3) * ((pMap (γ s)).im + 1 / 2) := by
        dsimp [g]; rw [hd.deriv]
        simp [Complex.mul_re, Complex.add_re]
      have hp := pMap_pos_re_neg_im hbs (by simpa [γ] using xiStar_pos.trans hz.1)
        (by simp [γ]; exact hs0)
      rw [hgs]
      constructor <;> nlinarith [hp.2.1, hp.2.2]
    have hftc : ∀ δ ∈ Ioo 0 z.im, -(c' / 3) * (z.im - δ) ≤ f z.im - f δ ∧ f z.im - f δ ≤ 0 := by
      intro δ hδ
      have hderiv : ∀ s ∈ uIcc δ z.im, HasDerivAt f (g s) s := fun s hs => by
        rw [uIcc_of_le hδ.2.le] at hs
        have hms := hmem_s (hδ.1.le.trans hs.1) hs.2
        have hc : HasDerivAt γ Complex.I s := by
          simpa [γ] using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add (z.re : ℂ)
        have hζ := ((hasDerivAt_zetaRight (c' := c') hms).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hc
        refine (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hζ).congr_deriv ?_
        simp [g]
      have hg_cont : ContinuousOn g (Icc δ z.im) := by
        intro s hs
        have hms := hmem_s (hδ.1.le.trans hs.1) hs.2
        have hd_cont : ContinuousAt (deriv (zetaRight c')) (γ s) :=
          ((analyticOnNhd_zetaRight c').deriv _ hms).continuousAt
        have hc_γ : Continuous γ := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        exact (Complex.continuous_re.continuousAt.comp
          ((hd_cont.comp_of_eq hc_γ.continuousAt rfl).mul continuousAt_const)).continuousWithinAt
      have hi : IntervalIntegrable g volume δ z.im := hg_cont.intervalIntegrable_of_Icc hδ.2.le
      have heq := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi).symm
      rw [heq]
      constructor
      · have hlo : ∫ _ in δ..z.im, (-(c' / 3) : ℝ) ≤ ∫ s in δ..z.im, g s :=
          intervalIntegral.integral_mono_on hδ.2.le intervalIntegrable_const hi fun s hs =>
            (hg_bd (hδ.1.trans_le hs.1) hs.2).1
        rw [intervalIntegral.integral_const, smul_eq_mul] at hlo
        linarith
      · have hhi : ∫ s in δ..z.im, g s ≤ ∫ _ in δ..z.im, (0 : ℝ) :=
          intervalIntegral.integral_mono_on hδ.2.le hi intervalIntegrable_const fun s hs =>
            (hg_bd (hδ.1.trans_le hs.1) hs.2).2
        simpa using hhi
    have hf_lim : Tendsto f (𝓝[>] 0) (𝓝 (c' * cumulN z.re)) := by
      have hmem0 := hmem_s le_rfl hzim.le
      have hc0 : ContinuousAt (zetaRight c') (z.re : ℂ) :=
        (differentiableOn_zetaRight c').continuousOn.continuousAt
          (isOpen_lowerBoasRightDom.mem_nhds (by simpa [γ] using hmem0))
      have hγ_tend : Tendsto γ (𝓝[>] 0) (𝓝 (z.re : ℂ)) := by
        have hc : Continuous γ := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have h1 := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa [γ] using h1
      have hres := (Complex.continuous_re.continuousAt.comp hc0).tendsto.comp hγ_tend
      dsimp [Function.comp_def] at hres
      rw [zetaRight_ofReal hz.1, Complex.ofReal_re] at hres
      exact hres
    have hlow_tend : Tendsto (fun δ : ℝ => -(c' / 3) * (z.im - δ)) (𝓝[>] 0)
        (𝓝 (-(c' / 3) * z.im)) := by
      have hc : Continuous (fun δ : ℝ => -(c' / 3) * (z.im - δ)) := by fun_prop
      have h1 := hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := 0))
      simpa using h1
    have hlim_sub : Tendsto (fun δ : ℝ => f z.im - f δ) (𝓝[>] 0)
        (𝓝 (f z.im - c' * cumulN z.re)) := tendsto_const_nhds.sub hf_lim
    have h1 : -(c' / 3) * z.im ≤ f z.im - c' * cumulN z.re :=
      le_of_tendsto_of_tendsto hlow_tend hlim_sub
        (Filter.Eventually.mono (Ioo_mem_nhdsGT hzim) fun δ hδ => (hftc δ hδ).1)
    have h2 : f z.im - c' * cumulN z.re ≤ 0 :=
      le_of_tendsto hlim_sub
        (Filter.Eventually.mono (Ioo_mem_nhdsGT hzim) fun δ hδ => (hftc δ hδ).2)
    have hfz : f z.im = (zetaRight c' z).re := by
      dsimp [f, γ]; congr 2; apply Complex.ext <;> simp
    rw [hfz] at h1 h2
    exact ⟨by linarith, by linarith⟩
  rcases lt_trichotomy b.im 0 with hneg | h0 | hpos
  · have hconj : starRingEnd ℂ b ∈ lowerBoasRightDom := conj_mem_lowerBoasRightDom hb
    have hc := hpos_case hconj (by simpa using hneg)
    have hre : (zetaRight c' (starRingEnd ℂ b)).re = (zetaRight c' b).re := by
      rw [zetaRight_conj hb]; simp
    have hre_b : (starRingEnd ℂ b).re = b.re := by simp
    have him_b : (starRingEnd ℂ b).im = -b.im := by simp
    rw [hre, hre_b, him_b] at hc
    rwa [abs_of_neg hneg]
  · have hb_eq : b = (b.re : ℂ) := Complex.ext rfl h0
    rw [hb_eq, zetaRight_ofReal hb.1]
    simp
  · have hc := hpos_case hb hpos
    rwa [abs_of_pos hpos]

/-! ### 2. Noshiro–Warschawski Injectivity and Surjectivity onto `zetaStrip c'` -/

theorem zetaRight_injOn {c' : ℝ} (hc' : 0 < c') : InjOn (zetaRight c') lowerBoasRightDom := by
  intro b₁ hb₁ b₂ hb₂ heq
  by_contra hne
  set d : ℂ := b₂ - b₁
  have hd_ne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let γ : ℝ → ℂ := fun t => b₁ + (t : ℂ) * d
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ lowerBoasRightDom := fun t ht => by
    have hconv : γ t = (1 - t) • b₁ + t • b₂ := by
      dsimp [γ, d]
      push_cast; ring
    rw [hconv]
    exact convex_lowerBoasRightDom hb₁ hb₂ (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => zetaRight c' (γ s) / d) (deriv (zetaRight c') (γ t)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hγd : HasDerivAt γ d t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * d) (1 * d) t :=
        (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const d
      simpa [γ] using h1.const_add b₁
    have hz := (hasDerivAt_zetaRight (c' := c') (hmem t ht)).comp t hγd
    refine (hz.div_const d).congr_deriv ?_
    field_simp [hd_ne]
  have hint_cont : ContinuousOn (fun t : ℝ => deriv (zetaRight c') (γ t)) (Icc 0 1) := by
    intro t ht
    have hγc : Continuous γ := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact ((analyticOnNhd_zetaRight c').deriv _ (hmem t ht)).continuousAt.comp_of_eq
      hγc.continuousAt rfl |>.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hint_cont.intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  have hzero_lhs : zetaRight c' (γ 1) / d - zetaRight c' (γ 0) / d = 0 := by
    have h1 : γ 1 = b₂ := by dsimp [γ, d]; ring
    have h0 : γ 0 = b₁ := by dsimp [γ, d]; ring
    rw [h1, h0, heq, sub_self]
  have hint_zero : ∫ t in (0 : ℝ)..1, deriv (zetaRight c') (γ t) = 0 :=
    hftc.trans hzero_lhs
  have hint_re_zero : ∫ t in (0 : ℝ)..1, (deriv (zetaRight c') (γ t)).re = 0 := by
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm
      (hint_cont.intervalIntegrable_of_Icc (μ := volume) zero_le_one)
    change (∫ t in (0 : ℝ)..1, (deriv (zetaRight c') (γ t)).re) = (∫ t in (0 : ℝ)..1, deriv (zetaRight c') (γ t)).re at hcomm
    rw [hcomm, hint_zero, Complex.zero_re]
  have hint_pos : 0 < ∫ t in (0 : ℝ)..1, (deriv (zetaRight c') (γ t)).re := by
    refine intervalIntegral.integral_pos zero_lt_one ?_ ?_ ?_
    · exact Complex.continuous_re.continuousOn.comp hint_cont (fun _ _ => mem_univ _)
    · intro t ht; exact (deriv_zetaRight_re_pos hc' (hmem t ⟨ht.1.le, ht.2⟩)).le
    · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, deriv_zetaRight_re_pos hc' (hmem (1 / 2) ⟨by norm_num, by norm_num⟩)⟩
  linarith

private lemma cumulN_tendsto_top_aux (u : ℝ) : ∃ R : ℝ, xiStar < R ∧ u < cumulN R := by
  set r : ℝ := Real.sqrt (3 * (max u 0 + 1))
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  refine ⟨xiStar + r, by linarith, ?_⟩
  have hsq : r ^ 2 = 3 * (max u 0 + 1) := Real.sq_sqrt (by positivity)
  have hge := cumulN_ge_sq_div_three hr_pos.le
  rw [hsq] at hge
  linarith [le_max_left u 0]

theorem zetaStrip_subset_zetaRight_image {c' : ℝ} (hc' : 0 < c') :
    zetaStrip c' ⊆ zetaRight c' '' lowerBoasRightDom := by
  intro ζ hζ
  set u : ℝ := ζ.re
  set v : ℝ := ζ.im
  have hu_pos : 0 < u := hζ.1
  have hv_lt : |v| < (c' / 3) * xiStar := hζ.2
  let linePt : ℝ → ℂ := fun t => (u : ℂ) + ((t * v : ℝ) : ℂ) * Complex.I
  let S : Set ℝ := {t : ℝ | ∃ b ∈ lowerBoasRightDom, zetaRight c' b = linePt t}
  have h0_mem : (0 : ℝ) ∈ S := by
    obtain ⟨R, hR_gt, hR_u⟩ := cumulN_tendsto_top_aux (u / c')
    have hiv := intermediate_value_Icc hR_gt.le (continuousOn_cumulN.mono (fun x hx => hx.1))
    rw [cumulN_xiStar] at hiv
    obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := hiv ⟨(div_pos hu_pos hc').le, hR_u.le⟩
    have hx₀_gt : xiStar < x₀ := by
      rcases eq_or_lt_of_le hx₀_mem.1 with rfl | hgt
      · rw [cumulN_xiStar] at hx₀_eq; exact absurd hx₀_eq.symm (div_pos hu_pos hc').ne'
      · exact hgt
    refine ⟨(x₀ : ℂ), ⟨by simpa using hx₀_gt, by simp⟩, ?_⟩
    rw [zetaRight_ofReal hx₀_gt, show c' * cumulN x₀ = u by rw [hx₀_eq]; field_simp [hc'.ne']]
    dsimp [linePt]; simp
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ⟨b₀, hb₀, hζ₀⟩
    have han := analyticOnNhd_zetaRight c' b₀ hb₀
    have hsd := han.differentiableAt.hasDerivAt
    have hne := deriv_zetaRight_ne_zero hc' hb₀
    have hstrict := (han.hasStrictDerivAt).hasStrictFDerivAt_equiv hne
    let g := hstrict.localInverse (zetaRight c') _ b₀
    have hg_cont : ContinuousAt g (linePt t₀) := hζ₀ ▸ hstrict.localInverse_continuousAt
    have hg_img : g (linePt t₀) = b₀ := hζ₀ ▸ hstrict.localInverse_apply_image
    have hg_right : ∀ᶠ w in 𝓝 (linePt t₀), zetaRight c' (g w) = w := by
      have := hstrict.eventually_right_inverse
      rwa [hζ₀] at this
    have hg_dom : ∀ᶠ w in 𝓝 (linePt t₀), g w ∈ lowerBoasRightDom :=
      hg_cont.eventually (by rw [hg_img]; exact isOpen_lowerBoasRightDom.mem_nhds hb₀)
    have hline_cont : Continuous linePt := by fun_prop
    exact (hline_cont.continuousAt.eventually (hg_dom.and hg_right)).mono fun t ⟨ht_dom, ht_eq⟩ =>
      ⟨g (linePt t), ht_dom, ht_eq⟩
  by_contra h_not_in
  have h1_not : (1 : ℝ) ∉ S := fun ⟨b, hb, heq⟩ => by
    apply h_not_in
    refine ⟨b, hb, heq.trans ?_⟩
    dsimp [linePt]; apply Complex.ext <;> simp [u, v]
  let K : Set ℝ := Icc (0 : ℝ) 1 \ S
  have hK_ne : K.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, h1_not⟩
  have hK_closed : IsClosed K := isClosed_Icc.sdiff hS_open
  have hK_bdd : BddBelow K := ⟨0, fun _ hx => hx.1.1⟩
  let tStar : ℝ := sInf K
  have htStar_mem : tStar ∈ K := hK_closed.csInf_mem hK_ne hK_bdd
  have htStar_pos : 0 < tStar := by
    rcases eq_or_lt_of_le htStar_mem.1.1 with h0 | hpos
    · rw [← h0] at htStar_mem; exact absurd h0_mem htStar_mem.2
    · exact hpos
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ t < tStar ∧ t ∈ S ∧ tStar - 1 / ((n : ℝ) + 1) ≤ t := by
    intro n
    set t := max 0 (tStar - 1 / ((n : ℝ) + 1))
    have ht0 : 0 ≤ t := le_max_left _ _
    have ht_lt : t < tStar := max_lt htStar_pos (sub_lt_self _ (by positivity))
    have ht1 : t ≤ 1 := ht_lt.le.trans htStar_mem.1.2
    have ht_notK : t ∉ K := fun h => not_le_of_gt ht_lt (csInf_le hK_bdd h)
    have ht_inS : t ∈ S := by
      by_contra hnot
      exact ht_notK ⟨⟨ht0, ht1⟩, hnot⟩
    exact ⟨t, ⟨ht0, ht1⟩, ht_lt, ht_inS, le_max_right _ _⟩
  choose tseq htseq_Icc htseq_lt htseq_S htseq_close using hseq
  choose bseq hbseq_dom hbseq_eq using fun n => htseq_S n
  have htseq_tend : Tendsto tseq atTop (𝓝 tStar) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by
        have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        have h1 : Tendsto (fun n : ℕ => tStar - 1 / ((n : ℝ) + 1)) atTop (𝓝 (tStar - 0)) :=
          tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (hnat.atTop_add tendsto_const_nhds))
        simpa using h1)
      tendsto_const_nhds htseq_close (fun n => (htseq_lt n).le)
  obtain ⟨R, hR_gt, hR_u⟩ := cumulN_tendsto_top_aux (u / c' + 1)
  have hbseq_rect : ∀ n : ℕ, bseq n ∈ Icc xiStar R ×ℂ Icc (-(1 / 2 : ℝ)) (1 / 2) := fun n => by
    have hbd := re_zetaRight_sub_cumulN_le hc' (hbseq_dom n)
    have hre_eq : (zetaRight c' (bseq n)).re = u := by
      rw [hbseq_eq n]; dsimp [linePt]; simp
    have hcum_le : cumulN (bseq n).re ≤ u / c' + 1 / 6 := by
      have h1 : c' * cumulN (bseq n).re ≤ u + (c' / 3) * (1 / 2) := by
        have him_le : |(bseq n).im| ≤ 1 / 2 := (hbseq_dom n).2.le
        nlinarith [hbd.2, hre_eq]
      rw [show u + (c' / 3) * (1 / 2) = c' * (u / c' + 1 / 6) by field_simp [hc'.ne']; ring] at h1
      exact le_of_mul_le_mul_left h1 hc'
    have hbre_le : (bseq n).re ≤ R := by
      by_contra hgt
      push Not at hgt
      have hmono := cumulN_strictMonoOn hR_gt.le ((hbseq_dom n).1.le) hgt
      linarith
    have him_bd := abs_le.mp (hbseq_dom n).2.le
    exact ⟨⟨(hbseq_dom n).1.le, hbre_le⟩, him_bd⟩
  have hcomp_rect : IsCompact (Icc xiStar R ×ℂ Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨bStar, hbStar_mem, φ, hφ_mono, hbφ_tend⟩ := hcomp_rect.tendsto_subseq hbseq_rect
  have htφ_tend : Tendsto (tseq ∘ φ) atTop (𝓝 tStar) := htseq_tend.comp hφ_mono.tendsto_atTop
  have hζφ_tend : Tendsto (fun k => zetaRight c' (bseq (φ k))) atTop (𝓝 (linePt tStar)) := by
    have heq : (fun k => zetaRight c' (bseq (φ k))) = fun k => linePt (tseq (φ k)) :=
      funext fun k => hbseq_eq (φ k)
    rw [heq]
    have hline_cont : Continuous linePt := by fun_prop
    exact hline_cont.continuousAt.tendsto.comp htφ_tend
  have hbStar_im_lt : |bStar.im| < 1 / 2 := by
    by_contra hge
    push Not at hge
    have heq_half : |bStar.im| = 1 / 2 := le_antisymm (abs_le.mpr hbStar_mem.2) hge
    have him_abs_tend : Tendsto (fun k => |(bseq (φ k)).im|) atTop (𝓝 (1 / 2)) :=
      heq_half ▸ (continuous_abs.comp Complex.continuous_im).continuousAt.tendsto.comp hbφ_tend
    have hev_nz : ∀ᶠ k in atTop, (bseq (φ k)).im ≠ 0 :=
      (him_abs_tend.eventually (Ioi_mem_nhds (show (1 / 4 : ℝ) < 1 / 2 by norm_num))).mono
        fun k hk h0 => by simp [h0] at hk; linarith
    have hm_tend : Tendsto (fun k => majorant2D (bseq (φ k))) atTop (𝓝 0) := by
      rcases eq_or_eq_neg_of_abs_eq heq_half with him_top | him_bot
      · have hb_eq : bStar = (bStar.re : ℂ) + (1 / 2 : ℝ) * Complex.I := by
          apply Complex.ext <;> simp [him_top]
        have htop := tendsto_majorant2D_edge_top bStar.re
        rw [← hb_eq] at htop
        refine htop.comp (tendsto_nhdsWithin_iff.mpr ⟨hbφ_tend, hev_nz.mono fun k hk =>
          mem_slitStrip_of_im_ne_zero (hbseq_dom (φ k)).2 hk⟩)
      · have hb_eq : bStar = (bStar.re : ℂ) - (1 / 2 : ℝ) * Complex.I := by
          apply Complex.ext <;> simp [him_bot]
        have hbot := tendsto_majorant2D_edge_bot bStar.re
        rw [← hb_eq] at hbot
        refine hbot.comp (tendsto_nhdsWithin_iff.mpr ⟨hbφ_tend, hev_nz.mono fun k hk =>
          mem_slitStrip_of_im_ne_zero (hbseq_dom (φ k)).2 hk⟩)
    have h_abs_lhs : Tendsto (fun k => 2 * π * |(zetaRight c' (bseq (φ k))).im|) atTop
        (𝓝 (2 * π * |tStar * v|)) := by
      have hc : Tendsto (fun k => 2 * π * |(zetaRight c' (bseq (φ k))).im|) atTop
          (𝓝 (2 * π * |(linePt tStar).im|)) :=
        (continuous_const.mul (continuous_abs.comp Complex.continuous_im)).continuousAt.tendsto.comp
          hζφ_tend
      simpa [linePt] using hc
    have h_abs_rhs : Tendsto (fun k => c' * (majorant2D (bseq (φ k)) + (2 * π / 3) * (bseq (φ k)).re))
        atTop (𝓝 ((2 * π * c' / 3) * bStar.re)) := by
      have hre_t := Complex.continuous_re.continuousAt.tendsto.comp hbφ_tend
      have hcomb := (tendsto_const_nhds (x := c')).mul
        (hm_tend.add ((tendsto_const_nhds (x := 2 * π / 3)).mul hre_t))
      dsimp only [Function.comp_def] at hcomb
      rwa [show c' * (0 + 2 * π / 3 * bStar.re) = (2 * π * c' / 3) * bStar.re by ring] at hcomb
    have hev_eq : ∀ᶠ k in atTop,
        2 * π * |(zetaRight c' (bseq (φ k))).im| =
          c' * (majorant2D (bseq (φ k)) + (2 * π / 3) * (bseq (φ k)).re) := by
      filter_upwards [hev_nz] with k hk
      rw [zetaRight_im_abs_eq hc' (hbseq_dom (φ k))]
      have huext : majorantUExt (bseq (φ k)) = majorant2D (bseq (φ k)) := by
        unfold majorantUExt
        rw [ite_eq_right (hbseq_dom (φ k)).2.ne, ite_eq_right (fun h => hk h.1)]
      rw [huext]
    have heq_lim := tendsto_nhds_unique h_abs_lhs
      (h_abs_rhs.congr' (hev_eq.mono fun _ hk => hk.symm))
    have h_in1 : 2 * π * |tStar * v| ≤ 2 * π * |v| := by
      have hpi := Real.pi_pos
      have h1 : |tStar * v| ≤ |v| := by
        rw [abs_mul, abs_of_nonneg htStar_mem.1.1]
        exact mul_le_of_le_one_left (abs_nonneg v) htStar_mem.1.2
      gcongr
    have h_in2 : 2 * π * |v| < (2 * π * c' / 3) * xiStar := by
      have hpi := Real.pi_pos
      nlinarith [hv_lt]
    have h_in3 : (2 * π * c' / 3) * xiStar ≤ (2 * π * c' / 3) * bStar.re := by
      have hpi := Real.pi_pos
      gcongr; exact hbStar_mem.1.1
    linarith
  have hbStar_re_gt : xiStar < bStar.re := by
    by_contra hle
    push Not at hle
    have hxi : bStar.re = xiStar := le_antisymm hle hbStar_mem.1.1
    rcases lt_trichotomy bStar.im 0 with hneg | h0 | hpos
    · have hbs := mem_slitStrip_of_im_ne_zero hbStar_im_lt hneg.ne
      have hev_neg : ∀ᶠ k in atTop, (bseq (φ k)).im < 0 :=
        (Complex.continuous_im.continuousAt.tendsto.comp hbφ_tend).eventually
          (Iio_mem_nhds hneg)
      have hre_lim : Tendsto (fun k => (zetaRight c' (bseq (φ k))).re) atTop
          (𝓝 (-zetaPlus c' bStar).re) := by
        have h1 := (Complex.continuous_re.continuousAt.comp
          (hasDerivAt_zetaPlus (c' := c') hbs).neg.continuousAt).tendsto.comp hbφ_tend
        refine h1.congr' (hev_neg.mono fun k hk => ?_)
        dsimp [Function.comp_def]; unfold zetaRight
        rw [ite_eq_right (not_lt.mpr hk.le), ite_eq_left hk]
        simp
      have hre_u : (-zetaPlus c' bStar).re = u := by
        have h1 := Complex.continuous_re.continuousAt.tendsto.comp hζφ_tend
        simp [Function.comp_def, linePt] at h1
        exact tendsto_nhds_unique hre_lim h1
      have hconj_eq : (-zetaPlus c' bStar).re = (zetaPlus c' (starRingEnd ℂ bStar)).re := by
        rw [zetaPlus_conj hbs]; simp
      have hb_eq : starRingEnd ℂ bStar = (xiStar : ℂ) + (-bStar.im : ℝ) * Complex.I := by
        apply Complex.ext <;> simp [hxi]
      rw [hconj_eq, hb_eq] at hre_u
      have hneg_re := zetaPlus_xiStar_re_neg (c' := c') (y := -bStar.im) hc' (by linarith)
        (by linarith [(abs_lt.mp hbStar_im_lt).1])
      linarith
    · have hcum_tend : Tendsto (fun k => c' * cumulN (bseq (φ k)).re) atTop (𝓝 0) := by
        have hre_tend : Tendsto (fun k => (bseq (φ k)).re) atTop (𝓝[Ici xiStar] xiStar) :=
          tendsto_nhdsWithin_iff.mpr
            ⟨hxi ▸ Complex.continuous_re.continuousAt.tendsto.comp hbφ_tend,
              Eventually.of_forall fun k => (hbseq_dom (φ k)).1.le⟩
        have h1 := ((tendsto_const_nhds (x := c')).mul
          (continuousOn_cumulN.continuousWithinAt le_rfl).tendsto).comp hre_tend
        simpa [Function.comp_def, cumulN_xiStar] using h1
      have hle_u : u ≤ 0 := ge_of_tendsto hcum_tend (Eventually.of_forall fun k => by
        have hbd := (re_zetaRight_sub_cumulN_le hc' (hbseq_dom (φ k))).1
        have heq : (zetaRight c' (bseq (φ k))).re = u := by rw [hbseq_eq (φ k)]; dsimp [linePt]; simp
        linarith)
      linarith
    · have hbs := mem_slitStrip_of_im_ne_zero hbStar_im_lt hpos.ne'
      have hev_pos : ∀ᶠ k in atTop, 0 < (bseq (φ k)).im :=
        (Complex.continuous_im.continuousAt.tendsto.comp hbφ_tend).eventually (Ioi_mem_nhds hpos)
      have hre_lim : Tendsto (fun k => (zetaRight c' (bseq (φ k))).re) atTop
          (𝓝 (zetaPlus c' bStar).re) := by
        have h1 := (Complex.continuous_re.continuousAt.comp
          (hasDerivAt_zetaPlus (c' := c') hbs).continuousAt).tendsto.comp hbφ_tend
        refine h1.congr' (hev_pos.mono fun k hk => ?_)
        dsimp [Function.comp_def]; unfold zetaRight; rw [ite_eq_left hk]
      have hre_u : (zetaPlus c' bStar).re = u := by
        have h1 := Complex.continuous_re.continuousAt.tendsto.comp hζφ_tend
        simp [Function.comp_def, linePt] at h1
        exact tendsto_nhds_unique hre_lim h1
      have hb_eq : bStar = (xiStar : ℂ) + (bStar.im : ℝ) * Complex.I := by
        apply Complex.ext <;> simp [hxi]
      rw [hb_eq] at hre_u
      have hneg_re := zetaPlus_xiStar_re_neg (c' := c') (y := bStar.im) hc' hpos
        (abs_lt.mp hbStar_im_lt).2
      linarith
  have hbStar_dom : bStar ∈ lowerBoasRightDom := ⟨hbStar_re_gt, hbStar_im_lt⟩
  have hζ_cont := (differentiableOn_zetaRight c').continuousOn.continuousAt
    (isOpen_lowerBoasRightDom.mem_nhds hbStar_dom)
  have htStar_in : tStar ∈ S := ⟨bStar, hbStar_dom, tendsto_nhds_unique (hζ_cont.tendsto.comp hbφ_tend) hζφ_tend⟩
  exact htStar_mem.2 htStar_in

/-! ### 3. Holomorphic Inverse `bOfZeta` on `zetaStrip c'` -/

/-- Inverse conformal phase coordinate `b(ζ)` on `zetaStrip c' = {0 < Re ζ, |Im ζ| < (c'/3) ξ_*}`. -/
noncomputable def bOfZeta (c' : ℝ) (ζ : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if h : 0 < c' ∧ ζ ∈ zetaStrip c' then
    Classical.choose (zetaStrip_subset_zetaRight_image h.1 h.2)
  else (xiStar + 1 : ℂ)

lemma bOfZeta_mem {c' : ℝ} (hc' : 0 < c') {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    bOfZeta c' ζ ∈ lowerBoasRightDom := by
  let _ := Classical.propDecidable
  unfold bOfZeta
  split_ifs with h
  · exact (Classical.choose_spec (zetaStrip_subset_zetaRight_image h.1 h.2)).1
  · exact absurd ⟨hc', hζ⟩ h

lemma zetaRight_bOfZeta {c' : ℝ} (hc' : 0 < c') {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    zetaRight c' (bOfZeta c' ζ) = ζ := by
  let _ := Classical.propDecidable
  unfold bOfZeta
  split_ifs with h
  · exact (Classical.choose_spec (zetaStrip_subset_zetaRight_image h.1 h.2)).2
  · exact absurd ⟨hc', hζ⟩ h

lemma bOfZeta_zetaRight {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom)
    (hζ : zetaRight c' b ∈ zetaStrip c') : bOfZeta c' (zetaRight c' b) = b :=
  zetaRight_injOn hc' (bOfZeta_mem hc' hζ) hb (zetaRight_bOfZeta hc' hζ)

lemma bOfZeta_conj {c' : ℝ} (hc' : 0 < c') {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    bOfZeta c' (starRingEnd ℂ ζ) = starRingEnd ℂ (bOfZeta c' ζ) := by
  have hb := bOfZeta_mem hc' hζ
  have hcζ := conj_mem_zetaStrip hζ
  refine zetaRight_injOn hc' (bOfZeta_mem hc' hcζ) (conj_mem_lowerBoasRightDom hb) ?_
  rw [zetaRight_bOfZeta hc' hcζ, zetaRight_conj hb, zetaRight_bOfZeta hc' hζ]

lemma bOfZeta_ofReal {c' u : ℝ} (hc' : 0 < c') (hu : 0 < u) :
    (bOfZeta c' (u : ℂ)).im = 0 ∧ xiStar < (bOfZeta c' (u : ℂ)).re ∧
      c' * cumulN (bOfZeta c' (u : ℂ)).re = u := by
  have hζ : (u : ℂ) ∈ zetaStrip c' :=
    ⟨by simpa using hu, by simpa using mul_pos (div_pos hc' three_pos) xiStar_pos⟩
  have hb := bOfZeta_mem hc' hζ
  have hc := bOfZeta_conj hc' hζ
  rw [Complex.conj_ofReal] at hc
  have him : (bOfZeta c' (u : ℂ)).im = 0 := by
    have h1 := congrArg Complex.im hc
    simp only [Complex.conj_im] at h1
    linarith
  have hre : xiStar < (bOfZeta c' (u : ℂ)).re := hb.1
  have hb_eq : bOfZeta c' (u : ℂ) = ((bOfZeta c' (u : ℂ)).re : ℂ) := Complex.ext rfl him
  have heq := zetaRight_bOfZeta hc' hζ
  rw [hb_eq, zetaRight_ofReal hre] at heq
  exact ⟨him, hre, Complex.ofReal_injective heq⟩

lemma bOfZeta_cumulN {c' x : ℝ} (hc' : 0 < c') (hx : xiStar < x) :
    bOfZeta c' ((c' * cumulN x : ℝ) : ℂ) = (x : ℂ) := by
  have hcum_pos : 0 < cumulN x := by
    rw [← cumulN_xiStar]; exact cumulN_strictMonoOn le_rfl hx.le hx
  have hζ : ((c' * cumulN x : ℝ) : ℂ) ∈ zetaStrip c' :=
    ⟨by simpa using mul_pos hc' hcum_pos, by
      simpa using mul_pos (div_pos hc' three_pos) xiStar_pos⟩
  rw [← zetaRight_ofReal hx]
  exact bOfZeta_zetaRight hc' ⟨by simpa using hx, by simp⟩ (by rwa [zetaRight_ofReal hx])

theorem hasDerivAt_bOfZeta {c' : ℝ} (hc' : 0 < c') {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    HasDerivAt (bOfZeta c') (deriv (zetaRight c') (bOfZeta c' ζ))⁻¹ ζ := by
  set b₀ := bOfZeta c' ζ
  have hb₀ : b₀ ∈ lowerBoasRightDom := bOfZeta_mem hc' hζ
  have hζ_eq : zetaRight c' b₀ = ζ := zetaRight_bOfZeta hc' hζ
  have han := analyticOnNhd_zetaRight c' b₀ hb₀
  have hne := deriv_zetaRight_ne_zero hc' hb₀
  have hstrict := (han.hasStrictDerivAt).hasStrictFDerivAt_equiv hne
  let g := hstrict.localInverse (zetaRight c') _ b₀
  have hg_cont : ContinuousAt g ζ := hζ_eq ▸ hstrict.localInverse_continuousAt
  have hg_img : g ζ = b₀ := by rw [← hζ_eq]; exact hstrict.localInverse_apply_image
  have hg_dom : ∀ᶠ w in 𝓝 ζ, g w ∈ lowerBoasRightDom :=
    hg_cont.eventually (by rw [hg_img]; exact isOpen_lowerBoasRightDom.mem_nhds hb₀)
  have hg_right : ∀ᶠ w in 𝓝 ζ, zetaRight c' (g w) = w := by
    have := hstrict.eventually_right_inverse
    rwa [hζ_eq] at this
  have hev : g =ᶠ[𝓝 ζ] bOfZeta c' := by
    filter_upwards [(isOpen_zetaStrip c').mem_nhds hζ, hg_dom, hg_right] with w hwζ hwdom hweq
    exact zetaRight_injOn hc' hwdom (bOfZeta_mem hc' hwζ) (hweq.trans (zetaRight_bOfZeta hc' hwζ).symm)
  have hd_g : HasDerivAt g (deriv (zetaRight c') b₀)⁻¹ ζ := by
    have h1 := ((han.hasStrictDerivAt).to_localInverse hne).hasDerivAt
    rwa [hζ_eq] at h1
  exact hd_g.congr_of_eventuallyEq hev.symm

theorem differentiableOn_bOfZeta {c' : ℝ} (hc' : 0 < c') :
    DifferentiableOn ℂ (bOfZeta c') (zetaStrip c') :=
  fun _ hζ => (hasDerivAt_bOfZeta hc' hζ).differentiableAt.differentiableWithinAt

theorem majorantUExt_bOfZeta {c' : ℝ} (hc' : 0 < c') {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    c' * (majorantUExt (bOfZeta c' ζ) + (2 * π / 3) * (bOfZeta c' ζ).re) = 2 * π * |ζ.im| := by
  have h := zetaRight_im_abs_eq hc' (bOfZeta_mem hc' hζ)
  rw [zetaRight_bOfZeta hc' hζ] at h
  exact h.symm

theorem cumulN_bOfZeta_re_sub_le {c' : ℝ} (hc' : 0 < c') {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    0 ≤ c' * cumulN (bOfZeta c' ζ).re - ζ.re ∧
      c' * cumulN (bOfZeta c' ζ).re - ζ.re ≤ (c' / 3) * |(bOfZeta c' ζ).im| := by
  have h := re_zetaRight_sub_cumulN_le hc' (bOfZeta_mem hc' hζ)
  rwa [zetaRight_bOfZeta hc' hζ] at h

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.re_zetaRight_sub_cumulN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.re_zetaRight_sub_cumulN_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaRight_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaRight_injOn

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaStrip_subset_zetaRight_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaStrip_subset_zetaRight_image

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.differentiableOn_bOfZeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.differentiableOn_bOfZeta

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.majorantUExt_bOfZeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.majorantUExt_bOfZeta

end FormalResearch.ModularBootstrap.FiveTerm
