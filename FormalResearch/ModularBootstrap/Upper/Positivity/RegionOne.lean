module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionII
public import FormalResearch.ModularBootstrap.Upper.Window.LemmaR
public import FormalResearch.ModularBootstrap.Upper.Holes.HoleLimit
public import FormalResearch.ModularBootstrap.Upper.Design.CombTransform

/-!
# Proposition I: positivity in Region I, the Airy window at the tip (`ut:I`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition I (`ut:I`, lines 433--441) and the
sentence "Region I and II overlap, so `g > 0` on `t ≥ t_f + 1` at `w = 1`".  For the designs
`D(N, η_*, d)` (`f = 1`, `η_* ∈ (0, 1/4]`, `η₀ = 1/4`; `designComb c' 1 N (1/4) (designSigma1 d)
(designWidth1 c' η_*)`), `c'` large, with `2 g = h₀^D - ĥ₀` (`twoG`, `t = c' x²/3`) and
`χ'_1 = ξ_* + λ σ_1 = designSite c' (designSigma1 d) 1` the simple zero:

* (a) `x ∈ [χ'_1 + C λ c'^{1/2 - 4 n₁/3}, ξ_* + λ Σ₀]`, `n₁ = 3/4`, i.e. `x - χ'_1 ≥ C λ c'^{-1/2}`
  (`proposition_I_a`): Lemma R (`lemma_R_lower`: `h₀ e^{c'L} ≥ K̃_c w₀ (σ - σ_f)` with `K̃_c = c_K c'`)
  against Lemma `SD_G` (`designProfile_global_bound`: `e^{c'L} ‖ĥ₀‖ ≤ K √(c'/x)`).
* (b) `x ∈ [ξ_* + λ Σ₀, ξ_I]`, `ξ_I = ξ_* + c'^{-2/5}` (`proposition_I_b`): `Σ₀` is fixed so that `lemma_P_b`
  gives `|B_D| ≥ ½ |B_ref|` and every such `x` lies in a cell `n ≥ max(N_ov, 2)` of `band_overshoot_K5`;
  the overshoot `h₀^{ref} e^{c'L} ≥ c_T sech²(π x/2) (2/(π(x - ξ_*)))^{3/2} ≥ c c'^{3/5}` beats
  `K √(c'/x) ≲ √c'` (`2 n₁ θ = 3/5 > 1/2`).

The final comparison (`pos_of_lower_hankel`) and the overshoot of a finite modification at any level `f`
(`designProfile_overshoot_lower`, `pow_overshoot_gen`) are `f`-general and used at `f = 2` by
`TwoLevel.TwoZeroRegionOne`.  The overlap with Region II and the passage to `t ≥ t_f + 1` are in
`Upper.Positivity.RegionOneAssembly`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Window

/-! ### 1. The normalisation `K̃_c` at `f = 1` and the design in window form -/

/-- `K̃_c^{(1)} = c_K c'`: `(2√2/(πλ))^{3/2} = (2√2/π)^{3/2} k_tip c'` since `λ = (k_tip c')^{-2/3}`. -/
noncomputable def cKtilde : ℝ :=
  (1 / Real.cosh (π * xiStar / 2) ^ 2) * (2 * √2 / π) ^ (3 / 2 : ℝ) * kTip

lemma cKtilde_pos : 0 < cKtilde := by
  unfold cKtilde
  have := kTip_pos
  positivity

lemma windowNormKTilde_one {c' : ℝ} (hc' : 0 < c') : windowNormKTilde 1 c' = cKtilde * c' := by
  have hk : 0 < kTip * c' := mul_pos kTip_pos hc'
  have hl : lambdaComb c' = ((kTip * c') ^ (2 / 3 : ℝ))⁻¹ := by
    unfold lambdaComb; rw [Real.rpow_neg hk.le]
  have hu : 0 < (kTip * c') ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk _
  have e : 2 * √2 / (π * lambdaComb c') = (2 * √2 / π) * (kTip * c') ^ (2 / 3 : ℝ) := by
    rw [hl]; field_simp
  have hexp : (2 * (((1 : ℕ) : ℝ) - 1 / 4) : ℝ) = 3 / 2 := by norm_num
  unfold windowNormKTilde cKtilde
  rw [hexp, e, Real.mul_rpow (by positivity) hu.le, ← Real.rpow_mul hk.le,
    show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one]
  ring

lemma phiWKB_succ_sub_pos {k : ℕ} (hk : 1 ≤ k) : 0 < phiWKB (k + 1) - phiWKB k := by
  unfold phiWKB
  refine sub_pos.mpr (Real.rpow_lt_rpow ?_ ?_ (by norm_num))
  · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  · push_cast; linarith

/-- The limit widths of the modification `sigMod N η σs` are non-zero for `η_* > 0`. -/
lemma posLimitWidths_sigMod (N : ℕ) {η : ℝ} (hη : 0 < η) (σs : ℕ → ℝ) :
    PosLimitWidths (sigMod N η σs) := by
  intro k hk
  have hk1 : 1 ≤ k := by omega
  have hgap := phiWKB_succ_sub_pos hk1
  by_cases hkN : k ≤ N
  · simp only [ModifiedCombData.allEpsLim, hkN, ↓reduceIte, sigMod]
    exact (mul_pos hη hgap).ne'
  · simp only [ModifiedCombData.allEpsLim, hkN, ↓reduceIte, sigMod]
    exact (mul_pos (by norm_num) hgap).ne'

/-- The limit widths of the design `D(N, η_*, d)` are non-zero for `η_* > 0`. -/
lemma posLimitWidths_designMod (N : ℕ) {η : ℝ} (hη : 0 < η) (d : ℝ) :
    PosLimitWidths (designMod N η d) :=
  posLimitWidths_sigMod N hη (designSigma1 d)

/-- The widths `ε'_k = η_* ℓ_k` of the design lie in the family of `lemma_P_b`. -/
lemma designWidth1_family (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ᶠ c' in atTop, ∀ k : ℕ, 1 < k → k ≤ N →
      0 ≤ designWidth1 c' η k ∧ designWidth1 c' η k ≤ Cg * lambdaComb c' := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  refine ⟨Cg, hCg.le, ?_⟩
  filter_upwards [h_ev, eventually_gt_atTop (0 : ℝ)]
    with c' ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos k hk hkN
  refine ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), ?_⟩
  have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
  unfold designWidth1
  calc η * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
        mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
    _ = Cg * lambdaComb c' := one_mul _

/-- The real part of `h₀ = sech² B` on the real axis is `modifiedH0` of the window form (offsets `σs`). -/
lemma sigProfile_re_eq_modifiedH0 (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ x : ℝ,
      (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re =
        modifiedH0 1 N (sigMod N η σs) c' x := by
  filter_upwards [sigComb_eq_modifiedCombB N hη0 hη1 σs] with c' h x
  unfold designProfile modifiedH0
  rw [h, sechSqProfile_ofReal, Complex.re_ofReal_mul]

/-- The real part of `h₀^D = sech² B_D` on the real axis is `modifiedH0` of the window form. -/
lemma designProfile_re_eq_modifiedH0 (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∀ᶠ c' in atTop, ∀ x : ℝ,
      (designProfile c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η) (x : ℂ)).re =
        modifiedH0 1 N (designMod N η d) c' x :=
  sigProfile_re_eq_modifiedH0 N hη0 hη1 (designSigma1 d)

lemma exp_slitL_eq_edgeL {x : ℝ} (hx : 0 ≤ x) : slitL x = edgeL x := by
  unfold slitL edgeL; rw [abs_of_nonneg hx]

/-! ### 2. Region I(a): the window `[χ'_1 + C λ c'^{-1/2}, ξ_* + λ Σ₀]` -/

lemma sub_pos_of_bounds {Hh R N E Q Q' : ℝ} (hE : 0 < E) (hR : R ≤ N) (hlow : Q ≤ Hh * E)
    (hup : E * N ≤ Q') (hQ : Q' < Q) : 0 < Hh - R := by
  have h1 : E * R ≤ E * N := mul_le_mul_of_nonneg_left hR hE.le
  have : 0 < E * (Hh - R) := by nlinarith
  exact pos_of_mul_pos_right this hE.le

lemma edge_bound_sqrt {K c' x E Nn : ℝ} (hK0 : 0 ≤ K) (hc' : 0 < c') (hxhalf : xiStar / 2 ≤ x)
    (h : E * Nn ≤ K * √(c' / x)) : E * Nn ≤ K * √(2 / xiStar) * √c' := by
  have hxi := xiStar_pos
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxhalf
  have hsq : √(c' / x) ≤ √(2 / xiStar) * √c' := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hx0]
    have : 2 / xiStar * c' * x ≥ 2 / xiStar * c' * (xiStar / 2) :=
      mul_le_mul_of_nonneg_left hxhalf (by positivity)
    have e : 2 / xiStar * c' * (xiStar / 2) = c' := by field_simp
    linarith
  calc E * Nn ≤ K * √(c' / x) := h
    _ ≤ K * (√(2 / xiStar) * √c') := mul_le_mul_of_nonneg_left hsq hK0
    _ = K * √(2 / xiStar) * √c' := by ring

/-- **The final comparison of Region I**: `Q ≤ h e^{c'L}`, `e^{c'L} ‖ĥ‖ ≤ K √(c'/x)` and
`K √(2/ξ_*) √c' < Q` give `h - Re ĥ > 0` (for `x ≥ ξ_*/2`). -/
lemma pos_of_lower_hankel {c' x E K Hre Q : ℝ} {Hh : ℂ} (hc' : 0 < c') (hxhalf : xiStar / 2 ≤ x)
    (hK0 : 0 ≤ K) (hE : 0 < E) (hglob : E * ‖Hh‖ ≤ K * √(c' / x)) (hQ : Q ≤ Hre * E)
    (hbig : K * √(2 / xiStar) * √c' < Q) : 0 < Hre - Hh.re :=
  sub_pos_of_bounds hE (Complex.re_le_norm Hh) hQ (edge_bound_sqrt hK0 hc' hxhalf hglob) hbig

/-- **The final comparison of Region I at every order** (`ut:III`, Region I; `fw:e1.3`).  For fixed `p`, `f`, `η₀`
there is `A ≥ 0` such that for `c'` large, every cut `N`, all admissible data and every `x ≥ ξ_*/2` with
`A √c' < h₀(x) e^{c' L(x)}` one has `2 g_w(c' x²/3) > 0`: the transform is bounded by `K √(c'/x) x^{-p}`
(`designProfile_global_bound_of_admissible_P`, `x ≥ ξ_*/2`).  At `p = 0` this is the final step of Proposition I. -/
theorem twoGW_pos_of_lower (p f : ℕ) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), DesignAdmissible c' f N η₀ σ ε →
      ∀ x : ℝ, xiStar / 2 ≤ x →
        A * √c' < (designProfile c' f N η₀ σ ε (x : ℂ)).re * Real.exp (c' * edgeL x) →
        0 < twoGW p c' f N η₀ σ ε x := by
  obtain ⟨K, hK0, hK⟩ := designProfile_global_bound_of_admissible_P p f hη₀0 hη₀1
  have hxi := xiStar_pos
  refine ⟨K * (2 / xiStar) ^ p * √(2 / xiStar), by positivity, ?_⟩
  filter_upwards [hK, eventually_ge_atTop (3 / (2 * π * xiStar)), eventually_gt_atTop (0 : ℝ)]
    with c' hKc hc3 hcpos N σ ε hA x hx hlow
  have hpi := Real.pi_pos
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hk : 1 ≤ 4 * π * c' * x / 3 := by
    have h1 : 3 / (2 * π * xiStar) * (2 * π * xiStar) = 3 := by field_simp
    have h2 : 3 ≤ c' * (2 * π * xiStar) := by
      calc (3 : ℝ) = 3 / (2 * π * xiStar) * (2 * π * xiStar) := h1.symm
        _ ≤ c' * (2 * π * xiStar) := mul_le_mul_of_nonneg_right hc3 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 4 * π * c' / 3)]
  have hglob := hKc N σ ε hA x hx0 hk
  have hpow : (1 / x) ^ p ≤ (2 / xiStar) ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [div_le_div_iff₀ hx0 hxi]
    linarith
  have hglob' : Real.exp (c' * edgeL x) *
      ‖edgeHankelP p c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)‖ ≤
        (K * (2 / xiStar) ^ p) * √(c' / x) := by
    refine hglob.trans ?_
    calc K * √(c' / x) * (1 / x) ^ p ≤ K * √(c' / x) * (2 / xiStar) ^ p :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  unfold twoGW
  rw [Complex.sub_re]
  exact pos_of_lower_hankel hcpos hx (by positivity) (Real.exp_pos _) hglob' le_rfl hlow

/-- The widths `η ℓ_k` of the designs (`designWidth1`) of the `f = 1` finite modifications with offsets `σs` give
admissible data for `c'` large. -/
lemma designWidth1_admissible (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, DesignAdmissible c' 1 N (1 / 4) σs (designWidth1 c' η) := by
  obtain ⟨Cg, hCg, hfam⟩ := designWidth1_family N hη0 hη1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  filter_upwards [designAdmissible_eventually 1 N le_rfl hN M Cg (η₀ := 1 / 4) (by norm_num) le_rfl,
    hfam] with c' hAd hfamc
  exact hAd σs (designWidth1 c' η) (fun k hk hkN => hM k hk hkN) (fun k hk hkN => hfamc k hk hkN)

/-- **Proposition I (a), lower bound** (`ut:I`, Lemma R): for the `f = 1` finite modifications at fixed sites `σs`
and every threshold `A ≥ 0` there is `C > 0` such that for large `c'` every `x` with
`χ'_1 + C λ c'^{-1/2} ≤ x ≤ ξ_* + λ Σ₀` satisfies `x ≥ ξ_*/2` and `(A + 1) √c' ≤ h₀(x) e^{c' L(x)}`
(`h₀ e^{c'L} ≥ K̃_c w₀ (σ - σ_1)`).  Both the order-`0` and the order-`p` comparison with the transform
(`twoGW_pos_of_lower`) start from it. -/
theorem proposition_I_a_sig_lower (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) (Sg0 A : ℝ) (hA0 : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      designSite c' σs 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
      x ≤ xiStar + lambdaComb c' * Sg0 →
      xiStar / 2 ≤ x ∧ (A + 1) * √c' ≤
        (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re * Real.exp (c' * edgeL x) := by
  set 𝒦 := sigModFamily N hN hη0.le hη1 σs with h𝒦
  have hd : sigMod N η σs ∈ 𝒦.members := sigModFamily_mem N hN hη0.le hη1 σs
  obtain ⟨w0, hw0, C0, hlow⟩ := lemma_R_lower 𝒦 hd (posLimitWidths_sigMod N hη0 σs) Sg0
  have hxi := xiStar_pos
  set C : ℝ := (A + 1) / (cKtilde * w0) with hC
  have hCpos : 0 < C := by have := cKtilde_pos; positivity
  refine ⟨C, hCpos, ?_⟩
  have hlam1 : ∀ᶠ c' in atTop, lambdaComb c' * |σs 1| ≤ xiStar / 2 := by
    have h := tendsto_lambdaComb_atTop.mul_const |σs 1|
    rw [zero_mul] at h
    exact h.eventually_le_const (by positivity)
  filter_upwards [sigProfile_re_eq_modifiedH0 N hη0.le hη1 σs, hlam1,
    eventually_ge_atTop C0, eventually_gt_atTop (0 : ℝ)]
    with c' hre hl1 hc0 hcpos x hx1 hx2
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  set σ : ℝ := (x - xiStar) / lambdaComb c' with hσ
  have hxσ : xiStar + lambdaComb c' * σ = x := by rw [hσ]; field_simp; ring
  have hσ1 : (sigMod N η σs).sigmaF c' = σs 1 := rfl
  have hc12 : 0 < c' ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hcpos _
  have hgap : C * c' ^ (-(1 / 2 : ℝ)) ≤ σ - (sigMod N η σs).sigmaF c' := by
    rw [hσ1, hσ, le_sub_iff_add_le, le_div_iff₀ hlam]
    unfold designSite at hx1
    nlinarith
  have hσpos : (sigMod N η σs).sigmaF c' < σ := by
    have : 0 < C * c' ^ (-(1 / 2 : ℝ)) := by positivity
    linarith
  have hσle : σ ≤ Sg0 := by
    rw [hσ, div_le_iff₀ hlam]; linarith
  have hlow' := hlow hc0 σ hσpos hσle
  rw [hxσ] at hlow'
  have hxhalf : xiStar / 2 ≤ x := by
    unfold designSite at hx1
    have h1 : 0 ≤ C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) := by positivity
    have h2 : -(lambdaComb c' * |σs 1|) ≤ lambdaComb c' * σs 1 := by
      have := neg_abs_le (σs 1)
      nlinarith
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxhalf
  refine ⟨hxhalf, ?_⟩
  have hH := hre x
  rw [exp_slitL_eq_edgeL hx0.le] at hlow'
  have hsqrt : c' * c' ^ (-(1 / 2 : ℝ)) = √c' := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hcpos.le (by norm_num)]
    norm_num
  rw [hH]
  refine le_trans ?_ hlow'
  rw [windowNormKTilde_one hcpos]
  have : cKtilde * c' * w0 * (σ - (sigMod N η σs).sigmaF c') ≥ cKtilde * c' * w0 * (C * c' ^ (-(1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hgap (by have := cKtilde_pos; positivity)
  refine le_trans (le_of_eq ?_) this
  rw [hC]
  have h1 := cKtilde_pos.ne'
  have h2 := hw0.ne'
  calc (A + 1) * √c' = (A + 1) * (c' * c' ^ (-(1 / 2 : ℝ))) := by rw [hsqrt]
    _ = _ := by field_simp

/-- **Proposition I (a)** (`ut:I`) for the `f = 1` finite modifications at fixed sites `σs` (first site `σs 1`
arbitrary, sites `2..N` arbitrary): see `proposition_I_a`, the case `σs = designSigma1 d`. -/
theorem proposition_I_a_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (Sg0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      designSite c' σs 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
      x ≤ xiStar + lambdaComb c' * Sg0 →
      0 < twoG c' 1 N (1 / 4) σs (designWidth1 c' η) x := by
  obtain ⟨A, hA0, hA⟩ := twoGW_pos_of_lower 0 1 (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨C, hC, hlow⟩ := proposition_I_a_sig_lower N hN hη0 hη1 σs Sg0 A hA0
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlow, hA, designWidth1_admissible N hN hη0.le hη1 σs, eventually_gt_atTop (0 : ℝ)]
    with c' hlowc hAc hadm hcpos x hx1 hx2
  obtain ⟨hxhalf, hQ⟩ := hlowc x hx1 hx2
  rw [← twoGW_zero]
  refine hAc N σs (designWidth1 c' η) hadm x hxhalf (lt_of_lt_of_le ?_ hQ)
  have : 0 < √c' := Real.sqrt_pos.mpr hcpos
  nlinarith

/-- **Proposition I (a)** (`ut:I`): for every `Σ₀` there is `C > 0` such that for large `c'` and every
`x` with `χ'_1 + C λ c'^{1/2 - 4n₁/3} ≤ x ≤ ξ_* + λ Σ₀` (`n₁ = 3/4`, so the exponent is `-1/2`) one has
`2 g(c' x²/3) > 0`.  Lemma R gives `h₀ e^{c'L} ≥ K̃_c w₀ (σ - σ_1)` and Lemma `SD_G` gives
`e^{c'L} |ĥ₀| ≤ K √(c'/x)`. -/
theorem proposition_I_a (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d Sg0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      designSite c' (designSigma1 d) 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
      x ≤ xiStar + lambdaComb c' * Sg0 →
      0 < twoG c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η) x :=
  proposition_I_a_sig N hN hη0 hη1 (designSigma1 d) Sg0

/-! ### 3. Region I(b): the overshoot window `[ξ_* + λ Σ₀, ξ_I]` -/

lemma phiQuantile_add_two_pos (N : ℕ) : 0 < phiQuantile ((N : ℝ) + 2) := by
  unfold phiQuantile
  apply Real.rpow_pos_of_pos
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

lemma phiQuantile_add_two_nonneg (N : ℕ) : 0 ≤ phiQuantile ((N : ℝ) + 2) :=
  (phiQuantile_add_two_pos N).le

/-- `(2/π)^a c'^{2a/5} ≤ (2/(π u))^a` for `0 < u ≤ c'^{-2/5}`, `a ≥ 0`. -/
lemma pow_overshoot_gen {c' u a : ℝ} (hc' : 0 < c') (hu : 0 < u) (huup : u ≤ c' ^ (-(2 / 5 : ℝ)))
    (ha : 0 ≤ a) : (2 / π) ^ a * c' ^ (2 / 5 * a : ℝ) ≤ (2 / (π * u)) ^ a := by
  have hπ := Real.pi_pos
  have hw : 0 < c' ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hwu : c' ^ (2 / 5 : ℝ) ≤ 1 / u := by
    rw [le_div_iff₀ hu]
    have hneg : c' ^ (-(2 / 5 : ℝ)) = (c' ^ (2 / 5 : ℝ))⁻¹ := Real.rpow_neg hc'.le _
    rw [hneg] at huup
    calc c' ^ (2 / 5 : ℝ) * u ≤ c' ^ (2 / 5 : ℝ) * (c' ^ (2 / 5 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left huup hw.le
      _ = 1 := mul_inv_cancel₀ hw.ne'
  have h1 : (2 / π) * c' ^ (2 / 5 : ℝ) ≤ 2 / (π * u) := by
    calc (2 / π) * c' ^ (2 / 5 : ℝ) ≤ (2 / π) * (1 / u) :=
          mul_le_mul_of_nonneg_left hwu (by positivity)
      _ = 2 / (π * u) := by field_simp
  have h2 := Real.rpow_le_rpow (by positivity) h1 ha
  rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc'.le] at h2

lemma sech_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ xiStar + 1) :
    1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2 ≤ 1 / Real.cosh (π * x / 2) ^ 2 := by
  have hxi := xiStar_pos
  have hc : Real.cosh (π * x / 2) ≤ Real.cosh (π * (xiStar + 1) / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    nlinarith [Real.pi_pos]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (Real.cosh_pos _).le hc 2)

lemma half_le_of_log_le {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (h : |Real.log (r / R)| ≤ Real.log 2) :
    1 / 2 * R ≤ r := by
  have h1 := (abs_le.mp h).1
  have hq : 0 < r / R := div_pos hr hR
  have : (1 / 2 : ℝ) ≤ r / R := by
    calc (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      _ ≤ Real.exp (Real.log (r / R)) := Real.exp_le_exp.mpr h1
      _ = _ := Real.exp_log hq
  rwa [le_div_iff₀ hR] at this

lemma lowerH_alg {sx s0 R r E cT P Pl : ℝ} (hcT : 0 ≤ cT) (_hs0 : 0 ≤ s0) (hPl : 0 ≤ Pl) (hsx : 0 ≤ sx)
    (hE : 0 ≤ E) (hs : s0 ≤ sx) (hP : Pl ≤ P) (hov : cT * sx * P ≤ sx * R * E) (hr : 1 / 2 * R ≤ r) :
    1 / 2 * cT * s0 * Pl ≤ sx * r * E := by
  have h1 : s0 * Pl ≤ sx * P := mul_le_mul hs hP hPl hsx
  have h2 : 1 / 2 * cT * s0 * Pl ≤ 1 / 2 * (cT * sx * P) := by nlinarith [mul_le_mul_of_nonneg_left h1 hcT]
  have h3 : sx * (1 / 2 * R) * E ≤ sx * r * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hsx) hE
  nlinarith

lemma big_pow_lt {A cc c' : ℝ} (hc' : 0 < c') (h : A + 1 ≤ cc * c' ^ (1 / 10 : ℝ)) :
    A * √c' < cc * c' ^ (3 / 5 : ℝ) := by
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hc'
  have h35 : c' ^ (3 / 5 : ℝ) = c' ^ (1 / 10 : ℝ) * √c' := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc']; norm_num
  rw [h35, ← mul_assoc]
  nlinarith

/-- **The overshoot window of Region I(b) at level `f`** (`ut:I`(b), `ut:T2` Region I(b)): for every `f ≥ 1`,
`N ≥ f`, `M`, `E ≥ 0` there are `Σ₀ > 0` and `c > 0` such that for large `c'`, every finite modification with
`|σ_k| ≤ M` (`f ≤ k ≤ N`), `0 ≤ ε'_k ≤ E λ` (`f < k ≤ N`) and every `x` with
`ξ_* + λ Σ₀ ≤ x ≤ ξ_* + c'^{-2/5}`:
`Re h₀^D(x) e^{c' L(x)} ≥ c (2/(π(x - ξ_*)))^{2 n₁}`, `n₁ = f - 1/4`.  `Σ₀` is chosen so that `lemma_P_b` gives
`B_D ≥ ½ B_ref` and `x` lies in a cell `n ≥ max(N_ov, f + 1)` of `band_overshoot_K5`. -/
theorem designProfile_overshoot_lower (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) :
    ∃ Sg0 cc : ℝ, 0 < Sg0 ∧ 0 < cc ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ,
      (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
        cc * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) ≤
          (designProfile c' f N (1 / 4) σ ε (x : ℂ)).re * Real.exp (c' * edgeL x) := by
  obtain ⟨CP, hCP, hP⟩ := lemma_P_b f N hf hfN M E
  obtain ⟨Nov, cT, hNov, hcT, hov⟩ := band_overshoot_K5 (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨Cg', hCg', hgapev⟩ := siteGap_eventually_le
  have hxi := xiStar_pos
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = max (phiQuantile ((N : ℝ) + 2)) M := ⟨_, rfl⟩
  obtain ⟨Mov, hMov⟩ : ∃ Mov : ℕ, Mov = max Nov (f + 1) := ⟨_, rfl⟩
  have hMov1 : 1 ≤ Mov := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hΦ0 : 0 ≤ phiQuantile ((Mov : ℝ) + 2) := phiQuantile_add_two_nonneg Mov
  have hΦN0 : 0 < phiQuantile ((N : ℝ) + 2) := phiQuantile_add_two_pos N
  have hsge : phiQuantile ((N : ℝ) + 2) ≤ s := hsdef ▸ le_max_left _ _
  have hMs : M ≤ s := hsdef ▸ le_max_right _ _
  have _hs0 : 0 < s := lt_of_lt_of_le hΦN0 hsge
  have hCPl : 0 ≤ CP / Real.log 2 := div_nonneg hCP hlog2.le
  obtain ⟨Sg0, hSg0⟩ : ∃ Sg0 : ℝ, Sg0 = 4 * s + CP / Real.log 2 + phiQuantile ((Mov : ℝ) + 2) + 1 :=
    ⟨_, rfl⟩
  have hSg0pos : 0 < Sg0 := by rw [hSg0]; linarith
  have hS1 : 4 * s ≤ Sg0 := by rw [hSg0]; linarith
  have hS2 : CP / Real.log 2 ≤ Sg0 := by rw [hSg0]; linarith
  have hS3 : phiQuantile ((Mov : ℝ) + 2) ≤ Sg0 := by rw [hSg0]; linarith
  have hS4 : phiQuantile ((N : ℝ) + 2) < Sg0 := by rw [hSg0]; linarith
  obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = (1 / 2) * cT * (1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2) := ⟨_, rfl⟩
  have hccpos : 0 < cc := by rw [hcc]; positivity
  refine ⟨Sg0, cc, hSg0pos, hccpos, ?_⟩
  have hlamM : ∀ᶠ c' in atTop, lambdaComb c' * M ≤ xiStar := by
    have h := tendsto_lambdaComb_atTop.mul_const M
    rw [zero_mul] at h
    exact h.eventually_le_const hxi
  have hlamE : ∀ᶠ c' in atTop, E * lambdaComb c' ≤ 1 / 2 := by
    have h := tendsto_lambdaComb_atTop.const_mul E
    rw [mul_zero] at h
    exact h.eventually_le_const (by norm_num)
  filter_upwards [hP (η₀ := 1 / 4) (by norm_num) le_rfl, hov, hgapev, hlamM, hlamE,
    tail_ne_zero_of_refComb_ne_zero f N hfN (η₀ := 1 / 4) (by norm_num) le_rfl,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)]
    with c' hPc hovc hgapc hlM hlE htailc hcpos hc1 σ ε hM hεE x hx1 hx2
  obtain ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_half⟩ := hgapc
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  have hlam0 : 0 ≤ lambdaComb c' := hlam.le
  have hu1 : c' ^ (-(2 / 5 : ℝ)) ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hux : lambdaComb c' * Sg0 ≤ x - xiStar := by linarith
  have hupos : 0 < x - xiStar := lt_of_lt_of_le (mul_pos hlam hSg0pos) hux
  have hx0 : 0 < x := by linarith
  have h4s : 4 * s * lambdaComb c' ≤ 1 * (lambdaComb c' * Sg0) := by
    have := mul_le_mul_of_nonneg_left hS1 hlam0
    linarith
  have hsite := design_site_facts (s := s) (x := x) (u := lambdaComb c' * Sg0) hlam0 hlM hMs h4s
    (mul_pos hlam hSg0pos) (by linarith) hM
  have hεw : ∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ 1 / 2 := fun k hk hkN =>
    ⟨(hεE k hk hkN).1, (hεE k hk hkN).2.trans hlE⟩
  obtain ⟨r, hr, hr0, hrpos⟩ := designComb_ofReal hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half f N σ ε hsite hεw hfN
  have hχMov : chiQuantile c' (Mov : ℝ) ≤ x := by
    have h := (refSite_bounds hcpos hMov1 (le_refl Mov)).2
    have := mul_le_mul_of_nonneg_left hS3 hlam0
    linarith
  have hχ1 : chiQuantile c' (f : ℝ) < x := by
    have h1 : chiQuantile c' (f : ℝ) ≤ xiStar + lambdaComb c' * phiQuantile ((N : ℝ) + 2) :=
      (refSite_bounds hcpos hf hfN).2
    have h2 := mul_lt_mul_of_pos_left hS4 hlam
    linarith
  obtain ⟨-, -, -, -, h0_norm⟩ := refComb_re_nonneg_of_gt hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half hf hχ1
  have hsech : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have hov1 := hovc f x hf (hMov ▸ hχMov)
  have hsechlow := sech_lower hx0.le (by linarith : x ≤ xiStar + 1)
  have hnormD : ‖designComb c' f N (1 / 4) σ ε (x : ℂ)‖ = r := by
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hHre : (designProfile c' f N (1 / 4) σ ε (x : ℂ)).re =
      1 / Real.cosh (π * x / 2) ^ 2 * r := by
    rw [designProfile_ofReal hr, Complex.ofReal_re]
  have hE : 0 < Real.exp (c' * slitL x) := Real.exp_pos _
  have hPi : 0 < 2 / (π * (x - xiStar)) := by have := Real.pi_pos; positivity
  have hrhs : 0 < cT * (1 / Real.cosh (π * x / 2) ^ 2) *
      (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) :=
    mul_pos (mul_pos hcT hsech) (Real.rpow_pos_of_pos hPi _)
  have hovpos : 0 < h0Comb c' f (1 / 4) x * Real.exp (c' * slitL x) := lt_of_lt_of_le hrhs hov1
  have hh0pos : 0 < h0Comb c' f (1 / 4) x := by
    by_contra hneg
    push Not at hneg
    exact absurd hovpos (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hneg hE.le))
  have hrefpos : 0 < ‖refComb c' f (1 / 4) (x : ℂ)‖ := by
    rw [h0_norm] at hh0pos
    exact pos_of_mul_pos_right hh0pos hsech.le
  have hrp : 0 < r := hrpos (htailc x (norm_pos_iff.mp hrefpos))
  have h4s' : xiStar + 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ x := by
    rw [← hsdef]; linarith
  have hPbd := hPc σ ε hM hεE x h4s'
  rw [hnormD] at hPbd
  have hlogle : |Real.log (r / ‖refComb c' f (1 / 4) (x : ℂ)‖)| ≤ Real.log 2 := by
    refine hPbd.trans ?_
    have hl : lambdaComb c' / (x - xiStar) ≤ 1 / Sg0 := by
      rw [div_le_div_iff₀ hupos hSg0pos]; linarith
    calc CP * (lambdaComb c' / (x - xiStar)) ≤ CP * (1 / Sg0) := mul_le_mul_of_nonneg_left hl hCP
      _ = CP / Sg0 := by ring
      _ ≤ Real.log 2 := by
        rw [div_le_iff₀ hSg0pos]
        have := (div_le_iff₀ hlog2).mp hS2
        linarith
  have hr_ge := half_le_of_log_le hrp hrefpos hlogle
  have hex : Real.exp (c' * slitL x) = Real.exp (c' * edgeL x) := by rw [exp_slitL_eq_edgeL hx0.le]
  rw [hHre, ← hex, hcc]
  have hov2 : cT * (1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) ≤
      1 / Real.cosh (π * x / 2) ^ 2 * ‖refComb c' f (1 / 4) (x : ℂ)‖ * Real.exp (c' * slitL x) := by
    rw [← h0_norm]; exact hov1
  have hsl : 0 ≤ 1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2 := by positivity
  have hP0 : 0 ≤ (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) := Real.rpow_nonneg hPi.le _
  have := lowerH_alg hcT.le hsl hP0 hsech.le hE.le hsechlow le_rfl hov2 hr_ge
  calc 1 / 2 * cT * (1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f)
      ≤ 1 / Real.cosh (π * x / 2) ^ 2 * r * Real.exp (c' * slitL x) := this
    _ = _ := by rw [hex]

/-- **Proposition I (b), lower bound** (`ut:I`(b)): for the `f = 1` finite modifications at fixed sites `σs` there is
`Σ₀ > 0` such that for every threshold `A` and large `c'`, every `x ∈ [ξ_* + λ Σ₀, ξ_I]` satisfies `x ≥ ξ_*/2` and
`A √c' < h₀(x) e^{c' L(x)}` (the overshoot `≳ c'^{3/5}`). -/
theorem proposition_I_b_sig_lower (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∃ Sg0 : ℝ, 0 < Sg0 ∧ ∀ A : ℝ, ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      xiStar / 2 ≤ x ∧ A * √c' <
        (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re * Real.exp (c' * edgeL x) := by
  obtain ⟨Cg, hCg, hfam⟩ := designWidth1_family N hη0.le hη1
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
      fun k hk hkN => Finset.single_le_sum (f := fun j => |σs j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨Sg0, cc, hSg0, hcc, hov⟩ := designProfile_overshoot_lower 1 N le_rfl hN M Cg
  have hxi := xiStar_pos
  refine ⟨Sg0, hSg0, fun A => ?_⟩
  obtain ⟨cc', hcc'⟩ : ∃ cc' : ℝ, cc' = cc * (2 / π) ^ (3 / 2 : ℝ) := ⟨_, rfl⟩
  have hcc'pos : 0 < cc' := by rw [hcc']; positivity
  have hbig : ∀ᶠ c' in atTop, A + 1 ≤ cc' * c' ^ (1 / 10 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).const_mul_atTop hcc'pos
    exact h.eventually_ge_atTop (A + 1)
  filter_upwards [hov, hfam, hbig, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)]
    with c' hovc hfamc hbigc hcpos hc1 x hx1 hx2
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  have hu1 : c' ^ (-(2 / 5 : ℝ)) ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hux : lambdaComb c' * Sg0 ≤ x - xiStar := by linarith
  have hupos : 0 < x - xiStar := lt_of_lt_of_le (mul_pos hlam hSg0) hux
  have huup : x - xiStar ≤ c' ^ (-(2 / 5 : ℝ)) := by linarith
  refine ⟨by linarith, ?_⟩
  have hov' := hovc σs (designWidth1 c' η) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => hfamc k hk hkN) x hx1 hx2
  have hn1 : 2 * n1Comb 1 = 3 / 2 := by unfold n1Comb; norm_num
  rw [hn1] at hov'
  have hpow := pow_overshoot_gen (a := 3 / 2) hcpos hupos huup (by norm_num)
  rw [show (2 / 5 : ℝ) * (3 / 2) = 3 / 5 by norm_num] at hpow
  have hQ : cc' * c' ^ (3 / 5 : ℝ) ≤
      (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re * Real.exp (c' * edgeL x) := by
    refine le_trans ?_ hov'
    rw [hcc', mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow hcc.le
  exact lt_of_lt_of_le (big_pow_lt hcpos hbigc) hQ

/-- **Proposition I (b)** (`ut:I`) for the `f = 1` finite modifications at fixed sites `σs`: see
`proposition_I_b`, the case `σs = designSigma1 d`. -/
theorem proposition_I_b_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ Sg0 : ℝ, 0 < Sg0 ∧ ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      0 < twoG c' 1 N (1 / 4) σs (designWidth1 c' η) x := by
  obtain ⟨A, hA0, hA⟩ := twoGW_pos_of_lower 0 1 (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨Sg0, hSg0, hlow⟩ := proposition_I_b_sig_lower N hN hη0 hη1 σs
  refine ⟨Sg0, hSg0, ?_⟩
  filter_upwards [hlow A, hA, designWidth1_admissible N hN hη0.le hη1 σs] with c' hlowc hAc hadm x hx1 hx2
  obtain ⟨hxhalf, hQ⟩ := hlowc x hx1 hx2
  rw [← twoGW_zero]
  exact hAc N σs (designWidth1 c' η) hadm x hxhalf hQ

/-- **Proposition I (b)** (`ut:I`): there is `Σ₀ > 0` such that for large `c'` and every
`x ∈ [ξ_* + λ Σ₀, ξ_I]`, `ξ_I = ξ_* + c'^{-2/5}`, one has `2 g(c' x²/3) > 0`.  `Σ₀` is chosen so that
`lemma_P_b` gives `B_D ≥ ½ B_ref` and `x ≥ χ_{max(N_ov, 2)}`; then `band_overshoot_K5` gives
`h₀^{ref} e^{c'L} ≥ c_T sech²(πx/2) (2/(π(x - ξ_*)))^{2n₁} ≳ c'^{2 n₁ θ} = c'^{3/5}`, `θ = 2/5`, which
exceeds the `√c'` bound of `SD_G` for `ĥ₀`. -/
theorem proposition_I_b (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∃ Sg0 : ℝ, 0 < Sg0 ∧ ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      0 < twoG c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η) x :=
  proposition_I_b_sig N hN hη0 hη1 (designSigma1 d)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.pos_of_lower_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pos_of_lower_hankel

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.pow_overshoot_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pow_overshoot_gen

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.designProfile_overshoot_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_overshoot_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_a_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_a_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_b_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_b_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_a

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_I_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_I_b

end FormalResearch.ModularBootstrap.Upper.Positivity
