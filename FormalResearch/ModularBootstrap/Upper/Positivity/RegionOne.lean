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

The overlap with Region II and the passage to `t ≥ t_f + 1` are in `Upper.Positivity.RegionOneAssembly`.

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

/-- **Proposition I (a)** (`ut:I`) for the `f = 1` finite modifications at fixed sites `σs` (first site `σs 1`
arbitrary, sites `2..N` arbitrary): see `proposition_I_a`, the case `σs = designSigma1 d`. -/
theorem proposition_I_a_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) (Sg0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      designSite c' σs 1 + C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) ≤ x →
      x ≤ xiStar + lambdaComb c' * Sg0 →
      0 < twoG c' 1 N (1 / 4) σs (designWidth1 c' η) x := by
  set 𝒦 := sigModFamily N hN hη0.le hη1 σs with h𝒦
  have hd : sigMod N η σs ∈ 𝒦.members := sigModFamily_mem N hN hη0.le hη1 σs
  obtain ⟨w0, hw0, C0, hlow⟩ := lemma_R_lower 𝒦 hd (posLimitWidths_sigMod N hη0 σs) Sg0
  obtain ⟨Cg, hCg, hfam⟩ := designWidth1_family N hη0.le hη1
  set M : ℝ := ∑ k ∈ Finset.Icc 1 N, |σs k| with hMdef
  have hM : ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M := fun k hk hkN =>
    Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_Icc.mpr ⟨hk, hkN⟩)
  obtain ⟨K, hK0, hK⟩ := designProfile_global_bound 1 N le_rfl hN M Cg
    (η₀ := 1 / 4) (by norm_num) (by norm_num)
  have hxi := xiStar_pos
  set A : ℝ := K * √(2 / xiStar) with hA
  have hA0 : 0 ≤ A := by positivity
  set C : ℝ := (A + 1) / (cKtilde * w0) with hC
  have hCpos : 0 < C := by have := cKtilde_pos; positivity
  refine ⟨C, hCpos, ?_⟩
  have hs1 : |σs 1| ≤ M := hM 1 le_rfl hN
  have hlam1 : ∀ᶠ c' in atTop, lambdaComb c' * |σs 1| ≤ xiStar / 2 := by
    have h := tendsto_lambdaComb_atTop.mul_const |σs 1|
    rw [zero_mul] at h
    exact h.eventually_le_const (by positivity)
  filter_upwards [hK, sigProfile_re_eq_modifiedH0 N hη0.le hη1 σs, hfam, hlam1,
    eventually_ge_atTop C0, eventually_gt_atTop (0 : ℝ)]
    with c' hKc hre hfamc hl1 hc0 hcpos x hx1 hx2
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
  -- `x ≥ ξ_*/2`
  have hxhalf : xiStar / 2 ≤ x := by
    unfold designSite at hx1
    have h1 : 0 ≤ C * lambdaComb c' * c' ^ (-(1 / 2 : ℝ)) := by positivity
    have h2 : -(lambdaComb c' * |σs 1|) ≤ lambdaComb c' * σs 1 := by
      have := neg_abs_le (σs 1)
      nlinarith
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxhalf
  -- the bound on the transform
  have hglob := hKc σs (designWidth1 c' η) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => hfamc k hk hkN) x hx0
  have hsq : √(c' / x) ≤ √(2 / xiStar) * √c' := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hx0]
    have : 2 / xiStar * c' * x ≥ 2 / xiStar * c' * (xiStar / 2) :=
      mul_le_mul_of_nonneg_left hxhalf (by positivity)
    have e : 2 / xiStar * c' * (xiStar / 2) = c' := by field_simp
    linarith
  have hhat : Real.exp (c' * edgeL x) * ‖edgeHankel c' (designProfile c' 1 N (1 / 4) (σs)
      (designWidth1 c' η)) (c' * x ^ 2 / 3)‖ ≤ A * √c' := by
    refine hglob.trans ?_
    calc K * √(c' / x) ≤ K * (√(2 / xiStar) * √c') := mul_le_mul_of_nonneg_left hsq hK0
      _ = A * √c' := by rw [hA]; ring
  -- the lower bound for `h₀`
  have hH := hre x
  rw [exp_slitL_eq_edgeL hx0.le] at hlow'
  have hsqrt : c' * c' ^ (-(1 / 2 : ℝ)) = √c' := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hcpos.le (by norm_num)]
    norm_num
  have hlow2 : (A + 1) * √c' ≤ (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η)
      (x : ℂ)).re * Real.exp (c' * edgeL x) := by
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
  -- conclusion
  unfold twoG
  rw [Complex.sub_re]
  have hre_le : (edgeHankel c' (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η))
      (c' * x ^ 2 / 3)).re ≤ ‖edgeHankel c' (designProfile c' 1 N (1 / 4) (σs)
      (designWidth1 c' η)) (c' * x ^ 2 / 3)‖ := Complex.re_le_norm _
  have hexp := Real.exp_pos (c' * edgeL x)
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hcpos
  have hprod : 0 < Real.exp (c' * edgeL x) *
      ((designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re -
        (edgeHankel c' (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η))
          (c' * x ^ 2 / 3)).re) := by
    have : Real.exp (c' * edgeL x) *
        ((designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re -
        (edgeHankel c' (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η))
          (c' * x ^ 2 / 3)).re) ≥
        (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re *
          Real.exp (c' * edgeL x) - Real.exp (c' * edgeL x) * ‖edgeHankel c' (designProfile c' 1 N
          (1 / 4) σs (designWidth1 c' η)) (c' * x ^ 2 / 3)‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hre_le hexp.le]
    nlinarith
  exact pos_of_mul_pos_right hprod hexp.le

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

lemma sub_pos_of_bounds {Hh R N E Q Q' : ℝ} (hE : 0 < E) (hR : R ≤ N) (hlow : Q ≤ Hh * E)
    (hup : E * N ≤ Q') (hQ : Q' < Q) : 0 < Hh - R := by
  have h1 : E * R ≤ E * N := mul_le_mul_of_nonneg_left hR hE.le
  have : 0 < E * (Hh - R) := by nlinarith
  exact pos_of_mul_pos_right this hE.le

lemma phiQuantile_add_two_pos (N : ℕ) : 0 < phiQuantile ((N : ℝ) + 2) := by
  unfold phiQuantile
  apply Real.rpow_pos_of_pos
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

lemma phiQuantile_add_two_nonneg (N : ℕ) : 0 ≤ phiQuantile ((N : ℝ) + 2) :=
  (phiQuantile_add_two_pos N).le

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

lemma pow_overshoot {c' u : ℝ} (hc' : 0 < c') (hu : 0 < u) (huup : u ≤ c' ^ (-(2 / 5 : ℝ))) :
    (2 / π) ^ (3 / 2 : ℝ) * c' ^ (3 / 5 : ℝ) ≤ (2 / (π * u)) ^ (3 / 2 : ℝ) := by
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
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc'.le,
    show (2 / 5 : ℝ) * (3 / 2) = 3 / 5 by norm_num] at h2
  exact h2

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

/-- **Proposition I (b)** (`ut:I`) for the `f = 1` finite modifications at fixed sites `σs`: see
`proposition_I_b`, the case `σs = designSigma1 d`. -/
theorem proposition_I_b_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ Sg0 : ℝ, 0 < Sg0 ∧ ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      0 < twoG c' 1 N (1 / 4) σs (designWidth1 c' η) x := by
  obtain ⟨Cg, hCg, hfam⟩ := designWidth1_family N hη0.le hη1
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
      fun k hk hkN => Finset.single_le_sum (f := fun j => |σs j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨CP, hCP, hP⟩ := lemma_P_b 1 N le_rfl hN M Cg
  obtain ⟨Nov, cT, hNov, hcT, hov⟩ := band_overshoot_K5 (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨K, hK0, hK⟩ := designProfile_global_bound 1 N le_rfl hN M Cg
    (η₀ := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Cg', hCg', hgapev⟩ := siteGap_eventually_le
  have hxi := xiStar_pos
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = max (phiQuantile ((N : ℝ) + 2)) M := ⟨_, rfl⟩
  obtain ⟨Mov, hMov⟩ : ∃ Mov : ℕ, Mov = max Nov (1 + 1) := ⟨_, rfl⟩
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
  refine ⟨Sg0, hSg0pos, ?_⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * √(2 / xiStar) := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = (1 / 2) * cT * (1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2) *
      (2 / π) ^ (3 / 2 : ℝ) := ⟨_, rfl⟩
  have hccpos : 0 < cc := by rw [hcc]; positivity
  have hlamM : ∀ᶠ c' in atTop, lambdaComb c' * M ≤ xiStar := by
    have h := tendsto_lambdaComb_atTop.mul_const M
    rw [zero_mul] at h
    exact h.eventually_le_const hxi
  have hbig : ∀ᶠ c' in atTop, A + 1 ≤ cc * c' ^ (1 / 10 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).const_mul_atTop hccpos
    exact h.eventually_ge_atTop (A + 1)
  filter_upwards [hK, hP (η₀ := 1 / 4) (by norm_num) le_rfl, hov, hfam, hgapev, hlamM, hbig,
    tail_ne_zero_of_refComb_ne_zero 1 N hN (η₀ := 1 / 4) (by norm_num) le_rfl,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)]
    with c' hKc hPc hovc hfamc hgapc hlM hbigc htailc hcpos hc1 x hx1 hx2
  obtain ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_half⟩ := hgapc
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  have hlam0 : 0 ≤ lambdaComb c' := hlam.le
  have hu1 : c' ^ (-(2 / 5 : ℝ)) ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hux : lambdaComb c' * Sg0 ≤ x - xiStar := by linarith
  have hupos : 0 < x - xiStar := lt_of_lt_of_le (mul_pos hlam hSg0pos) hux
  have huup : x - xiStar ≤ c' ^ (-(2 / 5 : ℝ)) := by linarith
  have hx0 : 0 < x := by linarith
  have h4s : 4 * s * lambdaComb c' ≤ 1 * (lambdaComb c' * Sg0) := by
    have := mul_le_mul_of_nonneg_left hS1 hlam0
    linarith
  have hsite := design_site_facts (s := s) (x := x) (u := lambdaComb c' * Sg0) hlam0 hlM hMs h4s
    (mul_pos hlam hSg0pos) (by linarith) hM
  have hεw : ∀ k, 1 < k → k ≤ N → 0 ≤ designWidth1 c' η k ∧ designWidth1 c' η k ≤ 1 / 2 := by
    intro k hk hkN
    refine ⟨(hfamc k hk hkN).1, ?_⟩
    have hsg1 : siteGap c' k ≤ 1 / 2 := (hgap_k k (by omega)).trans hgap_half
    unfold designWidth1
    calc η * siteGap c' k ≤ (1 / 4) * (1 / 2) :=
          mul_le_mul hη1 hsg1 (siteGap_nonneg hcpos (by omega)) (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  obtain ⟨r, hr, hr0, hrpos⟩ := designComb_ofReal hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half 1 N σs (designWidth1 c' η) hsite hεw hN
  have hχMov : chiQuantile c' (Mov : ℝ) ≤ x := by
    have h := (refSite_bounds hcpos hMov1 (le_refl Mov)).2
    have := mul_le_mul_of_nonneg_left hS3 hlam0
    linarith
  have hχ1 : chiQuantile c' ((1 : ℕ) : ℝ) < x := by
    have h1 : chiQuantile c' ((1 : ℕ) : ℝ) ≤ xiStar + lambdaComb c' * phiQuantile ((N : ℝ) + 2) :=
      (refSite_bounds hcpos (le_refl 1) hN).2
    have h2 := mul_lt_mul_of_pos_left hS4 hlam
    linarith
  obtain ⟨-, -, -, -, h0_norm⟩ := refComb_re_nonneg_of_gt hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half (f := 1) le_rfl hχ1
  have hsech : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have hov1 := hovc 1 x le_rfl (hMov ▸ hχMov)
  have hn1 : 2 * n1Comb 1 = 3 / 2 := by unfold n1Comb; norm_num
  rw [hn1] at hov1
  have hpow := pow_overshoot hcpos hupos huup
  have hsechlow := sech_lower hx0.le (by linarith : x ≤ xiStar + 1)
  have hnormD : ‖designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)‖ = r := by
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hHre : (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re =
      1 / Real.cosh (π * x / 2) ^ 2 * r := by
    rw [designProfile_ofReal hr, Complex.ofReal_re]
  have hE : 0 < Real.exp (c' * slitL x) := Real.exp_pos _
  have hPi : 0 < 2 / (π * (x - xiStar)) := by have := Real.pi_pos; positivity
  have hrhs : 0 < cT * (1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (3 / 2 : ℝ) :=
    mul_pos (mul_pos hcT hsech) (Real.rpow_pos_of_pos hPi _)
  have hovpos : 0 < h0Comb c' 1 (1 / 4) x * Real.exp (c' * slitL x) := lt_of_lt_of_le hrhs hov1
  have hh0pos : 0 < h0Comb c' 1 (1 / 4) x := by
    by_contra hneg
    push Not at hneg
    exact absurd hovpos (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hneg hE.le))
  have hrefpos : 0 < ‖refComb c' 1 (1 / 4) (x : ℂ)‖ := by
    rw [h0_norm] at hh0pos
    exact pos_of_mul_pos_right hh0pos hsech.le
  have hrp : 0 < r := hrpos (htailc x (norm_pos_iff.mp hrefpos))
  have h4s' : xiStar + 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ x := by
    rw [← hsdef]; linarith
  have hPbd := hPc σs (designWidth1 c' η) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => hfamc k hk hkN) x h4s'
  rw [hnormD] at hPbd
  have hlogle : |Real.log (r / ‖refComb c' 1 (1 / 4) (x : ℂ)‖)| ≤ Real.log 2 := by
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
  have hQ : cc * c' ^ (3 / 5 : ℝ) ≤
      (designProfile c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re *
        Real.exp (c' * edgeL x) := by
    rw [hHre, ← hex, hcc]
    have hov2 : cT * (1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (3 / 2 : ℝ) ≤
        1 / Real.cosh (π * x / 2) ^ 2 * ‖refComb c' 1 (1 / 4) (x : ℂ)‖ * Real.exp (c' * slitL x) := by
      rw [← h0_norm]; exact hov1
    have hsl : 0 ≤ 1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2 := by positivity
    have := lowerH_alg hcT.le hsl (by positivity) hsech.le hE.le hsechlow hpow hov2 hr_ge
    linarith [this]
  have hxhalf : xiStar / 2 ≤ x := by linarith
  have hglob := hKc σs (designWidth1 c' η) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => hfamc k hk hkN) x hx0
  have hhat := edge_bound_sqrt hK0 hcpos hxhalf hglob
  have hlt : K * √(2 / xiStar) * √c' < cc * c' ^ (3 / 5 : ℝ) := by
    rw [← hA] at *
    exact big_pow_lt hcpos hbigc
  unfold twoG
  rw [Complex.sub_re]
  exact sub_pos_of_bounds (Real.exp_pos _) (Complex.re_le_norm _) hQ hhat hlt

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
