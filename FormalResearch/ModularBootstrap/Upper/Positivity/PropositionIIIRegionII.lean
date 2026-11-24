module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOneAssembly
public import FormalResearch.ModularBootstrap.Upper.Positivity.RpAmplitudeParams
public import FormalResearch.ModularBootstrap.Upper.Bump.Floor
public import FormalResearch.ModularBootstrap.Upper.Bump.PhaseHyp

/-!
# Proposition III, Region II: the bumped designs at weight `w = p + 1` (`ut:III`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition III (`ut:III`), "Near-tip Region II" and
"Macroscopic Region II", with `fw:e1.6`, `fw:e2.2`, `fw:e2.3`, `fw:e3.1`, `fw:e3.5` and the parameter selection.

Fix `p` and the parameters `P : RpParams p` (`r_p`, `X_p`, `η_big(p)`, `Upper.Positivity.rpParams`); `P.bumpData` is the
bump of `Upper.Bump`.  Let `(f, N₀, σ, ε)` be a member of the compact family of finite modifications `B_D^{(f)}`
(`|σ_k| ≤ M`, `0 ≤ ε_k ≤ E λ`; any `f ≥ 1`) and `N ≥ N₀` a cut above the block `[ξ_* + 2r_p, X_p]`.  The bumped design is
`designComb c' f N (1/4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1/4) ε)` and
`twoGW p` is `2 g_w`, `w = p + 1`.

* `phaseHyp_compact`: members of the compact family satisfy `PhaseHyp` with total pair change `≤ 1` for `c'` large;
  with `Bump.bumped_phaseHyp` the bumped comb satisfies `PhaseHyp … 2`, so the order-`p` phase package
  (`Ramped.phase_packageP`) gives the transform bound at order `p`.
* `norm_le_rhoRp_mul_lev`: the transform bound `‖𝓗_{p+1} h₀‖ ≤ 𝒜_x R_p (1 + w)` and `𝒜_x ≤ vρ_∞ Lev`, with
  `vρ_∞(x; n_eff) R_p ≤ ρ_∞ R_p` (`fw:e1.6`) give `‖𝓗_{p+1} h₀‖ ≤ ρ_∞ R_p (1 + w) Lev`.
* `bumped_regionII`: for `c'` large, every family member, every cut above the block and every `x ≥ ξ_* + c'^{-2/5}`:
  `Lev^{(f)}(x)/20 ≤ 2 g_w(c' x²/3)`.  The three ranges are the near-tip range `x ≤ ξ_* + 3r_p` (floor `0.6965` of the
  unbumped design, `R_bump ≥ 1`, against `ρ_∞ R_p ≤ 0.10`, `fw:e2.2`), the macroscopic range
  `ξ_* + 3r_p ≤ x ≤ X_p - 1` (boosted floor `bump_floor_family` against `M_amp` and `bumpFloor η_big > 2 M_amp + 1`) and the far
  range `x ≥ X_p - 1` (`R_bump ≥ 1` against `ρ_∞ R_p ≤ 0.60`, `fw:e2.3`).
* `bumped_regionII_pos`: `2 g_w > 0` on Region II.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Upper.Ramped

/-! ### 1. The bump of the parameter selection and `PhaseHyp` for the compact family -/

/-- The bump `(r_p, X_p, η_big(p))` of the parameter selection `P : RpParams p` as `Upper.Bump` data. -/
noncomputable def RpParams.bumpData {p : ℕ} (P : RpParams p) : BumpData :=
  ⟨P.r, P.X, P.eta, P.r_pos, P.X_gt, P.eta_ge⟩

/-- Members of the compact family `|σ_k| ≤ M`, `0 ≤ ε_k ≤ E λ` satisfy `PhaseHyp` with total pair change `≤ 1`
for `c'` large (the pair change of a member is `O(λ)`). -/
theorem phaseHyp_compact (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') → PhaseHyp c' f N η₀ σ ε 1 := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  set s : ℝ := max (phiQuantile ((N : ℝ) + 2)) M with hs_def
  have hMs : M ≤ s := le_max_right _ _
  have hΦs : phiQuantile ((N : ℝ) + 2) ≤ s := le_max_left _ _
  set Cp : ℝ := 2 * s + ((N - f : ℕ) : ℝ) * (4 * s + 2 * E + Cg / 2) with hCp
  have hlim : ∀ᶠ c' in atTop, Cp * lambdaComb c' ≤ 1 := by
    have h := tendsto_lambdaComb_atTop.const_mul Cp
    rw [mul_zero] at h
    exact h.eventually_le_const zero_lt_one
  filter_upwards [designAdmissible_eventually f N hf hfN M E hη₀0 hη₀1, h_ev, hlim,
    eventually_gt_atTop (0 : ℝ)] with c' hAd ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hl hc' σ ε hσ hε
  have hA := hAd σ ε hσ hε
  have hpc := designPairChange_le_compact hc' hf hfN hη₀0 hη₀1 hσ hε hA hMs hΦs
    (fun k hk => (hgap_k k hk).trans (hgap_1_bd.trans hcd1_bd))
  exact ⟨hfN, hA, hpc.trans (by rw [← hCp]; exact hl)⟩

/-! ### 2. The transform against the level -/

/-- **The transform against the level** (`fw:e1.6`): from `‖𝓗_{p+1} h₀‖ ≤ 𝒜_x R_p (1 + w)`, `x > χ_{f+1/2}` and
`x > ξ_*`: `‖𝓗_{p+1} h₀‖ ≤ ρ_∞(x) R_p(x) (1 + w) Lev^{(f)}(x)`. -/
lemma norm_le_rhoRp_mul_lev {c' x : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f)
    (hx : chiQuantile c' ((f : ℝ) + 1 / 2) < x) (hxi : xiStar < x) (p : ℕ) {nh w : ℝ} (hw : 0 ≤ w)
    (h : nh ≤ combAmplitude c' x * fwsdRatio p x * (1 + w)) :
    nh ≤ rhoRp p x * (1 + w) * levComb c' f x := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hn1 : (3 / 4 : ℝ) ≤ n1Comb f := by unfold n1Comb; linarith
  have hA := combAmplitude_le_vRhoInfty_mul_levComb hc' hf hx
  have hR := rhoRp_neff_le p hn1 hxi
  have hR0 : 0 ≤ rAmp p x := rAmp_nonneg p (xiStar_pos.trans hxi).le
  have hlev := levComb_pos c' f x
  rw [fwsdRatio_eq_rAmp p hxi] at h
  refine h.trans ?_
  have h1 : combAmplitude c' x * rAmp p x ≤ vRhoInfty x (n1Comb f) * levComb c' f x * rAmp p x :=
    mul_le_mul_of_nonneg_right hA hR0
  calc combAmplitude c' x * rAmp p x * (1 + w)
      ≤ vRhoInfty x (n1Comb f) * levComb c' f x * rAmp p x * (1 + w) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = (vRhoInfty x (n1Comb f) * rAmp p x) * (1 + w) * levComb c' f x := by ring
    _ ≤ rhoRp p x * (1 + w) * levComb c' f x := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR (by linarith)) hlev.le

/-! ### 3. The arithmetic of the three ranges -/

/-- The closing step: `hh ≤ q (1 + w) Lev` and `c Lev ≤ a` with `q (1 + w) + 1/20 ≤ c` give `Lev/20 ≤ a - hh`. -/
lemma close_of_bounds {Lev a hh q w c : ℝ} (hLev : 0 < Lev) (_hq : 0 ≤ q) (_hw : 0 ≤ w)
    (hhh : hh ≤ q * (1 + w) * Lev) (ha : c * Lev ≤ a) (hc : q * (1 + w) + 1 / 20 ≤ c) :
    1 / 20 * Lev ≤ a - hh := by
  have : (q * (1 + w) + 1 / 20) * Lev ≤ c * Lev := mul_le_mul_of_nonneg_right hc hLev.le
  nlinarith

/-- The unbumped floor `ν Lev ≤ sech² r` from the floor of `proposition_II_floor`, `ν = 0.7 · 0.998² · 0.999`. -/
lemma base_floor_nu {Lev s R r : ℝ} (hs : 0 ≤ s) (hR : 0 < R) (hr : 0 < r)
    (hfl : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * Lev ≤ s * R)
    (hlog : |Real.log (r / R)| ≤ 1 / 1000) :
    (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * Lev ≤ s * r := by
  have hr' := ratio_ge_of_log_le hr hR hlog
  calc (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * Lev
      = (999 / 1000 : ℝ) * ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * Lev) := by ring
    _ ≤ (999 / 1000 : ℝ) * (s * R) := mul_le_mul_of_nonneg_left hfl (by norm_num)
    _ = s * ((999 / 1000 : ℝ) * R) := by ring
    _ ≤ s * r := mul_le_mul_of_nonneg_left hr' hs

/-- The numerical margins: `ν = 0.7 · 0.998² · 0.999` closes the near-tip range (`ρ_∞ R_p ≤ 0.10`) and the far range
(`ρ_∞ R_p ≤ 0.60`) with margin `1/20`. -/
lemma nu_margin_near : (1 / 10 : ℝ) * (1 + 1 / 50) + 1 / 20 ≤
    (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) := by norm_num

lemma nu_margin_far : (6 / 10 : ℝ) * (1 + 1 / 50) + 1 / 20 ≤
    (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) := by norm_num

/-- The macroscopic margin: `bumpFloor H > 2 M + 1`, `M ≥ 0` gives
`M (1 + 1/50) + 1/20 ≤ (1 - 1/100) ((16/5)(H² + 1/4)) ν`. -/
lemma macro_margin {M H : ℝ} (hM : 0 ≤ M) (hfl : 2 * M + 1 < bumpFloor H) :
    M * (1 + 1 / 50) + 1 / 20 ≤
      (1 - 1 / 100 : ℝ) * ((16 / 5) * (H ^ 2 + 1 / 4)) *
        ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) := by
  unfold bumpFloor at hfl
  have h : (1 - 1 / 100 : ℝ) * ((16 / 5) * (H ^ 2 + 1 / 4)) *
        ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) =
      (7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4))) *
        ((1 - 1 / 100 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) := by ring
  rw [h]
  have hk : (98 / 100 : ℝ) ≤ (1 - 1 / 100 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) := by
    norm_num
  have h2 : (98 / 100 : ℝ) * (2 * M + 1) ≤
      (7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4))) *
        ((1 - 1 / 100 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) := by
    have hpos : 0 ≤ 7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4)) := by positivity
    calc (98 / 100 : ℝ) * (2 * M + 1) ≤ (98 / 100 : ℝ) * (7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4))) :=
          mul_le_mul_of_nonneg_left hfl.le (by norm_num)
      _ ≤ _ := by nlinarith
  nlinarith

/-- **Negative regression**: with the unboosted height `η_big = 1/4` (gain `1`) the macroscopic margin does not close once
`M_amp ≥ 7/10` (the floor is `0.6896 Lev`, the transform is `M_amp · 1.02 · Lev`), so `η_big > 1/4` is needed for large `p`. -/
lemma macro_margin_quarter_fails {M : ℝ} (hM : 7 / 10 ≤ M) :
    ¬ M * (1 + 1 / 50) + 1 / 20 ≤
      (1 - 1 / 100 : ℝ) * ((16 / 5) * ((1 / 4 : ℝ) ^ 2 + 1 / 4)) *
        ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) := by
  intro h
  norm_num at h
  linarith

/-! ### 4. Region II for the bumped designs -/

/-- **Proposition III, Region II** (`ut:III`, near-tip and macroscopic Region II; `fw:e1.6`, `fw:e2.2`, `fw:e2.3`,
`fw:e3.5`).  Fix `p`, the parameters `P : RpParams p`, `f ≥ 1`, `N₀ ≥ f`, `M`, `E`.  For `c'` large, every member
`(σ, ε)` of the compact family (`|σ_k| ≤ M`, `0 ≤ ε_k ≤ E λ`, `f ≤ k ≤ N₀`), every cut `N ≥ N₀` above the block
(every index with `χ_k ≤ X_p` is `≤ N`) and every `x ≥ ξ_I = ξ_* + c'^{-2/5}`:
`Lev^{(f)}(x)/20 ≤ 2 g_w(c' x²/3)` for the bumped design. -/
theorem bumped_regionII (p : ℕ) (P : RpParams p) (f N₀ : ℕ) (hf : 1 ≤ f) (hfN₀ : f ≤ N₀) (M E : ℝ) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), N₀ ≤ N →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ P.X → k ≤ N) →
      (∀ k, f ≤ k → k ≤ N₀ → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N₀ → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
        1 / 20 * levComb c' f x ≤
          twoGW p c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε) x := by
  obtain ⟨K, A, Cε, C, KG, hK, hA0, hCε, hC, hKG, hpk⟩ :=
    phase_packageP p f hf (η₀ := 1 / 4) (P := 1 + 1) (θ := 2 / 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hexp : (-1 + 3 * (2 / 5 : ℝ) / 2) = -(2 / 5 : ℝ) := by norm_num
  have e8 : ∀ᶠ c' in atTop, C * c' ^ (-(2 / 5 : ℝ)) ≤ 1 / 50 :=
    (tendsto_rpow_neg_two_fifths.const_mul C).eventually_le_const (by norm_num)
  filter_upwards [phaseHyp_compact f N₀ hf hfN₀ M E (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumped_phaseHyp P.bumpData f hf (η₀ := 1 / 4) (by norm_num) le_rfl, hpk, e8,
    proposition_II_floor f N₀ hf hfN₀ M E,
    bump_floor_family P.bumpData f N₀ hf hfN₀ M E (τ := 1 / 100) (by norm_num),
    bumped_value P.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_one_le P.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    eventually_ge_atTop (1 : ℝ)]
    with c' hph0 hbph hpkc he8 hII hfloorfam hv hR1 hc1 N σ ε hN hcut hσ hε x hx
  have hc' : 0 < c' := lt_of_lt_of_le one_pos hc1
  have hu0 : 0 < c' ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hxi : xiStar < x := by linarith only [hx, hu0]
  have hPH := hbph N₀ N σ ε 1 (hph0 σ ε hσ hε) hN
  obtain ⟨-, -, htrans, -⟩ := hpkc N _ _ hPH
  rw [hexp] at htrans
  obtain ⟨hχf2, R, r, hR, hr, hD, hfl, hlog⟩ := hII σ ε hσ hε x hx
  obtain ⟨hbase, hbump⟩ := hv f N₀ N σ ε x hfN₀ hN
  have hrr : r = combReal c' f N₀ (1 / 4) σ ε x := by
    have := hD.symm.trans hbase
    exact_mod_cast this
  set Rb := bumpFactor P.bumpData c' (1 / 4) N₀ N x with hRb
  have hRb1 : 1 ≤ Rb := hR1 N₀ N x
  set s : ℝ := 1 / Real.cosh (π * x / 2) ^ 2 with hs
  have hspos : 0 < s := by positivity
  have hLev := levComb_pos c' f x
  -- the bumped value is the real number `Rb * r`
  have hbc : designComb c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε)
      (x : ℂ) = ((Rb * r : ℝ) : ℂ) := by
    have h := hbump
    unfold bumpedComb at h
    rw [h, hrr]
  have hprof : (designProfile c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε)
      (x : ℂ)).re = s * (Rb * r) := by
    rw [designProfile_ofReal hbc, Complex.ofReal_re]
  -- the floor of the unbumped design and the monotonicity of the bump
  have hbfl := base_floor_nu hspos.le hR hr hfl hlog
  have hmono : s * r ≤ s * (Rb * r) := by
    refine mul_le_mul_of_nonneg_left ?_ hspos.le
    nlinarith
  -- the transform against the level
  have hnorm := norm_le_rhoRp_mul_lev hc' hf hχf2 hxi p (nh := ‖edgeHankelP p c'
      (designProfile c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε))
      (c' * x ^ 2 / 3)‖) (w := C * c' ^ (-(2 / 5 : ℝ))) (mul_nonneg hC hu0.le)
    (htrans x hx)
  have hw0 : 0 ≤ C * c' ^ (-(2 / 5 : ℝ)) := mul_nonneg hC hu0.le
  have hq0 : 0 ≤ rhoRp p x := rhoRp_nonneg p hxi
  have hhh := (Complex.re_le_norm _).trans hnorm
  have hhh' : _ ≤ rhoRp p x * (1 + C * c' ^ (-(2 / 5 : ℝ))) * levComb c' f x := hhh
  unfold twoGW
  rw [Complex.sub_re, hprof]
  -- the closing step with `w = C c'^{-2/5} ≤ 1/50`
  have hw1 : C * c' ^ (-(2 / 5 : ℝ)) ≤ 1 / 50 := he8
  have hq1 : ∀ q : ℝ, 0 ≤ q → q * (1 + C * c' ^ (-(2 / 5 : ℝ))) ≤ q * (1 + 1 / 50) := fun q hq =>
    mul_le_mul_of_nonneg_left (by linarith) hq
  by_cases hnear : x ≤ xiStar + 3 * P.r
  · have hq : rhoRp p x ≤ 1 / 10 := P.near x hxi (by linarith [P.r_pos])
    refine close_of_bounds hLev hq0 hw0 hhh' (c := (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000))
      (hbfl.trans hmono) ?_
    have := hq1 _ hq0
    nlinarith [nu_margin_near]
  · push Not at hnear
    by_cases hmac : x ≤ P.X - 1
    · have hq : rhoRp p x ≤ P.M := P.macro_le ⟨hnear.le, hmac⟩
      obtain ⟨rb, hrb, hfin⟩ := hfloorfam N σ ε hN hcut hσ hε x hnear.le hmac
      have hrb' : rb = Rb * r := by
        have h1 : designComb c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε)
            (x : ℂ) = (rb : ℂ) := hrb
        have := h1.symm.trans hbc
        exact_mod_cast this
      rw [hrb'] at hfin
      refine close_of_bounds hLev hq0 hw0 hhh' (c := (1 - 1 / 100 : ℝ) * ((16 / 5) * (P.bumpData.H ^ 2 + 1 / 4)) *
        ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000))) ?_ ?_
      · refine le_trans (le_of_eq ?_) hfin
        ring
      · have hmg := macro_margin P.M_nonneg P.floor_gt
        have hMq : rhoRp p x * (1 + 1 / 50) ≤ P.M * (1 + 1 / 50) :=
          mul_le_mul_of_nonneg_right hq (by norm_num)
        have := hq1 _ hq0
        have hHd : P.bumpData.H = P.eta := rfl
        rw [hHd]
        nlinarith
    · push Not at hmac
      have hq : rhoRp p x ≤ 6 / 10 := P.far x hmac.le
      refine close_of_bounds hLev hq0 hw0 hhh' (c := (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000))
        (hbfl.trans hmono) ?_
      have := hq1 _ hq0
      nlinarith [nu_margin_far]

/-- **Proposition III, Region II, positivity form**: `2 g_w > 0` on `x ≥ ξ_I` for the bumped designs, uniformly over the
compact family and the cuts above the block. -/
theorem bumped_regionII_pos (p : ℕ) (P : RpParams p) (f N₀ : ℕ) (hf : 1 ≤ f) (hfN₀ : f ≤ N₀) (M E : ℝ) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), N₀ ≤ N →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ P.X → k ≤ N) →
      (∀ k, f ≤ k → k ≤ N₀ → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N₀ → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
        0 < twoGW p c' f N (1 / 4) (bumpSigma c' N₀ σ) (bumpEps P.bumpData c' N₀ (1 / 4) ε) x := by
  filter_upwards [bumped_regionII p P f N₀ hf hfN₀ M E] with c' h N σ ε hN hcut hσ hε x hx
  have := h N σ ε hN hcut hσ hε x hx
  have hlev := levComb_pos c' f x
  linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.macro_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms macro_margin

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.macro_margin_quarter_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms macro_margin_quarter_fails

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.phaseHyp_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phaseHyp_compact

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.bumped_regionII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumped_regionII

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.bumped_regionII_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumped_regionII_pos

end FormalResearch.ModularBootstrap.Upper.Positivity
