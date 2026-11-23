module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerChart
public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerSites
public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerKernelAux
public import FormalResearch.ModularBootstrap.Upper.Ramped.PhaseUniform
public import FormalResearch.ModularBootstrap.Upper.Window.Product

/-!
# The ramped design `D_*(c)`: parameters, heights, sites (`rem:thmU`, "Design `D_*(c)`")

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`), paragraph "Design `D_*(c)`" and the facts quoted
after it.

* `RampedParams` (`C_I, C_mid ≥ 1`, `M_0 > 0`), `nTr c' = c' N(ξ_I)` with `ξ_I = ξ_* + c'^{-3/5}` (`≍ c'^{1/10}`,
  `nTr_bounds`), `nAi c' = ⌈c'^{1/6}⌉`, `etaSq P c' k = min(1/16, C_I² min(k, N_tr)/√c' + C_mid² (k/c')^{5/6})`,
  `rampedEta = √etaSq`, `nCap P c'` (the least `k` at which the minimum is attained by `1/16`), `rampedD P c' =
  M_0 c'^{-1/3}`;
* the sites `χ'_1 = τ⁻¹(λ(|a_1| + d)/κ)`, `χ'_k = τ⁻¹(λ|a_k|/κ)` (`2 ≤ k ≤ N_Ai`), `χ'_k = τ⁻¹(λ Φ_k) = χ_k`
  beyond, as `designSite c' (rampedSigma d c') k` (`designSite_rampedSigma`); the widths `ε'_k = η_k ℓ_k`
  (`rampedEps`); the comb `rampedComb P d c' = designComb c' 1 (n_cap + 6) (1/4) σ ε'`.  The site coordinate `σ`
  depends on `d` and `c'` only, not on `C_I, C_mid`.

Facts proved here, all with absolute constants (independent of `C_I, C_mid, M_0`, and of `d ∈ [0, 1]`):

* `rampedEta_mono`, `rampedEta_eq_quarter`: `η_k` is nondecreasing, `η_k = 1/4` exactly for `k ≥ n_cap`;
* `nCap_le`: `n_cap ≤ 0.036 c'` for `c' ≥ 10⁴`; `nCap_ge`: `n_cap ≥ c'(32 C_mid²)^{-6/5}` for `c' ≥ c₀(C_I, C_mid)`;
* `rampedShift_le`: `|χ'_k - χ_k| ≤ C λ k^{-4/3}` for every `k ≥ 1` (for `k = 1` this is `|Δ_1| ≤ C λ`);
  `designSite_ramped_eq_of_gt`: `Δ_k = 0` for `k > N_Ai`; `rampedSite_first_ge`: `χ'_1 ≥ χ_1`;
* `rampedGap_two_sided`, `rampedShift_div_gap_le`: `ℓ_k ≍ λ k^{-1/3}` and `|Δ_k| ≤ (C/k) ℓ_k` for `k ≤ n_cap + 8`;
* `etaSq_le_of_le_nAi`: `η_k² ≤ 1/32` for `k ≤ N_Ai`, `c' ≥ c₀(C_I, C_mid)`;
* `siteRadius_le_window`, `siteRadius_le_fifth`: the sites up to `n_cap + 8` lie within `0.2` of `ξ_*`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design FormalResearch.Special
  FormalResearch.ModularBootstrap.Upper.Window

structure RampedParams where
  CI : ℝ
  Cmid : ℝ
  M0 : ℝ
  one_le_CI : 1 ≤ CI
  one_le_Cmid : 1 ≤ Cmid
  M0_pos : 0 < M0

noncomputable def nTr (c' : ℝ) : ℝ := c' * cumulN (xiStar + c' ^ (-(3 / 5 : ℝ)))

noncomputable def nAi (c' : ℝ) : ℕ := ⌈c' ^ (1 / 6 : ℝ)⌉₊

noncomputable def etaArg (P : RampedParams) (c' : ℝ) (k : ℕ) : ℝ :=
  P.CI ^ 2 * min (k : ℝ) (nTr c') / √c' + P.Cmid ^ 2 * ((k : ℝ) / c') ^ (5 / 6 : ℝ)

noncomputable def etaSq (P : RampedParams) (c' : ℝ) (k : ℕ) : ℝ :=
  min (1 / 16) (etaArg P c' k)

noncomputable def rampedEta (P : RampedParams) (c' : ℝ) (k : ℕ) : ℝ := √(etaSq P c' k)

noncomputable def nCap (P : RampedParams) (c' : ℝ) : ℕ := sInf {k : ℕ | 1 / 16 ≤ etaArg P c' k}

noncomputable def rampedD (P : RampedParams) (c' : ℝ) : ℝ := P.M0 * c' ^ (-(1 / 3 : ℝ))

lemma nTr_nonneg {c' : ℝ} (hc' : 0 < c') : 0 ≤ nTr c' := by
  unfold nTr
  have : 0 ≤ cumulN (xiStar + c' ^ (-(3 / 5 : ℝ))) := cumulN_nonneg (by
    have := Real.rpow_nonneg hc'.le (-(3 / 5 : ℝ)); linarith)
  positivity

lemma etaArg_nonneg (P : RampedParams) {c' : ℝ} (hc' : 0 < c') (k : ℕ) : 0 ≤ etaArg P c' k := by
  unfold etaArg
  have := nTr_nonneg hc'
  positivity

lemma etaArg_mono (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {j k : ℕ} (h : j ≤ k) :
    etaArg P c' j ≤ etaArg P c' k := by
  unfold etaArg
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast h
  have h1 : min (j : ℝ) (nTr c') ≤ min (k : ℝ) (nTr c') := min_le_min_right _ hjk
  have h2 : ((j : ℝ) / c') ^ (5 / 6 : ℝ) ≤ ((k : ℝ) / c') ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hjk hc'.le) (by norm_num)
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'
  have hCI : 0 ≤ P.CI ^ 2 := by positivity
  have hCm : 0 ≤ P.Cmid ^ 2 := by positivity
  gcongr


lemma rpow56_ge {a : ℝ} (ha : 0 ≤ a) (h : (1 / 16 : ℝ) ^ 6 ≤ a ^ 5) : 1 / 16 ≤ a ^ (5 / 6 : ℝ) := by
  by_contra hcon
  push Not at hcon
  have h0 : 0 ≤ a ^ (5 / 6 : ℝ) := Real.rpow_nonneg ha _
  have h1 : (a ^ (5 / 6 : ℝ)) ^ 6 < (1 / 16 : ℝ) ^ 6 := pow_lt_pow_left₀ hcon h0 (by norm_num)
  have h2 : (a ^ (5 / 6 : ℝ)) ^ 6 = a ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  linarith

lemma etaArg_ge_of {P : RampedParams} {c' : ℝ} (hc' : 0 < c') {k : ℕ}
    (hk : 359 / 10000 * c' ≤ k) : 1 / 16 ≤ etaArg P c' k := by
  unfold etaArg
  have hnT := nTr_nonneg hc'
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'
  have h1 : 0 ≤ P.CI ^ 2 * min (k : ℝ) (nTr c') / √c' := by
    have : 0 ≤ min (k : ℝ) (nTr c') := le_min (by positivity) hnT
    positivity
  have ha : (359 / 10000 : ℝ) ≤ (k : ℝ) / c' := by
    rw [le_div_iff₀ hc']; linarith
  have h2 : 1 / 16 ≤ ((k : ℝ) / c') ^ (5 / 6 : ℝ) := by
    apply rpow56_ge (by positivity)
    have : ((359 : ℝ) / 10000) ^ 5 ≤ ((k : ℝ) / c') ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
    refine le_trans ?_ this
    norm_num
  have h3 : 1 ≤ P.Cmid ^ 2 := by nlinarith [P.one_le_Cmid]
  have h4 : 0 ≤ ((k : ℝ) / c') ^ (5 / 6 : ℝ) := Real.rpow_nonneg (by positivity) _
  nlinarith

lemma nonempty_cap (P : RampedParams) {c' : ℝ} (hc' : 0 < c') :
    {k : ℕ | 1 / 16 ≤ etaArg P c' k}.Nonempty :=
  ⟨⌈359 / 10000 * c'⌉₊, etaArg_ge_of hc' (Nat.le_ceil _)⟩

lemma etaArg_nCap_ge (P : RampedParams) {c' : ℝ} (hc' : 0 < c') :
    1 / 16 ≤ etaArg P c' (nCap P c') :=
  Nat.sInf_mem (nonempty_cap P hc')

lemma etaArg_lt_of_lt_nCap (P : RampedParams) (c' : ℝ) {k : ℕ} (hk : k < nCap P c') :
    etaArg P c' k < 1 / 16 := by
  by_contra h
  push Not at h
  exact absurd (Nat.sInf_le (show k ∈ {k : ℕ | 1 / 16 ≤ etaArg P c' k} from h)) (not_le.2 hk)

/-- `n_cap ≤ 0.036 c'` for `c' ≥ 10⁴`, with an absolute threshold. -/
theorem nCap_le (P : RampedParams) {c' : ℝ} (hc' : 10000 ≤ c') :
    (nCap P c' : ℝ) ≤ 36 / 1000 * c' := by
  have hc0 : 0 < c' := by linarith
  have h1 : nCap P c' ≤ ⌈359 / 10000 * c'⌉₊ := Nat.sInf_le (etaArg_ge_of hc0 (Nat.le_ceil _))
  have h2 : (nCap P c' : ℝ) ≤ (⌈359 / 10000 * c'⌉₊ : ℝ) := by exact_mod_cast h1
  have h3 := Nat.ceil_lt_add_one (show 0 ≤ 359 / 10000 * c' by positivity)
  linarith

lemma etaSq_nonneg (P : RampedParams) {c' : ℝ} (hc' : 0 < c') (k : ℕ) : 0 ≤ etaSq P c' k :=
  le_min (by norm_num) (etaArg_nonneg P hc' k)

lemma etaSq_le (P : RampedParams) (c' : ℝ) (k : ℕ) : etaSq P c' k ≤ 1 / 16 := min_le_left _ _

lemma etaSq_mono (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {j k : ℕ} (h : j ≤ k) :
    etaSq P c' j ≤ etaSq P c' k :=
  min_le_min_left _ (etaArg_mono P hc' h)

lemma etaSq_eq_of_ge_nCap (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : nCap P c' ≤ k) :
    etaSq P c' k = 1 / 16 :=
  le_antisymm (etaSq_le P c' k)
    (le_min le_rfl ((etaArg_nCap_ge P hc').trans (etaArg_mono P hc' hk)))

lemma rampedEta_nonneg (P : RampedParams) (c' : ℝ) (k : ℕ) : 0 ≤ rampedEta P c' k := Real.sqrt_nonneg _

lemma rampedEta_le (P : RampedParams) (c' : ℝ) (k : ℕ) : rampedEta P c' k ≤ 1 / 4 := by
  unfold rampedEta
  rw [show (1 / 4 : ℝ) = √(1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (etaSq_le P c' k)

lemma rampedEta_sq (P : RampedParams) {c' : ℝ} (hc' : 0 < c') (k : ℕ) :
    rampedEta P c' k ^ 2 = etaSq P c' k := by
  unfold rampedEta
  exact Real.sq_sqrt (etaSq_nonneg P hc' k)

/-- The heights `η_k` are nondecreasing. -/
lemma rampedEta_mono (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {j k : ℕ} (h : j ≤ k) :
    rampedEta P c' j ≤ rampedEta P c' k :=
  Real.sqrt_le_sqrt (etaSq_mono P hc' h)

/-- `η_k = 1/4` exactly for `k ≥ n_cap`. -/
lemma rampedEta_eq_quarter (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : nCap P c' ≤ k) :
    rampedEta P c' k = 1 / 4 := by
  unfold rampedEta
  rw [etaSq_eq_of_ge_nCap P hc' hk, show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]


/-! ### 2. The sites -/

/-- The scaled Airy node `s_k` of the site `χ'_k = τ⁻¹(λ s_k)`: `(|a_1| + d)/κ` for `k = 1`, `|a_k|/κ` for
`2 ≤ k ≤ N_Ai`, and the reference exponent `Φ_k = (k - 1/4)^{2/3}` beyond. -/
noncomputable def rampedNode (d c' : ℝ) (k : ℕ) : ℝ :=
  if k = 1 then sNodeAiry 1 + d / kappaAiry else if k ≤ nAi c' then sNodeAiry k else phiWKB k

/-- The site coordinate `σ_k` with `χ'_k = ξ_* + λ σ_k = τ⁻¹(λ s_k)`. -/
noncomputable def rampedSigma (d c' : ℝ) (k : ℕ) : ℝ :=
  (langerTauInv (lambdaComb c' * rampedNode d c' k) - xiStar) / lambdaComb c'

/-- The widths `ε'_k = η_k ℓ_k`. -/
noncomputable def rampedEps (P : RampedParams) (c' : ℝ) (k : ℕ) : ℝ := rampedEta P c' k * siteGap c' k

/-- The ramped comb `B_{D_*}`: a simple zero at `χ'_1`, pairs at `χ'_k ± iη_kℓ_k` for `2 ≤ k ≤ n_cap + 6`,
reference pairs beyond (`rem:thmU`, "Design `D_*(c)`"). -/
noncomputable def rampedComb (P : RampedParams) (d c' : ℝ) : ℂ → ℂ :=
  designComb c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c')

lemma lambdaComb_pos' {c' : ℝ} (hc' : 0 < c') : 0 < lambdaComb c' :=
  Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _

lemma langerTauInv_lip : ∃ L : ℝ, 0 < L ∧ ∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' →
    |langerTauInv s - langerTauInv s'| ≤ L * |s - s'| := by
  have hxs := xiStar_pos
  obtain ⟨c, hc, hcd⟩ := langerTau_deriv_ge_const_of (a := xiStar / 2) (by linarith)
  have key : ∀ s s' : ℝ, 0 ≤ s → s ≤ s' → langerTauInv s' - langerTauInv s ≤ c⁻¹ * (s' - s) := by
    intro s s' hs hss'
    have hx := (langerTauInv_spec hs).1
    have hx' := (langerTauInv_spec (hs.trans hss')).1
    have hle : langerTauInv s ≤ langerTauInv s' :=
      langerTauInv_strictMonoOn.monotoneOn (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hss')) hss'
    have h := langerTau_sub_ge (a := xiStar / 2) (c := c) (by linarith) hcd (by linarith) hle
    rw [langerTau_langerTauInv hs, langerTau_langerTauInv (hs.trans hss')] at h
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    linarith
  refine ⟨c⁻¹, inv_pos.2 hc, fun s s' hs hs' => ?_⟩
  rcases le_total s s' with h | h
  · have := key s s' hs h
    have hle : langerTauInv s ≤ langerTauInv s' :=
      langerTauInv_strictMonoOn.monotoneOn (Set.mem_Ici.2 hs) (Set.mem_Ici.2 hs') h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have := key s' s hs' h
    have hle : langerTauInv s' ≤ langerTauInv s :=
      langerTauInv_strictMonoOn.monotoneOn (Set.mem_Ici.2 hs') (Set.mem_Ici.2 hs) h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

lemma sNodeAiry_nonneg (k : ℕ) : 0 ≤ sNodeAiry k := by
  unfold sNodeAiry
  have := kappaAiry_pos
  positivity

lemma phiWKB_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ phiWKB k := by
  unfold phiWKB
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact Real.rpow_nonneg (by linarith) _

lemma rampedNode_nonneg {d : ℝ} (hd : 0 ≤ d) (c' : ℝ) {k : ℕ} (hk : 1 ≤ k) : 0 ≤ rampedNode d c' k := by
  unfold rampedNode
  have := kappaAiry_pos
  split_ifs
  · have := sNodeAiry_nonneg 1; positivity
  · exact sNodeAiry_nonneg k
  · exact phiWKB_nonneg hk

lemma designSite_rampedSigma {c' : ℝ} (hc' : 0 < c') (d : ℝ) (k : ℕ) :
    designSite c' (rampedSigma d c') k = langerTauInv (lambdaComb c' * rampedNode d c' k) := by
  have := lambdaComb_pos' hc'
  unfold designSite rampedSigma
  field_simp
  ring

lemma chiQuantile_nat_eq {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) :
    chiQuantile c' (k : ℝ) = langerTauInv (lambdaComb c' * phiWKB k) := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [chiQuantile_eq_langerTauInv hc' (by linarith)]
  rfl

lemma rampedSigma_nonneg {c' : ℝ} (hc' : 0 < c') {d : ℝ} (hd : 0 ≤ d) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ rampedSigma d c' k := by
  have hl := lambdaComb_pos' hc'
  unfold rampedSigma
  have hn := rampedNode_nonneg hd c' hk
  have := (langerTauInv_spec (mul_nonneg hl.le hn)).1
  exact div_nonneg (by linarith) hl.le

lemma designSite_ramped_nonneg {c' : ℝ} (hc' : 0 < c') {d : ℝ} (hd : 0 ≤ d) {k : ℕ} (hk : 1 ≤ k) :
    xiStar ≤ designSite c' (rampedSigma d c') k := by
  have := rampedSigma_nonneg hc' hd hk
  have hl := lambdaComb_pos' hc'
  unfold designSite
  nlinarith

/-- Beyond the Airy cut the design site is the reference site. -/
lemma designSite_ramped_eq_of_gt {c' : ℝ} (hc' : 0 < c') (d : ℝ) {k : ℕ} (hk : nAi c' < k) (hk1 : 2 ≤ k) :
    designSite c' (rampedSigma d c') k = chiQuantile c' (k : ℝ) := by
  rw [designSite_rampedSigma hc', chiQuantile_nat_eq hc' (by omega)]
  have h1 : k ≠ 1 := by omega
  have h2 : ¬ k ≤ nAi c' := not_le.2 hk
  simp [rampedNode, h1, h2]

/-- The nodes are within `C k^{-4/3}` of the reference exponents: `|s_k - Φ_k| ≤ C k^{-4/3}` for every `k ≥ 1`,
`d ∈ [0, 1]` (`k = 1` includes the shift `d/κ`), `C` absolute; `s_k = Φ_k` for `k > N_Ai` (Lemma `Z`). -/
theorem rampedNode_sub_phi_le : ∃ C : ℝ, 0 < C ∧ ∀ c' d : ℝ, 0 ≤ d → d ≤ 1 → ∀ k : ℕ, 1 ≤ k →
    |rampedNode d c' k - phiWKB k| ≤ C * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨CZ, hCZ, hZ⟩ := deltaWKB_le_exists
  have hκ := kappaAiry_pos
  refine ⟨(CZ + 1) / kappaAiry, by positivity, fun c' d hd hd1 k hk => ?_⟩
  have hkp : 0 < (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hZk := hZ k hk
  have hZ' : |deltaWKB k| / kappaAiry ≤ CZ / kappaAiry * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hZk hκ.le
  unfold rampedNode
  by_cases h1 : k = 1
  · subst h1
    simp only [ite_true, Nat.cast_one, Real.one_rpow, mul_one]
    have e : sNodeAiry 1 + d / kappaAiry - phiWKB 1 = -deltaWKB 1 / kappaAiry + d / kappaAiry := by
      rw [← sNodeAiry_sub_phiWKB le_rfl]; ring
    rw [e]
    have : |-deltaWKB 1 / kappaAiry + d / kappaAiry| ≤ |deltaWKB 1| / kappaAiry + d / kappaAiry := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_neg, abs_of_pos hκ, abs_of_nonneg (div_nonneg hd hκ.le)]
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at hZ'
    have : d / kappaAiry ≤ 1 / kappaAiry := div_le_div_of_nonneg_right hd1 hκ.le
    have e2 : (CZ + 1) / kappaAiry = CZ / kappaAiry + 1 / kappaAiry := by ring
    linarith
  · simp only [h1, ite_false]
    by_cases h2 : k ≤ nAi c'
    · simp only [h2, ite_true]
      rw [sNodeAiry_sub_phiWKB hk, abs_div, abs_neg, abs_of_pos hκ]
      have : CZ / kappaAiry * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤
          (CZ + 1) / kappaAiry * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        gcongr; linarith
      linarith
    · simp only [h2, ite_false, sub_self, abs_zero]
      positivity

/-- `|Δ_k| ≤ C λ k^{-4/3}` for every `k ≥ 1` (`k = 1` includes the shift `d ≤ 1`), with `C` absolute and valid for
every `c' > 0`, every `d ∈ [0, 1]`; `Δ_k = 0` for `k > N_Ai`. -/
theorem rampedShift_le : ∃ C : ℝ, 0 < C ∧ ∀ c' : ℝ, 0 < c' → ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ k : ℕ, 1 ≤ k →
    |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤
      C * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨L, hL, hlip⟩ := langerTauInv_lip
  obtain ⟨Cn, hCn, hnode⟩ := rampedNode_sub_phi_le
  refine ⟨L * Cn, by positivity, fun c' hc' d hd hd1 k hk => ?_⟩
  have hl := lambdaComb_pos' hc'
  rw [designSite_rampedSigma hc', chiQuantile_nat_eq hc' hk]
  have hn := rampedNode_nonneg hd c' hk
  have hφ := phiWKB_nonneg hk
  refine (hlip _ _ (mul_nonneg hl.le hn) (mul_nonneg hl.le hφ)).trans ?_
  rw [← mul_sub, abs_mul, abs_of_pos hl]
  calc L * (lambdaComb c' * |rampedNode d c' k - phiWKB k|)
      ≤ L * (lambdaComb c' * (Cn * (k : ℝ) ^ (-(4 / 3 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hnode c' d hd hd1 k hk) hl.le) hL.le
    _ = _ := by ring


/-! ### 3. The tip window, the first site, `N_tr` -/

lemma rpow23_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 3) : x ^ (2 / 3 : ℝ) ≤ y := by
  by_contra hcon
  push Not at hcon
  have h0 : 0 ≤ x ^ (2 / 3 : ℝ) := Real.rpow_nonneg hx _
  have h1 : y ^ 3 < (x ^ (2 / 3 : ℝ)) ^ 3 := pow_lt_pow_left₀ hcon hy (by norm_num)
  have h2 : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  linarith

lemma kTip_ge : 21 / 50 ≤ kTip := by
  unfold kTip
  have h1 : (168 / 100 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) := by
    have h : ((168 / 100 : ℝ)) ^ 4 ≤ 2 ^ 3 := by norm_num
    by_contra hcon
    push Not at hcon
    have h3 : 0 ≤ (2 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
    have h4 : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 < (168 / 100 : ℝ) ^ 4 := pow_lt_pow_left₀ hcon h3 (by norm_num)
    have h5 : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = 2 ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have h2 : √π ≤ 17725 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.pi_lt_d4
    nlinarith
  have hs : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma siteRadius_le_pow {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    siteRadius c' a ≤ (a / (kTip * c')) ^ (2 / 3 : ℝ) := by
  refine (siteRadius_bounds hc' ha).2.trans ?_
  have hk := kTip_pos
  have hkc : 0 < kTip * c' := by positivity
  have h0 : 0 ≤ a - 1 / 4 := by linarith
  unfold lambdaComb phiQuantile
  rw [Real.rpow_neg hkc.le, ← div_eq_inv_mul, ← Real.div_rpow h0 (by positivity)]
  apply Real.rpow_le_rpow (div_nonneg h0 (by positivity)) _ (by norm_num)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- In the tip window: `a ≤ c'/20` gives `χ_a - ξ_* ≤ 0.63`. -/
lemma siteRadius_le_window {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) (h : a ≤ c' / 20) :
    siteRadius c' a ≤ 63 / 100 := by
  have hkp := kTip_pos
  refine (siteRadius_le_pow hc' ha).trans (rpow23_le (div_nonneg (by linarith) (by positivity)) (by norm_num) ?_)
  have hk := kTip_ge
  have h1 : a / (kTip * c') ≤ 9 / 40 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h0 : 0 ≤ a / (kTip * c') := div_nonneg (by linarith) (by positivity)
  calc (a / (kTip * c')) ^ 2 ≤ (9 / 40) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ (63 / 100) ^ 3 := by norm_num

/-- The cut `n_cap + 6` (and the next sites) lie in the tip window `χ - ξ_* ≤ 1/5` for `c' ≥ 10⁴`:
`a ≤ 0.037 c'` gives `χ_a - ξ_* ≤ 1/5`. -/
lemma siteRadius_le_fifth {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) (h : a ≤ 37 / 1000 * c') :
    siteRadius c' a ≤ 1 / 5 := by
  have hkp := kTip_pos
  refine (siteRadius_le_pow hc' ha).trans (rpow23_le (div_nonneg (by linarith) (by positivity)) (by norm_num) ?_)
  have hk := kTip_ge
  have h1 : a / (kTip * c') ≤ 37 / 1000 / (21 / 50) := by
    rw [div_le_iff₀ (by positivity)]
    have : 37 / 1000 / (21 / 50 : ℝ) * (kTip * c') ≥ 37 / 1000 / (21 / 50 : ℝ) * ((21 / 50) * c') := by
      gcongr
    have e : 37 / 1000 / (21 / 50 : ℝ) * ((21 / 50) * c') = 37 / 1000 * c' := by field_simp
    linarith
  have h0 : 0 ≤ a / (kTip * c') := div_nonneg (by linarith) (by positivity)
  calc (a / (kTip * c')) ^ 2 ≤ (37 / 1000 / (21 / 50 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ (1 / 5) ^ 3 := by norm_num

lemma phiWKB_one_le : kappaAiry * phiWKB 1 ≤ 233 / 100 := by
  have hκ := kappaAiry_pos
  have hφ : 0 ≤ phiWKB 1 := phiWKB_nonneg le_rfl
  have hk3 : kappaAiry ^ 3 = (3 * π / 2) ^ 2 := by
    unfold kappaAiry
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hp3 : phiWKB 1 ^ 3 = (3 / 4) ^ 2 := by
    unfold phiWKB
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  by_contra hcon
  push Not at hcon
  have h1 : (233 / 100 : ℝ) ^ 3 < (kappaAiry * phiWKB 1) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
  rw [mul_pow, hk3, hp3] at h1
  nlinarith

/-- `|a_1| ≥ κ Φ_1`, i.e. `δ_1 ≤ 0`. -/
lemma phiWKB_one_le_sNode : phiWKB 1 ≤ sNodeAiry 1 := by
  have hκ := kappaAiry_pos
  have h1 := airyZero_one.2
  have h2 := phiWKB_one_le
  unfold sNodeAiry
  rw [abs_of_neg (by linarith), le_div_iff₀ hκ]
  linarith

/-- `χ'_1 ≥ χ_1`. -/
theorem rampedSite_first_ge {c' : ℝ} (hc' : 0 < c') {d : ℝ} (hd : 0 ≤ d) :
    chiQuantile c' (1 : ℕ) ≤ designSite c' (rampedSigma d c') 1 := by
  rw [designSite_rampedSigma hc', chiQuantile_nat_eq hc' le_rfl]
  have hl := lambdaComb_pos' hc'
  have hφ := phiWKB_nonneg (le_refl 1)
  have hκ := kappaAiry_pos
  have hn : phiWKB 1 ≤ rampedNode d c' 1 := by
    unfold rampedNode
    simp only [ite_true]
    have := phiWKB_one_le_sNode
    have : 0 ≤ d / kappaAiry := div_nonneg hd hκ.le
    linarith
  exact langerTauInv_strictMonoOn.monotoneOn (Set.mem_Ici.2 (mul_nonneg hl.le hφ))
    (Set.mem_Ici.2 (mul_nonneg hl.le (hφ.trans hn))) (mul_le_mul_of_nonneg_left hn hl.le)


lemma langerTau_sub_le {a b C x y : ℝ} (ha : 0 < a) (hC : ∀ z ∈ Icc a b, |deriv langerTau z| ≤ C)
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) : langerTau y - langerTau x ≤ C * (y - x) := by
  rcases hxy.eq_or_lt with h | h
  · rw [h]; simp
  · have hcont : ContinuousOn langerTau (Icc x y) :=
      (contDiffOn_langerTau 0).continuousOn.mono fun z hz => lt_of_lt_of_le ha (hax.trans hz.1)
    have hder : ∀ z ∈ Ioo x y, HasDerivAt langerTau (deriv langerTau z) z := fun z hz =>
      hasDerivAt_langerTau_pos (lt_of_lt_of_le ha (hax.trans hz.1.le))
    obtain ⟨z, hz, hz2⟩ := exists_hasDerivAt_eq_slope langerTau (deriv langerTau) h hcont hder
    have := (le_abs_self _).trans (hC z ⟨hax.trans hz.1.le, hz.2.le.trans hyb⟩)
    rw [hz2, div_le_iff₀ (sub_pos.2 h)] at this
    linarith

lemma c_mul_rpow_neg {c' : ℝ} (hc' : 0 < c') :
    c' * (c' ^ (-(3 / 5 : ℝ))) ^ (3 / 2 : ℝ) = c' ^ (1 / 10 : ℝ) := by
  rw [← Real.rpow_mul hc'.le]
  calc c' * c' ^ (-(3 / 5 : ℝ) * (3 / 2 : ℝ)) = c' ^ (1 : ℝ) * c' ^ (-(3 / 5 : ℝ) * (3 / 2 : ℝ)) := by
        rw [Real.rpow_one]
    _ = c' ^ (1 / 10 : ℝ) := by
        rw [← Real.rpow_add hc']
        norm_num

/-- `N_tr = c' N(ξ_I) ≍ c'^{1/10}` (`ξ_I = ξ_* + c'^{-3/5}`), for `c' ≥ 1`. -/
theorem nTr_bounds : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ c' : ℝ, 1 ≤ c' →
    a * c' ^ (1 / 10 : ℝ) ≤ nTr c' ∧ nTr c' ≤ b * c' ^ (1 / 10 : ℝ) := by
  have hxs := xiStar_pos
  have hk := kTip_pos
  obtain ⟨c, hc, hcd⟩ := langerTau_deriv_ge_const_of (a := xiStar / 2) (by linarith)
  obtain ⟨C0, hC0⟩ := langerTau_deriv_bound_compact (a := xiStar / 2) (b := xiStar + 1) (by linarith)
  set C := max C0 1 with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨kTip * c ^ (3 / 2 : ℝ), kTip * C ^ (3 / 2 : ℝ), by positivity, by positivity, fun c' hc'1 => ?_⟩
  have hc'0 : 0 < c' := by linarith
  set r : ℝ := c' ^ (-(3 / 5 : ℝ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hc'0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc'1 (by norm_num)
  have hge : xiStar ≤ xiStar + r := by linarith
  have hτ0 : langerTau (xiStar + r) = langerTau (xiStar + r) - langerTau xiStar := by
    rw [langerTau_xiStar, sub_zero]
  have hlow : c * r ≤ langerTau (xiStar + r) := by
    have := langerTau_sub_ge (a := xiStar / 2) (c := c) (by linarith) hcd
      (by linarith : xiStar / 2 ≤ xiStar) (by linarith : xiStar ≤ xiStar + r)
    rw [langerTau_xiStar] at this
    linarith
  have hup : langerTau (xiStar + r) ≤ C * r := by
    have := langerTau_sub_le (a := xiStar / 2) (b := xiStar + 1) (C := C) (by linarith)
      (fun z hz => (hC0 z hz).1.trans (le_max_left _ _)) (by linarith) hge (by linarith)
    rw [langerTau_xiStar] at this
    linarith
  have hnT : nTr c' = c' * (kTip * langerTau (xiStar + r) ^ (3 / 2 : ℝ)) := by
    unfold nTr
    rw [cumulN_eq_kTip_mul_langerTau hge]
  have hid := c_mul_rpow_neg hc'0
  rw [← hr] at hid
  have hpos : 0 ≤ c * r := by positivity
  constructor
  · rw [hnT]
    have h1 : (c * r) ^ (3 / 2 : ℝ) ≤ langerTau (xiStar + r) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hpos hlow (by norm_num)
    rw [Real.mul_rpow hc.le hr0.le] at h1
    calc kTip * c ^ (3 / 2 : ℝ) * c' ^ (1 / 10 : ℝ) = kTip * c ^ (3 / 2 : ℝ) * (c' * r ^ (3 / 2 : ℝ)) := by
          rw [hid]
      _ = c' * (kTip * (c ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ))) := by ring
      _ ≤ _ := by gcongr
  · rw [hnT]
    have h1 : langerTau (xiStar + r) ^ (3 / 2 : ℝ) ≤ (C * r) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (hpos.trans hlow) hup (by norm_num)
    rw [Real.mul_rpow hCpos.le hr0.le] at h1
    calc c' * (kTip * langerTau (xiStar + r) ^ (3 / 2 : ℝ))
        ≤ c' * (kTip * (C ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ))) := by gcongr
      _ = kTip * C ^ (3 / 2 : ℝ) * (c' * r ^ (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hid]


lemma nAi_le {c' : ℝ} (hc'1 : 1 ≤ c') : (nAi c' : ℝ) ≤ 2 * c' ^ (1 / 6 : ℝ) := by
  have h1 : 1 ≤ c' ^ (1 / 6 : ℝ) := Real.one_le_rpow hc'1 (by norm_num)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ c' ^ (1 / 6 : ℝ) by linarith)
  unfold nAi
  linarith

lemma eventually_rpow_neg_le {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∀ᶠ c' : ℝ in atTop, c' ^ (-p) ≤ ε :=
  (tendsto_rpow_neg_atTop hp).eventually_le_const hε

lemma eventually_first_term (P : RampedParams) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' : ℝ in atTop, ∀ k : ℕ, P.CI ^ 2 * min (k : ℝ) (nTr c') / √c' ≤ ε := by
  obtain ⟨a, b, ha, hb, hnb⟩ := nTr_bounds
  have hK : 0 < P.CI ^ 2 * b := by have := P.one_le_CI; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_rpow_neg_le (p := 2 / 5) (by norm_num) (div_pos hε hK)] with c' hc'1 hsm k
  have hc'0 : 0 < c' := by linarith
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'0
  have hnT := (hnb c' hc'1).2
  have hmin : min (k : ℝ) (nTr c') ≤ b * c' ^ (1 / 10 : ℝ) := (min_le_right _ _).trans hnT
  have hsq : √c' = c' ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow c'
  have e : c' ^ (1 / 10 : ℝ) / √c' = c' ^ (-(2 / 5 : ℝ)) := by
    rw [hsq, ← Real.rpow_sub hc'0]; norm_num
  have hCI : 0 ≤ P.CI ^ 2 := by positivity
  calc P.CI ^ 2 * min (k : ℝ) (nTr c') / √c'
      ≤ P.CI ^ 2 * (b * c' ^ (1 / 10 : ℝ)) / √c' := by gcongr
    _ = P.CI ^ 2 * b * (c' ^ (1 / 10 : ℝ) / √c') := by ring
    _ = P.CI ^ 2 * b * c' ^ (-(2 / 5 : ℝ)) := by rw [e]
    _ ≤ P.CI ^ 2 * b * (ε / (P.CI ^ 2 * b)) := by gcongr
    _ = ε := by rw [mul_comm]; exact div_mul_cancel₀ ε hK.ne'

lemma eventually_second_term (P : RampedParams) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' : ℝ in atTop, ∀ k : ℕ, k ≤ nAi c' → P.Cmid ^ 2 * ((k : ℝ) / c') ^ (5 / 6 : ℝ) ≤ ε := by
  have hK : 0 < P.Cmid ^ 2 * 2 ^ (5 / 6 : ℝ) := by have := P.one_le_Cmid; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_rpow_neg_le (p := 25 / 36) (by norm_num) (div_pos hε hK)] with c' hc'1 hsm k hk
  have hc'0 : 0 < c' := by linarith
  have hkr : (k : ℝ) ≤ 2 * c' ^ (1 / 6 : ℝ) := ((by exact_mod_cast hk : (k : ℝ) ≤ nAi c')).trans (nAi_le hc'1)
  have h1 : ((k : ℝ) / c') ^ (5 / 6 : ℝ) ≤ (2 * c' ^ (1 / 6 : ℝ) / c') ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hkr hc'0.le) (by norm_num)
  have e : (2 * c' ^ (1 / 6 : ℝ) / c') ^ (5 / 6 : ℝ) = 2 ^ (5 / 6 : ℝ) * c' ^ (-(25 / 36 : ℝ)) := by
    have : 2 * c' ^ (1 / 6 : ℝ) / c' = 2 * c' ^ (-(5 / 6 : ℝ)) := by
      rw [show (-(5 / 6 : ℝ)) = (1 / 6 : ℝ) - 1 by norm_num, Real.rpow_sub hc'0, Real.rpow_one]; ring
    rw [this, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc'0.le _), ← Real.rpow_mul hc'0.le]
    norm_num
  have hCm : 0 ≤ P.Cmid ^ 2 := by positivity
  calc P.Cmid ^ 2 * ((k : ℝ) / c') ^ (5 / 6 : ℝ) ≤ P.Cmid ^ 2 * (2 ^ (5 / 6 : ℝ) * c' ^ (-(25 / 36 : ℝ))) := by
        rw [← e]; gcongr
    _ = P.Cmid ^ 2 * 2 ^ (5 / 6 : ℝ) * c' ^ (-(25 / 36 : ℝ)) := by ring
    _ ≤ P.Cmid ^ 2 * 2 ^ (5 / 6 : ℝ) * (ε / (P.Cmid ^ 2 * 2 ^ (5 / 6 : ℝ))) := by gcongr
    _ = ε := by rw [mul_comm]; exact div_mul_cancel₀ ε hK.ne'

/-- Below the Airy cut the squared heights are small: `η_k² ≤ 1/32` for `k ≤ N_Ai`, `c' ≥ c₀(C_I, C_mid)`. -/
theorem etaSq_le_of_le_nAi (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ k : ℕ, k ≤ nAi c' → etaSq P c' k ≤ 1 / 32 := by
  filter_upwards [eventually_first_term P (ε := 1 / 64) (by norm_num),
    eventually_second_term P (ε := 1 / 64) (by norm_num)] with c' h1 h2 k hk
  refine (min_le_right _ _).trans ?_
  unfold etaArg
  linarith [h1 k, h2 k hk]

/-- `n_cap ≥ c' (32 C_mid²)^{-6/5}` for `c'` large (`C_I`, `C_mid` fixed): `χ_{n_cap} - ξ_* ≥ r_1'(C_mid)`. -/
theorem nCap_ge (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' ≤ nCap P c' := by
  filter_upwards [eventually_first_term P (ε := 1 / 32) (by norm_num), eventually_gt_atTop (0 : ℝ)]
    with c' h1 hc'
  have hge := etaArg_nCap_ge P hc'
  unfold etaArg at hge
  have h2 : 1 / 32 ≤ P.Cmid ^ 2 * ((nCap P c' : ℝ) / c') ^ (5 / 6 : ℝ) := by
    linarith [h1 (nCap P c')]
  have hCm : 0 < P.Cmid ^ 2 := by have := P.one_le_Cmid; positivity
  have h3 : 1 / (32 * P.Cmid ^ 2) ≤ ((nCap P c' : ℝ) / c') ^ (5 / 6 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) ≤ (nCap P c' : ℝ) / c' := by
    have := Real.rpow_le_rpow (by positivity) h3 (show (0 : ℝ) ≤ 6 / 5 by norm_num)
    rwa [← Real.rpow_mul (by positivity), show (5 / 6 : ℝ) * (6 / 5) = 1 by norm_num, Real.rpow_one] at this
  rwa [le_div_iff₀ hc'] at h4


/-- `ℓ_k ≍ λ k^{-1/3}` for all `k ≤ n_cap + 8` (`c' ≥ c₀` absolute): these cells lie in the tip window. -/
theorem rampedGap_two_sided : ∃ c C c0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < c0 ∧ ∀ (P : RampedParams) (c' : ℝ),
    c0 ≤ c' → ∀ k : ℕ, 1 ≤ k → k ≤ nCap P c' + 8 →
      c * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ siteGap c' k ∧
        siteGap c' k ≤ C * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨c, C, c1, hc, hC, hc1, h⟩ := siteGap_two_sided
  refine ⟨c, C, max c1 10000, hc, hC, by positivity, fun P c' hc' k hk hkn => ?_⟩
  have hc'1 : 10000 ≤ c' := (le_max_right _ _).trans hc'
  have hc'0 : 0 < c' := by linarith
  have hcap := nCap_le P hc'1
  have hk' : (k : ℝ) ≤ c' / 20 := by
    have : (k : ℝ) ≤ nCap P c' + 8 := by exact_mod_cast hkn
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact h c' ((le_max_left _ _).trans hc') k hk
    (siteRadius_le_window hc'0 (by linarith) hk')

/-- `|Δ_k| / ℓ_k ≤ C / k` for `1 ≤ k ≤ n_cap + 8` (`c' ≥ c₀`, `d ∈ [0, 1]`). -/
theorem rampedShift_div_gap_le : ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ (P : RampedParams) (c' : ℝ), c0 ≤ c' →
    ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ k : ℕ, 1 ≤ k → k ≤ nCap P c' + 8 →
      |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤ C / k * siteGap c' k := by
  obtain ⟨c, C, c0, hc, hC, hc0, hgap⟩ := rampedGap_two_sided
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  refine ⟨Cs / c, c0, by positivity, hc0, fun P c' hc' d hd hd1 k hk hkn => ?_⟩
  have hc'0 : 0 < c' := lt_of_lt_of_le hc0 hc'
  have hl := lambdaComb_pos' hc'0
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := hsh c' hc'0 d hd hd1 k hk
  have h2 := (hgap P c' hc' k hk hkn).1
  have e : (k : ℝ) ^ (-(4 / 3 : ℝ)) = (k : ℝ) ^ (-(1 / 3 : ℝ)) / k := by
    rw [show (-(4 / 3 : ℝ)) = -(1 / 3 : ℝ) - 1 by norm_num, Real.rpow_sub hkr, Real.rpow_one]
  rw [e] at h1
  have hp : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hkr _
  have h3 : lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ siteGap c' k / c := by
    rw [le_div_iff₀ hc]; linarith
  have : Cs * lambdaComb c' * ((k : ℝ) ^ (-(1 / 3 : ℝ)) / k) ≤ Cs / c / k * siteGap c' k :=
    calc Cs * lambdaComb c' * ((k : ℝ) ^ (-(1 / 3 : ℝ)) / k)
        = Cs * (lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ))) / k := by ring
      _ ≤ Cs * (siteGap c' k / c) / k := by gcongr
      _ = Cs / c / k * siteGap c' k := by ring
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedShift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedShift_le


/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.nCap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nCap_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.nCap_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nCap_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.nTr_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nTr_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedSite_first_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedSite_first_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.etaSq_le_of_le_nAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etaSq_le_of_le_nAi

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedShift_div_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedShift_div_gap_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedGap_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedGap_two_sided

end FormalResearch.ModularBootstrap.Upper.Ramped
