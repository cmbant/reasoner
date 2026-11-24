module

public import FormalResearch.ModularBootstrap.Upper.Positivity.AmplitudeLevel
public import FormalResearch.ModularBootstrap.Upper.Positivity.DesignReal
public import FormalResearch.ModularBootstrap.Upper.Holes.BandLobe

/-!
# Proposition II: positivity of `g` at weight `1` in Region II

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition II (`ut:II`, lines 349--370):
for `c'` large and every `x ≥ ξ_I = ξ_* + c'^{-2/5}` (`t = c' x²/3`), `2 g(t) / Lev(x) ≥ 13/100`, where
`Lev = 4 sech²(π x/2) exp(-c' L + c' P + J_end)` is the level of the reference comb, and the same for
any fixed `f ≥ 1` and any compact family of finite modifications `B_D^{(f)}`, uniformly over the
family, relative to `Lev^{(f)}`.

**Lean dictionary.**
* `twoG c' f N η₀ σ ε x` is `2 g(c' x²/3) = h₀^D(x) - ĥ₀(c' x²/3)` (real part), with
  `h₀^D = designProfile = sech²(π b/2) B_D^{(f)}` (`Upper.Design.CombTransform`) and
  `ĥ₀ = edgeHankel c' designProfile` the order-zero Hankel transform in the variable `t = c' x²/3`.
  Both are real numbers (`designProfile_ofReal` for `h₀^D`); the real part is taken so that no
  separate reality statement for the Hankel transform is needed.
* `levComb c' f x` is `Lev^{(f)}(x)` of the paper verbatim (`Upper.Holes.HoleLimit`, with
  `L(x) = 2π|x|/3 = slitL x`).
* the family is encoded by the bounded finite data `σ_k` (`|σ_k| ≤ M`, `f ≤ k ≤ N`) and `ε'_k`
  (`0 ≤ ε'_k ≤ E λ`, `f < k ≤ N`) of `designComb`, as in `lemma_P_b`; the reference parameter is
  `η₀ = 1/4` (`j = 4`).

**Proof, as in the paper.**  (1) `combAmplitude_le_levComb_frac` and `lemma_Phi_transform` with
`θ = 2/5`: `‖ĥ₀‖ ≤ (55/100)(1 + C c'^{-2/5}) Lev^{(f)}`.  (2) `lemma_P_b`:
`|log(|B_D|/|B_ref|)| ≤ C_P λ/(x - ξ_*)`.  (3) `hole_floor_K5` with `j = 4`, `η₀ = 1/4`, with
`muHole_four_quarter_gt : 7/10 < μ₄(1/4)`, `eLeftComb_bounds`.  (4) Combination: the lower factors exceed
`0.995` and the upper factor is at most `1.02`: `0.7 · 0.995 - 0.55 · 1.02 > 0.13`.

* `proposition_II_floor`: the `h₀^D` half of the proof (steps (2)--(3)): node, real value `r` of `B_D^{(f)}(x)`, floor and
  `|log (r/R)| ≤ 1/1000`, reused by the two-zero comb (`TwoLevel/TwoZeroRegionTwo`).
* `proposition_II`: the compact-family statement.
* `proposition_II_sig`: the `f = 1` combs with arbitrary offsets `σ`, `designWidth1`; `proposition_II_design`:
  the designs `D(N, η_*, d)` (`σ = designSigma1 d`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes

/-! ### 1. Definitions -/

/-- `2 g(t) = h₀^D(x) - ĥ₀(t)` at `t = c' x² / 3` (real part), for the test function
`h₀^D = sech²(π b/2) B_D^{(f)}`. -/
noncomputable def twoG (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (x : ℝ) : ℝ :=
  (designProfile c' f N η₀ σ ε (x : ℂ) -
    edgeHankel c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)).re

/-- `2 g_w(t) = h₀(x) - (𝓗_{p+1} h₀)(t)` at `t = c' x² / 3` (real part), the order-`p` test of
weight `w = p + 1` (`ut:III`): the transform is `edgeHankelP p`, the `(p+1)`-st Hankel transform of the radial profile
(`fw:e1.2a`). -/
noncomputable def twoGW (p : ℕ) (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (x : ℝ) : ℝ :=
  (designProfile c' f N η₀ σ ε (x : ℂ) -
    edgeHankelP p c' (designProfile c' f N η₀ σ ε) (c' * x ^ 2 / 3)).re

/-- At weight `1` (`p = 0`) the order-`p` test is the original one. -/
lemma twoGW_zero (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (x : ℝ) :
    twoGW 0 c' f N η₀ σ ε x = twoG c' f N η₀ σ ε x := by
  unfold twoGW twoG
  rw [edgeHankelP_zero]

/-! ### 2. Elementary lemmas -/

lemma sechSqProfile_ofReal (x : ℝ) :
    sechSqProfile (x : ℂ) = ((1 / Real.cosh (π * x / 2) ^ 2 : ℝ) : ℂ) := by
  unfold sechSqProfile
  have : (π : ℂ) * (x : ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_cosh]
  push_cast
  ring

/-- Every cell index `n ≥ M` containing `x` exists as soon as `x ≥ χ_M`. -/
lemma exists_inCell {c' : ℝ} (hc' : 0 < c') {M : ℕ} (hM : 1 ≤ M) {x : ℝ}
    (hx : chiQuantile c' (M : ℝ) ≤ x) : ∃ n : ℕ, M ≤ n ∧ inCell c' n x := by
  have htend := tendsto_chiQuantile_atTop hc'
  have hev := (htend.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop x
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp hev
  have hex : ∃ m : ℕ, x < chiQuantile c' ((m + 1 : ℕ) : ℝ) := ⟨m0, hm0 (m0 + 1) (by omega)⟩
  classical
  set n := Nat.find hex with hn
  have hspec : x < chiQuantile c' ((n + 1 : ℕ) : ℝ) := Nat.find_spec hex
  have hmono : ∀ a b : ℕ, 1 ≤ a → a ≤ b → chiQuantile c' (a : ℝ) ≤ chiQuantile c' (b : ℝ) :=
    fun a b ha hab =>
      (chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by have : (1 : ℝ) ≤ a := by exact_mod_cast ha
                             linarith))
        (Set.mem_Ici.mpr (by have : (1 : ℝ) ≤ a := by exact_mod_cast ha
                             have : (a : ℝ) ≤ b := by exact_mod_cast hab
                             linarith))
        (by exact_mod_cast hab)
  have hnM : M ≤ n := by
    by_contra hlt
    push Not at hlt
    have h1 := hmono (n + 1) M (by omega) (by omega)
    linarith
  refine ⟨n, hnM, ?_, hspec⟩
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlt : m < n := by omega
  have hmin := Nat.find_min hex hlt
  push Not at hmin
  rw [hm]
  exact hmin

lemma tendsto_rpow_neg_two_fifths :
    Tendsto (fun c' : ℝ => c' ^ (-(2 / 5 : ℝ))) atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop (by norm_num)

/-- `λ(c') = o(c'^{-2/5})`: `K λ ≤ ε₀ c'^{-2/5}` for large `c'`. -/
lemma eventually_mul_lambda_le (K ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∀ᶠ c' in atTop, K * lambdaComb c' ≤ ε₀ * c' ^ (-(2 / 5 : ℝ)) := by
  have hrate : Tendsto (fun c' : ℝ => (kTip ^ (-(2 / 3 : ℝ)) * K) * c' ^ (-(4 / 15 : ℝ)))
      atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 15)).const_mul
      (kTip ^ (-(2 / 3 : ℝ)) * K)
    simpa using this
  filter_upwards [hrate.eventually_le_const hε₀, eventually_gt_atTop (0 : ℝ)] with c' h1 hc'
  have hu : 0 < c' ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hlam : lambdaComb c' = kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
    unfold lambdaComb
    rw [Real.mul_rpow kTip_pos.le hc'.le]
  have hsplit : c' ^ (-(2 / 3 : ℝ)) = c' ^ (-(4 / 15 : ℝ)) * c' ^ (-(2 / 5 : ℝ)) := by
    rw [← Real.rpow_add hc']; congr 1; norm_num
  rw [hlam, hsplit]
  calc K * (kTip ^ (-(2 / 3 : ℝ)) * (c' ^ (-(4 / 15 : ℝ)) * c' ^ (-(2 / 5 : ℝ))))
      = ((kTip ^ (-(2 / 3 : ℝ)) * K) * c' ^ (-(4 / 15 : ℝ))) * c' ^ (-(2 / 5 : ℝ)) := by ring
    _ ≤ ε₀ * c' ^ (-(2 / 5 : ℝ)) := mul_le_mul_of_nonneg_right h1 hu.le

lemma rpow_neg_two_fifths_le_one {c' : ℝ} (hc' : 1 ≤ c') : c' ^ (-(2 / 5 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hc' (by norm_num)

/-- A bound `K λ ≤ ε₀ u` gives `K λ / (x - ξ_*) ≤ ε₀` for `x - ξ_* ≥ u`. -/
lemma div_le_of_mul_le {K lam u ε₀ X : ℝ} (hu : 0 < u) (hε : 0 ≤ ε₀) (hK : K * lam ≤ ε₀ * u)
    (hX : u ≤ X) : K * lam / X ≤ ε₀ := by
  have hX0 : 0 < X := lt_of_lt_of_le hu hX
  rw [div_le_iff₀ hX0]
  nlinarith [mul_le_mul_of_nonneg_left hX hε]

/-! ### 3. The reality of `h₀^D` -/

lemma designProfile_ofReal {c' η₀ x : ℝ} {f N : ℕ} {σ ε : ℕ → ℝ} {r : ℝ}
    (hr : designComb c' f N η₀ σ ε (x : ℂ) = (r : ℂ)) :
    designProfile c' f N η₀ σ ε (x : ℂ) = ((1 / Real.cosh (π * x / 2) ^ 2 * r : ℝ) : ℂ) := by
  unfold designProfile
  rw [hr, sechSqProfile_ofReal, ← Complex.ofReal_mul]

/-! ### 4. Pointwise ingredients -/

/-- `|log (r/R)| ≤ 1/1000` gives `0.999 R ≤ r` (for `r, R > 0`). -/
lemma ratio_ge_of_log_le {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hlog : |Real.log (r / R)| ≤ 1 / 1000) :
    (999 / 1000 : ℝ) * R ≤ r := by
  have hratio : (999 / 1000 : ℝ) ≤ r / R := by
    have hrR : 0 < r / R := div_pos hr hR
    have hl : -(1 / 1000 : ℝ) ≤ Real.log (r / R) := (abs_le.mp hlog).1
    have h1 : Real.exp (-(1 / 1000 : ℝ)) ≤ r / R := by
      calc Real.exp (-(1 / 1000 : ℝ)) ≤ Real.exp (Real.log (r / R)) := Real.exp_le_exp.mpr hl
        _ = r / R := Real.exp_log hrR
    have h2 := Real.add_one_le_exp (-(1 / 1000 : ℝ))
    have h3 : (999 / 1000 : ℝ) ≤ Real.exp (-(1 / 1000 : ℝ)) := by linarith only [h2]
    exact h3.trans h1
  exact (le_div_iff₀ hR).mp hratio

/-- Step (4), the arithmetic of the combination: with the lower factors `≥ 0.995` and the upper
factor `≤ 1.02`, `0.7 · 0.995 - 0.55 · 1.02 > 0.13`. -/
lemma regionII_assemble {Lev h0r R r sech a hh nh : ℝ} (hlev : 0 < Lev) (hs : 0 ≤ sech)
    (hR : 0 < R) (hr : 0 < r)
    (hfl : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) ≤ h0r / Lev) (h0n : h0r = sech * R)
    (hlog : |Real.log (r / R)| ≤ 1 / 1000) (ha : a = sech * r) (hhn : hh ≤ nh)
    (hn : nh ≤ (55 / 100 : ℝ) * (102 / 100) * Lev) : 13 / 100 ≤ (a - hh) / Lev := by
  have hr' : (999 / 1000 : ℝ) * R ≤ r := ratio_ge_of_log_le hr hR hlog
  have hq1' : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * Lev ≤ sech * R := by
    rw [← h0n]; exact (le_div_iff₀ hlev).mp hfl
  have hmain : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * Lev ≤ a := by
    rw [ha]
    calc (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * Lev
        = (999 / 1000 : ℝ) * ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * Lev) := by ring
      _ ≤ (999 / 1000 : ℝ) * (sech * R) := mul_le_mul_of_nonneg_left hq1' (by norm_num)
      _ = sech * ((999 / 1000 : ℝ) * R) := by ring
      _ ≤ sech * r := mul_le_mul_of_nonneg_left hr' hs
  rw [le_div_iff₀ hlev]
  linarith only [hmain, hhn, hn, hlev]

/-- The Hankel bound against the level: `‖ĥ₀‖ ≤ (55/100)(1 + w) Lev ≤ (55/100)(102/100) Lev`. -/
lemma hat_bound_real {nh A Lev w : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ (55 / 100 : ℝ) * Lev) (hw0 : 0 ≤ w)
    (hw : w ≤ 1 / 50) (h : nh ≤ A * (1 + w)) : nh ≤ (55 / 100 : ℝ) * (102 / 100) * Lev := by
  have hL : 0 ≤ Lev := by linarith only [hA0, hA]
  calc nh ≤ A * (1 + w) := h
    _ ≤ ((55 / 100 : ℝ) * Lev) * (102 / 100) :=
        mul_le_mul hA (by linarith only [hw]) (by linarith only [hw0]) (by positivity)
    _ = _ := by ring

/-- Step (3), arithmetic: the hole floor with `μ₄ > 7/10`, `C₄(1/n + ℓ_n) ≤ 2/1000`,
`𝓔_left ≤ 1/1000`. -/
lemma floor_lower {μ C δ eL H : ℝ} (hμ : 7 / 10 < μ) (hδ : C * δ ≤ 2 / 1000) (heL : eL ≤ 1 / 1000)
    (hfl : μ * (1 - C * δ) * Real.exp (-2 * eL) ≤ H) :
    (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) ≤ H := by
  refine le_trans ?_ hfl
  have ha1 : 998 / 1000 ≤ 1 - C * δ := by linarith only [hδ]
  have ha2 : 998 / 1000 ≤ Real.exp (-2 * eL) := by
    have := Real.add_one_le_exp (-2 * eL)
    linarith only [this, heL]
  have hμ0 : 0 ≤ μ := by linarith only [hμ]
  exact mul_le_mul (mul_le_mul hμ.le ha1 (by norm_num) hμ0) ha2 (by norm_num)
    (mul_nonneg hμ0 (by linarith only [ha1]))

/-- The sites of the modification lie in `[0, x)`. -/
lemma design_site_facts {c' u x M s : ℝ} {f N : ℕ} {σ : ℕ → ℝ} (hlam0 : 0 ≤ lambdaComb c')
    (hMl : lambdaComb c' * M ≤ xiStar) (hMs : M ≤ s) (he1 : 4 * s * lambdaComb c' ≤ 1 * u)
    (hu0 : 0 < u) (hx : xiStar + u ≤ x) (hσ : ∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) :
    ∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k ∧ designSite c' σ k < x := by
  intro k hk hkN
  have hb := designSite_bounds (s := s) hlam0 (hσ k hk hkN) hMs hMl
  refine ⟨hb.1, ?_⟩
  linarith only [hb.2, he1, hx, hu0]

/-- The cell of `x` and the position of `x` to the right of `χ_{f+1/2}`. -/
lemma cell_facts {c' x : ℝ} (hc' : 0 < c') {f N₄ n₀ : ℕ} (hf : 1 ≤ f)
    (hx : chiQuantile c' ((max (max N₄ (f + 4)) n₀ : ℕ) : ℝ) ≤ x) :
    ∃ n : ℕ, max N₄ (f + 4) ≤ n ∧ n₀ ≤ n ∧ inCell c' n x ∧
      chiQuantile c' (f : ℝ) < x ∧ chiQuantile c' ((f : ℝ) + 1 / 2) < x := by
  have hM0pos : 1 ≤ max (max N₄ (f + 4)) n₀ := by
    have : f + 4 ≤ max (max N₄ (f + 4)) n₀ := le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  obtain ⟨n, hnM, hcell⟩ := exists_inCell hc' hM0pos hx
  have hn_f4 : f + 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnM
  have hfR : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hfn : (f : ℝ) + 4 ≤ (n : ℝ) := by exact_mod_cast hn_f4
  refine ⟨n, le_trans (le_max_left _ _) hnM, le_trans (le_max_right _ _) hnM, hcell, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ hcell.1
    exact (chiQuantile_strictMonoOn hc') (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith)
  · refine lt_of_lt_of_le ?_ hcell.1
    exact (chiQuantile_strictMonoOn hc') (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith)

/-! ### 5. Proposition II -/

/-- **Proposition II, floor half** (`ut:II` steps (2)--(3)): for `c'` large, every family member and every
`x ≥ ξ_* + c'^{-2/5}`, `x` lies right of the node `χ_{f+1/2}`, `B_D^{(f)}(x) = r > 0` is real, and with
`R = ‖B_ref^{(f)}(x)‖`: `0.7 · 0.998² · Lev^{(f)} ≤ sech²(πx/2) R` and `|log (r/R)| ≤ 1/1000`. -/
theorem proposition_II_floor (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
        chiQuantile c' ((f : ℝ) + 1 / 2) < x ∧
        ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ designComb c' f N (1 / 4) σ ε (x : ℂ) = (r : ℂ) ∧
          (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * levComb c' f x ≤
            1 / Real.cosh (π * x / 2) ^ 2 * R ∧
          |Real.log (r / R)| ≤ 1 / 1000 := by
  obtain ⟨CP, hCP, hP⟩ := lemma_P_b f N hf hfN M E
  obtain ⟨CL, hCL, hL⟩ := eLeftComb_bounds
  obtain ⟨N₄, C₄, hN₄, hC₄, hfloor⟩ :=
    hole_floor_K5 (j := 4) (η₀ := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cg, hCg, hgapev⟩ := siteGap_eventually_le
  set s : ℝ := max (phiQuantile ((N : ℝ) + 2)) M with hs
  set n₀ : ℕ := ⌈1000 * C₄⌉₊ + 1 with hn₀
  set M0 : ℕ := max (max N₄ (f + 4)) n₀ with hM0
  have hM0pos : 1 ≤ M0 := by
    have : f + 4 ≤ M0 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) le_rfl
    omega
  have hmuc := muHole_four_quarter_gt
  have e1 := eventually_mul_lambda_le (4 * s) 1 one_pos
  have e2 := eventually_mul_lambda_le (phiQuantile ((M0 : ℝ) + 2)) 1 one_pos
  have e3 := eventually_mul_lambda_le CL (1 / 1000) (by norm_num)
  have e4 := eventually_mul_lambda_le CP (1 / 1000) (by norm_num)
  have e5 := eventually_mul_lambda_le (C₄ * Cg) (1 / 1000) (by norm_num)
  have e6 := eventually_mul_lambda_le M xiStar xiStar_pos
  have e7 := eventually_mul_lambda_le E (1 / 2) (by norm_num)
  filter_upwards [hP (η₀ := 1 / 4) (by norm_num) (by norm_num), hL, hfloor, hgapev,
    tail_ne_zero_of_refComb_ne_zero f N hfN (η₀ := 1 / 4) (by norm_num) (by norm_num),
    e1, e2, e3, e4, e5, e6, e7, eventually_ge_atTop (1 : ℝ)]
    with c' hPc hLc hflc hgc htailc he1 he2 he3 he4 he5 he6 he7 hc1 σ ε hσ hε x hx
  obtain ⟨hgap_k, hgap_1, hcd, hgap_half⟩ := hgc
  have hc' : 0 < c' := lt_of_lt_of_le one_pos hc1
  set u : ℝ := c' ^ (-(2 / 5 : ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hc' _
  have hu1 : u ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hlam0 : 0 ≤ lambdaComb c' := (Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _).le
  have hxu : u ≤ x - xiStar := by linarith only [hx]
  have hxi : xiStar < x := by linarith only [hx, hu0]
  have hχM0 : chiQuantile c' (M0 : ℝ) ≤ x := by
    have h := (refSite_bounds hc' hM0pos (le_refl M0)).2
    linarith only [h, he2, hx]
  obtain ⟨n, hnmax, hn_n0, hcell, hχf, hχf2⟩ := cell_facts hc' hf hχM0
  have hn1 : 1 ≤ n := by
    have : f + 4 ≤ max N₄ (f + 4) := le_max_right _ _
    omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hMl : lambdaComb c' * M ≤ xiStar := by
    have h : M * lambdaComb c' ≤ xiStar * u := he6
    have h' : xiStar * u ≤ xiStar := by nlinarith only [hu1, xiStar_pos]
    linarith only [h, h']
  have hsite := design_site_facts (s := s) (x := x) hlam0 hMl (by rw [hs]; exact le_max_right _ M) he1 hu0
    (by linarith only [hx]) hσ
  have hεw : ∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ 1 / 2 := by
    intro k hk hkN
    have h := hε k hk hkN
    have h7 : E * lambdaComb c' ≤ 1 / 2 * u := he7
    exact ⟨h.1, by linarith only [h.2, h7, hu1]⟩
  obtain ⟨-, -, -, -, h0_norm⟩ :=
    refComb_re_nonneg_of_gt hc' (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hgap_half hf hχf
  have hlev := levComb_pos c' f x
  have hfl := hflc f n x hf hnmax hcell
  have hsg : siteGap c' n ≤ Cg * lambdaComb c' := (hgap_k n hn1).trans (hgap_1.trans hcd)
  have hnC : C₄ / (n : ℝ) ≤ 1 / 1000 := by
    have h1 : 1000 * C₄ ≤ (n₀ : ℝ) := by
      have := Nat.le_ceil (1000 * C₄)
      have h2 : (⌈1000 * C₄⌉₊ : ℝ) + 1 = (n₀ : ℝ) := by rw [hn₀]; push_cast; ring
      linarith only [this, h2]
    have h2 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn_n0
    rw [div_le_iff₀ hnR]
    linarith only [h1, h2]
  have hδ1 : C₄ * (1 / (n : ℝ) + siteGap c' n) ≤ 2 / 1000 := by
    have h1 : C₄ * siteGap c' n ≤ C₄ * (Cg * lambdaComb c') :=
      mul_le_mul_of_nonneg_left hsg hC₄.le
    have h2 : C₄ * Cg * lambdaComb c' ≤ 1 / 1000 * u := he5
    have h3 : C₄ * (1 / (n : ℝ) + siteGap c' n) = C₄ / n + C₄ * siteGap c' n := by ring
    have h4 : C₄ * (Cg * lambdaComb c') = C₄ * Cg * lambdaComb c' := by ring
    rw [h3]
    linarith only [h1, h2, h4, hnC, hu1]
  have hLbd := (hLc f n 4 x hf hxi).2
  have hδ2 : eLeftComb c' f n 4 x ≤ 1 / 1000 :=
    hLbd.trans (div_le_of_mul_le hu0 (by norm_num) he3 hxu)
  have hq1 := floor_lower hmuc hδ1 hδ2 hfl
  have hq1pos : 0 < h0Comb c' f (1 / 4) x := by
    have h := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000)) hq1
    rwa [lt_div_iff₀ hlev, zero_mul] at h
  have hsech : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have href_pos : 0 < ‖refComb c' f (1 / 4) (x : ℂ)‖ := by
    rw [h0_norm] at hq1pos
    exact pos_of_mul_pos_right hq1pos hsech.le
  obtain ⟨r, hr, hr0, hrpos⟩ := designComb_ofReal hc' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half f N σ ε hsite hεw hfN
  have hrp : 0 < r := hrpos (htailc x (norm_pos_iff.mp href_pos))
  have hnormD : ‖designComb c' f N (1 / 4) σ ε (x : ℂ)‖ = r := by
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hPbd := hPc σ ε hσ hε x (by linarith only [he1, hx])
  rw [hnormD] at hPbd
  have hlogbd : |Real.log (r / ‖refComb c' f (1 / 4) (x : ℂ)‖)| ≤ 1 / 1000 := by
    have h := div_le_of_mul_le hu0 (by norm_num) he4 hxu
    rw [mul_div_assoc] at h
    exact hPbd.trans h
  have hfloor' : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * levComb c' f x ≤
      1 / Real.cosh (π * x / 2) ^ 2 * ‖refComb c' f (1 / 4) (x : ℂ)‖ := by
    rw [← h0_norm]; exact (le_div_iff₀ hlev).mp hq1
  exact ⟨hχf2, ‖refComb c' f (1 / 4) (x : ℂ)‖, r, href_pos, hrp, hr, hfloor', hlogbd⟩

/-- **Proposition II** (`ut:II`), compact-family version: fix `f ≥ 1`, `N ≥ f`, `M`, `E ≥ 0`.  For `c'`
large, every finite modification `B_D^{(f)}` of the `η₀ = 1/4` reference comb with `|σ_k| ≤ M`,
`0 ≤ ε'_k ≤ E λ` (the family of `lemma_P_b`), and every `x ≥ ξ_* + c'^{-2/5}`,
`2 g(c' x²/3) / Lev^{(f)}(x) ≥ 13/100`, where `2 g = h₀^D - ĥ₀` (`twoG`). -/
theorem proposition_II (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
        13 / 100 ≤ twoG c' f N (1 / 4) σ ε x / levComb c' f x := by
  obtain ⟨C₁, hC₁, hΦ⟩ := lemma_Phi_transform f N hf hfN M E hE (η₀ := 1 / 4) (by norm_num)
    (by norm_num) (θ := 2 / 5) (by norm_num) (by norm_num)
  have hexp1 : (-1 + 3 * (2 / 5 : ℝ) / 2) = -(2 / 5 : ℝ) := by norm_num
  have e8 : ∀ᶠ c' in atTop, C₁ * c' ^ (-(2 / 5 : ℝ)) ≤ 1 / 50 :=
    (tendsto_rpow_neg_two_fifths.const_mul C₁).eventually_le_const (by norm_num)
  filter_upwards [hΦ, proposition_II_floor f N hf hfN M E, e8, eventually_ge_atTop (1 : ℝ)]
    with c' hΦc hfl he8 hc1 σ ε hσ hε x hx
  obtain ⟨hχf2, R, r, hR, hr, hcomb, hf1, hlog⟩ := hfl σ ε hσ hε x hx
  have hc' : 0 < c' := lt_of_lt_of_le one_pos hc1
  have hu0 : 0 < c' ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hlev := levComb_pos c' f x
  have hsech : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have hh0 : (designProfile c' f N (1 / 4) σ ε (x : ℂ)).re = 1 / Real.cosh (π * x / 2) ^ 2 * r := by
    rw [designProfile_ofReal hcomb, Complex.ofReal_re]
  have hA := combAmplitude_le_levComb_frac hc' hf hχf2
  have hA0 : 0 ≤ combAmplitude c' x := by
    unfold combAmplitude sdvPrefactor; positivity
  have hΦx := hΦc σ ε hσ hε x hx
  rw [hexp1] at hΦx
  have hhat := hat_bound_real hA0 hA (mul_nonneg hC₁ hu0.le) he8 hΦx
  unfold twoG
  rw [Complex.sub_re]
  exact regionII_assemble hlev hsech.le hR hr
    ((le_div_iff₀ hlev).mpr hf1) rfl hlog hh0
    (Complex.re_le_norm _) hhat

/-- **Proposition II, positivity form**: `g > 0` on Region II, uniformly over the family. -/
theorem proposition_II_pos (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x → 0 < twoG c' f N (1 / 4) σ ε x := by
  filter_upwards [proposition_II f N hf hfN M E hE] with c' hc' σ ε hσ hε x hx
  have h := hc' σ ε hσ hε x hx
  have hlev := levComb_pos c' f x
  rw [le_div_iff₀ hlev] at h
  linarith only [h, hlev]

/-- **Proposition II for the `f = 1` finite modifications at fixed sites** (`ut:II`, `η₀ = 1/4`): the family is
the single comb with arbitrary offsets `σ` (bounded by `M` on `1 ≤ k ≤ N`) and `ε = designWidth1 c' η_*`.
`proposition_II_design` is the case `σ = designSigma1 d`. -/
theorem proposition_II_sig (N : ℕ) (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar)
    (hη1 : etaStar ≤ 1 / 4) (σ : ℕ → ℝ) (M : ℝ) (hM : ∀ k, 1 ≤ k → k ≤ N → |σ k| ≤ M) :
    ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      13 / 100 ≤ twoG c' 1 N (1 / 4) σ (designWidth1 c' etaStar) x /
        levComb c' 1 x := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  filter_upwards [proposition_II 1 N le_rfl hN M Cg hCg.le, h_ev, eventually_gt_atTop (0 : ℝ)]
    with c' hc' ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos
  refine fun x hx => hc' σ (designWidth1 c' etaStar) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), ?_⟩) x hx
  have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
  unfold designWidth1
  calc etaStar * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
        mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
    _ = Cg * lambdaComb c' := one_mul _

/-- **Proposition II for the designs `D(N, η_*, d)`** (`ut:II`, `f = 1`, `η₀ = 1/4`): the family is the
single design `σ = designSigma1 d`, `ε = designWidth1 c' η_*` of `lemma_P_a_fixedN`, with `M` a bound
for the finitely many offsets `σ_1, …, σ_N`. -/
theorem proposition_II_design (N : ℕ) (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar)
    (hη1 : etaStar ≤ 1 / 4) (d M : ℝ) (hM : ∀ k, 1 ≤ k → k ≤ N → |designSigma1 d k| ≤ M) :
    ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      13 / 100 ≤ twoG c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' etaStar) x /
        levComb c' 1 x :=
  proposition_II_sig N hN hη0 hη1 (designSigma1 d) M hM

/-- Non-vacuity of the family: the zero modification (`σ = 0`, `ε = 0`) satisfies the constraints of
`proposition_II` for every `c' > 0` whenever `M, E ≥ 0`. -/
theorem proposition_II_family_nonempty (f N : ℕ) {M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E) {c' : ℝ}
    (hc' : 0 < c') :
    ∃ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) ∧
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') :=
  ⟨fun _ => 0, fun _ => 0, fun k _ _ => by simpa using hM, fun k _ _ =>
    ⟨le_rfl, mul_nonneg hE (Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _).le⟩⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_II' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_II

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_II_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_II_floor

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_II_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_II_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_II_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_II_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_II_design' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_II_design

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.proposition_II_family_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_II_family_nonempty

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.regionII_assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionII_assemble

end FormalResearch.ModularBootstrap.Upper.Positivity
