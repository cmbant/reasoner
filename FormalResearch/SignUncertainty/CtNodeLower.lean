module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLowerChartGap
public import FormalResearch.SignUncertainty.CtChartComplex
public import FormalResearch.SignUncertainty.CtDyadicPsiWindow
public import FormalResearch.SignUncertainty.HankelQuantC1Feasible
public import FormalResearch.Special.BulkWindowAiry
public import FormalResearch.Special.AiryCftMittagLeffler

/-!
# `thm:ct-lower`: the node lower bound (field `node_lower`)

`constant_terms_lower.tex`, proof of the lower bound in `thm:ct-lower`(i), second half: `g_vac ≥ 0` (`ε f(0) ≤ 0`), the sign of the
`n ≥ 2` Airy nodes (`gt:7.7p` (b): `Ψ̃ ≥ -r_∞` below `ũ₁`, `hankel_psi_sign`) and the effective `C¹` stability at the first node
(`gt:7.7p` (d): `Re Ψ̃' ≤ -2κ_*`, `hankelPsiR_slope`).  **Proved, unconditional** (`ct_node_lower`, `CtNodeLowerStatement`).

* `ctPhi_hasDerivAt`: `φ_c = û⁻¹` is differentiable at the Airy nodes `a < -1` of the window with `φ_c' = 1/û' ∈ [2/3, 2]`
  (`û` has slope `≥ 1/2` there, `ctUhat_sub_ge`; local left inverse `HasDerivAt.of_local_left_inverse`).
* `tsum_nodes_lower`: the node series bound with `≤ R^{3/2} + 1` nodes in `(-R, 0)` (`|a_n| ≥ 2.5 n^{2/3}`), `Ai'(a_n)² ≥ Ai'(0)²`
  (`E = Ai'² - x Ai²` is monotone: `airyZero_deriv_sq_ge`).
* `ctNodeLower_eps`: `κ (ũ₁ - φ_c(a₁)) ≤ P_R(H) + g_vac/2π + C' e^{-c/80000}` for `ε = ±1`, `κ = κ_*/(3 Ai'(a₁)²)`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- **The node lower bound** of the proof of `thm:ct-lower` (`gt:7.7p` (b), (d), `g_vac ≥ 0`, sign of the `n ≥ 2` nodes), for the window
of `c₁`: at every radius of the window the budget is at least `κ` times the gap up to an exponentially small term. -/
def CtNodeLowerStatement (c₁ : ℝ) : Prop :=
  ∃ κ κ' C' c₀ : ℝ, 0 < κ ∧ 0 < κ' ∧ ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Set.Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
        κ * ctGap ε c T ≤ ctBudget R ε c f + C' * Real.exp (-κ' * c)

/-! ### Airy node sums -/

/-- `Ai'(a_n)² ≥ Ai'(0)²` (`E = Ai'² - x Ai²` is non-increasing and `Ai(a_n) = 0`). -/
lemma airyZero_deriv_sq_ge (n : ℕ) : bwn_c0 ^ 2 ≤ airyAi' (airyZero n) ^ 2 := by
  have h := bwn_E_ge (airyZero_nonpos n)
  rw [airyAi_airyZero] at h
  simpa using h

/-- Every node `a_{n+1}` with `n ≥ ⌈R^{3/2}⌉₊` lies at or below `-R` (`|a_n| ≥ 2.5 n^{2/3}`). -/
lemma airyZero_le_neg_of_ge {R : ℝ} (hR : 0 ≤ R) {n : ℕ} (hn : ⌈R ^ (3 / 2 : ℝ)⌉₊ ≤ n) :
    airyZero (n + 1) ≤ -R := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have : R ^ (3 / 2 : ℝ) ≤ 0 := by simpa using Nat.ceil_le.1 hn
    have hR0 : R = 0 := by
      by_contra hne
      have := Real.rpow_pos_of_pos (lt_of_le_of_ne hR (Ne.symm hne)) (3 / 2 : ℝ)
      linarith
    subst hR0
    simpa using airyZero_nonpos 1
  have h1 : 2 ≤ n + 1 := by omega
  have hb := (airyZero_abs_bounds h1).1
  have hR32 : R ^ (3 / 2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (R ^ (3 / 2 : ℝ))
    have h2 : ((⌈R ^ (3 / 2 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast
    linarith
  have h23 : R ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hR _) hR32 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rwa [← Real.rpow_mul hR, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at this
  have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) := by positivity
  linarith

/-- **Node sum lower bound**: a node series whose terms vanish for the nodes `a_{n+1} ≤ -R` and are `≥ -D` for `n ≥ 1` has
`∑' t ≥ t₀ - D (R^{3/2} + 1)` (there are at most `R^{3/2} + 1` nodes in `(-R, 0)`). -/
lemma tsum_nodes_lower {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) {t : ℕ → ℝ}
    (h0 : ∀ n, airyZero (n + 1) ≤ -R → t n = 0) (h : ∀ n, 1 ≤ n → -D ≤ t n) :
    t 0 - D * (R ^ (3 / 2 : ℝ) + 1) ≤ ∑' n, t n := by
  set N := ⌈R ^ (3 / 2 : ℝ)⌉₊ with hN
  have hz : ∀ n ∉ Finset.range (N + 1), t n = 0 := fun n hn =>
    h0 n (airyZero_le_neg_of_ge hR (by simp at hn; omega))
  rw [tsum_eq_sum hz, Finset.sum_range_succ']
  have h1 : ∑ i ∈ Finset.range N, t (i + 1) ≥ ∑ i ∈ Finset.range N, (-D) :=
    Finset.sum_le_sum fun i _ => h (i + 1) (by omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have h2 : (N : ℝ) ≤ R ^ (3 / 2 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h3 : -(D * (R ^ (3 / 2 : ℝ) + 1)) ≤ (N : ℝ) * -D := by nlinarith
  linarith

/-! ### The chart `φ_c = û⁻¹` at the Airy nodes -/

section Chart

variable {ε c ρ M : ℝ}

/-- `û` has slope `≥ 1/2` on a window: `(u₂ - u₁)/2 ≤ û(u₂) - û(u₁)` for `u₁ ≤ u₂ < 0`, `-ρ < μ u₁`. -/
lemma ctUhat_sub_ge (hW : PsiWin ε ρ M) (hc : 0 < c) (hcM : 2 * M ≤ c) {u₁ u₂ : ℝ} (h12 : u₁ ≤ u₂) (h2 : u₂ < 0)
    (h1 : -ρ < ctMu c * u₁) : (1 / 2) * (u₂ - u₁) ≤ ctUhat ε c u₂ - ctUhat ε c u₁ := by
  have hmu := ctMu_pos hc
  have hwin : ∀ x ∈ Icc u₁ u₂, -ρ < ctMu c * x := fun x hx => by
    have := mul_le_mul_of_nonneg_left hx.1 hmu.le
    linarith
  refine (convex_Icc u₁ u₂).mul_sub_le_image_sub_of_le_deriv (continuousOn_ctUhat hW hc h2 h1) ?_ ?_ u₁
    ⟨le_rfl, h12⟩ u₂ ⟨h12, le_rfl⟩ h12
  · intro x hx
    rw [interior_Icc] at hx
    exact (ctUhat_hasDerivAt hW hc (hx.2.trans h2) (hwin x ⟨hx.1.le, hx.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x < 0 := hx.2.trans h2
    have hxw := hwin x ⟨hx.1.le, hx.2.le⟩
    rw [(ctUhat_hasDerivAt hW hc hx0 hxw).deriv]
    exact (ctUhat_deriv_bounds hW hc hcM hx0 hxw).1

/-- `û` is monotone on a window (up to `0`). -/
lemma ctUhat_mono_window (hW : PsiWin ε ρ M) (hc : 0 < c) (hcM : 2 * M ≤ c) {u₁ u₂ : ℝ} (h12 : u₁ ≤ u₂) (h2 : u₂ < 0)
    (h1 : -ρ < ctMu c * u₁) : ctUhat ε c u₁ ≤ ctUhat ε c u₂ := by
  have := ctUhat_sub_ge hW hc hcM h12 h2 h1
  linarith

/-- **The preimage of a node-region point**: for `a < -1` in the window (`-ρ < μ a`) and `λM ≤ 1/2`, `û(u) = a` has a solution
`u ∈ [a, -1/2]` and `φ_c(a) = u`. -/
lemma ctPhi_pre (hW : PsiWin ε ρ M) (hc : 0 < c) (hcM : 2 * M ≤ c) (hlam : ctLam c * M ≤ 1 / 2) {a : ℝ} (ha : a < -1)
    (haw : -ρ < ctMu c * a) :
    ∃ u : ℝ, u ∈ Icc a (-(1 / 2)) ∧ ctUhat ε c u = a ∧ ctPhi ε c a = u := by
  have hR : -ρ < ctMu c * (-(-a)) := by rw [neg_neg]; exact haw
  obtain ⟨u, hu, hv⟩ := exists_ctUhat_eq hW hc hlam (R := -a) (by linarith) hR
  rw [neg_neg] at hu hv
  refine ⟨u, hu, hv, ?_⟩
  have := ctPhi_eq hW hc hcM (R := -a) (u := u) hR (by rwa [neg_neg]) (by rw [neg_neg]; exact hv)
  rwa [neg_neg] at this

/-- **`φ_c` at a node-region point is differentiable with `φ_c' = 1/û'`** (`ct:cfu`): for `a < -1` with `-ρ < μ a`,
`φ_c(a) = u ∈ [a, -1/2]`, `û(u) = a` and `HasDerivAt φ_c (1/û'(u)) a`, `û'(u) = 1 + c⁻¹ψ_ε'(μu) ∈ [1/2, 3/2]`. -/
lemma ctPhi_hasDerivAt (hW : PsiWin ε ρ M) (hc : 0 < c) (hcM : 2 * M ≤ c) (hlam : ctLam c * M ≤ 1 / 2) {a : ℝ}
    (ha : a < -1) (haw : -ρ < ctMu c * a) :
    ∃ u : ℝ, u ∈ Icc a (-(1 / 2)) ∧ ctUhat ε c u = a ∧ ctPhi ε c a = u ∧
      HasDerivAt (ctPhi ε c) (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u))⁻¹ a ∧
      1 / 2 ≤ 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u) ∧ 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u) ≤ 3 / 2 := by
  have hmu := ctMu_pos hc
  obtain ⟨u, hu, hv, hφ⟩ := ctPhi_pre hW hc hcM hlam ha haw
  have hu0 : u < 0 := by linarith [hu.2]
  have huw : -ρ < ctMu c * u := by
    have := mul_le_mul_of_nonneg_left hu.1 hmu.le
    linarith
  obtain ⟨hb1, hb2⟩ := ctUhat_deriv_bounds hW hc hcM hu0 huw
  refine ⟨u, hu, hv, hφ, ?_, hb1, hb2⟩
  have hU : IsOpen {y : ℝ | y < -1 ∧ -ρ < ctMu c * y} :=
    (isOpen_lt continuous_id continuous_const).inter (isOpen_lt continuous_const (continuous_const.mul continuous_id))
  have hUa : a ∈ {y : ℝ | y < -1 ∧ -ρ < ctMu c * y} := ⟨ha, haw⟩
  -- for `y ∈ U`: `φ(y)` is the preimage and `φ` is `2`-Lipschitz at `a`
  have hlip : ∀ y ∈ {y : ℝ | y < -1 ∧ -ρ < ctMu c * y}, |ctPhi ε c y - ctPhi ε c a| ≤ 2 * |y - a| := by
    intro y hy
    obtain ⟨u', hu', hv', hφ'⟩ := ctPhi_pre hW hc hcM hlam hy.1 hy.2
    rw [hφ', hφ]
    have hu'0 : u' < 0 := by linarith [hu'.2]
    have hu'w : -ρ < ctMu c * u' := by
      have := mul_le_mul_of_nonneg_left hu'.1 hmu.le
      linarith [hy.2]
    rcases le_total u u' with h | h
    · have := ctUhat_sub_ge hW hc hcM h hu'0 huw
      rw [hv, hv'] at this
      rw [abs_of_nonneg (by linarith)]
      have h3 : y - a ≤ |y - a| := le_abs_self _
      linarith
    · have := ctUhat_sub_ge hW hc hcM h hu0 hu'w
      rw [hv, hv'] at this
      rw [abs_of_nonpos (by linarith)]
      have h3 : -(y - a) ≤ |y - a| := neg_le_abs _
      linarith
  have hcont : ContinuousAt (ctPhi ε c) a := by
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hU.mem_nhds hUa)
    refine continuousAt_of_locally_lipschitz hr 2 fun y hy => ?_
    rw [Real.dist_eq, Real.dist_eq]
    exact hlip y (hball hy)
  have hfg : ∀ᶠ y in 𝓝 a, ctUhat ε c (ctPhi ε c y) = y := by
    filter_upwards [hU.mem_nhds hUa] with y hy
    obtain ⟨u', hu', hv', hφ'⟩ := ctPhi_pre hW hc hcM hlam hy.1 hy.2
    rw [hφ']; exact hv'
  have hd := ctUhat_hasDerivAt hW hc hu0 huw
  have := HasDerivAt.of_local_left_inverse hcont (by rw [hφ]; exact hd) (by linarith) hfg
  exact this

end Chart

/-! ### The Hankel side: `Ψ̃` near the first node -/

section Hankel

/-- `ξ` is injective on the Langer disc. -/
lemma hankelXi_inj {c : ℝ} (hc : 0 < c) {x y : ℝ} (hx : |x| ≤ langerRadius c) (hy : |y| ≤ langerRadius c)
    (h : hankelXi c x = hankelXi c y) : x = y := by
  have hanti : StrictAntiOn (hankelXi c) (Icc (-langerRadius c) (langerRadius c)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · intro z hz
      exact (hasDerivAt_hankelXi hc (abs_le.2 hz)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hasDerivAt_hankelXi hc (abs_le.2 ⟨hz.1.le, hz.2.le⟩)).deriv]
      exact hankelXiD_neg hc (abs_le.2 ⟨hz.1.le, hz.2.le⟩)
  exact hanti.injOn (abs_le.1 hx |> fun h => ⟨h.1, h.2⟩) (abs_le.1 hy |> fun h => ⟨h.1, h.2⟩) h

/-- `ũ(T/c) = u_T` when `u_T ∈ [-3, 0]` is in the Langer disc with `c ξ(u_T) = T`. -/
lemma ctUtilde_eq {c T u : ℝ} (hc : 0 < c) (h3 : 3 ≤ langerRadius c) (hu : u ∈ Icc (-3 : ℝ) 0)
    (hξ : c * hankelXi c u = T) : ctUtilde c T = u := by
  have hex : ∃ x ∈ Icc (-3 : ℝ) 0, hankelXi c x = T / c :=
    ⟨u, hu, by rw [eq_div_iff hc.ne']; linarith⟩
  have hspec : ctUtilde c T ∈ Icc (-3 : ℝ) 0 ∧ hankelXi c (ctUtilde c T) = T / c := by
    unfold ctUtilde; exact Function.invFunOn_pos hex
  refine hankelXi_inj hc (abs_le.2 ⟨by linarith [hspec.1.1], by linarith [hspec.1.2]⟩)
    (abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩) ?_
  rw [hspec.2, ← hξ]; field_simp

/-- `Re Ψ̃` is differentiable on the Langer disc with derivative `Re Ψ̃'`. -/
lemma hankelPsiR_hasDerivAt {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {x : ℝ}
    (hx : |x| ≤ langerRadius c) : HasDerivAt (hankelPsiR c f) (deriv (hankelPsi c f) (x : ℂ)).re x := by
  have han := analyticOnNhd_hankelPsi hc hf (x : ℂ) (by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; unfold langerRadius langerScale at hx; exact hx)
  have h : HasDerivAt (fun y : ℝ => hankelPsi c f (y : ℂ)) (deriv (hankelPsi c f) (x : ℂ)) x :=
    (han.differentiableAt.hasDerivAt).comp_ofReal
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- **The effective `C¹` stability at the first node** (`gt:7.7p` (d), consequence of `QuantC1B2Holds`): for `a₁ ≤ φ ≤ u_T ≤ a₁ + δ_*`,
`Re Ψ̃(φ) ≥ Re Ψ̃(u_T) + 2κ_*(u_T - φ)`. -/
lemma hankelPsiR_slope {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {u_T φ : ℝ}
    (hB2 : QuantC1B2Holds (hankelPsi c f) u_T) (hφ : airyZero 1 ≤ φ) (hφT : φ ≤ u_T)
    (hA : |airyZero 1| + 1 ≤ langerRadius c) :
    hankelPsiR c f u_T + 2 * quantC1KappaStar * (u_T - φ) ≤ hankelPsiR c f φ := by
  have hδ := quantC1DeltaStar_le
  have hT1 : u_T - airyZero 1 ≤ quantC1DeltaStar := hB2.1.trans (min_le_left _ _)
  have hdisc : ∀ x ∈ Icc φ u_T, |x| ≤ langerRadius c := fun x hx => by
    have h1 : -|airyZero 1| ≤ airyZero 1 := neg_abs_le _
    have h2 : airyZero 1 ≤ |airyZero 1| := le_abs_self _
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hT1, hδ]
  have hD := (convex_Icc φ u_T).image_sub_le_mul_sub_of_deriv_le (f := hankelPsiR c f) (C := -(2 * quantC1KappaStar))
    (fun x hx => (hankelPsiR_hasDerivAt hc hf (hdisc x hx)).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hankelPsiR_hasDerivAt hc hf (hdisc x ⟨hx.1.le, hx.2.le⟩)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hankelPsiR_hasDerivAt hc hf (hdisc x ⟨hx.1.le, hx.2.le⟩)).deriv]
      have := (hB2.2 x ⟨by linarith [hx.1, quantC1DeltaStar_pos], by linarith [hx.2]⟩).2
      linarith) φ ⟨le_rfl, hφT⟩ u_T ⟨hφT, le_rfl⟩ hφT
  linarith

end Hankel

/-! ### Term bounds -/

/-- A node term with `Ψ̃ ≥ -r`: `W (P g)/Q ≥ -2r/c₀²` for `W ∈ [0,1]`, `g ∈ [2/3, 2]`, `Q ≥ c₀² > 0`, `r ≥ 0`. -/
lemma node_term_ge {W P g Q r c0 : ℝ} (hW0 : 0 ≤ W) (hW1 : W ≤ 1) (hg0 : 2 / 3 ≤ g) (hg1 : g ≤ 2)
    (hP : -r ≤ P) (hr : 0 ≤ r) (hc0 : 0 < c0) (hQ : c0 ≤ Q) : -(2 * r / c0) ≤ W * (P * g) / Q := by
  have hQ0 : 0 < Q := lt_of_lt_of_le hc0 hQ
  have h1 : -(2 * r) ≤ W * (P * g) := by
    rcases le_total 0 P with hP0 | hP0
    · nlinarith [mul_nonneg hW0 (mul_nonneg hP0 (by linarith : (0 : ℝ) ≤ g))]
    · have : -r * 2 ≤ P * g := by nlinarith
      nlinarith [mul_nonneg hW0 (by nlinarith : (0 : ℝ) ≤ 2 * r + P * g + r * 0 + r * 0 + 0), hW1]
  rw [le_div_iff₀ hQ0]
  have h2 : 2 * r / c0 * Q ≥ 2 * r := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hc0]; nlinarith
  nlinarith

/-- The first node term: `W ∈ [1/4, 1]`, `g ∈ [2/3, 2]`, `P ≥ -r + 2κ x` (`x ≥ 0`), `Q ≥ c₀²`:
`W(Pg)/Q ≥ κ x/(3Q) - 2r/c₀²`. -/
lemma node_term_first {W P g Q r κ x c0 : ℝ} (hW0 : 1 / 4 ≤ W) (hW1 : W ≤ 1) (hg0 : 2 / 3 ≤ g) (hg1 : g ≤ 2)
    (hP : -r + 2 * κ * x ≤ P) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hc0 : 0 < c0) (hQ : c0 ≤ Q) :
    κ * x / (3 * Q) - 2 * r / c0 ≤ W * (P * g) / Q := by
  have hQ0 : 0 < Q := lt_of_lt_of_le hc0 hQ
  have hkx : 0 ≤ κ * x := mul_nonneg hκ hx
  have hWg1 : 1 / 6 ≤ W * g := by nlinarith [mul_nonneg (sub_nonneg.2 hW0) (sub_nonneg.2 hg0)]
  have hWg2 : W * g ≤ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hW1) (by linarith : (0 : ℝ) ≤ g)]
  have h1 : κ * x / 3 - 2 * r ≤ W * (P * g) := by
    rcases le_total 0 P with hP0 | hP0
    · have : (1 / 6 : ℝ) * P ≤ W * (P * g) := by nlinarith [mul_nonneg hP0 (by linarith : (0 : ℝ) ≤ W * g - 1 / 6)]
      nlinarith
    · have : P * 2 ≤ W * (P * g) := by
        nlinarith [mul_nonneg (neg_nonneg.2 hP0) (by linarith : (0 : ℝ) ≤ 2 - W * g)]
      nlinarith
  have e : κ * x / (3 * Q) - 2 * r / c0 ≤ (κ * x / 3 - 2 * r) / Q := by
    have h2 : 2 * r / c0 ≥ 2 * r / Q := by
      apply div_le_div_of_nonneg_left (by linarith) hc0 hQ
    have : (κ * x / 3 - 2 * r) / Q = κ * x / (3 * Q) - 2 * r / Q := by field_simp
    rw [this]; linarith
  exact e.trans (div_le_div_of_nonneg_right h1 hQ0.le)

/-- `c^{4/3} e^{-c/80000} ≤ 1` for large `c`. -/
lemma rpow_exp_small : ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → c ^ (4 / 3 : ℝ) * Real.exp (-(1 / 80000 : ℝ) * c) ≤ 1 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / 3 : ℝ) (1 / 80000) (by norm_num)
  obtain ⟨c₀, h⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  exact ⟨c₀, h⟩

/-! ### The node lower bound for one `ε` -/

lemma rpow_third_ge' {c M : ℝ} (hM : 0 ≤ M) (hc : (2 * M + 1) ^ 3 ≤ c) : 2 * M + 1 ≤ c ^ (1 / 3 : ℝ) := by
  have hx : 0 ≤ 2 * M + 1 := by linarith
  have := Real.rpow_le_rpow (by positivity) hc (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have e : ((2 * M + 1) ^ 3) ^ (1 / 3 : ℝ) = 2 * M + 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  rwa [e] at this

lemma inv_bounds {D : ℝ} (h1 : 1 / 2 ≤ D) (h2 : D ≤ 3 / 2) : 2 / 3 ≤ D⁻¹ ∧ D⁻¹ ≤ 2 := by
  have hD : 0 < D := by linarith
  constructor
  · rw [inv_eq_one_div, le_div_iff₀ hD]; linarith
  · rw [inv_eq_one_div, div_le_iff₀ hD]; linarith

/-- The taper `W₆(a) = (1 - (a/R)^{12})²` is in `[0, 1]` for `|a| ≤ R`. -/
lemma W6_bounds {a R : ℝ} (hR : 0 < R) (ha : |a| ≤ R) : 0 ≤ (1 - (a / R) ^ 12) ^ 2 ∧ (1 - (a / R) ^ 12) ^ 2 ≤ 1 := by
  have hx0 : 0 ≤ (a / R) ^ 12 := by positivity
  have hx1 : (a / R) ^ 12 ≤ 1 := by
    have h1 : |a / R| ≤ 1 := by rw [abs_div, abs_of_pos hR, div_le_one hR]; exact ha
    rw [← Even.pow_abs (by decide : Even 12)]
    exact pow_le_one₀ (abs_nonneg _) h1
  constructor
  · positivity
  · nlinarith

/-- `W₆(a) ≥ 1/4` for `|a| ≤ 5/2`, `R ≥ 4`. -/
lemma W6_first {a R : ℝ} (hR : 4 ≤ R) (ha : |a| ≤ 5 / 2) : 1 / 4 ≤ (1 - (a / R) ^ 12) ^ 2 := by
  have hR0 : 0 < R := by linarith
  have h1 : |a / R| ≤ 5 / 8 := by
    rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]; nlinarith [abs_nonneg a]
  have h2 : (a / R) ^ 12 ≤ (5 / 8) ^ 12 := by
    rw [← Even.pow_abs (by decide : Even 12)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 12
  have h3 : (5 / 8 : ℝ) ^ 12 ≤ 1 / 2 := by norm_num
  nlinarith

/-- `r_∞ = 2 I c^{1/3} e^{-c/40000} ≤ 2|I| c^{1/3} e^{-c/40000}`. -/
lemma hankelRinf_le (c : ℝ) (hc0 : 0 < c) :
    hankelRinf c ≤ 2 * |hankelTailI0| * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000)) := by
  have h1 : 0 ≤ c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000)) := by positivity
  calc hankelRinf c = (2 * hankelTailI0) * (c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000))) := by unfold hankelRinf; ring
    _ ≤ (2 * |hankelTailI0|) * (c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000))) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self hankelTailI0]) h1
    _ = _ := by ring

/-- The exponentially small error: `(2r/c₀)(c + 2) ≤ (12|I|/c₀) e^{-c/80000}` when `r ≤ 2|I| c^{1/3} e^{-c/40000}` and
`c^{4/3} e^{-c/80000} ≤ 1`. -/
lemma node_err_small {c r I c0 : ℝ} (hc : 1 ≤ c) (_hr0 : 0 ≤ r)
    (hr : r ≤ 2 * |I| * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000)))
    (hsm : c ^ (4 / 3 : ℝ) * Real.exp (-(1 / 80000 : ℝ) * c) ≤ 1) (hc0 : 0 < c0) :
    2 * r / c0 * (c + 2) ≤ (12 * |I| / c0) * Real.exp (-(1 / 80000 : ℝ) * c) := by
  have hc0' : 0 < c := by linarith
  have hp43 : c ^ (1 / 3 : ℝ) * c = c ^ (4 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.rpow_add hc0', Real.rpow_one]
  have hexp : Real.exp (-(c / 40000)) = Real.exp (-(1 / 80000 : ℝ) * c) * Real.exp (-(1 / 80000 : ℝ) * c) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE0 := Real.exp_pos (-(1 / 80000 : ℝ) * c)
  have hX : 0 ≤ 2 * |I| * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000)) := by positivity
  have h2 : 2 * r * (c + 2) ≤ 2 * (2 * |I| * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000))) * (3 * c) := by
    have h3 : r * (c + 2) ≤ (2 * |I| * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000))) * (3 * c) :=
      mul_le_mul hr (by linarith) (by linarith) hX
    linarith
  have h4 : 2 * (2 * |I| * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000))) * (3 * c) =
      12 * |I| * ((c ^ (4 / 3 : ℝ) * Real.exp (-(1 / 80000 : ℝ) * c)) * Real.exp (-(1 / 80000 : ℝ) * c)) := by
    rw [← hp43, hexp]; ring
  have h5 : (c ^ (4 / 3 : ℝ) * Real.exp (-(1 / 80000 : ℝ) * c)) * Real.exp (-(1 / 80000 : ℝ) * c) ≤
      Real.exp (-(1 / 80000 : ℝ) * c) := by
    calc _ ≤ 1 * Real.exp (-(1 / 80000 : ℝ) * c) := mul_le_mul_of_nonneg_right hsm hE0.le
      _ = _ := one_mul _
  have h6 : 2 * r * (c + 2) ≤ 12 * |I| * Real.exp (-(1 / 80000 : ℝ) * c) := by
    have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 12 * |I|)
    linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc0]
  linarith

set_option maxHeartbeats 800000 in
/-- **The node lower bound for one `ε`** (`thm:ct-lower`, proof, second half): there are `γ, κ > 0` such that for every
`0 < c₁ ≤ γ`, all large `c`, every feasible `f` with `M[f] = 1`, violator `T < cξ(a₁)`, gap `ũ₁ > φ_c(a₁)` and every radius `R`
of the window `[c₁²c^{2/3}, 4c₁²c^{2/3}]`: `κ (ũ₁ - φ_c(a₁)) ≤ P_R(H) + g_vac/2π + C' e^{-c/80000}`. -/
theorem ctNodeLower_eps {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ → ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
      ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
        T < c * hankelXi c (airyZero 1) → 0 < ctGap ε c T →
        ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
          κ * ctGap ε c T ≤
            ctBudget R ε c f + (12 * |hankelTailI0| / bwn_c0 ^ 2) * Real.exp (-(1 / 80000 : ℝ) * c) := by
  obtain ⟨ρ, M, hρ, hM0, hwin⟩ := ctPsi_window hε
  have hW : PsiWin ε ρ M := ⟨hρ, hM0, hwin⟩
  obtain ⟨c6, hc6, hq⟩ := hankel_quantC1_of_feasible
  obtain ⟨C5, c5, hc5, hnode⟩ := ctNode_expansion hε
  obtain ⟨ce, hce⟩ := rpow_exp_small
  have hc0pos : 0 < bwn_c0 ^ 2 := pow_pos bwn_c0_pos 2
  have hκs := quantC1KappaStar_pos
  have hQpos : 0 < airyAi' (airyZero 1) ^ 2 := lt_of_lt_of_le hc0pos (airyZero_deriv_sq_ge 1)
  have hLamL : 0 < langerKappa * 4.94e-4 := by have := langerKappa_pos; positivity
  refine ⟨min (1 / 2) (min (ρ / 16) (langerKappa * 4.94e-4 / 2)),
    quantC1KappaStar / (3 * airyAi' (airyZero 1) ^ 2), lt_min (by norm_num) (lt_min (by positivity) (by positivity)),
    by positivity, fun c₁ hc₁ hγ => ?_⟩
  have hγ1 : c₁ ≤ 1 / 2 := hγ.trans (min_le_left _ _)
  have hγ2 : c₁ ≤ ρ / 16 := hγ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ3 : c₁ ≤ langerKappa * 4.94e-4 / 2 := hγ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsq1 : c₁ ^ 2 ≤ c₁ / 2 := by nlinarith
  have h8ρ : 8 * c₁ ^ 2 < ρ := by nlinarith
  have h4A : 4 * c₁ ^ 2 ≤ langerKappa * 4.94e-4 := by nlinarith
  have h41 : 4 * c₁ ^ 2 ≤ 1 := by nlinarith
  refine ⟨max (max (max c6 c5) (max ce 5000)) (max ((2 * M + 1) ^ 3) (max ((4 / c₁ ^ 2) ^ (3 / 2 : ℝ)) 3e6)), ?_⟩
  intro c hc T f hf hM hT hgap R hR
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨hc6', hc5'⟩, hce', hc5000⟩, hcM3, hcR4, hc3e6⟩ := hc
  have hc0 : 0 < c := by linarith
  -- window facts
  have hk := rpow_third_ge' hM0 hcM3
  have hlam : ctLam c * M ≤ 1 / 2 := by
    have h1 : ctLam c ≤ (c ^ (1 / 3 : ℝ))⁻¹ := by
      have := ctLam_le_rpow_neg hc0; rwa [Real.rpow_neg hc0.le] at this
    have hpos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    calc ctLam c * M ≤ (c ^ (1 / 3 : ℝ))⁻¹ * M := mul_le_mul_of_nonneg_right h1 hM0
      _ ≤ 1 / 2 := by rw [inv_mul_le_iff₀ hpos]; linarith
  have hcM : 2 * M ≤ c := by
    have : 2 * M + 1 ≤ (2 * M + 1) ^ 3 := by
      calc 2 * M + 1 = (2 * M + 1) ^ 1 := (pow_one _).symm
        _ ≤ (2 * M + 1) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hRr : R ≤ ctRmax c₁ c := hR.2
  have hμR : ∀ x : ℝ, -R ≤ x → -ρ < ctMu c * x := fun x hx => by
    have hmu := ctMu_pos hc0
    have h1 := ctMu_mul_ctRmax_le (c₁ := c₁) hc0
    have h3 : ctMu c * (-R) ≤ ctMu c * x := mul_le_mul_of_nonneg_left hx hmu.le
    have h2 : ctMu c * R ≤ ctMu c * ctRmax c₁ c := mul_le_mul_of_nonneg_left hRr hmu.le
    have h4 : ctMu c * (-R) = -(ctMu c * R) := by ring
    linarith
  have hR4 : 4 ≤ R := by
    have h1 := Real.rpow_le_rpow (by positivity) hcR4 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have e : ((4 / c₁ ^ 2) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = 4 / c₁ ^ 2 := by
      rw [← Real.rpow_mul (by positivity)]; norm_num
    rw [e] at h1
    have hc1 : 0 < c₁ ^ 2 := by positivity
    have : 4 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
      calc 4 = c₁ ^ 2 * (4 / c₁ ^ 2) := by field_simp
        _ ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left h1 hc1.le
    linarith [hR.1]
  have hR0 : 0 < R := by linarith
  have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hRA : R ≤ langerRadius c := by
    calc R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) := hR.2
      _ ≤ (langerKappa * 4.94e-4) * c ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_right h4A h23.le
      _ = langerRadius c := by unfold langerRadius langerScale; ring
  have hR32 : R ^ (3 / 2 : ℝ) ≤ c := by
    have h1 : R ≤ c ^ (2 / 3 : ℝ) := by nlinarith [hR.2]
    have := Real.rpow_le_rpow hR0.le h1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rwa [← Real.rpow_mul hc0.le, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at this
  have hA4 : 4 ≤ langerRadius c := hR4.trans hRA
  -- the Hankel side
  obtain ⟨u_T, ha1, huA, hcT, hB2⟩ := hq c ε T f hc6' hf hε hM hT
  obtain ⟨huT0, huT3⟩ := hankelBoot_uT_range ha1 hB2
  have hũ : ctUtilde c T = u_T := ctUtilde_eq hc0 (by linarith) ⟨huT3, huT0⟩ hcT
  obtain ⟨⟨φ, hφ, hφe⟩, -⟩ := hnode c hc5'
  have hφex : ∃ φ ∈ Icc (-3 : ℝ) (-2), ctUhat ε c φ = airyZero 1 := ⟨φ, hφ, hφe⟩
  have hφspec := Function.invFunOn_pos hφex
  set φ₁ := Function.invFunOn (ctUhat ε c) (Icc (-3 : ℝ) (-2)) (airyZero 1) with hφ₁
  have hφ₁1 : -3 ≤ φ₁ ∧ φ₁ ≤ -2 := hφspec.1
  have hφ₁e : ctUhat ε c φ₁ = airyZero 1 := hφspec.2
  have hgapd : ctGap ε c T = u_T - φ₁ := by rw [← hũ]; rfl
  have hφ₁w : -ρ < ctMu c * φ₁ := hμR φ₁ (by linarith [hφ₁1.1])
  have ha1v := airyZero_one
  have hφ₁lt : airyZero 1 < φ₁ := by
    have := ctUhat_lt hW hc0 (u := φ₁) (by linarith [hφ₁1.2]) hφ₁w
    rwa [hφ₁e] at this
  have hφT : φ₁ < u_T := by rw [hgapd] at hgap; linarith
  -- the first node
  have ha1w : -ρ < ctMu c * airyZero 1 := hμR _ (by linarith [ha1v.1])
  have hφa1 : ctPhi ε c (airyZero 1) = φ₁ := by
    have hRw : -ρ < ctMu c * (-(-airyZero 1)) := by rw [neg_neg]; exact ha1w
    have := ctPhi_eq hW hc0 hcM (R := -airyZero 1) (u := φ₁) hRw
      (by rw [neg_neg]; exact ⟨hφ₁lt.le, by linarith [hφ₁1.2]⟩) (by rw [neg_neg]; exact hφ₁e)
    rwa [neg_neg] at this
  obtain ⟨u₁, hu₁, hu₁v, hu₁φ, hd₁, hb₁, hb₂⟩ :=
    ctPhi_hasDerivAt hW hc0 hcM hlam (a := airyZero 1) (by linarith [ha1v.2]) ha1w
  have hu₁eq : u₁ = φ₁ := by rw [← hu₁φ, hφa1]
  subst hu₁eq
  obtain ⟨hg1l, hg1u⟩ := inv_bounds hb₁ hb₂
  have hr0 : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5000 hf.toIsHankelEigenfn hε hM
  set r := hankelRinf c with hrdef
  -- `Ψ̃` at `u_T` and at `φ₁`
  have huTA : |u_T| ≤ langerRadius c := abs_le.2 ⟨by linarith, by linarith⟩
  have hPT : -r ≤ hankelPsiR c f u_T := hankel_psi_sign hc5000 hf hε hM huTA (by rw [hcT])
  have hslope := hankelPsiR_slope (by linarith : 0 < c) hf.toIsHankelEigenfn hB2 hφ₁lt.le hφT.le
    (by have := ha1v.1; rw [abs_of_neg (by linarith [ha1v.2])]; linarith)
  have hQ1 : bwn_c0 ^ 2 ≤ airyAi' (airyZero 1) ^ 2 := airyZero_deriv_sq_ge 1
  have hW1 := W6_first (a := airyZero 1) (R := R) hR4 (by rw [abs_of_neg (by linarith [ha1v.2])]; linarith [ha1v.1])
  have hW1' := (W6_bounds (a := airyZero 1) hR0 (by rw [abs_of_neg (by linarith [ha1v.2])]; linarith [ha1v.1])).2
  set t : ℕ → ℝ := fun n => if -R < airyZero (n + 1) then
      ctH R ε c f (airyZero (n + 1)) / (deriv airyAi (airyZero (n + 1))) ^ 2 else 0 with ht
  have hbud : ctBudget R ε c f = (∑' n, t n) - ε * f 0 := rfl
  have ht0 : t 0 = (1 - (airyZero 1 / R) ^ 12) ^ 2 * (hankelPsiR c f φ₁ * (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * φ₁))⁻¹) /
      airyAi' (airyZero 1) ^ 2 := by
    have hlt1 : -R < airyZero 1 := by linarith [ha1v.1]
    simp only [ht, zero_add, hlt1, ↓reduceIte]
    rw [deriv_airyAi]
    unfold ctH ctFc
    rw [hφa1, hd₁.deriv]
  have hfirst : quantC1KappaStar * (u_T - φ₁) / (3 * airyAi' (airyZero 1) ^ 2) - 2 * r / bwn_c0 ^ 2 ≤ t 0 := by
    rw [ht0]
    exact node_term_first hW1 hW1' hg1l hg1u (by linarith) hr0 hκs.le (by linarith) hc0pos hQ1
  have hn : ∀ n : ℕ, 1 ≤ n → -(2 * r / bwn_c0 ^ 2) ≤ t n := by
    intro n hn1
    simp only [ht]
    split_ifs with hlt
    · have han : airyZero (n + 1) < airyZero 1 := airyZero_lt_of_lt (le_refl 1) (by omega)
      set a := airyZero (n + 1) with hadef
      have haw : -ρ < ctMu c * a := hμR a hlt.le
      obtain ⟨u, hu, huv, huφ, hdu, hb1, hb2⟩ := ctPhi_hasDerivAt hW hc0 hcM hlam (a := a) (by linarith [ha1v.2]) haw
      have huφ₁ : u ≤ φ₁ := by
        by_contra hcon
        rw [not_le] at hcon
        have := ctUhat_mono_window hW hc0 hcM hcon.le (by linarith [hu.2]) hφ₁w
        rw [hφ₁e, huv] at this
        linarith
      have hxu : |u| ≤ langerRadius c := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hTu : T ≤ c * hankelXi c u := by
        have := hankel_phi_anti hc0 hxu huTA (by linarith)
        rw [hcT] at this; exact this
      have hP := hankel_psi_sign hc5000 hf hε hM hxu hTu
      obtain ⟨hgl, hgu⟩ := inv_bounds hb1 hb2
      have hWb := W6_bounds (a := a) hR0 (abs_le.2 ⟨by linarith [hlt], by linarith [hu.2, hlt]⟩)
      have e : ctH R ε c f a / (deriv airyAi a) ^ 2 =
          (1 - (a / R) ^ 12) ^ 2 * (hankelPsiR c f u * (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u))⁻¹) / airyAi' a ^ 2 := by
        rw [deriv_airyAi]; unfold ctH ctFc; rw [huφ, hdu.deriv]
      rw [e]
      exact node_term_ge hWb.1 hWb.2 hgl hgu hP hr0 hc0pos (airyZero_deriv_sq_ge (n + 1))
    · have : 0 ≤ 2 * r / bwn_c0 ^ 2 := div_nonneg (by linarith) hc0pos.le
      linarith
  have h0 : ∀ n : ℕ, airyZero (n + 1) ≤ -R → t n = 0 := fun n h => by
    have hnl : ¬ -R < airyZero (n + 1) := not_lt.2 h
    simp only [ht, hnl, ↓reduceIte]
  have hsum := tsum_nodes_lower (R := R) (D := 2 * r / bwn_c0 ^ 2) hR0.le
    (div_nonneg (by linarith) hc0pos.le) h0 hn
  have hf0 : ε * f 0 ≤ 0 := hf.origin_sign
  -- the exponentially small error
  have hdef := node_err_small (c := c) (r := r) (c0 := bwn_c0 ^ 2) (I := hankelTailI0) (by linarith) hr0
    (hankelRinf_le c hc0) (hce c hce') hc0pos
  have hsum2 : (∑' n, t n) ≥ t 0 - 2 * r / bwn_c0 ^ 2 * (c + 1) := by
    have : 2 * r / bwn_c0 ^ 2 * (R ^ (3 / 2 : ℝ) + 1) ≤ 2 * r / bwn_c0 ^ 2 * (c + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) hc0pos.le)
    linarith
  have hkap : quantC1KappaStar / (3 * airyAi' (airyZero 1) ^ 2) * ctGap ε c T =
      quantC1KappaStar * (u_T - φ₁) / (3 * airyAi' (airyZero 1) ^ 2) := by
    rw [hgapd]; ring
  have hd2 : 2 * r / bwn_c0 ^ 2 * (c + 2) = 2 * r / bwn_c0 ^ 2 + 2 * r / bwn_c0 ^ 2 * (c + 1) := by ring
  rw [hkap, hbud]
  linarith

/-- **The node lower bound** (`thm:ct-lower`, proof, second half: `g_vac ≥ 0`, the sign of the `n ≥ 2` nodes `gt:7.7p` (b), and the effective
`C¹` stability at the first node `gt:7.7p` (d)): for every small window constant `c₁`, `CtNodeLowerStatement c₁`.  Proved: from
`ctNodeLower_eps` for `ε = ±1`. -/
theorem ct_node_lower : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtNodeLowerStatement c₁ := by
  obtain ⟨γ₁, κ₁, hγ₁, hκ₁, h₁⟩ := ctNodeLower_eps (Or.inl rfl)
  obtain ⟨γ₂, κ₂, hγ₂, hκ₂, h₂⟩ := ctNodeLower_eps (Or.inr rfl)
  refine ⟨min γ₁ γ₂, lt_min hγ₁ hγ₂, fun c₁ hc₁ hle => ?_⟩
  obtain ⟨c₀₁, hc₀₁⟩ := h₁ c₁ hc₁ (hle.trans (min_le_left _ _))
  obtain ⟨c₀₂, hc₀₂⟩ := h₂ c₁ hc₁ (hle.trans (min_le_right _ _))
  refine ⟨min κ₁ κ₂, 1 / 80000, 12 * |hankelTailI0| / bwn_c0 ^ 2, max c₀₁ c₀₂, lt_min hκ₁ hκ₂, by norm_num, ?_⟩
  intro c hc ε hε T f hf hM hT hgap R hR
  have e : (-(1 / 80000 : ℝ)) * c = -(1 / 80000 : ℝ) * c := by ring
  rw [e]
  rcases hε with rfl | rfl
  · have := hc₀₁ c ((le_max_left _ _).trans hc) T f hf hM hT hgap R hR
    have h2 : min κ₁ κ₂ * ctGap 1 c T ≤ κ₁ * ctGap 1 c T := mul_le_mul_of_nonneg_right (min_le_left _ _) hgap.le
    linarith
  · have := hc₀₂ c ((le_max_right _ _).trans hc) T f hf hM hT hgap R hR
    have h2 : min κ₁ κ₂ * ctGap (-1) c T ≤ κ₂ * ctGap (-1) c T := mul_le_mul_of_nonneg_right (min_le_right _ _) hgap.le
    linarith

/-- info: 'FormalResearch.SignUncertainty.ctNodeLower_eps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctNodeLower_eps

/-- info: 'FormalResearch.SignUncertainty.ct_node_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_node_lower

end FormalResearch.SignUncertainty
