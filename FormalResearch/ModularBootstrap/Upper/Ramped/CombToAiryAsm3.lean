module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryAsm2

/-!
# The window limit of a comb design: Steps 1, 4 of Proposition 1.2(2) (`rem:P1.2`)

`pBracket_tendsto`: `P_K → L`.  `abs_windowFiniteProd`: `|M_K(σ)| = exp(P_K - 2πσ_-^{3/2})`.  `window_tendsto`:
`M_K(σ) → W̃(σ)` for a design (Lemma W with `f = N = 1`; the tail bounds hold for all `k ≥ 2`).
`abs_tildeW_eq`: `|W̃(σ)| = exp(L - 2πσ_-^{3/2}) > 0`.  Lemma ID (`tildeW_design`) identifies
`W̃(σ) = C_* κ Re W_D(-κσ)`.
-/

@[expose] public section

open Filter Topology Set Finset MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Window

/-- The Airy product of the design: sites `u_k = -κ σ_k`, heights `κ ε̂_k`, first site `-κ σ_1`. -/
noncomputable def designAiryW (σ η : ℕ → ℝ) (u : ℝ) : ℂ :=
  airyWindowProd 1 (-kappaAiry * σ 1) (fun k => -kappaAiry * σ k) (fun k => kappaAiry * epsHat η k)
    (u : ℂ)

lemma sigmaOf_sub_ne {c' : ℝ} (hc' : 0 < c') {σ : ℕ → ℝ} {k : ℕ} (hσk : 0 ≤ σ k) {x : ℝ}
    (hxpos : 0 < x) (hxy : x ≠ siteX c' σ k) : sigmaOf c' x - σ k ≠ 0 := by
  have hy : 0 < siteX c' σ k := lt_of_lt_of_le xiStar_pos (xiStar_le_siteX hc' hσk)
  intro h0
  have hD : langerTau x - langerTau (siteX c' σ k) = lambdaComb c' * (sigmaOf c' x - σ k) := by
    rw [langerTau_eq_lam_sigmaOf hc' x, langerTau_siteX hc' hσk]; ring
  have : langerTau x = langerTau (siteX c' σ k) := by
    have := hD; rw [h0, mul_zero] at this; linarith
  exact hxy (langerTau_strictMonoOn.injOn (Set.mem_Ioi.2 hxpos) (Set.mem_Ioi.2 hy) this)

lemma design_tail {Csh csep : ℝ} {σ η : ℕ → ℝ} (h : CombDesignHyp Csh csep σ η) :
    ∀ k : ℕ, 1 < k → |σ k - phiWKB k| ≤ max |Csh| 1 * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
      |epsHat η k| ≤ max |Csh| 1 * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  intro k hk
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkp : (0 : ℝ) < (k : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hkp' : (0 : ℝ) < (k : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  constructor
  · have := h.near k hk1
    have hphi : phiWKB k = phiQuantile (k : ℝ) := rfl
    rw [hphi]
    refine this.trans ?_
    calc Csh * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ |Csh| * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
          gcongr; exact le_abs_self _
      _ ≤ max |Csh| 1 * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by gcongr; exact le_max_left _ _
  · obtain ⟨hp0, hp1⟩ := phi_diff_bounds hk1
    obtain ⟨hη0, hη1⟩ := h.height k hk
    have h1 : epsHat η k ≤ 1 * cr k := by
      have := mul_le_mul hη1 hp1 hp0 (by norm_num)
      unfold epsHat; linarith
    have h2 : 0 ≤ epsHat η k := mul_nonneg hη0 hp0
    rw [abs_of_nonneg h2]
    have hcr : cr k = (k : ℝ) ^ (-(1 / 3 : ℝ)) := rfl
    calc epsHat η k ≤ 1 * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [← hcr]; exact h1
      _ ≤ max |Csh| 1 * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by gcongr; exact le_max_right _ _

/-- Lemma W for a design: the window approximants converge to `W̃(σ)`. -/
theorem window_tendsto {Csh csep : ℝ} {σ η : ℕ → ℝ} (h : CombDesignHyp Csh csep σ η) (s : ℝ) :
    Tendsto (fun K : ℕ => windowFiniteProd 1 (σ 1) σ (epsHat η) K s) atTop
      (𝓝 (tildeW 1 (σ 1) σ (epsHat η) s)) := by
  have hM : 0 < |σ 1| + 1 := by positivity
  have hCt : 0 < max |Csh| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨K_min, C, -, -, -, H⟩ := tendsto_windowFiniteProd_uniform 1 1 le_rfl le_rfl hM hCt
    (abs_nonneg s)
  have hH := H (σf := σ 1) (σSeq := σ) (εHat := epsHat η) (by linarith)
    (fun k hk => by simp at hk) (design_tail h)
  have hb : Tendsto (fun K : ℕ => C / (K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  refine tendsto_sub_nhds_zero_iff.1 ?_
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop K_min] with K hK
  rw [Real.norm_eq_abs]
  exact hH.2 hK (by rw [Set.mem_Icc]; constructor <;> linarith [neg_abs_le s, le_abs_self s])

/-- Lemma ID for a design: `W̃(σ) = C_* κ Re W_D(-κσ)`. -/
theorem tildeW_design {Csh csep : ℝ} {σ η : ℕ → ℝ} (h : CombDesignHyp Csh csep σ η) (s : ℝ) :
    tildeW 1 (σ 1) σ (epsHat η) s =
      CStar * kappaAiry * (designAiryW σ η (-kappaAiry * s)).re := by
  have hM : 0 < |σ 1| + 1 := by positivity
  have hCt : 0 < max |Csh| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have := lemma_ID 1 1 le_rfl le_rfl hM hCt (σf := σ 1) (σSeq := σ) (εHat := epsHat η)
    (by linarith) (fun k hk => by simp at hk) (design_tail h) s
  rw [this, CStarF_one]
  rfl

lemma designAiryW_im {Csh csep : ℝ} {σ η : ℕ → ℝ} (h : CombDesignHyp Csh csep σ η) (u : ℝ) :
    (designAiryW σ η u).im = 0 := by
  have hCt : 0 < max |Csh| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  exact airyWindowProd_im_eq_zero 1 _ _ _
    (airyProdTailHypothesis_of_tail (f := 1) (N := 1) le_rfl hCt (design_tail h)) u

/-- `|M_K(σ)| = exp(P_K - 2πσ_-^{3/2})`. -/
theorem abs_windowFiniteProd {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ} {Csh csep : ℝ}
    (h : CombDesignHyp Csh csep σ η) {x : ℝ} (hxpos : 0 < x)
    (hxk : ∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k) (K : ℕ) :
    |windowFiniteProd 1 (σ 1) σ (epsHat η) K (sigmaOf c' x)| =
      Real.exp (pBracket c' σ η x K - 2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ)) := by
  have hpos : ∀ k ∈ Finset.Icc 2 K, 0 < (sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2 := fun k hk => by
    have hk2 := (Finset.mem_Icc.1 hk).1
    have := sigmaOf_sub_ne hc' (h.nonneg k (by omega)) hxpos (hxk k (by omega))
    positivity
  have hΔ1 : 0 < |sigmaOf c' x - σ 1| :=
    abs_pos.2 (sigmaOf_sub_ne hc' (h.nonneg 1 le_rfl) hxpos (hxk 1 le_rfl))
  have hP : Real.exp (∑ k ∈ Finset.Icc 2 K, Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2)) =
      ∏ k ∈ Finset.Icc 2 K, ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun k hk => Real.exp_log (hpos k hk)
  have hP0 : 0 ≤ ∏ k ∈ Finset.Icc 2 K, ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) :=
    Finset.prod_nonneg fun k hk => (hpos k hk).le
  have e : pBracket c' σ η x K - 2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ) =
      Real.log |sigmaOf c' x - σ 1| +
        ∑ k ∈ Finset.Icc 2 K, Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) +
        (continuumFQ (continuumAK K) (sigmaOf c' x) -
          2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ)) := by
    unfold pBracket; ring
  rw [e, Real.exp_add, Real.exp_add, Real.exp_log hΔ1, hP]
  unfold windowFiniteProd
  show |Real.exp _ * (sigmaOf c' x - σ 1) * ∏ k ∈ Finset.Icc 2 K, _| = _
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hP0]
  ring

/-- `P_K → L = (log‖B_D‖ - c'U) + (3/2) log λ - S - T`. -/
theorem pBracket_tendsto {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) {x : ℝ} (hx : x ∈ langerX (1 / 2))
    (hxk : ∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k)
    (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) {S T : ℝ}
    (hsm : Tendsto (fun n : ℕ => smPartial c' σ x (n + 1)) atTop (𝓝 S))
    (hΞ : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 2 (n + 1), xiPair c' σ η x k) atTop (𝓝 T)) :
    Tendsto (fun n : ℕ => pBracket c' σ η x (n + 1)) atTop
      (𝓝 (Real.log ‖combBD c' σ η (x : ℂ)‖ - c' * majorantReal x +
        3 / 2 * Real.log (lambdaComb c') - S - T)) := by
  have hE := combEK_tendsto hc' h hx hxk hw
  have h3 := ((hE.add_const (3 / 2 * Real.log (lambdaComb c'))).sub hsm).sub hΞ
  refine h3.congr fun n => ?_
  have := combEK_eq hc' h hx hxk (n + 1) (by omega)
  linarith

/-- `|W̃(σ)| = exp(L - 2πσ_-^{3/2})`, in particular `W̃(σ) ≠ 0`. -/
theorem abs_tildeW_eq {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) {x : ℝ} (hx : x ∈ langerX (1 / 2))
    (hxk : ∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k)
    (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) {S T : ℝ}
    (hsm : Tendsto (fun n : ℕ => smPartial c' σ x (n + 1)) atTop (𝓝 S))
    (hΞ : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 2 (n + 1), xiPair c' σ η x k) atTop (𝓝 T)) :
    |tildeW 1 (σ 1) σ (epsHat η) (sigmaOf c' x)| =
      Real.exp (Real.log ‖combBD c' σ η (x : ℂ)‖ - c' * majorantReal x +
        3 / 2 * Real.log (lambdaComb c') - S - T -
          2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ)) := by
  have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
  have h1 := (pBracket_tendsto hc' h hx hxk hw hsm hΞ).sub_const
    (2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ))
  have h2 := ((Real.continuous_exp.tendsto _).comp h1)
  have h3 := ((window_tendsto h (sigmaOf c' x)).comp (tendsto_add_atTop_nat 1)).abs
  have h4 : (fun n : ℕ => |windowFiniteProd 1 (σ 1) σ (epsHat η) (n + 1) (sigmaOf c' x)|) =
      fun n : ℕ => Real.exp (pBracket c' σ η x (n + 1) -
        2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ)) := by
    funext n
    exact abs_windowFiniteProd hc' h hxpos hxk (n + 1)
  have h3' : Tendsto (fun n : ℕ => Real.exp (pBracket c' σ η x (n + 1) -
      2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ))) atTop
      (𝓝 |tildeW 1 (σ 1) σ (epsHat η) (sigmaOf c' x)|) := by
    rw [← h4]; exact h3
  exact tendsto_nhds_unique h3' h2

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.window_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_tendsto

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.tildeW_design' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tildeW_design

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.abs_tildeW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_tildeW_eq

end FormalResearch.ModularBootstrap.Upper.Ramped
