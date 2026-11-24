module

public import FormalResearch.SignUncertainty.HankelBootArc
public import FormalResearch.SignUncertainty.HankelBootLineAsm
public import FormalResearch.SignUncertainty.HankelBootNumerics
public import FormalResearch.SignUncertainty.HankelBootCircle
public import FormalResearch.SignUncertainty.HankelQuantC1Feasible
public import FormalResearch.TwoEdgeBootstrap.Bootstrap

/-!
# The Hankel `BootstrapHBInstance` (M5-S6a; `two_edge_bootstrap.tex` `teb:bootstrap`, `teb:mellin`)

`hankelBootParams`: the `BootstrapParams` of the Hankel lower half (`b = 1/100`, `k₀ = 9`, `C_α = (6π)²`, `κ = 1/600000`,
`C_a = max (virasoroArcCovConst) (4e^{6/5} + 180)`, `C_unc = hankelArcUncConst`, `C_L = 4 C_fb`, `γ = 1`), and
`hankelBootHB`: the `BootstrapHBInstance (hankelBootParams C_fb) 0` for `f` feasible at `T`, `M[f] = 1`, `cξ(u_T) = T`,
`T < cξ(a₁)` (through `QuantC1B2Holds`), at a good circle `R ∈ [b² c^{2/3}, b² c^{2/3} + 1]`, from the window hypothesis
`HankelYVAt C_fb c_YV` (the Hankel `TE.3(2)–(3)`, the content of S6b).  The core radius slack is the explicit
`r_inf = 70 · hankelRinf c`: `70 R r_∞` is the slack of `hankelBoot_line_bound`, and `(6π)²(N+1) r_∞ ≤ C_α R^{3/2} r_inf`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- The node-sum slack `(6π)²(N+1) r_∞` is at most `C_α R^{3/2} r_inf` with `C_α = (6π)²`, `r_inf = 70 r_∞`, using `N ≤ R^{3/2}`. -/
lemma hankelBoot_node_slack {N : ℕ} {R r : ℝ} (hr : 0 ≤ r) (hN : (N : ℝ) ≤ R ^ (3 / 2 : ℝ))
    (hR32 : 1 ≤ R ^ (3 / 2 : ℝ)) :
    (6 * π) ^ 2 * ((N : ℝ) + 1) * r ≤ (6 * π) ^ 2 * R ^ (3 / 2 : ℝ) * (70 * r) := by
  have h1 : ((N : ℝ) + 1) ≤ 70 * R ^ (3 / 2 : ℝ) := by linarith
  have h2 : 0 ≤ (6 * π) ^ 2 * r := by positivity
  calc (6 * π) ^ 2 * ((N : ℝ) + 1) * r = ((N : ℝ) + 1) * ((6 * π) ^ 2 * r) := by ring
    _ ≤ (70 * R ^ (3 / 2 : ℝ)) * ((6 * π) ^ 2 * r) := mul_le_mul_of_nonneg_right h1 h2
    _ = (6 * π) ^ 2 * R ^ (3 / 2 : ℝ) * (70 * r) := by ring

/-- Combination of the line bound with the constants of `hankelBootParams`. -/
lemma hankelBoot_line_combine {I B1k B2 Ca lobe E R r k c ek : ℝ}
    (hlb : I ≤ -(63 / 100 : ℝ) * B1k - B2 + (4 * Real.exp (6 / 5) + 180) * (k + 1) / R + lobe + 70 * R * r)
    (hca : (4 * Real.exp (6 / 5) + 180) * (k + 1) / R ≤ Ca * (k + 1) / R)
    (hlobe : lobe ≤ 16 * c * ek) (_hE : E = ek) :
    I ≤ -(63 / 100 : ℝ) * B1k - B2 + Ca * (k + 1) / R + R * (70 * r) + 16 * c * ek := by
  have : R * (70 * r) = 70 * R * r := by ring
  linarith

/-- Concrete `BootstrapParams` for the Hankel lower half. -/
noncomputable def hankelBootParams (C_fb : ℝ) (hC_fb : 1 ≤ C_fb) : BootstrapParams where
  b := 1 / 100
  C_a := max virasoroArcCovConst (4 * Real.exp (6 / 5) + 180)
  C_unc := hankelArcUncConst
  C_1 := quantC1C1
  w_star := quantC1WStar
  κ_star := quantC1KappaStar
  C_α := (6 * π) ^ 2
  C_fb := C_fb
  D_1 := 1
  η_0 := quantC1Eta0
  δ_star := quantC1DeltaStar
  κ := 1 / 600000
  C_0 := max 16 (140 * hankelTailI0)
  C_L := 4 * C_fb
  γ := 1
  k_0 := 9
  hb := by norm_num
  hCa := le_trans virasoroArcCovConst_pos.le (le_max_left _ _)
  hCunc := by unfold hankelArcUncConst; have := Real.pi_pos; positivity
  hC1 := quantC1C1_pos
  hw_star := quantC1WStar_pos
  hκ_star := quantC1KappaStar_pos
  hCα := by positivity
  hCfb := hC_fb
  hD1 := zero_le_one
  hη0 := quantC1Eta0_pos
  hδ_star := quantC1DeltaStar_pos
  hκ := by norm_num
  hC0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  hCL := by linarith
  hγ := zero_le_one
  hk0 := by norm_num

/-- The band-feedback hypothesis for the Hankel strip (`TE.3(2)–(3)`, `(B3)`, analogue of `YVInputAtForW`): for every feasible `f`
(`c ≥ c_YV`, `M[f] = 1`, `cξ(u_T) = T`, `u_T ∈ [-3, 0]`) the `YVEnvBound` at a radius `R ∈ [b² c^{2/3}, b² c^{2/3} + 1]` holds with
`L' = C_fb (c^{1/3}(B₁ + B₂) + 1)`.  **This is a hypothesis, not proved in this file**: it is the content of S6b (the window lemma
from `hankel_band_reduction`).  `hankelBootHB` assumes `c_YV ≤ c` and `3·10⁶ ≤ c` separately; a `c_YV < 3·10⁶` would only make this hypothesis stronger. -/
def HankelYVAt (C_fb c_YV : ℝ) : Prop :=
  ∀ ⦃c ε T u_T R : ℝ⦄ ⦃f : ℝ → ℝ⦄, c_YV ≤ c → IsHankelFeasible c ε T f → (ε = 1 ∨ ε = -1) →
    hankelMass c f = 1 → c * hankelXi c u_T = T → u_T ≤ 0 → -3 ≤ u_T →
    (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1 →
    YVEnvBound (hankelPsi c f) c R
      (C_fb * (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + 1))

/-- `u_T ∈ [-3, 0]` from `QuantC1B2Holds` and `a₁ < u_T`. -/
lemma hankelBoot_uT_range {Ψ : ℂ → ℂ} {u_T : ℝ} (ha1 : airyZero 1 < u_T) (hB2 : QuantC1B2Holds Ψ u_T) :
    u_T ≤ 0 ∧ -3 ≤ u_T := by
  have h1 : u_T - airyZero 1 ≤ 1 / 2 := hB2.1.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
  have := airyZero_one
  constructor <;> linarith [this.1, this.2]

set_option maxHeartbeats 1000000 in
/-- **The Hankel `BootstrapHBInstance`** (S6a), for `f` feasible at `T` with `M[f] = 1`, `cξ(u_T) = T`, `a₁ < u_T` and
`QuantC1B2Holds (hankelPsi c f) u_T`, at a good circle `R ∈ [b² c^{2/3}, b² c^{2/3} + 1]` chosen inside the proof
(`hankelBoot_good_circle_window`); the returned `L` is the feedback value `C_fb (c^{1/3}(B₁ + B₂) + 1)` and `c`, `x_tilde` are `c`,
`u_T - a₁`.  **Not covered here:** the window hypothesis `hYVat : HankelYVAt C_fb c_YV` (the Hankel `TE.3(2)–(3)`, to be proved in
S6b from `hankel_band_reduction`) is an explicit hypothesis, so this definition is only as non-vacuous as `HankelYVAt`;
likewise `hsmall : 4 r_c r_∞ ≤ 1` (true for large `c`, to be supplied from `r_∞ = O(c^{1/3} e^{-c/40000})`).  The core slack is the
explicit `r_inf = 70 r_∞`; no `r_∞` is dropped (`hankelBoot_line_bound`, `hankelBoot_nodes_lb`, `hankelBoot_node_slack`). -/
noncomputable def hankelBootHB {C_fb c_YV : ℝ} (hC_fb : 1 ≤ C_fb) (hYVat : HankelYVAt C_fb c_YV)
    {c ε T u_T : ℝ} {f : ℝ → ℝ} (hc_YV : c_YV ≤ c) (hc : 3e6 ≤ c) (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c)
    (h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (ha1 : airyZero 1 < u_T) (hB2 : QuantC1B2Holds (hankelPsi c f) u_T)
    (hsmall : 4 * langerRadius c * hankelRinf c ≤ 1) :
    let P := hankelBootParams C_fb hC_fb
    { I : BootstrapHBInstance P 0 //
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
      I.c = c ∧ I.x_tilde = u_T - airyZero 1 } := by
  intro P
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1 hB2
  set t : ℝ := (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) with ht
  have h_circ := hankelBoot_good_circle_window t (by linarith)
  let R : ℝ := Classical.choose h_circ
  have hR_spec := Classical.choose_spec h_circ
  have hR1 : t ≤ R := hR_spec.1
  have hR2 : R ≤ t + 1 := hR_spec.2.1
  have hR_low := hR_spec.2.2
  obtain ⟨hR48, hRA, hAR, hRc⟩ := hankelBoot_radius_facts hc h48 hR1 hR2
  have hR_pos : 0 < R := by linarith
  have hR10 : 10 ≤ R := by linarith
  have h_good_ai : ∀ u : ℂ, ‖u‖ = R → airyAiC u ≠ 0 := by
    intro u hu h0
    have h1 := hR_low u hu
    rw [h0, norm_zero] at h1
    have h2 : 0 < 1 / (25 * π) * (1 + R) ^ (-(1 / 2 : ℝ)) * airyEnv u := by
      have := airyEnv_pos u
      have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + R) (-(1 / 2 : ℝ))
      positivity
    linarith
  have hN_ex := airy_circleData hR_pos h_good_ai
  let N : ℕ := Classical.choose hN_ex
  have hN_spec := Classical.choose_spec hN_ex
  have hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R) := hN_spec.1
  have hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R := hN_spec.2
  have hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rplus_bound him (hw ▸ hR_low w hw)
  have hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rminus_bound him (hw ▸ hR_low w hw)
  have hRu : -R ≤ u_T := by linarith
  have hRA' : R ≤ langerRadius c := by linarith
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hsmall' : (2 * langerRadius c + 2 * R) * hankelRinf c ≤ 1 := by
    have : (2 * langerRadius c + 2 * R) * hankelRinf c ≤ 4 * langerRadius c * hankelRinf c :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    linarith
  have hB1_nn := hankelBootB1_nonneg hc hf hε hM hT hu0 hu3 hR_pos hRu hRA'
  have hB2_nn := hankelBootB2_nonneg c f R
  set B_1 := hankelBootB1 c f R u_T
  set B_2 := hankelBootB2 c f R
  have hB1_le2 : B_1 ≤ 2 :=
    (hankelBootB1_le_B1k hc hf hε hM hT hu0 hu3 hR_pos hRu hRA' 0).trans
      (hankelBootB1k_le_two hc hf hε hM hu0 hu3 hRu hRA' hR_pos hsmall' 0)
  have hB2_le1 : B_2 ≤ 1 := hankelBootB2_le_one hc0 hfe hM R
  set L := C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
  have hL_lb : 1 ≤ L := by
    have h1 : 1 ≤ c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 := by
      have : 0 ≤ c ^ (1 / 3 : ℝ) * (B_1 + B_2) :=
        mul_nonneg (Real.rpow_nonneg hc0.le _) (by linarith)
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) := mul_le_mul hC_fb h1 zero_le_one (by linarith)
  have hL_ub : L ≤ P.C_L * c ^ P.γ := by
    have hc13_le : c ^ (1 / 3 : ℝ) ≤ c := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have h1 : c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ 4 * c := by
      have hB3_le : B_1 + B_2 ≤ 3 := by linarith
      calc c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ c * 3 + c :=
          add_le_add (mul_le_mul hc13_le hB3_le (by linarith) hc0.le) hc1
        _ = 4 * c := by ring
    show C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) ≤ 4 * C_fb * c ^ (1 : ℝ)
    rw [Real.rpow_one]
    calc C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) ≤ C_fb * (4 * c) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 4 * C_fb * c := by ring
  have hYV : YVEnvBound (hankelPsi c f) c R L := hYVat hc_YV hf hε hM hT hu0 hu3 hR1 hR2
  have hlobe := hankelBoot_lobe_le hc1
  have hrinf := hankelBoot_rinf_le hc0
  have hNle := hankelBoot_zero_count_le hR_pos hN
  have hR32 : 1 ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  refine ⟨{
    c := c
    R := R
    a := √R
    B_1 := B_1
    B_2 := B_2
    L := L
    x_tilde := u_T - airyZero 1
    r_inf := 70 * hankelRinf c
    C_err := 16
    hc := by linarith
    ha_lb := by
      calc P.b * c ^ (1 / 3 : ℝ) = √(P.b ^ 2 * c ^ (2 / 3 : ℝ)) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq P.hb.le,
              show c ^ (2 / 3 : ℝ) = (c ^ (1 / 3 : ℝ)) ^ 2 by
                rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le]; norm_num,
              Real.sqrt_sq (Real.rpow_nonneg hc0.le _)]
        _ ≤ √R := Real.sqrt_le_sqrt hR1
    ha_sq := Real.sq_sqrt hR_pos.le
    hR_ub := by
      have : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by positivity
      show R ≤ 2 * (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1
      linarith
    hB1 := hB1_nn
    hB2 := hB2_nn
    hL_lb := hL_lb
    hL_ub := hL_ub
    hx_pos := by linarith
    hx_ub := hB2.1
    hr_inf_nn := by linarith
    hr_inf_ub := by
      show 70 * hankelRinf c ≤ max 16 (140 * hankelTailI0) * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 600000 : ℝ) * c)
      refine hrinf.trans ?_
      have h1 : 140 * hankelTailI0 ≤ max 16 (140 * hankelTailI0) := le_max_right _ _
      have h2 : 0 ≤ c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 600000 : ℝ) * c) :=
        mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.exp_pos _).le
      nlinarith
    hC_err_nn := by norm_num
    hC_err_ub := le_max_left _ _
    B_1k := fun k => hankelBootB1k c f R u_T k
    B_2' := fun _ => B_2
    P_nodes := fun k ℓ => hankelBootNodes c f R ℓ k N
    I_line := fun k ℓ => ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re
    Arc_cov := fun k ℓ => virasoroArcCov c R 0 L ℓ (fun _ => 0) k
    Arc_unc := hankelArcUncConst * c ^ (-(3 / 8 : ℝ))
    hB1k_nn := fun k _ _ => hankelBootB1k_nonneg hc hf hε hM hT hu0 hu3 hR_pos hRu hRA' k
    hB2'_nn := fun _ _ _ => hB2_nn
    hB_sum := fun k _ _ => by
      have := hankelBootB1_le_B1k hc hf hε hM hT hu0 hu3 hR_pos hRu hRA' k
      show B_1 + B_2 ≤ hankelBootB1k c f R u_T k + B_2
      linarith
    hP_le := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      exact hankelBoot_quad_arc hc hfe hε hM h_c12 hR10 hRA hRc (by linarith) hℓ_nn hℓ_half hYV hD hRp hRm
        (show 9 ≤ k from hk0)
    hArc_cov := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_pos : 0 < ℓ := by
        have hpos : 0 < P.D_1 * c ^ (-(1 / 3 : ℝ)) := by
          have : P.D_1 = 1 := rfl
          rw [this]; positivity
        exact lt_of_lt_of_le hpos hℓ_mem.1
      have hle := virasoroArcCov_le (c' := c) (T := 0) hR10 (zero_le_one.trans hL_lb) hℓ_pos
        (fun _ => (0 : ℝ)) (k := k) (by have : 9 ≤ k := hk0; omega)
      have hCa : virasoroArcCovConst ≤ P.C_a := le_max_left _ _
      refine hle.trans ?_
      gcongr
    hArc_unc := le_rfl
    hI_line := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      have hk9 : 9 ≤ k := hk0
      have hlb := hankelBoot_line_bound hc hf hε hM hT hu0 hu3 hR10 hRA hAR hℓ_nn hℓ_half
        (k := k) (by omega) hkR
      have hCa : 4 * Real.exp (6 / 5) + 180 ≤ P.C_a := le_max_right _ _
      have h_ca_term : (4 * Real.exp (6 / 5) + 180) * ((k : ℝ) + 1) / R ≤
          P.C_a * ((k : ℝ) + 1) / R := by gcongr
      have h_lobe : hankelLobe c ≤ 16 * c * Real.exp (-P.κ * c) := by
        have hκ : P.κ = 1 / 600000 := rfl
        rw [hκ]; linarith [hlobe]
      show ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re ≤
        -(63 / 100 : ℝ) * hankelBootB1k c f R u_T k - B_2 + P.C_a * ((k : ℝ) + 1) / R +
          R * (70 * hankelRinf c) + 16 * c * Real.exp (-P.κ * c)
      exact hankelBoot_line_combine hlb h_ca_term h_lobe rfl
    hW_top := le_rfl
    hP_nodes_lb_hb := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_mem.1
      have hℓ_le : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1) := hℓ_mem.2
      have hnb := hankelBoot_nodes_lb hc hf hε hM hT ha1 hB2 hu0 hu3 hR48 hRA hN hℓ_nn hℓ_le hkR
      show -tebLambdaN P 0 * ℓ - (6 * π) ^ 2 * R ^ (3 / 2 : ℝ) * (70 * hankelRinf c) ≤
        hankelBootNodes c f R ℓ k N
      have hΛ : tebLambdaN P 0 = 2 * quantC1C1 * (1 / quantC1WStar) := by
        unfold tebLambdaN
        show 2 * quantC1C1 * (1 / quantC1WStar + 0) = _
        rw [add_zero]
      have hslack := hankelBoot_node_slack hr hNle hR32
      rw [hΛ]
      linarith
    P_theta_bound := fun hk0_R hℓ_mem => by
      have hθ0 := tebThetaHB_pos P (le_refl (0 : ℝ))
      have hθ1 := tebThetaHB_le_half P 0
      have hℓ0 : 0 ≤ tebThetaHB P 0 * (u_T - airyZero 1) :=
        (mul_nonneg P.hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_mem.1
      have hnb := hankelBoot_nodes_theta hc hf hε hM hT ha1 hB2 hu0 hu3 hR48 hRA hN hθ0 hθ1 hℓ0 hℓ_mem.2
      show (P.κ_star / (4 * P.w_star)) * (u_T - airyZero 1) - (6 * π) ^ 2 * R ^ (3 / 2 : ℝ) * (70 * hankelRinf c) ≤
        hankelBootNodes c f R (tebThetaHB P 0 * (u_T - airyZero 1)) 9 N
      have hslack := hankelBoot_node_slack hr hNle hR32
      show _ ≤ _
      have hkap : P.κ_star = quantC1KappaStar := rfl
      have hws : P.w_star = quantC1WStar := rfl
      rw [hkap, hws]
      linarith
  }, le_rfl, rfl, rfl⟩

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_node_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_node_slack

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_line_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_line_combine

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_uT_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_uT_range

/-- info: 'FormalResearch.SignUncertainty.hankelBootParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootParams

/-- info: 'FormalResearch.SignUncertainty.hankelBootHB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootHB

end FormalResearch.SignUncertainty
