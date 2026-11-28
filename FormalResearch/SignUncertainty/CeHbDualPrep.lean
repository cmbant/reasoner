module

public import FormalResearch.SignUncertainty.CeLiftWindowNeg
public import FormalResearch.SignUncertainty.CeHbSeedGen
public import FormalResearch.SignUncertainty.CeHbSeedMass

/-!
# Shared dual scales, `η_c` tuning, and `O6DualEst` for `thm:ce-hb-lift`

First half of the dual-pair construction for general `D : ShellHBData` under weak Laplace
positivity `∀ y > 0, 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y`:

* `convSource_twisted_unif_eps`: `O(ε ‖1 + w‖^{-5/2})` right-half-plane bound for
  `convSource (3 / 4) 1 1 ε (1 * ε ^ 2)` (retaining the `ε` amplitude factor needed for
  the `K`-scaled convolution source `S_c = M_K S_c^{(0)}`).
* `CeHbDualScales D`: bundles the `K`-independent dual parameters `(b, γ₂, v₀, γ₁, δ₁, c₁, c₂,
  m₀, M₀, x₀, B₀, c₁', d₀, C_η, c_η)`, the scaled source amplitude `M_K`, the origin-tuned
  coefficient `r_eta K c`, the `O6DualEst 4` dual bound for the clamped `-M_K * S_c^{(0)}`,
  left-ray negativity `D_lift ≤ 0`, and the `hb_seed_mass_exists_unif` B-spline & shell floors.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- Right-half-plane twisted Laplace bound with the explicit `ε` factor for
`convSource (3/4) 1 1 ε (1 * ε^2)` (valid for all `ε > 0`). -/
lemma convSource_twisted_unif_eps :
    ∃ C_S0 : ℝ, 0 < C_S0 ∧ ∀ {ε : ℝ}, 0 < ε → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (convSource (3 / 4) 1 1 ε (1 * ε ^ 2)) ((ceCs : ℂ) * w)‖ ≤
        C_S0 * ε * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨Cg, _, hg⟩ := hasU2_ceG1.rhp
  set M : ℝ := 1 + 1 * ((2 + 1 / ((3 / 4 : ℝ) - 1 / 2)) * Real.sqrt 1) with hM
  have hM_pos : 0 < M := by norm_num [hM]
  refine ⟨M * Cg, by positivity, fun {ε} hε {w} hw => ?_⟩
  have hh : 0 < (1 : ℝ) * ε ^ 2 := by positivity
  have hz : 0 ≤ ((ceCs : ℂ) * w).re := by
    rw [Complex.re_ofReal_mul]; exact mul_nonneg ceCs_pos.le hw
  rw [airyTwistedLaplaceC_convSource (by norm_num : (1 / 2 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1) hh hz,
    norm_mul]
  have hlap : ‖lapW (convWc (3 / 4) 1 1 ε (1 * ε ^ 2)) ((ceCs : ℂ) * w)‖ ≤ M * ε := by
    refine (lapW_norm_le (convWc_integrableOn (by norm_num) (by norm_num) hh) hz).trans ?_
    have hn : ∫ y in Ioi (0 : ℝ), ‖convWc (3 / 4) 1 1 ε (1 * ε ^ 2) y‖ =
        ∫ y in Ioi (0 : ℝ), convWc (3 / 4) 1 1 ε (1 * ε ^ 2) y :=
      setIntegral_congr_fun measurableSet_Ioi fun y hy =>
        Real.norm_of_nonneg (convWc_nonneg zero_le_one zero_le_one hε.le hh.le hy)
    rw [hn]
    exact (convWc_integral_bounds (by norm_num) (by norm_num) zero_le_one one_pos hε).2
  calc ‖lapW (convWc (3 / 4) 1 1 ε (1 * ε ^ 2)) ((ceCs : ℂ) * w)‖ *
        ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * w)‖
      ≤ (M * ε) * (Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul hlap (hg w hw) (norm_nonneg _) (by positivity)
    _ = M * Cg * ε * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by ring

lemma odd_of_shellLaplacePos (D : ShellHBData)
    (hL : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) :
    Odd D.S.card := by
  by_contra hnot
  rw [Nat.not_odd_iff_even] at hnot
  obtain ⟨y, hy, hneg⟩ := even_m_laplace_sign D hnot
  linarith [hL y hy]

/-- Bundled `K`-independent dual scales, `η_c` tuning, `O6DualEst`, and seed floors for `D : ShellHBData`. -/
structure CeHbDualScales (D : ShellHBData) where
  hOdd : Odd D.S.card
  S : HBSeedSpec
  hS_eq : S = hbSeedSpec_of_shellHBData D hOdd
  b : ℝ
  hb : 0 < b
  hb_nodes : ∀ j : Fin S.m₀, j.val + 1 < S.m₀ → 0 < ceSb b (S.nodes j)
  γ₂ : ℝ
  hγ₂ : 0 < γ₂
  v₀ : ℝ
  hv₀ : 1 ≤ v₀
  γ₁ : ℝ
  hγ₁ : 0 < γ₁
  hγ₁_eq : γ₁ = (γ₂ * (1 + |airyDerivFirstZero|) + v₀) / S.I_N
  δ₁ : ℝ
  hδ₁ : 0 < δ₁
  c₁ : ℝ
  hc₁ : 0 < c₁
  c₂ : ℝ
  hc₂ : 0 < c₂
  m₀ : ℝ
  M₀ : ℝ
  hm₀ : 0 < m₀
  hM₀ : m₀ ≤ M₀
  hmass : ∀ {c : ℝ}, 2000 ≤ c →
    m₀ * liftEps c ≤ ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ∧
      ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ≤ M₀ * liftEps c
  x₀ : ℝ
  B₀ : ℝ
  c₁' : ℝ
  d₀ : ℝ
  hx₀ : 0 < x₀
  hx₀B : x₀ < B₀
  hc₁' : 0 < c₁'
  hd₀ : 0 < d₀
  hX_small : ∀ x ∈ Icc (0 : ℝ) x₀,
    c₁' * Real.sqrt x ≤ (airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re
  hX_tail : ∀ x : ℝ, B₀ / 2 ≤ x →
    d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
      (airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re
  hZ0_lap : ∀ x ∈ Icc (0 : ℝ) (2 * B₀),
    1 ≤ γ₁ * (airyTwistedLaplaceC (fun u => S.H_N u) ((ceCs * x : ℝ) : ℂ)).re -
      γ₂ * (airyTwistedLaplaceC (ceSb b) ((ceCs * x : ℝ) : ℂ)).re
  CX_negG : ℝ
  CH_N : ℝ
  CSb : ℝ
  Cg : ℝ
  CS0 : ℝ
  hCX_negG_pos : 0 < CX_negG
  hCH_N_pos : 0 < CH_N
  hCSb_pos : 0 < CSb
  hCg_pos : 0 < Cg
  hCS0_pos : 0 < CS0
  hCX_negG : ∀ w : ℂ, 0 ≤ w.re →
    ‖airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤
      CX_negG * ‖1 + w‖ ^ (-(5 / 2 : ℝ))
  hCH_N : ∀ w : ℂ, 0 ≤ w.re →
    ‖airyTwistedLaplaceC (fun u => S.H_N u) ((ceCs : ℂ) * w)‖ ≤ CH_N * ‖1 + w‖ ^ (-(5 / 2 : ℝ))
  hCSb : ∀ w : ℂ, 0 ≤ w.re →
    ‖airyTwistedLaplaceC (ceSb b) ((ceCs : ℂ) * w)‖ ≤ CSb * ‖1 + w‖ ^ (-(5 / 2 : ℝ))
  hCg : ∀ w : ℂ, 0 ≤ w.re →
    ‖airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤
      Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ))
  hCS0 : ∀ {c : ℝ}, 0 < c → ∀ {w : ℂ}, 0 ≤ w.re →
    ‖airyTwistedLaplaceC (convSourceFamily (3 / 4) 1 1 1 c) ((ceCs : ℂ) * w)‖ ≤
      CS0 * liftEps c * ‖1 + w‖ ^ (-(5 / 2 : ℝ))
  M_K : ℝ → ℝ → ℝ
  r_eta : ℝ → ℝ → ℝ
  c_η : ℝ
  C_η : ℝ
  hc_η : 2000 ≤ c_η
  hC_η : 0 < C_η
  hM_K_def : ∀ K c : ℝ,
    M_K K c = (v₀ * K * liftEps c) / ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u
  hM_K_bd : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c →
    v₀ * K / M₀ ≤ M_K K c ∧ M_K K c ≤ v₀ * K / m₀
  hr_eta_eq : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c →
    let δ := K * liftEps c
    let δ₀ := ceBeta1 * K * liftEps c / 2
    let Q₀ : ℝ → ℝ := fun u =>
      -(D.G (u : ℂ)).re + δ * (γ₁ * S.H_N u - γ₂ * ceSb b u) -
        M_K K c * convSourceFamily (3 / 4) 1 1 1 c u
    liftSymbol (fun u => Q₀ u + r_eta K c * (airySeedG 0 (u : ℂ)).re) δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
      liftSymbol (fun u => Q₀ u + r_eta K c * (airySeedG 0 (u : ℂ)).re) δ₀ 4 0 = 0
  hr_eta_bd : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c →
    |r_eta K c| ≤ C_η * K * c ^ (-(5 / 6 : ℝ))
  hr_eta_eps : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c →
    |r_eta K c| ≤ K * liftEps c
  hD_neg_left : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
    ∀ u : ℝ, u ≤ D.tm - 1 →
      -(D.G (u : ℂ)).re + (K * liftEps c) * (γ₁ * S.H_N u - γ₂ * ceSb b u) +
        r_eta K c * (airySeedG 0 (u : ℂ)).re ≤ 0
  hF_mass_floor : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
    let δ := K * liftEps c
    let F : ℝ → ℝ := fun u => S.G_N u - γ₁ * δ * S.H_N u + γ₂ * δ * ceSb b u +
      (-r_eta K c) * (airySeedG 0 (u : ℂ)).re
    let u₀ := S.lastNode - 2 * γ₁ * δ
    (Integrable F ∧ ∫ u : ℝ, F u = -v₀ * δ + (-r_eta K c)) ∧
    (∀ x ≥ |u₀| + ceBeta1 * δ / 2,
      (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
        ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2), F (-x + t) * bspline 4 (ceBeta1 * δ / 2) t) ∧
    (∀ j : Fin S.m₀, j.val + 1 < S.m₀ → ∀ u : ℝ, |u - S.nodes j| ≤ ceBeta1 * δ → δ / 2 ≤ F u)
  hS_dual_est : O6DualEst 4 (fun K c u =>
    -(if 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then M_K K c * convSourceFamily (3 / 4) 1 1 1 c u else 0))

private lemma hbSeed_GN_eq (D : ShellHBData) (hOdd : Odd D.S.card) :
    (hbSeedSpec_of_shellHBData D hOdd).G_N = fun u : ℝ => (D.G (u : ℂ)).re := rfl

private lemma hbSeed_HN_eq (D : ShellHBData) (hOdd : Odd D.S.card) :
    (hbSeedSpec_of_shellHBData D hOdd).H_N =
      fun u : ℝ => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re := rfl

private lemma hbSeed_IN_eq (D : ShellHBData) (hOdd : Odd D.S.card) :
    (hbSeedSpec_of_shellHBData D hOdd).I_N =
      ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm) := rfl

private noncomputable def ceHbMK (v₀ K c : ℝ) : ℝ :=
  (v₀ * K * liftEps c) / ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u

private lemma ceHbMK_bd {v₀ m₀ M₀ : ℝ} (hv₀ : 0 ≤ v₀) (hm₀ : 0 < m₀) (hM₀ : m₀ ≤ M₀)
    (hmass : ∀ {c : ℝ}, 2000 ≤ c →
      m₀ * liftEps c ≤ ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ∧
        ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ≤ M₀ * liftEps c)
    {K c : ℝ} (hK : 0 ≤ K) (hc : 2000 ≤ c) :
    v₀ * K / M₀ ≤ ceHbMK v₀ K c ∧ ceHbMK v₀ K c ≤ v₀ * K / m₀ := by
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hm := hmass hc
  have hI0 : 0 < ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u :=
    lt_of_lt_of_le (mul_pos hm₀ hε0) hm.1
  dsimp [ceHbMK]
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff₀ (hm₀.trans_le hM₀) hI0]
    calc v₀ * K * (∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u)
        ≤ v₀ * K * (M₀ * liftEps c) := mul_le_mul_of_nonneg_left hm.2 (by positivity)
      _ = v₀ * K * liftEps c * M₀ := by ring
  · rw [div_le_div_iff₀ hI0 hm₀]
    calc v₀ * K * liftEps c * m₀ = v₀ * K * (m₀ * liftEps c) := by ring
      _ ≤ v₀ * K * (∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u) :=
          mul_le_mul_of_nonneg_left hm.1 (by positivity)

private lemma ceHbDual_Z0_lap (D : ShellHBData) (S : HBSeedSpec)
    (hS_HN : S.H_N = fun u : ℝ => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re)
    (hIN_eq : S.I_N = ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm))
    (hdef : ∀ y : ℝ, 0 ≤ y →
      (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) * Real.exp (D.tm * y - y ^ 3 / 12) ≤
        airyLaplace (fun u => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re) y ∧
      0 < (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) * Real.exp (D.tm * y - y ^ 3 / 12))
    {b B₀ CSb γ₂ v₀ γ₁ : ℝ} (hγ₂ : 0 < γ₂) (hCSb_pos : 0 < CSb)
    (hCSb : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (ceSb b) ((ceCs : ℂ) * w)‖ ≤ CSb * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hγ₁ : 0 < γ₁) (hγ₁_eq : γ₁ = (γ₂ * (1 + |airyDerivFirstZero|) + v₀) / S.I_N)
    (hv₀_ge : (1 + γ₂ * CSb) / (ceK * Real.exp (D.tm * (ceCs * (2 * B₀)) - (ceCs * (2 * B₀)) ^ 3 / 12)) ≤ v₀) :
    ∀ x ∈ Icc (0 : ℝ) (2 * B₀),
      1 ≤ γ₁ * (airyTwistedLaplaceC (fun u => S.H_N u) ((ceCs * x : ℝ) : ℂ)).re -
        γ₂ * (airyTwistedLaplaceC (ceSb b) ((ceCs * x : ℝ) : ℂ)).re := by
  let m_H : ℝ := ceK * Real.exp (D.tm * (ceCs * (2 * B₀)) - (ceCs * (2 * B₀)) ^ 3 / 12)
  have hm_H_pos : 0 < m_H := by have := ceK_pos; positivity
  intro x hx
  have hx0 : 0 ≤ ceCs * x := mul_nonneg ceCs_pos.le hx.1
  have htm0 : D.tm ≤ 0 := le_trans D.tm_le_airyZero_one (by linarith [airyZero_one.2])
  have hxB : ceCs * x ≤ ceCs * (2 * B₀) := mul_le_mul_of_nonneg_left hx.2 ceCs_pos.le
  have htm_le : D.tm * (ceCs * (2 * B₀)) ≤ D.tm * (ceCs * x) := mul_le_mul_of_nonpos_left hxB htm0
  have hcub_le : (ceCs * x) ^ 3 ≤ (ceCs * (2 * B₀)) ^ 3 := by gcongr
  have hexp_le : m_H ≤ ceK * Real.exp (D.tm * (ceCs * x) - (ceCs * x) ^ 3 / 12) := by
    dsimp [m_H]; refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ceK_pos.le; linarith
  have hHL : S.I_N * m_H ≤ (airyTwistedLaplaceC (fun u => S.H_N u) ((ceCs * x : ℝ) : ℂ)).re := by
    rw [hS_HN, airyTwistedLaplaceC_ofReal, Complex.ofReal_re, airyTwistedLaplace_eq_ceK_airyLaplace]
    have h1 := (hdef (ceCs * x) hx0).1
    rw [← hIN_eq] at h1
    calc S.I_N * m_H ≤ S.I_N * (ceK * Real.exp (D.tm * (ceCs * x) - (ceCs * x) ^ 3 / 12)) :=
          mul_le_mul_of_nonneg_left hexp_le S.I_N_pos.le
      _ = ceK * (S.I_N * Real.exp (D.tm * (ceCs * x) - (ceCs * x) ^ 3 / 12)) := by ring
      _ ≤ ceK * airyLaplace (fun u => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re) (ceCs * x) :=
          mul_le_mul_of_nonneg_left h1 ceK_pos.le
  have hSb_bd : |(airyTwistedLaplaceC (ceSb b) ((ceCs * x : ℝ) : ℂ)).re| ≤ CSb := by
    have h1 := (Complex.abs_re_le_norm _).trans (hCSb (x : ℂ) (by simpa using hx.1))
    rw [← Complex.ofReal_mul] at h1
    have hnorm : ‖1 + (x : ℂ)‖ ^ (-(5 / 2 : ℝ)) ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by linarith [hx.1])]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by norm_num)
    exact h1.trans (mul_le_of_le_one_right hCSb_pos.le hnorm)
  have hγ₁IN : v₀ ≤ γ₁ * S.I_N := by
    rw [hγ₁_eq, div_mul_cancel₀ _ S.I_N_pos.ne']
    linarith [mul_nonneg hγ₂.le (by positivity : 0 ≤ 1 + |airyDerivFirstZero|)]
  have hprod : v₀ * m_H ≤ (γ₁ * S.I_N) * m_H := mul_le_mul_of_nonneg_right hγ₁IN hm_H_pos.le
  have hvm : 1 + γ₂ * CSb ≤ v₀ * m_H := (div_le_iff₀ hm_H_pos).mp hv₀_ge
  have hSb_hi : (airyTwistedLaplaceC (ceSb b) ((ceCs * x : ℝ) : ℂ)).re ≤ CSb := (abs_le.mp hSb_bd).2
  nlinarith [mul_le_mul_of_nonneg_left hHL hγ₁.le, mul_le_mul_of_nonneg_left hSb_hi hγ₂.le]

private lemma ceHbDual_eta_spec (D : ShellHBData) (S : HBSeedSpec)
    (hUX_negG : HasU2 (fun u => -(D.G (u : ℂ)).re)) (hUH_N : HasU2 (fun u => S.H_N u))
    (hUSb : HasU2 (ceSb b)) (hUX_int : ∫ u : ℝ, -(D.G (u : ℂ)).re = 0)
    {CX_negG CH_N CSb Cg C_S0 γ₁ γ₂ v₀ m₀ M₀ : ℝ}
    (hCX : 0 < CX_negG) (hCH : 0 < CH_N) (hCSb : 0 < CSb) (hCg : 0 < Cg) (hCS0 : 0 < C_S0)
    (hγ₂ : 0 < γ₂) (hv₀ : 0 ≤ v₀) (hm₀ : 0 < m₀) (hM₀ : m₀ ≤ M₀)
    (hγ₁_eq : γ₁ = (γ₂ * (1 + |airyDerivFirstZero|) + v₀) / S.I_N)
    (hmass : ∀ {c : ℝ}, 2000 ≤ c →
      m₀ * liftEps c ≤ ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ∧
        ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ≤ M₀ * liftEps c)
    (bX : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤ CX_negG * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (bH : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (fun u => S.H_N u) ((ceCs : ℂ) * w)‖ ≤ CH_N * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (bSb : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (ceSb b) ((ceCs : ℂ) * w)‖ ≤ CSb * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (bg : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤ Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (bS0 : ∀ {c : ℝ}, 0 < c → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (convSourceFamily (3 / 4) 1 1 1 c) ((ceCs : ℂ) * w)‖ ≤ C_S0 * liftEps c * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    {K c : ℝ} (hK : 1 ≤ K) (hc_g : (4 * Cg / ceK + 1) ^ 2 ≤ c) (hc2k : 2000 ≤ c) (hcK : 8 * K ^ 3 ≤ c) :
    let B_edge := CX_negG + (γ₁ * CH_N + γ₂ * CSb) / 2 + (v₀ / m₀) * C_S0 + 1
    let C_η := 2 / ceK * B_edge + 1
    let δ := K * liftEps c
    let δ₀ := ceBeta1 * K * liftEps c / 2
    let Q₀ : ℝ → ℝ := fun u => -(D.G (u : ℂ)).re + δ * (γ₁ * S.H_N u - γ₂ * ceSb b u) -
      ceHbMK v₀ K c * convSourceFamily (3 / 4) 1 1 1 c u
    ∃ η : ℝ,
      liftSymbol (fun u => Q₀ u + η * (airySeedG 0 (u : ℂ)).re) δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
        liftSymbol (fun u => Q₀ u + η * (airySeedG 0 (u : ℂ)).re) δ₀ 4 0 = 0 ∧
      |η| ≤ C_η * K * c ^ (-(5 / 6 : ℝ)) := by
  intro B_edge C_η δ δ₀ Q₀
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one hc1
  have hδ₀ : 0 ≤ δ₀ := by have := ceBeta1_pos; positivity
  let x : ℝ := c ^ (1 / 3 : ℝ)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hc0 _
  have hrhp_bd : ∀ {C : ℝ}, 0 ≤ C → ∀ (A : ℝ → ℝ),
      (∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC A ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ‖liftSymbol A δ₀ 4 (x : ℂ)‖ ≤ C * c ^ (-(5 / 6 : ℝ)) := by
    intro C hC A hA
    have hx_re : 0 ≤ (x : ℂ).re := by simp [hx0.le]
    have hnorm : ‖1 + (x : ℂ)‖ = 1 + x := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hpow : ‖1 + (x : ℂ)‖ ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) := by
      rw [hnorm]
      calc (1 + x) ^ (-(5 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
        _ = c ^ (-(5 / 6 : ℝ)) := by dsimp [x]; rw [← Real.rpow_mul hc0.le]; norm_num
    unfold liftSymbol; rw [norm_mul]
    exact (mul_le_mul (norm_liftMultiplier_le_one hδ₀ 4 hx_re)
      ((hA (x : ℂ) hx_re).trans (mul_le_mul_of_nonneg_left hpow hC)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hk0 : 0 < ceK := ceK_pos
  have hgx : |(liftSymbol (ceG1 (airyZero 1)) δ₀ 4 (x : ℂ)).re| ≤ ceK / 2 := by
    have hgnorm := hrhp_bd hCg.le _ bg
    rw [airySeedG0_eq_ceG1] at hgnorm
    have hc_c12 : 4 * Cg / ceK + 1 ≤ √c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * Cg / ceK + 1)]; exact Real.sqrt_le_sqrt hc_g
    have hsqrt_pos : 0 < √c := Real.sqrt_pos.mpr hc0
    have hc56 : c ^ (-(5 / 6 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hcg_le : Cg * c ^ (-(1 / 2 : ℝ)) ≤ ceK / 4 := by
      rw [show c ^ (-(1 / 2 : ℝ)) = (√c)⁻¹ by rw [Real.sqrt_eq_rpow, Real.rpow_neg hc0.le],
        ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      calc Cg = (ceK / 4) * (4 * Cg / ceK) := by field_simp [hk0.ne']
        _ ≤ (ceK / 4) * √c := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact (Complex.abs_re_le_norm _).trans (hgnorm.trans
      ((mul_le_mul_of_nonneg_left hc56 hCg.le).trans (by linarith [hk0])))
  have hS0_u2 : HasU2 (convSourceFamily (3 / 4) 1 1 1 c) :=
    hasU2_convSource (by norm_num) (by norm_num) (by positivity)
  have hUQ : HasU2 Q₀ := by
    have hD_term : HasU2 (fun u => -(D.G (u : ℂ)).re + δ * (γ₁ * S.H_N u - γ₂ * ceSb b u)) := by
      have h2 := (hUH_N.smul (δ * γ₁)).add (hUSb.smul (-(δ * γ₂)))
      convert hUX_negG.add h2 using 1
      ext u; ring
    simpa only [Q₀, sub_eq_add_neg, neg_mul] using hD_term.add (hS0_u2.smul (-(ceHbMK v₀ K c)))
  have hI0 : (∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u) ≠ 0 :=
    (lt_of_lt_of_le (mul_pos hm₀ hε0) (hmass hc2k).1).ne'
  have hQ0_int : ∫ u : ℝ, Q₀ u = 0 := by
    have intX : Integrable (fun u : ℝ => -(D.G (u : ℂ)).re) :=
      (Complex.reCLM.integrable_comp (hUX_negG.integrable 0 le_rfl)).congr (ae_of_all _ fun _ => by simp)
    have intH : Integrable (fun u : ℝ => S.H_N u) :=
      (Complex.reCLM.integrable_comp (hUH_N.integrable 0 le_rfl)).congr (ae_of_all _ fun _ => by simp)
    have intSb : Integrable (ceSb b) :=
      (Complex.reCLM.integrable_comp (hUSb.integrable 0 le_rfl)).congr (ae_of_all _ fun _ => by simp)
    have intS0 : Integrable (convSourceFamily (3 / 4) 1 1 1 c) :=
      (Complex.reCLM.integrable_comp (hS0_u2.integrable 0 le_rfl)).congr (ae_of_all _ fun _ => by simp)
    have h1 : Integrable (fun u => δ * (γ₁ * S.H_N u - γ₂ * ceSb b u)) :=
      ((intH.const_mul γ₁).sub (intSb.const_mul γ₂)).const_mul _
    calc ∫ u : ℝ, Q₀ u
        = (∫ u : ℝ, (-(D.G (u : ℂ)).re + δ * (γ₁ * S.H_N u - γ₂ * ceSb b u))) -
            ∫ u : ℝ, ceHbMK v₀ K c * convSourceFamily (3 / 4) 1 1 1 c u :=
          integral_sub (intX.add h1) (intS0.const_mul _)
      _ = ((∫ u : ℝ, -(D.G (u : ℂ)).re) + δ * (γ₁ * (∫ u : ℝ, S.H_N u) - γ₂ * (∫ u : ℝ, ceSb b u))) -
            ceHbMK v₀ K c * ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u := by
          rw [integral_add intX h1, integral_const_mul, integral_const_mul,
            integral_sub (intH.const_mul γ₁) (intSb.const_mul γ₂), integral_const_mul, integral_const_mul]
      _ = 0 := by
          rw [hUX_int, S.integral_H, ceSb_integral b]
          have hγ₁_val : γ₁ * S.I_N - γ₂ * (1 + |airyDerivFirstZero|) = v₀ := by
            rw [hγ₁_eq, div_mul_cancel₀ _ S.I_N_pos.ne']; ring
          rw [hγ₁_val]; dsimp [δ, ceHbMK]; rw [div_mul_cancel₀ _ hI0]; ring
  obtain ⟨η, hη0, hη_bd⟩ := exists_eta_tune hUQ 4 hx0.le hgx
  have hQ0 : liftSymbol Q₀ δ₀ 4 0 = 0 := by
    rw [liftSymbol_zero_eq hUQ δ₀ 4, hQ0_int, mul_zero, Complex.ofReal_zero]
  have hKeps : K * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) hcK
  have hsplit : liftSymbol Q₀ δ₀ 4 (x : ℂ) =
      liftSymbol (fun u => -(D.G (u : ℂ)).re) δ₀ 4 (x : ℂ) +
      ((δ * γ₁ : ℝ) : ℂ) * liftSymbol (fun u => S.H_N u) δ₀ 4 (x : ℂ) +
      (-(δ * γ₂ : ℝ) : ℂ) * liftSymbol (ceSb b) δ₀ 4 (x : ℂ) +
      (-(ceHbMK v₀ K c : ℝ) : ℂ) * liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 (x : ℂ) := by
    have hre : 0 ≤ (x : ℂ).re := by simp [hx0.le]
    have hfn1 : Q₀ = fun u : ℝ =>
        (-(D.G (u : ℂ)).re + ((δ * γ₁) * S.H_N u + -(δ * γ₂) * ceSb b u)) +
          (-(ceHbMK v₀ K c)) * convSourceFamily (3 / 4) 1 1 1 c u := by
      ext u; dsimp [Q₀]; ring
    rw [hfn1, liftSymbol_add_seed (hUX_negG.add ((hUH_N.smul _).add (hUSb.smul _))) (hS0_u2.smul _) δ₀ 4 hre,
      liftSymbol_add_seed hUX_negG ((hUH_N.smul _).add (hUSb.smul _)) δ₀ 4 hre,
      liftSymbol_add_seed (hUH_N.smul _) (hUSb.smul _) δ₀ 4 hre,
      liftSymbol_const_mul_seed, liftSymbol_const_mul_seed, liftSymbol_const_mul_seed]
    push_cast; ring
  have hQx : ‖liftSymbol Q₀ δ₀ 4 (x : ℂ)‖ ≤ B_edge * K * c ^ (-(5 / 6 : ℝ)) := by
    rw [hsplit]
    have b1 := hrhp_bd hCX.le _ bX
    have b2 := hrhp_bd hCH.le _ bH
    have b3 := hrhp_bd hCSb.le _ bSb
    have b4 := hrhp_bd (mul_nonneg hCS0.le hε0.le) _ (fun w hw => bS0 hc0 hw)
    have b4' : ‖liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 (x : ℂ)‖ ≤ C_S0 * c ^ (-(5 / 6 : ℝ)) :=
      b4.trans (by gcongr; exact mul_le_of_le_one_right hCS0.le hε1)
    have hMK_bd := ceHbMK_bd hv₀ hm₀ hM₀ hmass (by linarith : 0 ≤ K) hc2k
    have hMK_nn : 0 ≤ ceHbMK v₀ K c :=
      le_trans (div_nonneg (mul_nonneg hv₀ (by linarith)) (hm₀.trans_le hM₀).le) hMK_bd.1
    have hγ₁nn : 0 ≤ γ₁ := by rw [hγ₁_eq]; have := S.I_N_pos; positivity
    have hnorm_sum : ‖liftSymbol (fun u => -(D.G (u : ℂ)).re) δ₀ 4 (x : ℂ) +
          ((δ * γ₁ : ℝ) : ℂ) * liftSymbol (fun u => S.H_N u) δ₀ 4 (x : ℂ) +
          (-(δ * γ₂ : ℝ) : ℂ) * liftSymbol (ceSb b) δ₀ 4 (x : ℂ) +
          (-(ceHbMK v₀ K c : ℝ) : ℂ) * liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 (x : ℂ)‖ ≤
        ‖liftSymbol (fun u => -(D.G (u : ℂ)).re) δ₀ 4 (x : ℂ)‖ +
        ‖((δ * γ₁ : ℝ) : ℂ) * liftSymbol (fun u => S.H_N u) δ₀ 4 (x : ℂ)‖ +
        ‖(-(δ * γ₂ : ℝ) : ℂ) * liftSymbol (ceSb b) δ₀ 4 (x : ℂ)‖ +
        ‖(-(ceHbMK v₀ K c : ℝ) : ℂ) * liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 (x : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    have hn2 : ‖((δ * γ₁ : ℝ) : ℂ) * liftSymbol (fun u => S.H_N u) δ₀ 4 (x : ℂ)‖ ≤
        ((γ₁ * CH_N) / 2) * c ^ (-(5 / 6 : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by dsimp [δ]; positivity)]
      calc δ * γ₁ * ‖liftSymbol (fun u => S.H_N u) δ₀ 4 (x : ℂ)‖
          ≤ ((1 / 2) * γ₁) * (CH_N * c ^ (-(5 / 6 : ℝ))) := mul_le_mul (by dsimp [δ]; gcongr) b2 (norm_nonneg _) (by positivity)
        _ = ((γ₁ * CH_N) / 2) * c ^ (-(5 / 6 : ℝ)) := by ring
    have hn3 : ‖(-(δ * γ₂ : ℝ) : ℂ) * liftSymbol (ceSb b) δ₀ 4 (x : ℂ)‖ ≤
        ((γ₂ * CSb) / 2) * c ^ (-(5 / 6 : ℝ)) := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by dsimp [δ]; positivity)]
      calc δ * γ₂ * ‖liftSymbol (ceSb b) δ₀ 4 (x : ℂ)‖
          ≤ ((1 / 2) * γ₂) * (CSb * c ^ (-(5 / 6 : ℝ))) := mul_le_mul (by dsimp [δ]; gcongr) b3 (norm_nonneg _) (by positivity)
        _ = ((γ₂ * CSb) / 2) * c ^ (-(5 / 6 : ℝ)) := by ring
    have hn4 : ‖(-(ceHbMK v₀ K c : ℝ) : ℂ) * liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 (x : ℂ)‖ ≤
        (v₀ * K / m₀) * C_S0 * c ^ (-(5 / 6 : ℝ)) := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hMK_nn]
      exact (mul_le_mul hMK_bd.2 b4' (norm_nonneg _) (by positivity)).trans_eq (by ring)
    have hc56nn : 0 ≤ c ^ (-(5 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hle_k : (CX_negG + (γ₁ * CH_N + γ₂ * CSb) / 2) * c ^ (-(5 / 6 : ℝ)) ≤
        (CX_negG + (γ₁ * CH_N + γ₂ * CSb) / 2) * (K * c ^ (-(5 / 6 : ℝ))) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hc56nn hK) (by positivity)
    calc ‖_‖ ≤ CX_negG * c ^ (-(5 / 6 : ℝ)) + ((γ₁ * CH_N) / 2) * c ^ (-(5 / 6 : ℝ)) +
            ((γ₂ * CSb) / 2) * c ^ (-(5 / 6 : ℝ)) + (v₀ * K / m₀) * C_S0 * c ^ (-(5 / 6 : ℝ)) :=
          hnorm_sum.trans (add_le_add (add_le_add (add_le_add b1 hn2) hn3) hn4)
      _ = (CX_negG + (γ₁ * CH_N + γ₂ * CSb) / 2) * c ^ (-(5 / 6 : ℝ)) +
            (v₀ / m₀ * C_S0) * (K * c ^ (-(5 / 6 : ℝ))) := by ring
      _ ≤ (CX_negG + (γ₁ * CH_N + γ₂ * CSb) / 2) * (K * c ^ (-(5 / 6 : ℝ))) +
            (v₀ / m₀ * C_S0) * (K * c ^ (-(5 / 6 : ℝ))) := add_le_add hle_k le_rfl
      _ ≤ B_edge * K * c ^ (-(5 / 6 : ℝ)) := by
          have hk56 : 0 ≤ K * c ^ (-(5 / 6 : ℝ)) := mul_nonneg (by positivity) hc56nn
          dsimp [B_edge]; nlinarith
  refine ⟨η, ?_, ?_⟩
  · have hgg : ∀ u : ℝ, ceG1 (airyZero 1) u = (airySeedG 0 (u : ℂ)).re := fun u =>
      (congr_fun airySeedG0_eq_ceG1 u).symm
    simpa [δ₀, x, hgg] using hη0
  · rw [hQ0, sub_zero] at hη_bd
    calc |η| ≤ 2 / ceK * ‖liftSymbol Q₀ δ₀ 4 (x : ℂ)‖ := hη_bd
      _ ≤ 2 / ceK * (B_edge * K * c ^ (-(5 / 6 : ℝ))) := mul_le_mul_of_nonneg_left hQx (by have := hk0; positivity)
      _ ≤ C_η * K * c ^ (-(5 / 6 : ℝ)) := by
          have hk56 : 0 ≤ K * c ^ (-(5 / 6 : ℝ)) := mul_nonneg (by positivity) (Real.rpow_nonneg hc0.le _)
          dsimp [C_η]; nlinarith

private lemma ceHbDual_neg_left (D : ShellHBData) (S : HBSeedSpec)
    (hS_last : S.lastNode = D.tm) (hS_GN : S.G_N = fun u : ℝ => (D.G (u : ℂ)).re)
    {b γ₁ γ₂ δ₁ r_eta : ℝ} (hb : 0 < b) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hδ₁ : 0 < δ₁)
    (hγ₁δ12 : δ₁ ≤ 1 / (2 * γ₁))
    {K c : ℝ} (hK : 1 ≤ K) (hc2k : 2000 ≤ c) (hcδ : (K / δ₁) ^ 3 ≤ c)
    (hr_bd : |r_eta| ≤ (γ₂ / 2) * (K * liftEps c))
    (u : ℝ) (hu : u ≤ D.tm - 1) :
    -(D.G (u : ℂ)).re + (K * liftEps c) * (γ₁ * S.H_N u - γ₂ * ceSb b u) +
      r_eta * (airySeedG 0 (u : ℂ)).re ≤ 0 := by
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hKδ_le : K * liftEps c ≤ δ₁ := by
    have hc13 : K / δ₁ ≤ c ^ (1 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hcδ (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at h
      simpa using h
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
      ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
    exact ((div_le_iff₀ hδ₁).mp hc13).trans (mul_comm _ _).le
  have hγ₁δ : γ₁ * (K * liftEps c) ≤ 1 / 2 := calc
    γ₁ * (K * liftEps c) ≤ γ₁ * δ₁ := mul_le_mul_of_nonneg_left hKδ_le hγ₁.le
    _ ≤ γ₁ * (1 / (2 * γ₁)) := mul_le_mul_of_nonneg_left hγ₁δ12 hγ₁.le
    _ = 1 / 2 := by field_simp [hγ₁.ne']
  have hle_last : u ≤ S.lastNode := by linarith [hS_last]
  have hG_nn : 0 ≤ S.G_N u := S.G_nonneg_tail u hle_last
  have hu_lt : u < S.lastNode := by linarith [hS_last]
  have hH_eq : S.H_N u = S.G_N u / (D.tm - u) := by rw [← hS_last]; exact S.H_eq_div_tail u hu_lt
  have hH_le : S.H_N u ≤ S.G_N u := by rw [hH_eq]; exact div_le_self hG_nn (by linarith)
  have hterm1 : (K * liftEps c) * (γ₁ * S.H_N u) ≤ S.G_N u := by
    calc (K * liftEps c) * (γ₁ * S.H_N u) = (γ₁ * (K * liftEps c)) * S.H_N u := by ring
      _ ≤ (1 / 2) * S.G_N u := by
          by_cases hHnn : 0 ≤ S.H_N u
          · exact mul_le_mul hγ₁δ hH_le hHnn (by norm_num)
          · have hle : (γ₁ * (K * liftEps c)) * S.H_N u ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hγ₁.le (by positivity)) (le_of_not_ge hHnn)
            linarith
      _ ≤ S.G_N u := by linarith
  have hg_eq : (airySeedG 0 (u : ℂ)).re = ceG1 (airyZero 1) u := congr_fun airySeedG0_eq_ceG1 u
  have hceSb_ge : ceG1 (airyZero 1) u ≤ ceSb b u :=
    ceG1_le_ceSb hb.le (le_trans (by linarith) D.tm_le_airyZero_one)
  have hr_hi : r_eta ≤ (γ₂ / 2) * (K * liftEps c) := (abs_le.mp hr_bd).2
  have hgnn : 0 ≤ ceG1 (airyZero 1) u := sq_nonneg _
  have hterm2 : r_eta * (airySeedG 0 (u : ℂ)).re ≤ (K * liftEps c) * (γ₂ * ceSb b u) := by
    rw [hg_eq]
    have hhalf : ((γ₂ / 2) * (K * liftEps c)) * ceG1 (airyZero 1) u ≤
        (γ₂ * (K * liftEps c)) * ceG1 (airyZero 1) u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hgnn
    calc r_eta * ceG1 (airyZero 1) u
        ≤ ((γ₂ / 2) * (K * liftEps c)) * ceG1 (airyZero 1) u := mul_le_mul_of_nonneg_right hr_hi hgnn
      _ ≤ (γ₂ * (K * liftEps c)) * ceG1 (airyZero 1) u := hhalf
      _ = (K * liftEps c) * (γ₂ * ceG1 (airyZero 1) u) := by ring
      _ ≤ (K * liftEps c) * (γ₂ * ceSb b u) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hceSb_ge hγ₂.le) (by positivity)
  have hGN_eq : (D.G (u : ℂ)).re = S.G_N u := (congr_fun hS_GN u).symm
  rw [hGN_eq]
  linarith

private lemma ceHbDual_dual_est {v₀ m₀ M₀ C_S0 : ℝ} (hv₀ : 0 ≤ v₀) (hm₀ : 0 < m₀) (hM₀ : m₀ ≤ M₀)
    (hCS0_pos : 0 < C_S0)
    (hmass : ∀ {c : ℝ}, 2000 ≤ c →
      m₀ * liftEps c ≤ ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ∧
        ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ≤ M₀ * liftEps c)
    (hCS0_fam : ∀ {c : ℝ}, 0 < c → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (convSourceFamily (3 / 4) 1 1 1 c) ((ceCs : ℂ) * w)‖ ≤
        C_S0 * liftEps c * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :
    O6DualEst 4 (fun K c u =>
      -(if 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then ceHbMK v₀ K c * convSourceFamily (3 / 4) 1 1 1 c u else 0)) := by
  let S_fam : ℝ → ℝ → ℝ → ℝ := fun K c u =>
    -(if 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then ceHbMK v₀ K c * convSourceFamily (3 / 4) 1 1 1 c u else 0)
  let CD_fam : ℝ := (v₀ / m₀) * (2 * C_S0) + 1
  have hCD_fam : 0 ≤ CD_fam := by positivity
  have hbd_fam : ∀ {K c : ℝ}, 2 ≤ c → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (S_fam K c) ((ceCs : ℂ) * w)‖ ≤ CD_fam * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
    intro K c hc w hw
    have hT : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hcond : 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2
    · have hc0 : 0 < c := by linarith
      have hMK_bd := ceHbMK_bd hv₀ hm₀ hM₀ hmass hcond.1.le hcond.2.1
      have hMK_nn : 0 ≤ ceHbMK v₀ K c :=
        le_trans (div_nonneg (mul_nonneg hv₀ hcond.1.le) (hm₀.trans_le hM₀).le) hMK_bd.1
      have hfn : S_fam K c = fun u => (-(ceHbMK v₀ K c)) * convSourceFamily (3 / 4) 1 1 1 c u := by
        ext u; simp [S_fam, hcond]
      rw [hfn, airyTwistedLaplaceC_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg hMK_nn]
      calc ceHbMK v₀ K c * ‖airyTwistedLaplaceC (convSourceFamily (3 / 4) 1 1 1 c) ((ceCs : ℂ) * w)‖
          ≤ (v₀ * K / m₀) * (C_S0 * liftEps c * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul hMK_bd.2 (hCS0_fam hc0 hw) (norm_nonneg _) (by have := hcond.1.le; positivity)
        _ = (v₀ / m₀) * (C_S0 * (K * liftEps c)) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by ring
        _ ≤ (v₀ / m₀) * (C_S0 * 2) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by gcongr; exact hcond.2.2
        _ ≤ CD_fam * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hT; dsimp [CD_fam]; linarith
    · have hfn : S_fam K c = fun _ => 0 := by ext u; simp [S_fam, hcond]
      rw [hfn, show airyTwistedLaplaceC (fun _ : ℝ => (0 : ℝ)) ((ceCs : ℂ) * w) = 0 by
        unfold airyTwistedLaplaceC; simp, norm_zero]
      exact mul_nonneg hCD_fam hT
  have hdiff_fam : ∀ {K c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (S_fam K c)) {y : ℂ | 0 < y.re} := by
    intro K c hc
    by_cases hcond : 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2
    · have hc0 : 0 < c := by linarith
      have hS0 : HasU2 (convSourceFamily (3 / 4) 1 1 1 c) :=
        hasU2_convSource (by norm_num) (by norm_num) (by have := liftEps_pos hc0; positivity)
      have hfn : S_fam K c = fun u => (-(ceHbMK v₀ K c)) * convSourceFamily (3 / 4) 1 1 1 c u := by
        ext u; simp [S_fam, hcond]
      rw [hfn]; exact (hS0.smul _).differentiable
    · have hfn : S_fam K c = fun _ => 0 := by ext u; simp [S_fam, hcond]
      rw [hfn, show (fun _ : ℝ => (0 : ℝ)) = airySeedU2 0 0 0 from funext fun _ => by simp [airySeedU2]]
      exact (hasU2_airySeedU2 0 0 0).differentiable
  constructor
  · obtain ⟨C3, hC3, h3⟩ := iDual_bound_e3 (m := 4) (by norm_num) hCD_fam
    exact ⟨C3, hC3, fun {K c ξ} hδ hc hξ hS => h3 (hdiff_fam hc) (fun {w} hw => hbd_fam hc hw) hδ hc hξ hS⟩
  · intro Sw
    obtain ⟨C5, hC5, h5⟩ := dual_bound_window 4 (by norm_num) (max CD_fam 1) (by positivity)
    refine ⟨C5, hC5, fun {K c ξ} hK hc hξ _ => ?_⟩
    have hc2 : 2 ≤ c := by linarith
    have hc0 : 0 < c := by linarith
    have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have hbd1 : ∀ {w : ℂ}, 0 ≤ w.re →
        ‖airyTwistedLaplaceC (S_fam K c) ((ceCs : ℂ) * w)‖ ≤ max CD_fam 1 * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
      fun {w} hw => (hbd_fam hc2 hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (norm_nonneg _) _))
    refine (h5 (D := S_fam K c) hbd1 hδ hc0 hξ).trans ?_
    have hc12 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hinv : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ 1 := by
      refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
      have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := mul_nonneg hδ (Real.rpow_nonneg hc0.le _)
      linarith
    have hξ1 : (2 * Real.pi * ξ)⁻¹ ≤ ξ⁻¹ := by
      rw [mul_inv]
      have : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
      have hξi : 0 ≤ ξ⁻¹ := inv_nonneg.mpr hξ.le
      nlinarith
    have hrest : C5 * ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        C5 * c ^ (-(1 / 2 : ℝ)) := by
      have : 0 ≤ C5 * c ^ (-(1 / 2 : ℝ)) := by positivity
      calc _ ≤ C5 * 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = _ := by ring
    calc (2 * Real.pi * ξ)⁻¹ * (C5 * ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)))
        ≤ ξ⁻¹ * (C5 * c ^ (-(1 / 2 : ℝ))) := mul_le_mul hξ1 hrest (by positivity) (inv_nonneg.mpr hξ.le)
      _ = C5 * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by ring

/-- Constructs `CeHbDualScales D` from weak Laplace positivity. -/
theorem ceHbDualScales_exists (D : ShellHBData)
    (hL : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) :
    Nonempty (CeHbDualScales D) := by
  classical
  have hOdd : Odd D.S.card := odd_of_shellLaplacePos D hL
  suffices ∀ (S : HBSeedSpec), S = hbSeedSpec_of_shellHBData D hOdd → Nonempty (CeHbDualScales D) from
    this _ rfl
  intro S hS_eq
  have hS_last : S.lastNode = D.tm := hS_eq ▸ hbSeedSpec_of_shellHBData_lastNode D hOdd
  have hS_GN : S.G_N = fun u : ℝ => (D.G (u : ℂ)).re := hS_eq ▸ hbSeed_GN_eq D hOdd
  have hS_HN : S.H_N = fun u : ℝ => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re :=
    hS_eq ▸ hbSeed_HN_eq D hOdd
  have hIN_eq : S.I_N = ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm) := hS_eq ▸ hbSeed_IN_eq D hOdd
  have hnegG_cl := hasGenRationalAiryCoeffs_shellHBData_negG D hOdd
  have hHC_cl := hasGenRationalAiryCoeffs_terminal_cardinal D hOdd
  have hUX_negG : HasU2 (fun u => -(D.G (u : ℂ)).re) := by
    simpa only [Complex.neg_re] using hasU2_of_genRational hnegG_cl
  have hUH_N : HasU2 (fun u => S.H_N u) := by rw [hS_HN]; exact hasU2_of_genRational hHC_cl
  have hG_int0 : ∫ u : ℝ, -(D.G (u : ℂ)).re = 0 := by
    rw [show (fun u : ℝ => -(D.G (u : ℂ)).re) = fun u => -S.G_N u from by ext u; rw [hS_GN],
      integral_neg, S.integral_G, neg_zero]
  have hbinf_negG : airyBetaInf (fun z => -D.G z) < 0 := by
    rw [hnegG_cl.beta_eq.2.2.1]
    linarith [sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (shellHBData_P_degree_of_odd D hOdd).1)]
  have hbplus_negG : 0 < airyBetaPlus (fun z => -D.G z) := by
    rw [hnegG_cl.beta_eq.2.2.2]
    linarith [sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (shellHBData_P_degree_of_odd D hOdd).1)]
  obtain ⟨x₀, B₀, c₁', d₀, hx₀, hx₀B, hc₁', hd₀, hX_small, hX_tail⟩ :=
    ce_dual_floors hnegG_cl (by simpa only [Complex.neg_re] using hG_int0) hbinf_negG hbplus_negG
  obtain ⟨b, hb, hb_nodes⟩ := exists_ceSb_pos_at_nodes S
  have hUSb : HasU2 (ceSb b) := by
    simpa only [airySbC_re] using hasU2_of_genRational (hasGenRationalAiryCoeffs_airySbC b)
  obtain ⟨CX_negG, hCX_negG_pos, hCX_negG⟩ := hUX_negG.rhp
  obtain ⟨CH_N, hCH_N_pos, hCH_N⟩ := hUH_N.rhp
  obtain ⟨CSb, hCSb_pos, hCSb⟩ := hUSb.rhp
  obtain ⟨Cg, hCg_pos, hCg⟩ := (by rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1 : HasU2 (fun u => (airySeedG 0 (u : ℂ)).re)).rhp
  obtain ⟨C_S0, hCS0_pos, hC_S0⟩ := convSource_twisted_unif_eps
  obtain ⟨-, -, -, -, hdef⟩ := ce_terminal_deflation_full D hL
  obtain ⟨γ₂, hγ₂, hseed_unif⟩ := hb_seed_mass_exists_unif S hb hb_nodes zero_le_one
  let m_H : ℝ := ceK * Real.exp (D.tm * (ceCs * (2 * B₀)) - (ceCs * (2 * B₀)) ^ 3 / 12)
  let v₀ : ℝ := max 1 ((1 + γ₂ * CSb) / m_H)
  have hv₀ : 1 ≤ v₀ := le_max_left _ _
  obtain ⟨δ₁_raw, hδ₁_raw, c₁, hc₁, c₂, hc₂, hseed_body⟩ := hseed_unif (by positivity : 0 ≤ v₀)
  let γ₁ : ℝ := (γ₂ * (1 + |airyDerivFirstZero|) + v₀) / S.I_N
  have hγ₁ : 0 < γ₁ := div_pos (by have := S.I_N_pos; positivity) S.I_N_pos
  let δ₁ : ℝ := min δ₁_raw (1 / (2 * γ₁))
  have hδ₁ : 0 < δ₁ := lt_min hδ₁_raw (by positivity)
  have hZ0_lap := ceHbDual_Z0_lap D S hS_HN hIN_eq hdef hγ₂ hCSb_pos hCSb hγ₁ rfl (le_max_right _ _)
  obtain ⟨m₀_raw, M₀_raw, hm₀_raw, _, hmass_raw⟩ :=
    convSourceFamily_mass (by norm_num : (1 / 2 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1) one_pos zero_le_one one_pos
  let m₀ : ℝ := m₀_raw
  let M₀ : ℝ := max m₀_raw M₀_raw
  have hm₀ : 0 < m₀ := hm₀_raw
  have hM₀ : m₀ ≤ M₀ := le_max_left _ _
  have hmass : ∀ {c : ℝ}, 2000 ≤ c →
      m₀ * liftEps c ≤ ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ∧
        ∫ u : ℝ, convSourceFamily (3 / 4) 1 1 1 c u ≤ M₀ * liftEps c := fun {c} hc =>
    ⟨(hmass_raw hc).1, (hmass_raw hc).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (liftEps_pos (by linarith)).le)⟩
  have hCS0_fam : ∀ {c : ℝ}, 0 < c → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (convSourceFamily (3 / 4) 1 1 1 c) ((ceCs : ℂ) * w)‖ ≤ C_S0 * liftEps c * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
    fun {c} hc {_} hw => hC_S0 (liftEps_pos hc) hw
  let B_edge : ℝ := CX_negG + (γ₁ * CH_N + γ₂ * CSb) / 2 + (v₀ / m₀) * C_S0 + 1
  let C_η : ℝ := 2 / ceK * B_edge + 1
  have hC_η : 0 < C_η := by have := ceK_pos; positivity
  let c_η : ℝ := max (max 2000 ((4 * Cg / ceK + 1) ^ 2)) (max (C_η ^ 2 + 1) ((2 * C_η / γ₂ + 1) ^ 2))
  have hc_η_2k : 2000 ≤ c_η := (le_max_left _ _).trans (le_max_left _ _)
  have hη_spec : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c →
      ∃ η : ℝ,
        liftSymbol (fun u => (-(D.G (u : ℂ)).re + (K * liftEps c) * (γ₁ * S.H_N u - γ₂ * ceSb b u) -
              ceHbMK v₀ K c * convSourceFamily (3 / 4) 1 1 1 c u) + η * (airySeedG 0 (u : ℂ)).re)
            (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
          liftSymbol (fun u => (-(D.G (u : ℂ)).re + (K * liftEps c) * (γ₁ * S.H_N u - γ₂ * ceSb b u) -
              ceHbMK v₀ K c * convSourceFamily (3 / 4) 1 1 1 c u) + η * (airySeedG 0 (u : ℂ)).re)
            (ceBeta1 * K * liftEps c / 2) 4 0 = 0 ∧
        |η| ≤ C_η * K * c ^ (-(5 / 6 : ℝ)) := fun {K c} hK hc hcK =>
    ceHbDual_eta_spec D S hUX_negG hUH_N hUSb hG_int0 hCX_negG_pos hCH_N_pos hCSb_pos hCg_pos hCS0_pos
      hγ₂ (by positivity) hm₀ hM₀ rfl hmass hCX_negG hCH_N hCSb hCg hCS0_fam hK
      (((le_max_right _ _).trans (le_max_left _ _)).trans hc) (hc_η_2k.trans hc) hcK
  let r_eta : ℝ → ℝ → ℝ := fun K c =>
    if h : 1 ≤ K ∧ c_η ≤ c ∧ 8 * K ^ 3 ≤ c then Classical.choose (hη_spec h.1 h.2.1 h.2.2) else 0
  have hr_eta_eq : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c →
      let δ := K * liftEps c; let δ₀ := ceBeta1 * K * liftEps c / 2
      let Q₀ : ℝ → ℝ := fun u => -(D.G (u : ℂ)).re + δ * (γ₁ * S.H_N u - γ₂ * ceSb b u) -
        ceHbMK v₀ K c * convSourceFamily (3 / 4) 1 1 1 c u
      liftSymbol (fun u => Q₀ u + r_eta K c * (airySeedG 0 (u : ℂ)).re) δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
        liftSymbol (fun u => Q₀ u + r_eta K c * (airySeedG 0 (u : ℂ)).re) δ₀ 4 0 = 0 := fun {K c} hK hc hcK => by
    have hr_val : r_eta K c = Classical.choose (hη_spec hK hc hcK) := by
      dsimp [r_eta]; split_ifs with h
      · rfl
      · exact absurd ⟨hK, hc, hcK⟩ h
    rw [hr_val]; exact (Classical.choose_spec (hη_spec hK hc hcK)).1
  have hr_eta_bd : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c → |r_eta K c| ≤ C_η * K * c ^ (-(5 / 6 : ℝ)) :=
    fun {K c} hK hc hcK => by
      have hr_val : r_eta K c = Classical.choose (hη_spec hK hc hcK) := by
        dsimp [r_eta]; split_ifs with h
        · rfl
        · exact absurd ⟨hK, hc, hcK⟩ h
      rw [hr_val]; exact (Classical.choose_spec (hη_spec hK hc hcK)).2
  have hr_eta_eps : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c → |r_eta K c| ≤ K * liftEps c := fun {K c} hK hc hcK => by
    have hc0 : 0 < c := by linarith [hc_η_2k.trans hc]
    have hsqrt : C_η ≤ √c := by
      rw [← Real.sqrt_sq hC_η.le]
      exact Real.sqrt_le_sqrt (by linarith [((le_max_left _ _).trans (le_max_right _ _)).trans hc])
    have hc12 : C_η * c ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      rw [show c ^ (-(1 / 2 : ℝ)) = (√c)⁻¹ by rw [Real.sqrt_eq_rpow, Real.rpow_neg hc0.le],
        ← div_eq_mul_inv, div_le_one (Real.sqrt_pos.mpr hc0)]
      exact hsqrt
    have hc56 : c ^ (-(5 / 6 : ℝ)) = liftEps c * c ^ (-(1 / 2 : ℝ)) := by
      unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
    calc |r_eta K c| ≤ C_η * K * c ^ (-(5 / 6 : ℝ)) := hr_eta_bd hK hc hcK
      _ = (C_η * c ^ (-(1 / 2 : ℝ))) * (K * liftEps c) := by rw [hc56]; ring
      _ ≤ 1 * (K * liftEps c) := mul_le_mul_of_nonneg_right hc12 (mul_nonneg (by positivity) (liftEps_pos hc0).le)
      _ = K * liftEps c := one_mul _
  have hr_eta_half_γ₂ : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c → |r_eta K c| ≤ (γ₂ / 2) * (K * liftEps c) :=
    fun {K c} hK hc hcK => by
      have hc0 : 0 < c := by linarith [hc_η_2k.trans hc]
      have hsqrt : 2 * C_η / γ₂ ≤ √c := by
        have : 2 * C_η / γ₂ + 1 ≤ √c := by
          rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * C_η / γ₂ + 1)]
          exact Real.sqrt_le_sqrt (((le_max_right _ _).trans (le_max_right _ _)).trans hc)
        linarith
      have hc12 : C_η * c ^ (-(1 / 2 : ℝ)) ≤ γ₂ / 2 := by
        rw [show c ^ (-(1 / 2 : ℝ)) = (√c)⁻¹ by rw [Real.sqrt_eq_rpow, Real.rpow_neg hc0.le],
          ← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.mpr hc0)]
        calc C_η = (γ₂ / 2) * (2 * C_η / γ₂) := by field_simp [hγ₂.ne']
          _ ≤ (γ₂ / 2) * √c := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      have hc56 : c ^ (-(5 / 6 : ℝ)) = liftEps c * c ^ (-(1 / 2 : ℝ)) := by
        unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
      calc |r_eta K c| ≤ C_η * K * c ^ (-(5 / 6 : ℝ)) := hr_eta_bd hK hc hcK
        _ = (C_η * c ^ (-(1 / 2 : ℝ))) * (K * liftEps c) := by rw [hc56]; ring
        _ ≤ (γ₂ / 2) * (K * liftEps c) := mul_le_mul_of_nonneg_right hc12 (mul_nonneg (by positivity) (liftEps_pos hc0).le)
  have hF_mass_floor : ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      let δ := K * liftEps c
      let F : ℝ → ℝ := fun u => S.G_N u - γ₁ * δ * S.H_N u + γ₂ * δ * ceSb b u +
        (-r_eta K c) * (airySeedG 0 (u : ℂ)).re
      let u₀ := S.lastNode - 2 * γ₁ * δ
      (Integrable F ∧ ∫ u : ℝ, F u = -v₀ * δ + (-r_eta K c)) ∧
      (∀ x ≥ |u₀| + ceBeta1 * δ / 2,
        (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
          ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2), F (-x + t) * bspline 4 (ceBeta1 * δ / 2) t) ∧
      (∀ j : Fin S.m₀, j.val + 1 < S.m₀ → ∀ u : ℝ, |u - S.nodes j| ≤ ceBeta1 * δ → δ / 2 ≤ F u) := by
    intro K c hK hc hcK hcδ
    have hc0 : 0 < c := by linarith [hc_η_2k.trans hc]
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hKδ_le : K * liftEps c ≤ δ₁_raw := by
      have hc13 : K / δ₁ ≤ c ^ (1 / 3 : ℝ) := by
        have h := Real.rpow_le_rpow (by positivity) hcδ (by norm_num : (0 : ℝ) ≤ 1 / 3)
        rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at h; simpa using h
      have h1 : K * liftEps c ≤ δ₁ := by
        rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
          ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
        exact ((div_le_iff₀ hδ₁).mp hc13).trans (mul_comm _ _).le
      exact h1.trans (min_le_left _ _)
    have hr_eps : |-r_eta K c| ≤ 1 * (K * liftEps c) := by rw [abs_neg, one_mul]; exact hr_eta_eps hK hc hcK
    have hs := hseed_body v₀ ⟨by positivity, le_rfl⟩ (K * liftEps c) ⟨by positivity, hKδ_le⟩ (-r_eta K c) hr_eps
    dsimp only at hs
    have hγ_def : (γ₂ * (1 + |airyDerivFirstZero|) + v₀) / S.I_N = γ₁ := rfl
    rw [hγ_def] at hs
    have hgg : ∀ u : ℝ, ceG1 (airyZero 1) u = (airySeedG 0 (u : ℂ)).re := fun u =>
      (congr_fun airySeedG0_eq_ceG1 u).symm
    exact ⟨⟨hs.2.1.1.congr (ae_of_all _ fun u => by simp [hgg]),
      by rw [← hs.2.1.2]; exact integral_congr_ae (ae_of_all _ fun u => by simp [hgg])⟩,
      fun x hx => (hs.2.2.1 x hx).trans_eq (setIntegral_congr_fun measurableSet_Icc fun t _ => by simp [hgg]),
      fun j hj u hu => by have h1 := hs.2.2.2 j hj u hu; simp [hgg] at h1 ⊢; exact h1⟩
  exact ⟨{
    hOdd := hOdd, S := S, hS_eq := hS_eq, b := b, hb := hb, hb_nodes := hb_nodes,
    γ₂ := γ₂, hγ₂ := hγ₂, v₀ := v₀, hv₀ := hv₀, γ₁ := γ₁, hγ₁ := hγ₁, hγ₁_eq := rfl,
    δ₁ := δ₁, hδ₁ := hδ₁, c₁ := c₁, hc₁ := hc₁, c₂ := c₂, hc₂ := hc₂,
    m₀ := m₀, M₀ := M₀, hm₀ := hm₀, hM₀ := hM₀, hmass := hmass,
    x₀ := x₀, B₀ := B₀, c₁' := c₁', d₀ := d₀, hx₀ := hx₀, hx₀B := hx₀B, hc₁' := hc₁', hd₀ := hd₀,
    hX_small := hX_small, hX_tail := hX_tail, hZ0_lap := hZ0_lap,
    CX_negG := CX_negG, CH_N := CH_N, CSb := CSb, Cg := Cg, CS0 := C_S0,
    hCX_negG_pos := hCX_negG_pos, hCH_N_pos := hCH_N_pos, hCSb_pos := hCSb_pos,
    hCg_pos := hCg_pos, hCS0_pos := hCS0_pos,
    hCX_negG := hCX_negG, hCH_N := hCH_N, hCSb := hCSb, hCg := hCg, hCS0 := hCS0_fam,
    M_K := ceHbMK v₀, r_eta := r_eta, c_η := c_η, C_η := C_η, hc_η := hc_η_2k, hC_η := hC_η,
    hM_K_def := fun _ _ => rfl,
    hM_K_bd := fun hK hc => ceHbMK_bd (by positivity) hm₀ hM₀ hmass (by linarith) hc,
    hr_eta_eq := hr_eta_eq, hr_eta_bd := hr_eta_bd, hr_eta_eps := hr_eta_eps,
    hD_neg_left := fun hK hc hcK hcδ u hu => ceHbDual_neg_left D S hS_last hS_GN hb hγ₁ hγ₂ hδ₁
      (min_le_right _ _) hK (hc_η_2k.trans hc) hcδ (hr_eta_half_γ₂ hK hc hcK) u hu,
    hF_mass_floor := hF_mass_floor,
    hS_dual_est := ceHbDual_dual_est (by positivity) hm₀ hM₀ hCS0_pos hmass hCS0_fam }⟩

/-- info: 'FormalResearch.SignUncertainty.ceHbDualScales_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ceHbDualScales_exists

end FormalResearch.SignUncertainty
