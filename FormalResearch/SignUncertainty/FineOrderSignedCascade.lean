module

public import FormalResearch.SignUncertainty.FineOrderSignedCore
public import FormalResearch.SignUncertainty.FineOrderSignedDiv

/-!
# Shared signed half-cubic reduction (`fs:half-cubic`): division cascade

Source: `CFT/common/fine_order_signed.tex`, Lemma FS.1 (`fs:half-cubic`), equations `(fs:principal)`,
`(fs:aux)`, and the Airy pairing assertions of Part (3). Phase-free; shared between Paper I
(`SignUncertainty`) and Paper II (`ModularBootstrap`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty.FineOrderSigned

open FormalResearch.SignUncertainty CtSd

/-! ### Contour IBP and composition holomorphicity helpers -/

/-! ### Algebraic scaling, parameter evaluation, and double-division cascade -/

lemma rpow_lam_rels {n : ℝ} (hn : 1 ≤ n) :
    let lam := n ^ (-(1 / 3 : ℝ))
    0 < lam ∧ lam ≤ 1 ∧ lam ^ 2 = n ^ (-(2 / 3 : ℝ)) ∧ lam ^ 3 = n⁻¹ ∧
      lam ^ 4 = n ^ (-(4 / 3 : ℝ)) ∧ lam ^ 5 = n ^ (-(5 / 3 : ℝ)) ∧
      n ^ (2 / 3 : ℝ) * lam ^ 2 = 1 := by
  have hn0 : 0 < n := by linarith
  have hlam0 : 0 < n ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hlam1 : n ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hp : ∀ k : ℕ, (n ^ (-(1 / 3 : ℝ))) ^ k = n ^ (-((k : ℝ) / 3)) := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; ring
  have hp2 := hp 2
  have hp3 := (hp 3).trans (by norm_num; exact Real.rpow_neg_one n)
  have hp4 := hp 4
  have hp5 := hp 5
  have hmul : n ^ (2 / 3 : ℝ) * (n ^ (-(1 / 3 : ℝ))) ^ 2 = 1 := by
    rw [hp2, ← Real.rpow_add hn0]; norm_num
  exact ⟨hlam0, hlam1, hp2, hp3, hp4, hp5, hmul⟩

lemma differentiableOn_eval_param {H : ℂ → ℂ → ℂ} {q : ℂ → ℂ} {R r_q r_a r_c M : ℝ}
    (hR : 0 < R) (hRr : R < r_q) (hcR : r_c < R)
    (hHq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => H ζ a) (ball 0 r_q))
    (hHa : ∀ ζ ∈ sphere (0 : ℂ) R, DifferentiableOn ℂ (H ζ) (ball 0 r_a))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) R, ∀ a ∈ ball (0 : ℂ) r_a, ‖H ζ a‖ ≤ M)
    (hq_diff : DifferentiableOn ℂ q (ball 0 r_a)) (hq_bd : ∀ a ∈ ball (0 : ℂ) r_a, ‖q a‖ ≤ r_c) :
    DifferentiableOn ℂ (fun a => H (q a) a) (ball 0 r_a) := by
  by_cases hra : 0 < r_a
  · have hpos : 0 < R - r_c := sub_pos.2 hcR
    have hM0 : 0 ≤ M := (norm_nonneg (H (R : ℂ) 0)).trans
      (hM (R : ℂ) (mem_sphere_zero_iff_norm.2 (by simp [abs_of_pos hR])) 0 (mem_ball_self hra))
    have heq : Set.EqOn (fun a => H (q a) a)
        (fun a => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - q a)⁻¹ • H ζ a) (ball 0 r_a) := by
      intro a ha
      have hqR : q a ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 ((hq_bd a ha).trans_lt hcR)
      have hci := (hHq a ha |>.mono (closedBall_subset_ball hRr)).circleIntegral_sub_inv_smul hqR
      dsimp only
      rw [hci, inv_smul_smul₀ (by simp [Real.pi_ne_zero])]
    refine (differentiableOn_circleIntegral_param (M := M / (R - r_c)) hR ?_ ?_ ?_).congr heq
    · intro a ha
      have hH_cont : ContinuousOn (fun ζ => H ζ a) (sphere 0 R) :=
        (hHq a ha).continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hRr))
      refine ((continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => sub_ne_zero.2 fun h0 => by
        have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
        have h1 := hq_bd a ha; change ζ = q a at h0; rw [← h0, hζR] at h1; linarith).smul hH_cont
    · intro ζ hζ
      have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
      have hSub : DifferentiableOn ℂ (fun a : ℂ => ζ - q a) (ball 0 r_a) :=
        (differentiableOn_const ζ).sub hq_diff
      exact (hSub.inv fun a ha => sub_ne_zero.2 fun h0 => by
        have h1 := hq_bd a ha; rw [← h0, hζR] at h1; linarith).smul (hHa ζ hζ)
    · intro ζ hζ a ha
      have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
      have h1 : R - r_c ≤ ‖ζ - q a‖ := by linarith [norm_sub_norm_le ζ (q a), hq_bd a ha]
      rw [norm_smul, norm_inv, div_eq_inv_mul]
      exact mul_le_mul (inv_anti₀ hpos h1) (hM ζ hζ a ha) (norm_nonneg _) (inv_nonneg.2 hpos.le)
  · rw [ball_eq_empty.2 (not_lt.1 hra)]; exact fun _ hx => False.elim hx

/-! ### Amplitude structure and double-division cascade (`fs:principal`, `fs:aux`) -/

/-- Analytic amplitude data `B_n(s, a) = E_n(s^2, a) + i s O_n(s^2, a)` and phase shift
`â(a) = a + n⁻¹ ψ_n(a)` for `fs:half-cubic`. -/
structure HalfCubicData where
  r_q : ℝ
  r_a : ℝ
  s₁ : ℝ
  M_E : ℝ
  M_O : ℝ
  M_ψ : ℝ
  hr_q : 0 < r_q
  hr_a : 0 < r_a
  hs₁ : 0 < s₁
  hs₁_sq : s₁ ^ 2 < r_q
  hM_E : 0 ≤ M_E
  hM_O : 0 ≤ M_O
  hM_ψ : 0 ≤ M_ψ
  E : ℝ → ℂ → ℂ → ℂ
  O : ℝ → ℂ → ℂ → ℂ
  ψ : ℝ → ℂ → ℂ
  hE_q : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) r_a → DifferentiableOn ℂ (fun q => E n q a) (ball 0 r_q)
  hE_a : ∀ n q, 1 ≤ n → q ∈ ball (0 : ℂ) r_q → DifferentiableOn ℂ (fun a => E n q a) (ball 0 r_a)
  hE_bd : ∀ n q a, 1 ≤ n → q ∈ ball (0 : ℂ) r_q → a ∈ ball (0 : ℂ) r_a → ‖E n q a‖ ≤ M_E
  hE_real : ∀ n (q a : ℝ), 1 ≤ n → |q| < r_q → |a| < r_a → (E n q a).im = 0
  hO_q : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) r_a → DifferentiableOn ℂ (fun q => O n q a) (ball 0 r_q)
  hO_a : ∀ n q, 1 ≤ n → q ∈ ball (0 : ℂ) r_q → DifferentiableOn ℂ (fun a => O n q a) (ball 0 r_a)
  hO_bd : ∀ n q a, 1 ≤ n → q ∈ ball (0 : ℂ) r_q → a ∈ ball (0 : ℂ) r_a → ‖O n q a‖ ≤ M_O
  hO_real : ∀ n (q a : ℝ), 1 ≤ n → |q| < r_q → |a| < r_a → (O n q a).im = 0
  hψ_a : ∀ n, 1 ≤ n → DifferentiableOn ℂ (ψ n) (ball 0 r_a)
  hψ_bd : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) r_a → ‖ψ n a‖ ≤ M_ψ
  hψ_real : ∀ n (a : ℝ), 1 ≤ n → |a| < r_a → (ψ n a).im = 0

/-- Shifted parameter `â_n(a) = a + n⁻¹ ψ_n(a)`. -/
noncomputable def HalfCubicData.aHat (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ :=
  a + (n⁻¹ : ℂ) * d.ψ n a

/-- Half-cubic variable `u = 2^{-2/3} n^{2/3} Re(â_n(a))` for real `a`. -/
noncomputable def HalfCubicData.uReal (d : HalfCubicData) (n a : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(2 / 3 : ℝ)) * n ^ (2 / 3 : ℝ) * (d.aHat n a).re

/-- Full analytic amplitude `B_n(s, a) = E_n(s^2, a) + i s O_n(s^2, a)`. -/
noncomputable def HalfCubicData.B (d : HalfCubicData) (n : ℝ) (a s : ℂ) : ℂ :=
  d.E n (s ^ 2) a + Complex.I * s * d.O n (s ^ 2) a

/-- Shrunk complex parameter radius on which `|â_n(a)| ≤ s₁^2 / 16` holds uniformly. -/
noncomputable def HalfCubicData.rAShrunk (d : HalfCubicData) : ℝ := min (d.r_a / 2) (d.s₁ ^ 2 / 32)

/-- Threshold `n₀` above which `s₁ n^{1/3} ≥ 1` and `n⁻¹ M_ψ ≤ s₁^2 / 32`. -/
noncomputable def HalfCubicData.n₀ (d : HalfCubicData) : ℝ :=
  max 1 (max (d.s₁⁻¹ ^ 3) (32 * d.M_ψ / d.s₁ ^ 2 + 1))

lemma HalfCubicData.rAShrunk_pos (d : HalfCubicData) : 0 < d.rAShrunk :=
  lt_min (half_pos d.hr_a) (div_pos (sq_pos_of_pos d.hs₁) (by norm_num))

lemma HalfCubicData.rAShrunk_lt (d : HalfCubicData) : d.rAShrunk < d.r_a :=
  (min_le_left _ _).trans_lt (half_lt_self d.hr_a)

lemma HalfCubicData.n₀_ge_one (d : HalfCubicData) : 1 ≤ d.n₀ := le_max_left _ _

namespace HalfCubicInternal

noncomputable def δq (d : HalfCubicData) : ℝ := (d.r_q - d.s₁ ^ 2) / 6
noncomputable def rsSq (d : HalfCubicData) : ℝ := d.s₁ ^ 2 + δq d
noncomputable def Rs (d : HalfCubicData) : ℝ := Real.sqrt (rsSq d)
noncomputable def r3 (d : HalfCubicData) : ℝ := d.s₁ ^ 2 + 2 * δq d
noncomputable def r2 (d : HalfCubicData) : ℝ := d.s₁ ^ 2 + 3 * δq d
noncomputable def r1 (d : HalfCubicData) : ℝ := d.s₁ ^ 2 + 4 * δq d
noncomputable def r0 (d : HalfCubicData) : ℝ := d.s₁ ^ 2 + 5 * δq d
noncomputable def rc (d : HalfCubicData) : ℝ := d.s₁ ^ 2 / 16

lemma radii_chain (d : HalfCubicData) :
    0 < δq d ∧ 0 ≤ rc d ∧ rc d ≤ d.s₁ ^ 2 ∧ d.s₁ ^ 2 < rsSq d ∧
      rsSq d < r3 d ∧ r3 d < r2 d ∧ r2 d < r1 d ∧ r1 d < r0 d ∧ r0 d < d.r_q ∧
      d.s₁ < Rs d ∧ Rs d ^ 2 = rsSq d := by
  have hδ : 0 < δq d := by unfold δq; linarith [d.hs₁_sq]
  have hs0 : 0 ≤ rc d := by unfold rc; positivity
  have hs1 : rc d ≤ d.s₁ ^ 2 := by unfold rc; nlinarith [sq_nonneg d.s₁]
  have hr_sq : Rs d ^ 2 = rsSq d := Real.sq_sqrt (by unfold rsSq; positivity)
  have hss : d.s₁ < Rs d :=
    lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) (by rw [hr_sq]; unfold rsSq; linarith)
  refine ⟨hδ, hs0, hs1, ?_, ?_, ?_, ?_, ?_, ?_, hss, hr_sq⟩
  · unfold rsSq δq; linarith [d.hs₁_sq]
  · unfold rsSq r3 δq; linarith [d.hs₁_sq]
  · unfold r3 r2 δq; linarith [d.hs₁_sq]
  · unfold r2 r1 δq; linarith [d.hs₁_sq]
  · unfold r1 r0 δq; linarith [d.hs₁_sq]
  · unfold r0 δq; linarith [d.hs₁_sq]

lemma aHat_facts (d : HalfCubicData) {n : ℝ} (hn : d.n₀ ≤ n) :
    1 ≤ n ∧ d.s₁⁻¹ ^ 3 ≤ n ∧ 32 * d.M_ψ / d.s₁ ^ 2 + 1 ≤ n ∧
    DifferentiableOn ℂ (d.aHat n) (ball 0 d.rAShrunk) ∧
    (∀ a ∈ ball (0 : ℂ) d.rAShrunk, a ∈ ball (0 : ℂ) d.r_a ∧ ‖d.aHat n a‖ ≤ rc d) ∧
    (∀ a : ℝ, |a| < d.rAShrunk → (d.aHat n a).im = 0) := by
  have hn1 : 1 ≤ n := d.n₀_ge_one.trans hn
  have hns : d.s₁⁻¹ ^ 3 ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnψ : 32 * d.M_ψ / d.s₁ ^ 2 + 1 ≤ n :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hsub : ball (0 : ℂ) d.rAShrunk ⊆ ball (0 : ℂ) d.r_a :=
    ball_subset_ball d.rAShrunk_lt.le
  have hdiff : DifferentiableOn ℂ (d.aHat n) (ball 0 d.rAShrunk) :=
    differentiableOn_id.add ((differentiableOn_const _).mul ((d.hψ_a n hn1).mono hsub))
  have hbd : ∀ a ∈ ball (0 : ℂ) d.rAShrunk, a ∈ ball (0 : ℂ) d.r_a ∧ ‖d.aHat n a‖ ≤ rc d := by
    intro a ha
    have ha_ra : a ∈ ball (0 : ℂ) d.r_a := hsub ha
    have ha_s : ‖a‖ ≤ d.s₁ ^ 2 / 32 :=
      (mem_ball_zero_iff.1 ha).le.trans (min_le_right _ _)
    have hn_pos : 0 < n := by linarith
    have hψ_term : ‖(n⁻¹ : ℂ) * d.ψ n a‖ ≤ d.s₁ ^ 2 / 32 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn_pos.le]
      have hψ1 : n⁻¹ * d.M_ψ ≤ d.s₁ ^ 2 / 32 := by
        have h1 : 32 * d.M_ψ / d.s₁ ^ 2 ≤ n := by linarith
        have h2 := (div_le_iff₀ (sq_pos_of_pos d.hs₁)).1 h1
        rw [inv_mul_eq_div, div_le_div_iff₀ hn_pos (by norm_num)]; linarith
      exact (mul_le_mul_of_nonneg_left (d.hψ_bd n a hn1 ha_ra) (inv_nonneg.2 hn_pos.le)).trans hψ1
    refine ⟨ha_ra, ?_⟩
    calc ‖d.aHat n a‖ ≤ ‖a‖ + ‖(n⁻¹ : ℂ) * d.ψ n a‖ := norm_add_le _ _
      _ ≤ d.s₁ ^ 2 / 32 + d.s₁ ^ 2 / 32 := add_le_add ha_s hψ_term
      _ = rc d := by unfold rc; ring
  have hreal : ∀ a : ℝ, |a| < d.rAShrunk → (d.aHat n a).im = 0 := fun a ha => by
    have har : |a| < d.r_a := ha.trans d.rAShrunk_lt
    unfold HalfCubicData.aHat
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.inv_im,
      Complex.normSq_ofReal, zero_div, neg_zero, zero_mul, add_zero,
      d.hψ_real n a hn1 har, mul_zero]
  exact ⟨hn1, hns, hnψ, hdiff, hbd, hreal⟩

lemma uReal_facts (d : HalfCubicData) {n a : ℝ} (hn : d.n₀ ≤ n) (ha : |a| < d.rAShrunk) :
    let lam := n ^ (-(1 / 3 : ℝ))
    let R := d.s₁ / lam
    let R₀ := Rs d / lam
    1 ≤ R ∧ R < R₀ ∧ kap * |d.uReal n a| ≤ R ^ 2 / 16 ∧
      (kap : ℂ) * (d.uReal n a : ℂ) * lam ^ 2 = d.aHat n a := by
  have ⟨hn1, hns, _, _, hbd, hreal⟩ := aHat_facts d hn
  have ⟨hl0, _, hl2, _, _, _, hmul⟩ := rpow_lam_rels hn1
  have ⟨_, _, _, _, _, _, _, _, _, hss, _⟩ := radii_chain d
  have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) d.rAShrunk := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha
  have hn0 : 0 < n := by linarith
  have hR1 : 1 ≤ d.s₁ / n ^ (-(1 / 3 : ℝ)) := by
    have hs3 : (d.s₁⁻¹ : ℝ) ≤ n ^ (1 / 3 : ℝ) := by
      have h1 : (d.s₁⁻¹ : ℝ) ^ (3 : ℕ) ≤ (n ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hn0.le]; norm_num; rwa [← inv_pow]
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    have hlam_inv : (n ^ (-(1 / 3 : ℝ)))⁻¹ = n ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_neg hn0.le]; congr 1; norm_num
    rw [div_eq_mul_inv, hlam_inv]
    calc 1 = d.s₁ * d.s₁⁻¹ := (mul_inv_cancel₀ d.hs₁.ne').symm
      _ ≤ d.s₁ * n ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hs3 d.hs₁.le
  have hRR : d.s₁ / n ^ (-(1 / 3 : ℝ)) < Rs d / n ^ (-(1 / 3 : ℝ)) :=
    div_lt_div_of_pos_right hss hl0
  have hkap : (kap : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) := rfl
  have h2pow : (2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add two_pos]; norm_num
  have ha_re_eq : ((d.aHat n (a : ℂ)).re : ℂ) = d.aHat n a :=
    Complex.ext rfl (hreal a ha).symm
  have hUR : kap * |d.uReal n a| ≤ (d.s₁ / n ^ (-(1 / 3 : ℝ))) ^ 2 / 16 := by
    have hku : kap * d.uReal n a = n ^ (2 / 3 : ℝ) * (d.aHat n a).re := by
      unfold HalfCubicData.uReal
      calc kap * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * n ^ (2 / 3 : ℝ) * (d.aHat n a).re)
          = ((2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ))) * n ^ (2 / 3 : ℝ) * (d.aHat n a).re := by
            rw [hkap]; ring
        _ = n ^ (2 / 3 : ℝ) * (d.aHat n a).re := by rw [h2pow, one_mul]
    rw [← abs_of_pos kap_pos, ← abs_mul, hku, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
    have ha_norm : |(d.aHat n a).re| ≤ d.s₁ ^ 2 / 16 :=
      (Complex.abs_re_le_norm _).trans (hbd a ha_ball).2
    calc n ^ (2 / 3 : ℝ) * |(d.aHat n a).re|
        ≤ n ^ (2 / 3 : ℝ) * (d.s₁ ^ 2 / 16) := mul_le_mul_of_nonneg_left ha_norm (by positivity)
      _ = (d.s₁ / n ^ (-(1 / 3 : ℝ))) ^ 2 / 16 := by
          rw [div_pow, div_div]; field_simp [hl0.ne']
          calc n ^ (2 / 3 : ℝ) * d.s₁ ^ 2 * (n ^ (-(1 / 3 : ℝ))) ^ 2
              = (n ^ (2 / 3 : ℝ) * (n ^ (-(1 / 3 : ℝ))) ^ 2) * d.s₁ ^ 2 := by ring
            _ = d.s₁ ^ 2 := by rw [hmul, one_mul]
  set lam : ℝ := n ^ (-(1 / 3 : ℝ))
  have hC : (kap : ℂ) * (d.uReal n a : ℂ) * (lam : ℂ) ^ 2 = d.aHat n a := by
    have hkR : kap * d.uReal n a * lam ^ 2 = (d.aHat n a).re := by
      unfold HalfCubicData.uReal
      calc kap * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * n ^ (2 / 3 : ℝ) * (d.aHat n a).re) * lam ^ 2
          = ((2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ))) *
              (n ^ (2 / 3 : ℝ) * lam ^ 2) * (d.aHat n a).re := by
            rw [hkap]; ring
        _ = (d.aHat n a).re := by rw [h2pow, hmul, one_mul, one_mul]
    rw [← ha_re_eq, ← hkR]; push_cast; ring
  exact ⟨hR1, hRR, hUR, hC⟩

noncomputable def A0 (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ := d.E n (-d.aHat n a) a
noncomputable def A1 (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ := d.O n (-d.aHat n a) a
noncomputable def Qe (d : HalfCubicData) (n : ℝ) (q a : ℂ) : ℂ :=
  divQ (fun ζ => d.E n ζ a) (r0 d) (-d.aHat n a) q
noncomputable def Qo (d : HalfCubicData) (n : ℝ) (q a : ℂ) : ℂ :=
  divQ (fun ζ => d.O n ζ a) (r0 d) (-d.aHat n a) q
noncomputable def Qe0 (d : HalfCubicData) (n : ℝ) (q a : ℂ) : ℂ :=
  divQ (fun ζ => Qe d n ζ a) (r1 d) 0 q
noncomputable def De (d : HalfCubicData) (n : ℝ) (q a : ℂ) : ℂ :=
  -(3 / 2 : ℂ) * Qo d n q a - 2 * q * deriv (fun ζ => Qo d n ζ a) q
noncomputable def Do (d : HalfCubicData) (n : ℝ) (q a : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Qe0 d n q a + 2 * deriv (fun ζ => Qe d n ζ a) q
noncomputable def D0 (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ := De d n (-d.aHat n a) a
noncomputable def D1 (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ := Do d n (-d.aHat n a) a
noncomputable def Re2 (d : HalfCubicData) (n : ℝ) (q a : ℂ) : ℂ :=
  divQ (fun ζ => De d n ζ a) (r2 d) (-d.aHat n a) q
noncomputable def Ro2 (d : HalfCubicData) (n : ℝ) (q a : ℂ) : ℂ :=
  divQ (fun ζ => Do d n ζ a) (r2 d) (-d.aHat n a) q

noncomputable def MQe (d : HalfCubicData) : ℝ := r0 d * d.M_E / (r0 d - r1 d) ^ 2
noncomputable def MQo (d : HalfCubicData) : ℝ := r0 d * d.M_O / (r0 d - r1 d) ^ 2
noncomputable def MQeD (d : HalfCubicData) : ℝ := r1 d * MQe d / (r1 d - r2 d) ^ 2
noncomputable def MQoD (d : HalfCubicData) : ℝ := r1 d * MQo d / (r1 d - r2 d) ^ 2
noncomputable def MQe0 (d : HalfCubicData) : ℝ := r1 d * MQe d / (r1 d - r2 d) ^ 2
noncomputable def MDe (d : HalfCubicData) : ℝ := (3 / 2) * MQo d + 2 * r2 d * MQoD d
noncomputable def MDo (d : HalfCubicData) : ℝ := (1 / 2) * MQe0 d + 2 * MQeD d
noncomputable def MRe (d : HalfCubicData) : ℝ := r2 d * MDe d / (r2 d - r3 d) ^ 2
noncomputable def MRo (d : HalfCubicData) : ℝ := r2 d * MDo d / (r2 d - r3 d) ^ 2
noncomputable def MReD (d : HalfCubicData) : ℝ := r3 d * MRe d / (r3 d - rsSq d) ^ 2
noncomputable def MRoD (d : HalfCubicData) : ℝ := r3 d * MRo d / (r3 d - rsSq d) ^ 2

lemma c_ball (d : HalfCubicData) {n : ℝ} (hn : d.n₀ ≤ n) {a : ℂ}
    (ha : a ∈ ball (0 : ℂ) d.rAShrunk) :
    ‖-d.aHat n a‖ ≤ rc d ∧ (-d.aHat n a) ∈ ball (0 : ℂ) (r3 d) ∧
      (-d.aHat n a) ∈ ball (0 : ℂ) (r2 d) ∧ (-d.aHat n a) ∈ ball (0 : ℂ) (r1 d) ∧
      (-d.aHat n a) ∈ ball (0 : ℂ) (r0 d) ∧ (-d.aHat n a) ∈ ball (0 : ℂ) d.r_q := by
  have ⟨_, _, _, _, hbd, _⟩ := aHat_facts d hn
  have hnc : ‖-d.aHat n a‖ ≤ rc d := by rw [norm_neg]; exact (hbd a ha).2
  have ⟨_, _, h1, h2, h3, h4, h5, h6, h7, _, _⟩ := radii_chain d
  refine ⟨hnc, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mem_ball_zero_iff] <;> linarith

lemma A0_A1_facts (d : HalfCubicData) {n : ℝ} (hn : d.n₀ ≤ n) :
    DifferentiableOn ℂ (A0 d n) (ball 0 d.rAShrunk) ∧
    DifferentiableOn ℂ (A1 d n) (ball 0 d.rAShrunk) ∧
    (∀ a ∈ ball (0 : ℂ) d.rAShrunk, ‖A0 d n a‖ ≤ d.M_E ∧ ‖A1 d n a‖ ≤ d.M_O) ∧
    (∀ a : ℝ, |a| < d.rAShrunk → (A0 d n a).im = 0 ∧ (A1 d n a).im = 0) := by
  have ⟨hn1, _, _, hdiff_ah, hbd_ah, hreal_ah⟩ := aHat_facts d hn
  have ⟨_, hs0, h1, h2, h3, h4, h5, h6, h7, _, _⟩ := radii_chain d
  have hr0_pos : 0 < r0 d := by linarith
  have hrc0 : rc d < r0 d := by linarith
  have hsub : ball (0 : ℂ) d.rAShrunk ⊆ ball (0 : ℂ) d.r_a :=
    ball_subset_ball d.rAShrunk_lt.le
  have hc_neg_diff : DifferentiableOn ℂ (fun a => -d.aHat n a) (ball 0 d.rAShrunk) := hdiff_ah.neg
  have hc_neg_bd : ∀ a ∈ ball (0 : ℂ) d.rAShrunk, ‖-d.aHat n a‖ ≤ rc d :=
    fun a ha => (c_ball d hn ha).1
  have hA0_diff : DifferentiableOn ℂ (A0 d n) (ball 0 d.rAShrunk) :=
    differentiableOn_eval_param hr0_pos h7 hrc0
      (fun a ha => d.hE_q n a hn1 (hsub ha))
      (fun ζ hζ => (d.hE_a n ζ hn1 (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7))).mono hsub)
      (fun ζ hζ a ha => d.hE_bd n ζ a hn1
        (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7)) (hsub ha))
      hc_neg_diff hc_neg_bd
  have hA1_diff : DifferentiableOn ℂ (A1 d n) (ball 0 d.rAShrunk) :=
    differentiableOn_eval_param hr0_pos h7 hrc0
      (fun a ha => d.hO_q n a hn1 (hsub ha))
      (fun ζ hζ => (d.hO_a n ζ hn1 (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7))).mono hsub)
      (fun ζ hζ a ha => d.hO_bd n ζ a hn1
        (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7)) (hsub ha))
      hc_neg_diff hc_neg_bd
  have hbd : ∀ a ∈ ball (0 : ℂ) d.rAShrunk, ‖A0 d n a‖ ≤ d.M_E ∧ ‖A1 d n a‖ ≤ d.M_O := fun a ha =>
    ⟨d.hE_bd n _ a hn1 (c_ball d hn ha).2.2.2.2.2 (hsub ha),
      d.hO_bd n _ a hn1 (c_ball d hn ha).2.2.2.2.2 (hsub ha)⟩
  have hreal : ∀ a : ℝ, |a| < d.rAShrunk → (A0 d n a).im = 0 ∧ (A1 d n a).im = 0 := fun a ha => by
    have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) d.rAShrunk := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha
    have har : |a| < d.r_a := ha.trans d.rAShrunk_lt
    have hcr : |-(d.aHat n a).re| < d.r_q := by
      have hre := (c_ball d hn ha_ball).2.2.2.2.2
      rw [mem_ball_zero_iff] at hre
      calc |-(d.aHat n a).re| = |(d.aHat n a).re| := abs_neg _
        _ ≤ ‖d.aHat n a‖ := Complex.abs_re_le_norm _
        _ = ‖-d.aHat n a‖ := (norm_neg _).symm
        _ < d.r_q := hre
    have hce : ((-(d.aHat n a).re : ℝ) : ℂ) = -d.aHat n a :=
      Complex.ext rfl (by simp [hreal_ah a ha])
    refine ⟨?_, ?_⟩
    · unfold A0; rw [← hce]; exact d.hE_real n (-(d.aHat n a).re) a hn1 hcr har
    · unfold A1; rw [← hce]; exact d.hO_real n (-(d.aHat n a).re) a hn1 hcr har
  exact ⟨hA0_diff, hA1_diff, hbd, hreal⟩

lemma Q_facts (d : HalfCubicData) {n : ℝ} (hn : d.n₀ ≤ n) :
    (∀ a ∈ ball (0 : ℂ) d.rAShrunk,
      DifferentiableOn ℂ (fun q => Qe d n q a) (ball 0 (r0 d)) ∧
      DifferentiableOn ℂ (fun q => Qo d n q a) (ball 0 (r0 d)) ∧
      (∀ q ∈ closedBall (0 : ℂ) (r1 d), ‖Qe d n q a‖ ≤ MQe d ∧ ‖Qo d n q a‖ ≤ MQo d) ∧
      (∀ q ∈ closedBall (0 : ℂ) (r2 d), ‖deriv (fun ζ => Qe d n ζ a) q‖ ≤ MQeD d ∧
        ‖deriv (fun ζ => Qo d n ζ a) q‖ ≤ MQoD d)) ∧
    (∀ q ∈ closedBall (0 : ℂ) (r1 d),
      DifferentiableOn ℂ (fun a => Qe d n q a) (ball 0 d.rAShrunk) ∧
      DifferentiableOn ℂ (fun a => Qo d n q a) (ball 0 d.rAShrunk)) ∧
    (∀ (q a : ℝ), |q| < r0 d → |a| < d.rAShrunk →
      (Qe d n q a).im = 0 ∧ (Qo d n q a).im = 0) := by
  have ⟨hn1, _, _, hdiff_ah, hbd_ah, hreal_ah⟩ := aHat_facts d hn
  have ⟨_, _, h1, h2, h3, h4, h5, h6, h7, _, _⟩ := radii_chain d
  have hr0_pos : 0 < r0 d := by linarith
  have hr1_pos : 0 < r1 d := by linarith
  have hsub : ball (0 : ℂ) d.rAShrunk ⊆ ball (0 : ℂ) d.r_a := ball_subset_ball d.rAShrunk_lt.le
  have hpart1 : ∀ a ∈ ball (0 : ℂ) d.rAShrunk,
      DifferentiableOn ℂ (fun q => Qe d n q a) (ball 0 (r0 d)) ∧
      DifferentiableOn ℂ (fun q => Qo d n q a) (ball 0 (r0 d)) ∧
      (∀ q ∈ closedBall (0 : ℂ) (r1 d), ‖Qe d n q a‖ ≤ MQe d ∧ ‖Qo d n q a‖ ≤ MQo d) ∧
      (∀ q ∈ closedBall (0 : ℂ) (r2 d), ‖deriv (fun ζ => Qe d n ζ a) q‖ ≤ MQeD d ∧
        ‖deriv (fun ζ => Qo d n ζ a) q‖ ≤ MQoD d) := by
    intro a ha
    have hc0 := (c_ball d hn ha).2.2.2.2.1
    have hqE := differentiableOn_divQ_fst hr0_pos h7 (d.hE_q n a hn1 (hsub ha)) hc0
    have hqO := differentiableOn_divQ_fst hr0_pos h7 (d.hO_q n a hn1 (hsub ha)) hc0
    have hbdQ : ∀ q ∈ closedBall (0 : ℂ) (r1 d), ‖Qe d n q a‖ ≤ MQe d ∧ ‖Qo d n q a‖ ≤ MQo d :=
      fun q hq => by
      have hqr : ‖q‖ ≤ r1 d := mem_closedBall_zero_iff.1 hq
      have hcr : ‖-d.aHat n a‖ ≤ r1 d := (c_ball d hn ha).1.trans (by linarith)
      refine ⟨norm_divQ_le hr0_pos h6 (fun ζ hζ => d.hE_bd n ζ a hn1
          (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7)) (hsub ha)) hcr hqr,
        norm_divQ_le hr0_pos h6 (fun ζ hζ => d.hO_bd n ζ a hn1
          (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7)) (hsub ha)) hcr hqr⟩
    have hbdQD : ∀ q ∈ closedBall (0 : ℂ) (r2 d), ‖deriv (fun ζ => Qe d n ζ a) q‖ ≤ MQeD d ∧
        ‖deriv (fun ζ => Qo d n ζ a) q‖ ≤ MQoD d := fun q hq => by
      have hqr : ‖q‖ ≤ r2 d := mem_closedBall_zero_iff.1 hq
      refine ⟨cauchy_deriv_bound (by linarith) h5 h6 hqE hqr (fun ζ hζ =>
          (hbdQ ζ (sphere_subset_closedBall hζ)).1),
        cauchy_deriv_bound (by linarith) h5 h6 hqO hqr (fun ζ hζ =>
          (hbdQ ζ (sphere_subset_closedBall hζ)).2)⟩
    exact ⟨hqE, hqO, hbdQ, hbdQD⟩
  have hpart2 : ∀ q ∈ closedBall (0 : ℂ) (r1 d),
      DifferentiableOn ℂ (fun a => Qe d n q a) (ball 0 d.rAShrunk) ∧
      DifferentiableOn ℂ (fun a => Qo d n q a) (ball 0 d.rAShrunk) := fun q hq => by
    have hqr : ‖q‖ ≤ r1 d := mem_closedBall_zero_iff.1 hq
    refine ⟨differentiableOn_divQ_param hr0_pos h7 h6
        (fun a ha => d.hE_q n a hn1 (hsub ha))
        (fun ζ hζ => (d.hE_a n ζ hn1 (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7))).mono hsub)
        (fun ζ hζ a ha => d.hE_bd n ζ a hn1 (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7)) (hsub ha))
        hdiff_ah.neg (fun a ha => (c_ball d hn ha).1.trans (by linarith))
        (differentiableOn_const q) (fun _ _ => hqr),
      differentiableOn_divQ_param hr0_pos h7 h6
        (fun a ha => d.hO_q n a hn1 (hsub ha))
        (fun ζ hζ => (d.hO_a n ζ hn1 (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7))).mono hsub)
        (fun ζ hζ a ha => d.hO_bd n ζ a hn1 (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h7)) (hsub ha))
        hdiff_ah.neg (fun a ha => (c_ball d hn ha).1.trans (by linarith))
        (differentiableOn_const q) (fun _ _ => hqr)⟩
  have hpart3 : ∀ (q a : ℝ), |q| < r0 d → |a| < d.rAShrunk →
      (Qe d n q a).im = 0 ∧ (Qo d n q a).im = 0 := fun q a hq ha => by
    have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) d.rAShrunk := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha
    have har : |a| < d.r_a := ha.trans d.rAShrunk_lt
    have hcr : |-(d.aHat n a).re| < r0 d := by
      have hre := (c_ball d hn ha_ball).2.2.2.2.1
      rw [mem_ball_zero_iff] at hre
      calc |-(d.aHat n a).re| = |(d.aHat n a).re| := abs_neg _
        _ ≤ ‖d.aHat n a‖ := Complex.abs_re_le_norm _
        _ = ‖-d.aHat n a‖ := (norm_neg _).symm
        _ < r0 d := hre
    have hce : ((-(d.aHat n a).re : ℝ) : ℂ) = -d.aHat n a :=
      Complex.ext rfl (by simp [hreal_ah a ha])
    refine ⟨?_, ?_⟩
    · unfold Qe; rw [← hce]
      exact divQ_im_zero hr0_pos h7 (d.hE_q n a hn1 (hsub ha_ball))
        (fun x hx => d.hE_real n x a hn1 hx har) hcr hq
    · unfold Qo; rw [← hce]
      exact divQ_im_zero hr0_pos h7 (d.hO_q n a hn1 (hsub ha_ball))
        (fun x hx => d.hO_real n x a hn1 hx har) hcr hq
  exact ⟨hpart1, hpart2, hpart3⟩

lemma D_facts (d : HalfCubicData) {n : ℝ} (hn : d.n₀ ≤ n) :
    (∀ a ∈ ball (0 : ℂ) d.rAShrunk,
      DifferentiableOn ℂ (fun q => De d n q a) (ball 0 (r1 d)) ∧
      DifferentiableOn ℂ (fun q => Do d n q a) (ball 0 (r1 d)) ∧
      (∀ q ∈ closedBall (0 : ℂ) (r2 d), ‖De d n q a‖ ≤ MDe d ∧ ‖Do d n q a‖ ≤ MDo d)) ∧
    DifferentiableOn ℂ (D0 d n) (ball 0 d.rAShrunk) ∧
    DifferentiableOn ℂ (D1 d n) (ball 0 d.rAShrunk) ∧
    (∀ a ∈ ball (0 : ℂ) d.rAShrunk, ‖D0 d n a‖ ≤ MDe d ∧ ‖D1 d n a‖ ≤ MDo d) ∧
    (∀ a : ℝ, |a| < d.rAShrunk → (D0 d n a).im = 0 ∧ (D1 d n a).im = 0) := by
  have ⟨hQ1, hQ2, hQ3⟩ := Q_facts d hn
  have ⟨_, _, h1, h2, h3, h4, h5, h6, h7, _, _⟩ := radii_chain d
  have hr1_pos : 0 < r1 d := by linarith
  have hr2_pos : 0 < r2 d := by linarith
  have hc_bd : ∀ a ∈ ball (0 : ℂ) d.rAShrunk, ‖-d.aHat n a‖ ≤ rc d := fun a ha => (c_ball d hn ha).1
  have hrc_r2 : rc d < r2 d := by linarith
  have ⟨_, _, _, hdiff_ah, _, hreal_ah⟩ := aHat_facts d hn
  have hpart1 : ∀ a ∈ ball (0 : ℂ) d.rAShrunk,
      DifferentiableOn ℂ (fun q => De d n q a) (ball 0 (r1 d)) ∧
      DifferentiableOn ℂ (fun q => Do d n q a) (ball 0 (r1 d)) ∧
      (∀ q ∈ closedBall (0 : ℂ) (r2 d), ‖De d n q a‖ ≤ MDe d ∧ ‖Do d n q a‖ ≤ MDo d) := by
    intro a ha
    obtain ⟨hqE, hqO, hbdQ, hbdQD⟩ := hQ1 a ha
    have hqE_an : AnalyticOnNhd ℂ (fun ζ => Qe d n ζ a) (ball 0 (r0 d)) :=
      hqE.analyticOnNhd isOpen_ball
    have hqO_an : AnalyticOnNhd ℂ (fun ζ => Qo d n ζ a) (ball 0 (r0 d)) :=
      hqO.analyticOnNhd isOpen_ball
    have hdE_diff : DifferentiableOn ℂ (fun q => deriv (fun ζ => Qe d n ζ a) q) (ball 0 (r1 d)) :=
      hqE_an.deriv.differentiableOn.mono (ball_subset_ball h6.le)
    have hdO_diff : DifferentiableOn ℂ (fun q => deriv (fun ζ => Qo d n ζ a) q) (ball 0 (r1 d)) :=
      hqO_an.deriv.differentiableOn.mono (ball_subset_ball h6.le)
    have hqe0_diff : DifferentiableOn ℂ (fun q => Qe0 d n q a) (ball 0 (r1 d)) :=
      differentiableOn_divQ_fst hr1_pos h6 hqE (mem_ball_self hr1_pos)
    have hDe_diff : DifferentiableOn ℂ (fun q => De d n q a) (ball 0 (r1 d)) :=
      ((differentiableOn_const _).mul (hqO.mono (ball_subset_ball h6.le))).sub
        (((differentiableOn_const _).mul differentiableOn_id).mul hdO_diff)
    have hDo_diff : DifferentiableOn ℂ (fun q => Do d n q a) (ball 0 (r1 d)) :=
      ((differentiableOn_const _).mul hqe0_diff).add ((differentiableOn_const _).mul hdE_diff)
    have hbdD : ∀ q ∈ closedBall (0 : ℂ) (r2 d), ‖De d n q a‖ ≤ MDe d ∧ ‖Do d n q a‖ ≤ MDo d :=
      fun q hq => by
      have hq1 : q ∈ closedBall (0 : ℂ) (r1 d) := closedBall_subset_closedBall h5.le hq
      have hqr : ‖q‖ ≤ r2 d := mem_closedBall_zero_iff.1 hq
      have hqe0_bd : ‖Qe0 d n q a‖ ≤ MQe0 d :=
        norm_divQ_le hr1_pos h5 (fun ζ hζ => (hbdQ ζ (sphere_subset_closedBall hζ)).1)
          (by rw [norm_zero]; linarith) hqr
      refine ⟨?_, ?_⟩
      · unfold De MDe
        calc ‖-(3 / 2 : ℂ) * Qo d n q a - 2 * q * deriv (fun ζ => Qo d n ζ a) q‖
            ≤ ‖-(3 / 2 : ℂ) * Qo d n q a‖ + ‖2 * q * deriv (fun ζ => Qo d n ζ a) q‖ := norm_sub_le _ _
          _ ≤ (3 / 2) * MQo d + 2 * r2 d * MQoD d := by
            rw [norm_mul, norm_mul, norm_mul, norm_neg,
              show ‖(3 / 2 : ℂ)‖ = 3 / 2 by norm_num, show ‖(2 : ℂ)‖ = 2 by norm_num]
            gcongr
            · exact (hbdQ q hq1).2
            · exact (hbdQD q hq).2
      · unfold Do MDo
        calc ‖(1 / 2 : ℂ) * Qe0 d n q a + 2 * deriv (fun ζ => Qe d n ζ a) q‖
            ≤ ‖(1 / 2 : ℂ) * Qe0 d n q a‖ + ‖2 * deriv (fun ζ => Qe d n ζ a) q‖ := norm_add_le _ _
          _ ≤ (1 / 2) * MQe0 d + 2 * MQeD d := by
            rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num,
              norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
            gcongr
            exact (hbdQD q hq).1
    exact ⟨hDe_diff, hDo_diff, hbdD⟩
  have hDe_a : ∀ q ∈ closedBall (0 : ℂ) (r2 d),
      DifferentiableOn ℂ (fun a => De d n q a) (ball 0 d.rAShrunk) := fun q hq => by
    have hq1 : q ∈ closedBall (0 : ℂ) (r1 d) := closedBall_subset_closedBall h5.le hq
    have hqr : ‖q‖ ≤ r2 d := mem_closedBall_zero_iff.1 hq
    have hdO_a : DifferentiableOn ℂ (fun a => deriv (fun ζ => Qo d n ζ a) q) (ball 0 d.rAShrunk) :=
      differentiableOn_deriv_param hr1_pos h6 h5
        (fun a ha => (hQ1 a ha).2.1)
        (fun ζ hζ => (hQ2 ζ (sphere_subset_closedBall hζ)).2)
        (fun ζ hζ a ha => ((hQ1 a ha).2.2.1 ζ (sphere_subset_closedBall hζ)).2)
        (differentiableOn_const q) (fun _ _ => hqr)
    exact ((differentiableOn_const _).mul (hQ2 q hq1).2).sub
      ((differentiableOn_const _).mul hdO_a)
  have hDo_a : ∀ q ∈ closedBall (0 : ℂ) (r2 d),
      DifferentiableOn ℂ (fun a => Do d n q a) (ball 0 d.rAShrunk) := fun q hq => by
    have hqr : ‖q‖ ≤ r2 d := mem_closedBall_zero_iff.1 hq
    have hqe0_a : DifferentiableOn ℂ (fun a => Qe0 d n q a) (ball 0 d.rAShrunk) :=
      differentiableOn_divQ_param hr1_pos h6 h5
        (fun a ha => (hQ1 a ha).1)
        (fun ζ hζ => (hQ2 ζ (sphere_subset_closedBall hζ)).1)
        (fun ζ hζ a ha => ((hQ1 a ha).2.2.1 ζ (sphere_subset_closedBall hζ)).1)
        (differentiableOn_const 0) (fun _ _ => by rw [norm_zero]; linarith)
        (differentiableOn_const q) (fun _ _ => hqr)
    have hdE_a : DifferentiableOn ℂ (fun a => deriv (fun ζ => Qe d n ζ a) q) (ball 0 d.rAShrunk) :=
      differentiableOn_deriv_param hr1_pos h6 h5
        (fun a ha => (hQ1 a ha).1)
        (fun ζ hζ => (hQ2 ζ (sphere_subset_closedBall hζ)).1)
        (fun ζ hζ a ha => ((hQ1 a ha).2.2.1 ζ (sphere_subset_closedBall hζ)).1)
        (differentiableOn_const q) (fun _ _ => hqr)
    exact ((differentiableOn_const _).mul hqe0_a).add ((differentiableOn_const _).mul hdE_a)
  have hD0_diff : DifferentiableOn ℂ (D0 d n) (ball 0 d.rAShrunk) :=
    differentiableOn_eval_param hr2_pos h5 hrc_r2
      (fun a ha => (hpart1 a ha).1)
      (fun ζ hζ => hDe_a ζ (sphere_subset_closedBall hζ))
      (fun ζ hζ a ha => ((hpart1 a ha).2.2 ζ (sphere_subset_closedBall hζ)).1)
      hdiff_ah.neg hc_bd
  have hD1_diff : DifferentiableOn ℂ (D1 d n) (ball 0 d.rAShrunk) :=
    differentiableOn_eval_param hr2_pos h5 hrc_r2
      (fun a ha => (hpart1 a ha).2.1)
      (fun ζ hζ => hDo_a ζ (sphere_subset_closedBall hζ))
      (fun ζ hζ a ha => ((hpart1 a ha).2.2 ζ (sphere_subset_closedBall hζ)).2)
      hdiff_ah.neg hc_bd
  have hbd_eval : ∀ a ∈ ball (0 : ℂ) d.rAShrunk, ‖D0 d n a‖ ≤ MDe d ∧ ‖D1 d n a‖ ≤ MDo d :=
    fun a ha => (hpart1 a ha).2.2 (-d.aHat n a)
      (closedBall_subset_closedBall (by linarith) (mem_closedBall_zero_iff.2 (hc_bd a ha)))
  have hreal_eval : ∀ a : ℝ, |a| < d.rAShrunk → (D0 d n a).im = 0 ∧ (D1 d n a).im = 0 := by
    intro a ha
    have ha_ball : (a : ℂ) ∈ ball (0 : ℂ) d.rAShrunk := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha
    have hcr : |-(d.aHat n a).re| < r1 d := by
      have hre := (c_ball d hn ha_ball).2.2.2.1
      rw [mem_ball_zero_iff] at hre
      calc |-(d.aHat n a).re| = |(d.aHat n a).re| := abs_neg _
        _ ≤ ‖d.aHat n a‖ := Complex.abs_re_le_norm _
        _ = ‖-d.aHat n a‖ := (norm_neg _).symm
        _ < r1 d := hre
    have hce : ((-(d.aHat n a).re : ℝ) : ℂ) = -d.aHat n a :=
      Complex.ext rfl (by simp [hreal_ah a ha])
    have hDe_im : ∀ x : ℝ, |x| < r1 d → (De d n x a).im = 0 := fun x hx => by
      have hdO_im := real_im_deriv ((hQ1 a ha_ball).2.1.mono (ball_subset_ball h6.le))
        (fun y hy => (hQ3 y a (hy.trans h6) ha).2) hx
      unfold De
      have hQo_im := (hQ3 x a (hx.trans h6) ha).2
      simp only [Complex.sub_im, Complex.mul_im, Complex.neg_im, Complex.div_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
        hQo_im, hdO_im, zero_mul, mul_zero, add_zero, sub_zero, neg_zero, zero_div]
    have hDo_im : ∀ x : ℝ, |x| < r1 d → (Do d n x a).im = 0 := fun x hx => by
      have hqe0_im := divQ_im_zero hr1_pos h6 (hQ1 a ha_ball).1
        (fun y hy => (hQ3 y a hy ha).1) (by rw [abs_zero]; exact hr1_pos) hx
      have hdE_im := real_im_deriv ((hQ1 a ha_ball).1.mono (ball_subset_ball h6.le))
        (fun y hy => (hQ3 y a (hy.trans h6) ha).1) hx
      unfold Do Qe0
      rw [show (1 / 2 : ℂ) * divQ (fun ζ => Qe d n ζ ↑a) (r1 d) 0 ↑x =
          (((1 / 2 : ℝ) : ℂ)) * divQ (fun ζ => Qe d n ζ ↑a) (r1 d) (0 : ℝ) ↑x by push_cast; rfl,
        Complex.add_im, Complex.im_ofReal_mul, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
        hqe0_im, hdE_im]; norm_num
    unfold D0 D1; rw [← hce]
    exact ⟨hDe_im _ hcr, hDo_im _ hcr⟩
  exact ⟨hpart1, hD0_diff, hD1_diff, hbd_eval, hreal_eval⟩

end HalfCubicInternal

open HalfCubicInternal

/-- Coefficient functions for `(fs:principal)`: `C_n`, `Q_n`, `T_n`. -/
noncomputable def HalfCubicData.Cn (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ :=
  (n : ℂ) * (A0 d n a - 1) + D0 d n a
noncomputable def HalfCubicData.Qn (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ :=
  (((2 : ℝ) ^ (-(1 / 3 : ℝ)) * π : ℝ) : ℂ) * Qe d n 0 a
noncomputable def HalfCubicData.Tn (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ :=
  (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * ((n : ℂ) * A1 d n a + D1 d n a)

/-- Coefficient functions for `(fs:aux)`: `C_n^*`, `T_n^*`. -/
noncomputable def HalfCubicData.CnStar (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ := A0 d n a
noncomputable def HalfCubicData.TnStar (d : HalfCubicData) (n : ℝ) (a : ℂ) : ℂ :=
  (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * A1 d n a

end FineOrderSigned

end FormalResearch.SignUncertainty
