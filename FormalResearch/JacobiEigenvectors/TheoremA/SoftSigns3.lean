module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftSigns2

/-!
# Paper J, Layer 2 (L2.C7): the sign analysis of app_thmA Step 6, part 3: hypothesis (iii) of `lem:tha-count` on the soft chart, and `SoftCountHyps`

Source: `app_thmA.tex`, proof of prop:tha-W2, Step 6, item "(iii)" and the item "Order": at an eigenvalue `X` in the window of label `k`, `a = -(k + 1/2) + O(h^m Lm)`, so
`psi-hat^L_n psi-hat^R_n = lambda_L lambda_R kappa_b^{-2} phi^L_n phi^R_n` and `U(a,-Z) U(a,Z) = (-1)^k [cos(pi delta) u^2 + sin(pi delta) u w]` has the sign `(-1)^k` on the window; hence
`sign hat kappa = sign (lambda_L lambda_R) (-1)^k`, and `kappa' = kappa` up to a positive factor (`p = kappa' q`).

## What is proved (all axiom-pinned)

* `reflect_prod`, `uw_bound`: `kappa U(a,-Z) * kappa U(a,Z) = -sin(pi a) u^2 + cos(pi a) u w` with `u = kappa U(a,|Z|)`, `w = kappa^{-1} V(a,|Z|)` (`reflect`, `kappa^2 Gamma(1/2 - a) = 1`),
  and `|u w| <= C_PC^2 M_bal^2` (`env_well`).
* `win_row_pack`: the per-row facts of a window row of a chart (`gm <= A <= K_A`, `|phi - A y| <= h C M`, `|y| <= C_B M`, `u > u_c - eta/2`); `soft_win_u2`: `c_0 m_Omega <= sum_Omega (kappa U(a,|Z|))^2`.
* `row_alg`, `sum_alg`, `soft_sum_sign`: for `a = -(k + 1/2) + delta`, `|delta|` and `h` small, `(-1)^k sum_Omega phi^L_n phi^R_{N-n} > 0` (`phi^R` the corrected profile of the mirror chart `CR` at the reflected row).
* `soft_sign_kappa` (= the second conjunct of `SoftCountHyps`): there is a constant sign `sigma' = +-1` (that of `lambda_L lambda_R` on the energy window: `lamL_cont` of both charts, `soft_lamL_lower`,
  `sign_const_of_cont`) with `sign kappa' = sign (sigma' (-1)^k)` for every eigenvalue of an eigen-system obeying Step 0 in the window `|pi mu_0 - pi h (k + 1/2)| <= pi h/8`, `p = kappa' q`.
  Inputs: `soft_window_label` (`a <= 0`, `|mu-tilde - (j + 1/2) h| <= C h^{m+1} Lm`), the identification `j = k` (`idx_eq`, `|mu-tilde - mu_0| <= (q/2) C_mu h^2`),
  the exact solutions `psi^L = c_0 p`, `psi' = c_0' q(N - .)` (`pq_exact`, `kappa = kappa' c_0/c_0'`), `soft_match` (`|hat kappa - kappa| <= D_k h^m Lm |kappa|`) and `soft_sum_sign`.
* `softCountHyps_proved`: `SoftCountHyps CL CR Cs0` (hypotheses (ii), (iii) of `lem:tha-count` on the soft chart), from `soft_sign_D` (`SoftSigns2.lean`) and `soft_sign_kappa`.

## Differences from the paper

* The window of `SoftCountHyps` is `|pi mu_0 - pi h (k + 1/2)| <= pi h/8` (too wide for `cos(pi a)` to be small); the smallness `|a + k + 1/2| <= C h^m Lm` comes from Step 0 through `soft_window_label`, as in the paper
  (the eigenvalue is in the window of label `j` and `j = k` by `idx_eq`).  `Phi = pi mu_0` instead of `pi mu-tilde` (see `SoftCountHyps.lean`).
* The sign `sigma'` is the constant sign of `lambda_L lambda_R` on the window (not `+1`), which depends on `(p, N)`; that is all `lem:tha-count` needs.
* The sign of `sum_Omega psi-hat^L psi-hat^R` is computed from the corrected profiles `phi^{(1)}_2` of both charts on the window rows (`wm_row2`), with the mass bound `soft_win_u2` (first conjunct of `WmClaims`);
  `a <= 0` holds automatically for `|a + k + 1/2| <= 1/4`.

## Not formalised

Nothing of Step 6 (iii).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

lemma sin_half (k : ℕ) (δ : ℝ) : Real.sin (Real.pi * (-(k:ℝ) - 1/2 + δ)) = -((-1:ℝ)^k * Real.cos (Real.pi*δ)) := by
  have e : Real.pi * (-(k:ℝ) - 1/2 + δ) = (Real.pi*δ - Real.pi/2) - (k:ℝ) * Real.pi := by ring
  rw [e, Real.sin_sub_nat_mul_pi, Real.sin_sub_pi_div_two]; ring

lemma cos_half (k : ℕ) (δ : ℝ) : Real.cos (Real.pi * (-(k:ℝ) - 1/2 + δ)) = (-1:ℝ)^k * Real.sin (Real.pi*δ) := by
  have e : Real.pi * (-(k:ℝ) - 1/2 + δ) = (Real.pi*δ - Real.pi/2) - (k:ℝ) * Real.pi := by ring
  rw [e, Real.cos_sub_nat_mul_pi, Real.cos_sub_pi_div_two]

/-- pure algebra of one window row -/
lemma row_alg (k : ℕ) (δ : ℝ) (hδ : |Real.pi * δ| ≤ 1)
    (AL AR gL gR KL KR u w yL yR φL φR M h ecL ecR CB Cp : ℝ)
    (hgL : gL ≤ AL) (hgR : gR ≤ AR) (hAL : AL ≤ KL) (hAR : AR ≤ KR) (hg0L : 0 < gL) (hg0R : 0 < gR)
    (hyL : |yL| ≤ CB * M) (hyR : |yR| ≤ CB * M)
    (hprod : yL * yR = (-1 : ℝ) ^ k * (Real.cos (Real.pi * δ) * u ^ 2 + Real.sin (Real.pi * δ) * (u * w)))
    (huw : |u * w| ≤ Cp * M ^ 2)
    (heL : |φL - AL * yL| ≤ h * ecL * M) (heR : |φR - AR * yR| ≤ h * ecR * M)
    (h0 : 0 ≤ h) (hh1 : h ≤ 1) (hM : 0 ≤ M) (hecL : 0 ≤ ecL) (hecR : 0 ≤ ecR) (hCB : 0 ≤ CB) :
    (gL * gR / 2) * u ^ 2 - (KL * KR * (Real.pi * |δ|) * Cp + h * (KL * CB * ecR + KR * CB * ecL + ecL * ecR)) * M ^ 2 ≤
      (-1 : ℝ) ^ k * (φL * φR) := by
  have hKL : 0 < KL := lt_of_lt_of_le hg0L (hgL.trans hAL)
  have hKR : 0 < KR := lt_of_lt_of_le hg0R (hgR.trans hAR)
  have hAL0 : 0 < AL := lt_of_lt_of_le hg0L hgL
  have hAR0 : 0 < AR := lt_of_lt_of_le hg0R hgR
  set x : ℝ := (-1 : ℝ) ^ k with hx
  have hx2 : x * x = 1 := by rw [hx, ← mul_pow]; norm_num
  have hxabs : |x| = 1 := by rw [hx, abs_pow]; simp
  set c := Real.cos (Real.pi * δ) with hc
  set s := Real.sin (Real.pi * δ) with hs
  have hcos : 1 / 2 ≤ c := by
    have := Real.one_sub_sq_div_two_le_cos (x := Real.pi * δ)
    have h2 : (Real.pi * δ) ^ 2 ≤ 1 := by
      have := sq_abs (Real.pi * δ)
      nlinarith [abs_nonneg (Real.pi * δ)]
    linarith
  have hsin : |s| ≤ Real.pi * |δ| := by
    have := Real.abs_sin_le_abs (x := Real.pi * δ)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  set eL := φL - AL * yL with heLd
  set eR := φR - AR * yR with heRd
  have hφ : φL * φR = AL * AR * (yL * yR) + (AL * yL * eR + AR * yR * eL + eL * eR) := by
    simp only [heLd, heRd]; ring
  have hmain : x * (φL * φR) = AL * AR * (c * u ^ 2 + s * (u * w)) + x * (AL * yL * eR + AR * yR * eL + eL * eR) := by
    rw [hφ, hprod]
    have : x * (AL * AR * (x * (c * u ^ 2 + s * (u * w))) + (AL * yL * eR + AR * yR * eL + eL * eR)) =
        (x * x) * (AL * AR * (c * u ^ 2 + s * (u * w))) + x * (AL * yL * eR + AR * yR * eL + eL * eR) := by ring
    rw [this, hx2]; ring
  -- the three estimates
  have hALAR : gL * gR ≤ AL * AR := mul_le_mul hgL hgR hg0R.le hAL0.le
  have hALARK : AL * AR ≤ KL * KR := mul_le_mul hAL hAR hAR0.le hKL.le
  have t1 : (gL * gR / 2) * u ^ 2 ≤ AL * AR * (c * u ^ 2) := by
    have h1 : 0 ≤ u ^ 2 := sq_nonneg u
    have : (gL * gR / 2) ≤ AL * AR * c := by
      have := mul_le_mul hALAR hcos (by norm_num) (by positivity)
      linarith
    calc (gL * gR / 2) * u ^ 2 ≤ (AL * AR * c) * u ^ 2 := mul_le_mul_of_nonneg_right this h1
      _ = _ := by ring
  have t2 : -(KL * KR * (Real.pi * |δ|) * Cp * M ^ 2) ≤ AL * AR * (s * (u * w)) := by
    have h1 : |AL * AR * (s * (u * w))| ≤ KL * KR * (Real.pi * |δ|) * Cp * M ^ 2 := by
      have e0 : |AL * AR * (s * (u * w))| = AL * AR * (|s| * |u * w|) := by
        rw [abs_mul, abs_mul s, abs_of_pos (mul_pos hAL0 hAR0)]
      rw [e0]
      have a1 : |s| * |u * w| ≤ (Real.pi * |δ|) * (Cp * M ^ 2) :=
        mul_le_mul hsin huw (abs_nonneg _) (by positivity)
      calc AL * AR * (|s| * |u * w|) ≤ (KL * KR) * ((Real.pi * |δ|) * (Cp * M ^ 2)) :=
            mul_le_mul hALARK a1 (by positivity) (by positivity)
        _ = _ := by ring
    exact (abs_le.mp h1).1
  have t3 : -(h * (KL * CB * ecR + KR * CB * ecL + ecL * ecR) * M ^ 2) ≤
      x * (AL * yL * eR + AR * yR * eL + eL * eR) := by
    have h1 : |x * (AL * yL * eR + AR * yR * eL + eL * eR)| ≤ h * (KL * CB * ecR + KR * CB * ecL + ecL * ecR) * M ^ 2 := by
      rw [abs_mul, hxabs, one_mul]
      have b1 : |AL * yL * eR| ≤ KL * (CB * M) * (h * ecR * M) := by
        rw [abs_mul, abs_mul, abs_of_pos hAL0]
        exact mul_le_mul (mul_le_mul hAL hyL (abs_nonneg _) hKL.le) heR (abs_nonneg _) (by positivity)
      have b2 : |AR * yR * eL| ≤ KR * (CB * M) * (h * ecL * M) := by
        rw [abs_mul, abs_mul, abs_of_pos hAR0]
        exact mul_le_mul (mul_le_mul hAR hyR (abs_nonneg _) hKR.le) heL (abs_nonneg _) (by positivity)
      have b3 : |eL * eR| ≤ (h * ecL * M) * (h * ecR * M) := by
        rw [abs_mul]; exact mul_le_mul heL heR (abs_nonneg _) (by positivity)
      have b4 : (h * ecL * M) * (h * ecR * M) ≤ h * (ecL * ecR) * M ^ 2 := by
        have : (h * ecL * M) * (h * ecR * M) = (h * h) * (ecL * ecR) * M ^ 2 := by ring
        rw [this]
        have hh : h * h ≤ h := by nlinarith
        have h5 : 0 ≤ ecL * ecR * M ^ 2 := by positivity
        have h6 := mul_le_mul_of_nonneg_right hh h5
        calc (h * h) * (ecL * ecR) * M ^ 2 = (h * h) * (ecL * ecR * M ^ 2) := by ring
          _ ≤ h * (ecL * ecR * M ^ 2) := h6
          _ = _ := by ring
      have b5 : |AL * yL * eR + AR * yR * eL + eL * eR| ≤ |AL * yL * eR| + |AR * yR * eL| + |eL * eR| :=
        abs_add_three _ _ _
      calc |AL * yL * eR + AR * yR * eL + eL * eR| ≤ |AL * yL * eR| + |AR * yR * eL| + |eL * eR| := b5
        _ ≤ KL * (CB * M) * (h * ecR * M) + KR * (CB * M) * (h * ecL * M) + h * (ecL * ecR) * M ^ 2 :=
            add_le_add (add_le_add b1 b2) (b3.trans b4)
        _ = _ := by ring
    exact (abs_le.mp h1).1
  rw [hmain]
  have : AL * AR * (c * u ^ 2 + s * (u * w)) = AL * AR * (c * u ^ 2) + AL * AR * (s * (u * w)) := by ring
  rw [this]
  linarith [t1, t2, t3]

/-! ### The connection formula on the window -/

/-- `kappa U(a,-Z) * kappa U(a,Z) = -sin(pi a) u^2 + cos(pi a) u w`, `u = kappa U(a,|Z|)`, `w = kappa^{-1} V(a,|Z|)` (`a <= 0`; `reflect`, `kappa^2 Gamma(1/2 - a) = 1`). -/
lemma reflect_prod {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {a : ℝ} (ha : a ≤ 0) (Z : ℝ) :
    (kappaBal a * U a (-Z)) * (kappaBal a * U a Z) =
      -Real.sin (Real.pi * a) * (kappaBal a * U a |Z|) ^ 2 +
        Real.cos (Real.pi * a) * ((kappaBal a * U a |Z|) * ((kappaBal a)⁻¹ * V a |Z|)) := by
  obtain ⟨hκ0, hκG⟩ := kappa_sq_gamma a ha
  have hκ := kappaBal_pos a
  have hkG : kappaBal a * Real.Gamma (1 / 2 - a) = (kappaBal a)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by linear_combination hκG)
  have hrefl : ∀ z : ℝ, kappaBal a * U a (-z) = -Real.sin (Real.pi * a) * (kappaBal a * U a z) +
      Real.cos (Real.pi * a) * ((kappaBal a)⁻¹ * V a z) := by
    intro z
    rw [hf.reflect a ha z]
    have : kappaBal a * (Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a z) =
        Real.cos (Real.pi * a) * ((kappaBal a * Real.Gamma (1 / 2 - a)) * V a z) := by ring
    calc kappaBal a * (-Real.sin (Real.pi * a) * U a z + Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a z)
        = -Real.sin (Real.pi * a) * (kappaBal a * U a z) +
          kappaBal a * (Real.cos (Real.pi * a) * Real.Gamma (1 / 2 - a) * V a z) := by ring
      _ = _ := by rw [this, hkG]
  rcases le_total 0 Z with hZ | hZ
  · rw [abs_of_nonneg hZ, hrefl Z]; ring
  · rw [abs_of_nonpos hZ]
    have h2 := hrefl (-Z)
    rw [neg_neg] at h2
    rw [h2]
    ring

/-- `|kappa U(a,z) * kappa^{-1} V(a,z)| <= C_PC^2 M_bal(a,z)^2` for `a <= 0`, `z >= 0` (`env_well`). -/
lemma uw_bound {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {a : ℝ} (ha : a ≤ 0) {z : ℝ} (hz : 0 ≤ z) :
    |(kappaBal a * U a z) * ((kappaBal a)⁻¹ * V a z)| ≤ CPC ^ 2 * Mbal a z ^ 2 := by
  obtain ⟨hu, hv⟩ := hf.env_well a ha z hz
  have hk2 := k2_nonneg a z
  have hκ := kappaBal_pos a
  have hE := Ewell_pos a z
  have hM := Mbal_nonneg a z
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have h1 : |ut U a z| ≤ CPC * Ewell a z * Mbal a z := by
    refine le_trans ?_ hu
    apply Real.abs_le_sqrt
    have : 0 ≤ (kappaBal a * deriv (U a) z) ^ 2 / k2 a z := by positivity
    linarith
  have h2 : |vt V a z| ≤ CPC * (Ewell a z)⁻¹ * Mbal a z := by
    refine le_trans ?_ hv
    apply Real.abs_le_sqrt
    have : 0 ≤ (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (V a) z) ^ 2 / k2 a z := by positivity
    linarith
  have hw : |(kappaBal a)⁻¹ * V a z| ≤ |vt V a z| := by
    have e : (kappaBal a)⁻¹ * V a z = Real.sqrt (2 / Real.pi) * vt V a z := by
      unfold vt
      have : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have : 2 / Real.pi * (Real.pi / 2) = 1 := by field_simp
        rw [this, Real.sqrt_one]
      calc (kappaBal a)⁻¹ * V a z = (Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2)) * ((kappaBal a)⁻¹ * V a z) := by
            rw [this, one_mul]
        _ = _ := by ring
    rw [e, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : Real.sqrt (2 / Real.pi) ≤ 1 := by
      rw [Real.sqrt_le_one]
      rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
    calc Real.sqrt (2 / Real.pi) * |vt V a z| ≤ 1 * |vt V a z| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ = _ := one_mul _
  rw [abs_mul]
  have h3 : |kappaBal a * U a z| = |ut U a z| := rfl
  rw [h3]
  calc |ut U a z| * |(kappaBal a)⁻¹ * V a z| ≤ (CPC * Ewell a z * Mbal a z) * (CPC * (Ewell a z)⁻¹ * Mbal a z) :=
        mul_le_mul h1 (hw.trans h2) (abs_nonneg _) (by positivity)
    _ = CPC ^ 2 * Mbal a z ^ 2 := by field_simp

section Win

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **One window row of a chart** (patch 2): the corrector amplitude `A` is in `[g_m, K_A]`, `phi - A y` is `O(h) M`, and `y = kappa U(a,-Z)`, `kappa U(a,Z)` are `O(M)`;
the row is on the Airy-collar side `u > u_c - eta/2` of the definition of `psi-hat^L`. -/
theorem win_row_pack {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (ha : CL.aOf p X N ≤ aplus) (hs : Fz.step N ≤ asmH0 CL) {n : ℤ}
    (hn : n ∈ softWindow CL p X N) :
    CL.gm ≤ (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) ∧
      (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) ≤ CL.cs.KA ∧
      |(CL.chain p X N).phi (Fz.step N) 0 2 n -
          (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) * (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n)))| ≤
        Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) ∧
      |kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))| ≤ winCB CPC aplus * Mbal (CL.aOf p X N) (CL.Zof p X N n) ∧
      |kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)| ≤ winCB CPC aplus * Mbal (CL.aOf p X N) (CL.Zof p X N n) ∧
      CL.uc p - CL.η / 2 < uNode (Fz.step N) n := by
  have hs1 : Fz.step N ≤ winH1 CL := hs.trans (min_le_left _ _)
  have hcol := soft_win_loc CL hp hX hs hn
  obtain ⟨h0, hNn, hZ, hj1, hNR, hc2, hkz⟩ := wm_rowfacts CL hp hX hN hs1 hn hcol
  obtain ⟨hgt', -⟩ := abs_lt.mp hcol
  have hη := CL.consts_pos.2.1
  obtain ⟨hgm, hrow⟩ := wm_row2 hf CL aplus hp hX hN ha hs1 hn hcol
  have hAA := wm_AA_le CL hp hX hN hj1.le hNR
  obtain ⟨⟨-, -⟩, ⟨hy2, -⟩⟩ := wm_env_two hf aplus (CL.aOf p X N) ha (CL.Zof p X N n) hZ
  obtain ⟨⟨hy1, -⟩, -⟩ := wm_env_two hf aplus (CL.aOf p X N) ha (CL.Zof p X N n) hZ
  refine ⟨hgm, (abs_le.mp hAA).2, hrow, hy2, hy1, ?_⟩
  linarith

/-- **E4 for `U`**: `c_0 m_Omega <= sum_Omega (kappa U(a,|Z_n|))^2` (the first conjunct of `WmClaims` at the cut `s_A`; the proof of `soft_win_mass` without its unscaling). -/
theorem soft_win_u2 {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) :
    ∃ c0 h0 : ℝ, 0 < c0 ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ min h0 (asmH0 CL) → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ aplus →
        c0 * wmMass CL p X N ≤ ∑ n ∈ softWindow CL p X N, (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) |CL.Zof p X N n|) ^ 2 := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hC1pos : 0 < winCB CPC aplus := by unfold winCB; positivity
  obtain ⟨c1, hc1pos, hc1⟩ := wm_c1 hf aplus
  have hΔ : 0 < wmDelta c1 (winCB CPC aplus ^ 2) CL.dp := wmDelta_pos hc1pos (by positivity) hdp
  obtain ⟨cs, hs0, hcs, hhs, hsm⟩ := wm_small hf CL aplus hc1pos hc1
  obtain ⟨cl, hl0, hcl, hhl, hlg⟩ := wm_large hf CL aplus hΔ
  refine ⟨min cs cl, min hs0 hl0, lt_min hcs hcl, lt_min hhs hhl, ?_⟩
  intro p hp N hN hstep X hX haplus
  have hstep' : Fz.step N ≤ min hs0 hl0 := hstep.trans (min_le_left _ _)
  have hsmall := (le_min_iff.mp hstep').1
  have hlarge := (le_min_iff.mp hstep').2
  have hclaims : WmClaims CL p X N (min cs cl) := by
    by_cases hA : Fz.step N * max (-CL.aOf p X N) 0 ≤ wmDelta c1 (winCB CPC aplus ^ 2) CL.dp
    · exact (hsm p hp X hX N hN hsmall haplus hA).mono (min_le_left _ _) (wmMass_nonneg CL p X N)
    · push Not at hA
      exact (hlg p hp X hX N hN hlarge haplus hA).mono (min_le_right _ _) (wmMass_nonneg CL p X N)
  obtain ⟨h1, -, -⟩ := hclaims
  refine h1.trans ?_
  have hcut : 0 ≤ wmCut (CL.aOf p X N) := add_nonneg (Real.sqrt_nonneg _) (div_nonneg (ell_nonneg' _) (by norm_num))
  have hsub : (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n) ⊆ softWindow CL p X N :=
    Finset.filter_subset _ _
  calc ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
        (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)) ^ 2
      = ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
        (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) |CL.Zof p X N n|) ^ 2 := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have := (Finset.mem_filter.mp hn).2
        rw [abs_of_pos (lt_of_le_of_lt hcut this)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)

lemma Mbal_abs (a z : ℝ) : Mbal a |z| = Mbal a z := by
  rcases abs_choice z with h | h <;> rw [h]
  exact Mbal_neg a z

/-- small-parameter arithmetic for `soft_sum_sign`. -/
lemma sum_alg (g A0 B δ h m S : ℝ) (hg : 0 < g) (hA0 : 0 ≤ A0) (hB : 0 ≤ B) (_hδ : 0 ≤ δ) (_hh : 0 ≤ h)
    (hδ1 : δ ≤ g / (8 * (A0 + 1))) (hh1 : h ≤ g / (8 * (B + 1))) (hm : 0 < m)
    (hS : g / 2 * m - (A0 * δ + h * B) * m ≤ S) : 0 < S := by
  have h1 : A0 * δ ≤ g / 8 := by
    have : A0 * δ ≤ A0 * (g / (8 * (A0 + 1))) := mul_le_mul_of_nonneg_left hδ1 hA0
    refine this.trans ?_
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : h * B ≤ g / 8 := by
    have : h * B ≤ (g / (8 * (B + 1))) * B := mul_le_mul_of_nonneg_right hh1 hB
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 : (g / 4) * m ≤ (g / 2 - (A0 * δ + h * B)) * m := by
    apply mul_le_mul_of_nonneg_right _ hm.le
    linarith
  have h4 : 0 < (g / 4) * m := by positivity
  nlinarith

/-- **The sign of the window sum** `sum_Omega phi_L phi_R(N - .)` (app_thmA Step 6 (iii), the sign of `hat kappa`): at `a = -(k + 1/2) + delta`, `|delta|` small, the corrected profiles
`phi^{(1)}_2` of the two charts satisfy `(-1)^k sum_Omega phi^L_n phi^R_{N-n} > 0`.  (Connection formula: `U(a,-Z) U(a,Z) = (-1)^k [cos(pi delta) u^2 + sin(pi delta) u w]`, `u = kappa U(a,|Z|)`, `w = kappa^{-1} V(a,|Z|)`,
with the mass `sum_Omega u^2 >= c_0 m_Omega` and `|u w| <= C_PC^2 M_bal^2`.) -/
theorem soft_sum_sign (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) :
    ∃ δ1 h1 : ℝ, 0 < δ1 ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      ∀ k : ℕ, |CL.aOf p X N + k + 1 / 2| ≤ δ1 →
        0 < (-1 : ℝ) ^ k * ∑ n ∈ softWindow CL p X N,
          (CL.chain p X N).phi (Fz.step N) 0 2 n * (CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - n) := by
  obtain ⟨c0, h0u, hc0, hh0u, Hu⟩ := soft_win_u2 CL hf 0
  obtain ⟨cM, CM, h0M, hcM, h0Mp, HM⟩ := soft_win_massw CL hf 0
  have hgL := CL.consts_pos4.1
  have hgR := CR.consts_pos4.1
  have hCBL := CL.consts_pos4.2
  have hCBR := CR.consts_pos4.2
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hCB : 0 < winCB CPC 0 := by unfold winCB; positivity
  have hLamL := winCLam_nonneg CL
  have hLamR := winCLam_nonneg CR
  have hKL : 0 ≤ CL.cs.KA := CL.cs.KA_nonneg
  have hKR : 0 ≤ CR.cs.KA := CR.cs.KA_nonneg
  set g : ℝ := CL.gm * CR.gm * c0 with hg
  have hgpos : 0 < g := by positivity
  set A0 : ℝ := CL.cs.KA * CR.cs.KA * Real.pi * CPC ^ 2 with hA0
  have hA0n : 0 ≤ A0 := by positivity
  set ecL : ℝ := CL.CBc * winCB CPC 0 * winCLam CL with hecL
  set ecR : ℝ := CR.CBc * winCB CPC 0 * winCLam CR with hecR
  have hecL0 : 0 ≤ ecL := by positivity
  have hecR0 : 0 ≤ ecR := by positivity
  set B : ℝ := CL.cs.KA * winCB CPC 0 * ecR + CR.cs.KA * winCB CPC 0 * ecL + ecL * ecR with hB
  have hBn : 0 ≤ B := by positivity
  set δ1 : ℝ := min (1 / 4) (min (1 / Real.pi) (g / (8 * (A0 + 1)))) with hδ1
  have hδ1pos : 0 < δ1 := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  set h1 : ℝ := min (min h0u (asmH0 CL)) (min (min (asmH0 CR) h0M) (min 1 (g / (8 * (B + 1))))) with hh1def
  have hh1pos : 0 < h1 := lt_min (lt_min hh0u (asmH0_pos CL)) (lt_min (lt_min (asmH0_pos CR) h0Mp) (lt_min one_pos (by positivity)))
  refine ⟨δ1, h1, hδ1pos, hh1pos, ?_⟩
  intro p hp N hN hstep X hX k hk
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN1
  have haR : CR.aOf p X N = CL.aOf p X N := aOf_mirror hM hp X N
  have s1 : Fz.step N ≤ min h0u (asmH0 CL) := hstep.trans (min_le_left _ _)
  have s2 : Fz.step N ≤ asmH0 CL := s1.trans (min_le_right _ _)
  have s3 : Fz.step N ≤ asmH0 CR := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have s4 : Fz.step N ≤ h0M := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have s5 : Fz.step N ≤ 1 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have s6 : Fz.step N ≤ g / (8 * (B + 1)) := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  set a : ℝ := CL.aOf p X N with hadef
  set δ : ℝ := a + k + 1 / 2 with hδdef
  have hδabs : |δ| ≤ δ1 := hk
  have hδ14 : |δ| ≤ 1 / 4 := hδabs.trans (min_le_left _ _)
  have hδpi : |δ| ≤ 1 / Real.pi := hδabs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδg : |δ| ≤ g / (8 * (A0 + 1)) := hδabs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha0 : a ≤ 0 := by
    have := (abs_le.mp hδ14).2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have haRle : CR.aOf p X N ≤ 0 := by rw [haR]; exact ha0
  have hpiδ : |Real.pi * δ| ≤ 1 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc Real.pi * |δ| ≤ Real.pi * (1 / Real.pi) := mul_le_mul_of_nonneg_left hδpi Real.pi_pos.le
      _ = 1 := by field_simp
  have hm0 : 0 < wmMass CL p X N := by
    have := HM p hp N hN1 s4 X hX ha0
    have h2 : 0 < cM * Fz.step N ^ (-(1 : ℝ) / 2) := by positivity
    linarith [this.1]
  have hu := Hu p hp N hN1 s1 X hX ha0
  have hasin : a = -(k : ℝ) - 1 / 2 + δ := by rw [hδdef]; ring
  have hsin : Real.sin (Real.pi * a) = -((-1 : ℝ) ^ k * Real.cos (Real.pi * δ)) := by
    rw [hasin]; exact sin_half k δ
  have hcos : Real.cos (Real.pi * a) = (-1 : ℝ) ^ k * Real.sin (Real.pi * δ) := by
    rw [hasin]; exact cos_half k δ
  -- the row inequality
  have hrow : ∀ n ∈ softWindow CL p X N,
      (CL.gm * CR.gm / 2) * (kappaBal a * U a |CL.Zof p X N n|) ^ 2 -
        (CL.cs.KA * CR.cs.KA * (Real.pi * |δ|) * CPC ^ 2 + Fz.step N * B) * Mbal a (CL.Zof p X N n) ^ 2 ≤
      (-1 : ℝ) ^ k * ((CL.chain p X N).phi (Fz.step N) 0 2 n * (CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - n)) := by
    intro n hn
    have hn' : (N : ℤ) - n ∈ softWindow CR p X N := (window_reflect hM hp X N n).mp hn
    obtain ⟨gl, Al, eL, yL, -, -⟩ := win_row_pack CL hf 0 hp hX hN1 ha0 s2 hn
    obtain ⟨gr, Ar, eR, yR, -, -⟩ := win_row_pack CR hf 0 hp hXR hNR haRle s3 hn'
    have hZR : CR.Zof p X N ((N : ℤ) - n) = -CL.Zof p X N n := Zof_mirror hM hp X N n
    rw [haR, hZR, neg_neg, Mbal_neg] at eR yR
    have hprod : (kappaBal a * U a (-CL.Zof p X N n)) * (kappaBal a * U a (CL.Zof p X N n)) =
        (-1 : ℝ) ^ k * (Real.cos (Real.pi * δ) * (kappaBal a * U a |CL.Zof p X N n|) ^ 2 +
          Real.sin (Real.pi * δ) * ((kappaBal a * U a |CL.Zof p X N n|) * ((kappaBal a)⁻¹ * V a |CL.Zof p X N n|))) := by
      rw [reflect_prod hf ha0, hsin, hcos]; ring
    have huw := uw_bound hf ha0 (abs_nonneg (CL.Zof p X N n))
    rw [Mbal_abs] at huw
    exact row_alg k δ hpiδ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gl gr Al Ar hgL hgR yL yR hprod huw eL eR hh0.le s5
      (Mbal_nonneg a _) hecL0 hecR0 hCB.le
  have hsum := Finset.sum_le_sum hrow
  have eL : ∑ n ∈ softWindow CL p X N, ((CL.gm * CR.gm / 2) * (kappaBal a * U a |CL.Zof p X N n|) ^ 2 -
        (CL.cs.KA * CR.cs.KA * (Real.pi * |δ|) * CPC ^ 2 + Fz.step N * B) * Mbal a (CL.Zof p X N n) ^ 2) =
      (CL.gm * CR.gm / 2) * ∑ n ∈ softWindow CL p X N, (kappaBal a * U a |CL.Zof p X N n|) ^ 2 -
        (CL.cs.KA * CR.cs.KA * (Real.pi * |δ|) * CPC ^ 2 + Fz.step N * B) * wmMass CL p X N := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  rw [eL, ← Finset.mul_sum] at hsum
  have hc : 0 ≤ CL.gm * CR.gm / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hu hc
  refine sum_alg g A0 B |δ| (Fz.step N) (wmMass CL p X N) _ hgpos hA0n hBn (abs_nonneg _) hh0.le hδg s6 hm0 ?_
  have e2 : (CL.cs.KA * CR.cs.KA * (Real.pi * |δ|) * CPC ^ 2 + Fz.step N * B) = A0 * |δ| + Fz.step N * B := by
    rw [hA0]; ring
  rw [e2] at hsum
  have e3 : g / 2 * wmMass CL p X N = (CL.gm * CR.gm / 2) * (c0 * wmMass CL p X N) := by rw [hg]; ring
  rw [e3]
  linarith

lemma K_alg (K h : ℝ) (hK : 0 ≤ K) (hh : 0 < h) (h1 : h ≤ 1 / (16 * (K + 1))) : K * h ^ 2 ≤ h / 16 := by
  have h2 : h * (16 * (K + 1)) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (K + 1))).mp h1
    linarith
  have h3 : K * h ≤ 1 / 16 := by nlinarith
  nlinarith

lemma D_alg (D : ℝ) (hD : 0 ≤ D) : D * (1 / (2 * (D + 1))) ≤ 1 / 2 := by
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma pos_alg (s κ : ℝ) (h3 : -((1 / 2) * (κ * κ)) ≤ (s - κ) * κ) (h4 : 0 < κ * κ) : 0 < s * κ := by
  nlinarith

lemma sign_of_mul_pos {x y : ℝ} (h : 0 < x * y) : SignType.sign x = SignType.sign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : y < 0 := by
      by_contra hy
      push Not at hy
      nlinarith
    rw [sign_neg hx, sign_neg hy]
  · rw [hx, zero_mul] at h; exact absurd h (lt_irrefl _)
  · have hy : 0 < y := by
      by_contra hy
      push Not at hy
      nlinarith
    rw [sign_pos hx, sign_pos hy]

/-- the window label is the index: `|mu-tilde - (j + 1/2) h| <= h/16`, `|mu-tilde - mu_0| <= h/16`, `|pi mu_0 - pi h (k + 1/2)| <= pi h/8` force `j = k`. -/
lemma idx_eq (h mt m0 : ℝ) (j k : ℕ) (hh : 0 < h) (h1 : |mt - ((j : ℝ) + 1 / 2) * h| ≤ h / 16) (h2 : |mt - m0| ≤ h / 16)
    (h3 : |Real.pi * m0 - Real.pi * h * ((k : ℝ) + 1 / 2)| ≤ Real.pi * h / 8) : j = k := by
  have hpi := Real.pi_pos
  have h3' : |m0 - h * ((k : ℝ) + 1 / 2)| ≤ h / 8 := by
    have e : Real.pi * m0 - Real.pi * h * ((k : ℝ) + 1 / 2) = Real.pi * (m0 - h * ((k : ℝ) + 1 / 2)) := by ring
    rw [e, abs_mul, abs_of_pos hpi] at h3
    have : Real.pi * |m0 - h * ((k : ℝ) + 1 / 2)| ≤ Real.pi * (h / 8) := by linarith
    exact le_of_mul_le_mul_left this hpi
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  obtain ⟨c1, c2⟩ := abs_le.mp h3'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
    nlinarith
  · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hgt
    nlinarith

/-- **Step 6 (iii) on the soft chart**: there is a constant sign `sigma' = +-1` (that of `lambda_L lambda_R` on the energy window) such that `sign kappa' = sign (sigma' (-1)^k)` for every eigenvalue
`X_i` obeying Step 0 whose nominal action `pi mu_0` lies in the window `|pi mu_0 - pi h (k + 1/2)| <= pi h/8`, with `p = kappa' q`. -/
theorem soft_sign_kappa (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (Cs0 : ℝ) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∃ σ' : ℝ, (σ' = 1 ∨ σ' = -1) ∧
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
          (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) →
          ∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 → ∀ k : ℕ,
            |Real.pi * softMu0 CL p (Xs i) - Real.pi * Fz.step N * ((k : ℝ) + 1 / 2)| ≤ Real.pi * Fz.step N / 8 →
            ∀ κ' : ℝ, (∀ n ≤ N, pSol Fz p N (Xs i) n = κ' * qSol Fz p N (Xs i) (N - n)) →
              SignType.sign κ' = SignType.sign (σ' * (-1) ^ k) := by
  obtain ⟨δ1, h1s, hδ1, h1sp, Hs⟩ := soft_sum_sign CL CR hM hf
  obtain ⟨Cc, hw0, hw0p, HW⟩ := soft_window_label CL CR hM hf hm hLm Cs0
  obtain ⟨Ck, Dk, cn, h0b, h0bp, hCk, hDk, hcn, Hm⟩ := soft_match CL CR hf hm hLm hM 0
  obtain ⟨Cc1, h0a, clam, Clam, h0apos, hclam, Ha⟩ := propThaW2_item1 CL hf hm hLm
  obtain ⟨Cc2, h0aR, clamR, ClamR, h0aRpos, hclamR, HaR⟩ := propThaW2_item1 CR hf hm hLm
  have hCmu := CL.consts_pos2.1
  have hK : 0 ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu := mul_nonneg (Nat.cast_nonneg _) hCmu
  have hLpos := Fz.L_pos
  set ε1 : ℝ := min (δ1 / (|Cc| + 1)) (min (1 / (2 * (Dk + 1))) (1 / (16 * (|Cc| + 1)))) with hε1
  have hε1p : 0 < ε1 := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  obtain ⟨hL0, hL0p, HLs⟩ := CL.Lm_small ε1 hε1p
  obtain ⟨h0, h0p, h0le⟩ : ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, h ≤ h0 → h ≤ h1s ∧ h ≤ hw0 ∧ h ≤ h0b ∧ h ≤ CL.softH1 ∧ h ≤ CR.softH1 ∧
      h ≤ CL.η ∧ h ≤ CR.η ∧ h ≤ h0a ∧ h ≤ h0aR ∧ h ≤ 1 ∧ h ≤ Fz.L / 2 ∧ h ≤ hL0 ∧
      h ≤ 1 / (16 * (((q / 2 : ℕ) : ℝ) * CL.Cmu + 1)) ∧ h ≤ asmH0 CL ∧ h ≤ asmH0 CR := by
    refine ⟨min h1s (min hw0 (min h0b (min CL.softH1 (min CR.softH1 (min CL.η (min CR.η (min h0a (min h0aR
      (min 1 (min (Fz.L / 2) (min hL0 (min (1 / (16 * (((q / 2 : ℕ) : ℝ) * CL.Cmu + 1))) (min (asmH0 CL) (asmH0 CR)))))))))))))), ?_,
      fun h hh => by simpa only [le_min_iff] using hh⟩
    simp only [lt_min_iff]
    exact ⟨h1sp, hw0p, h0bp, CL.softH1_pos, CR.softH1_pos, CL.consts_pos.2.1, CR.consts_pos.2.1, h0apos, h0aRpos, one_pos,
      by positivity, hL0p, by positivity, asmH0_pos CL, asmH0_pos CR⟩
  refine ⟨h0, h0p, ?_⟩
  intro p hp N hN hstep
  obtain ⟨hs1s, hsw, hsb, hsH1, hsH1R, hsη, hsηR, hs0a, hs0aR, hs1, hsL, hsL0, hsK, hsA, hsAR⟩ := h0le _ hstep
  have hh : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hN1' : 1 ≤ N := by
    by_contra hc
    have hN0' : N = 0 := by omega
    subst hN0'
    have e : Fz.step 0 = Fz.L := by simp [SymbolFamily.step, FormalResearch.JB.stepSize]
    rw [e] at hsL
    linarith
  -- the constant sign of `lambda_L lambda_R`
  have hset : {X : ℝ | |X - Fz.bandHi p| ≤ CL.δ0} = Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmem : ∀ X : ℝ, |X - Fz.bandHi p| ≤ CL.δ0 → X ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) := by
    intro X hX
    rw [← hset]; exact hX
  have hmem' : ∀ X ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0), |X - Fz.bandHi p| ≤ CL.δ0 := by
    intro X hX0
    rw [abs_le]; constructor <;> linarith [hX0.1, hX0.2]
  have hcontL : ContinuousOn (fun X => CL.lamL p X N) (Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0)) := by
    rw [← hset]; exact CL.lamL_continuousOn p hp N hN1
  have hcontR : ContinuousOn (fun X => CR.lamL p X N) (Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0)) :=
    (CR.lamL_continuousOn p hp N hN2).mono (fun X hX0 => (mirror_ctx hM hp (hmem' X hX0) hN1).2)
  have hneL : ∀ X ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0), CL.lamL p X N ≠ 0 := by
    intro X hX0
    have hlow := (Ha p hp N hN1 hs0a X (hmem' X hX0)).2.1
    have h1 : 0 < clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) := by
      have := softLam_pos CL p X N
      have := kappaBal_pos (CL.aOf p X N)
      positivity
    intro h0
    rw [h0, abs_zero] at hlow
    linarith
  have hneR : ∀ X ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0), CR.lamL p X N ≠ 0 := by
    intro X hX0
    have hlow := (HaR p hp N hN2 hs0aR X (mirror_ctx hM hp (hmem' X hX0) hN1).2).2.1
    have h1 : 0 < clamR * (softLam CR p X N * kappaBal (CR.aOf p X N)) := by
      have := softLam_pos CR p X N
      have := kappaBal_pos (CR.aOf p X N)
      positivity
    intro h0
    rw [h0, abs_zero] at hlow
    linarith
  have hsc := sign_const_of_cont (Set.ordConnected_Icc) (hcontL.mul hcontR)
    (fun X hX0 => mul_ne_zero (hneL X hX0) (hneR X hX0))
  have hmain : ∃ σ' : ℝ, (σ' = 1 ∨ σ' = -1) ∧ ∀ X ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0),
      SignType.sign (CL.lamL p X N * CR.lamL p X N) = SignType.sign σ' := by
    rcases hsc with hpos | hneg
    · exact ⟨1, Or.inl rfl, fun X hX0 => by rw [sign_pos (show 0 < CL.lamL p X N * CR.lamL p X N from hpos X hX0), sign_pos one_pos]⟩
    · exact ⟨-1, Or.inr rfl, fun X hX0 => by rw [sign_neg (show CL.lamL p X N * CR.lamL p X N < 0 from hneg X hX0), sign_neg (by norm_num : (-1 : ℝ) < 0)]⟩
  obtain ⟨σ', hσ', hσs⟩ := hmain
  refine ⟨σ', hσ', ?_⟩
  intro Xs Um hE hs0 i hXi k hwin κ' hκ'
  set X : ℝ := Xs i with hXdef
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hXi hN1
  have haR : CR.aOf p X N = CL.aOf p X N := aOf_mirror hM hp X N
  obtain ⟨ha0, j, hj⟩ := HW p hp N hN hsw Xs Um hE hs0 i hXi
  have hε : Fz.step N ^ m * Lm (Fz.step N) ≤ ε1 := by
    have h1 : Fz.step N * Lm (Fz.step N) ≤ ε1 := HLs _ hh hsL0
    have h2 : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hh.le hs1 (by omega)
    have h3 : 0 ≤ Lm (Fz.step N) := le_trans zero_le_one (hLm _ hh hs1)
    exact (mul_le_mul_of_nonneg_right h2 h3).trans h1
  have hCcε : |Cc| * ε1 ≤ min (δ1) (1 / 16) := by
    have e1 : |Cc| * ε1 ≤ |Cc| * (δ1 / (|Cc| + 1)) := mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
    have e2 : |Cc| * ε1 ≤ |Cc| * (1 / (16 * (|Cc| + 1))) :=
      mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) (abs_nonneg _)
    refine le_min ?_ ?_
    · refine e1.trans ?_
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg Cc]
    · refine e2.trans ?_
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Cc]
  have hjbd : |CL.muTilde p X N - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ |Cc| * ε1 * Fz.step N := by
    have h1 : |CL.muTilde p X N - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ Cc * Fz.step N ^ (m + 1) * Lm (Fz.step N) := hj
    refine h1.trans ?_
    have e : Cc * Fz.step N ^ (m + 1) * Lm (Fz.step N) = Cc * (Fz.step N ^ m * Lm (Fz.step N)) * Fz.step N := by ring
    rw [e]
    have h3 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := mul_nonneg (pow_nonneg hh.le _) (le_trans zero_le_one (hLm _ hh hs1))
    have h4 : Cc * (Fz.step N ^ m * Lm (Fz.step N)) ≤ |Cc| * ε1 :=
      (mul_le_mul_of_nonneg_right (le_abs_self Cc) h3).trans (mul_le_mul_of_nonneg_left hε (abs_nonneg _))
    exact mul_le_mul_of_nonneg_right h4 hh.le
  have hmt := ss_muTilde_sub_le CL hp hXi hs1
  have hKh : ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 ≤ Fz.step N / 16 := K_alg _ _ hK hh hsK
  have hjk : j = k := by
    refine idx_eq (Fz.step N) (CL.muTilde p X N) (CL.muS 0 p (Fz.bandHi p - X)) j k hh ?_ (hmt.trans hKh) hwin
    refine hjbd.trans ?_
    calc |Cc| * ε1 * Fz.step N ≤ (1 / 16) * Fz.step N :=
          mul_le_mul_of_nonneg_right (hCcε.trans (min_le_right _ _)) hh.le
      _ = Fz.step N / 16 := by ring
  subst hjk
  have hδ : |CL.aOf p X N + j + 1 / 2| ≤ δ1 := by
    have e : CL.aOf p X N + j + 1 / 2 = -(CL.muTilde p X N - ((j : ℝ) + 1 / 2) * Fz.step N) / Fz.step N := by
      rw [SoftEdgeCore.aOf_eq]; field_simp; ring
    rw [e, abs_div, abs_neg, abs_of_pos hh, div_le_iff₀ hh]
    exact hjbd.trans (mul_le_mul_of_nonneg_right (hCcε.trans (min_le_left _ _)) hh.le)
  -- exact solutions `psi^L = c_0 p`, `psi' = c_0' q(N - .)`
  have hpos := bondA_pos_all CL CR hM hp hXi hN1 hsH1 hsH1R
  have hNRL : (CL.chain p X N).NR ≤ N := by
    have := row_le_N Fz N (j := (CL.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CL.shape p hp X hXi N hN1
      have := (CL.ucη_in p hp).2
      have hη := CL.consts_pos.2.1
      linarith)
    exact_mod_cast this
  have hNRR : (CR.chain p X N).NR ≤ N := by
    have := row_le_N (mirrorFamily Fz) N (j := (CR.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CR.shape p hp X hXR N hNR
      have := (CR.ucη_in p hp).2
      have hη := CR.consts_pos.2.1
      linarith)
    exact_mod_cast this
  have hc0 : 0 < CL.psiHatL p X N 0 := psiHatL_zero_pos CL hp hXi hN1 hsη
  have hc0' : 0 < CR.psiHatL p X N 0 := psiHatL_zero_pos CR hp hXR hNR hsηR
  obtain ⟨hJL, h0L, hJR, h0R⟩ := pq_exact Fz p N hpos hN1' X (CL.psiHatL p X N 0) (CR.psiHatL p X N 0)
    (CL.chain p X N).NR (CR.chain p X N).NR hNRL hNRR
  have hκ'0 : κ' ≠ 0 := by
    intro h0
    have := hκ' 0 (Nat.zero_le N)
    rw [h0, zero_mul] at this
    have h1 : pSol Fz p N X 0 = 1 := rfl
    rw [h1] at this
    exact one_ne_zero this
  set κ : ℝ := κ' * CL.psiHatL p X N 0 / CR.psiHatL p X N 0 with hκdef
  have hκne : κ ≠ 0 := div_ne_zero (mul_ne_zero hκ'0 hc0.ne') hc0'.ne'
  have hrel : ∀ n ∈ rowsOf N, (fun n => CL.psiHatL p X N 0 * pZ Fz p N X n) n =
      κ * (fun m => CR.psiHatL p X N 0 * qZ Fz p N X ((N : ℤ) - m)) ((N : ℤ) - n) := by
    intro n hn
    unfold rowsOf at hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Icc.mp hn
    show CL.psiHatL p X N 0 * pSol Fz p N X n.toNat = κ * (CR.psiHatL p X N 0 * qZ Fz p N X ((N : ℤ) - ((N : ℤ) - n)))
    have e2 : qZ Fz p N X ((N : ℤ) - ((N : ℤ) - n)) = qSol Fz p N X (N - n.toNat) := by
      unfold qZ; congr 1; omega
    rw [e2, hκ' n.toNat (by omega), hκdef]
    field_simp
  obtain ⟨-, -, hk, -, -⟩ := Hm p hp N hN1 hsb X hXi ha0 (fun n => CL.psiHatL p X N 0 * pZ Fz p N X n)
    (fun m => CR.psiHatL p X N 0 * qZ Fz p N X ((N : ℤ) - m)) κ hJL h0L hJR (by simpa using h0R) hrel
  have haRle : CR.aOf p X N ≤ 0 := by rw [haR]; exact ha0
  have hDk2 : Dk * (Fz.step N ^ m * Lm (Fz.step N)) ≤ 1 / 2 := by
    have e1 : Dk * (Fz.step N ^ m * Lm (Fz.step N)) ≤ Dk * ε1 := mul_le_mul_of_nonneg_left hε hDk
    refine e1.trans ?_
    have e2 : Dk * ε1 ≤ Dk * (1 / (2 * (Dk + 1))) :=
      mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hDk
    exact e2.trans (D_alg Dk hDk)
  have hsk : 0 < softKappa CL CR p X N * κ := by
    have h1 : |softKappa CL CR p X N - κ| ≤ (1 / 2) * |κ| :=
      hk.trans (mul_le_mul_of_nonneg_right hDk2 (abs_nonneg _))
    have h2 : |(softKappa CL CR p X N - κ) * κ| ≤ (1 / 2) * (κ * κ) := by
      rw [abs_mul]
      calc |softKappa CL CR p X N - κ| * |κ| ≤ ((1 / 2) * |κ|) * |κ| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = (1 / 2) * (κ * κ) := by rw [mul_assoc, abs_mul_abs_self]
    have h3 := (abs_le.mp h2).1
    have h4 : 0 < κ * κ := mul_self_pos.mpr hκne
    exact pos_alg _ _ h3 h4
  have hsignκ : SignType.sign κ' = SignType.sign κ := by
    have e : κ = κ' * (CL.psiHatL p X N 0 / CR.psiHatL p X N 0) := by rw [hκdef]; ring
    rw [e, sign_mul, sign_pos (div_pos hc0 hc0'), mul_one]
  have hsignK : SignType.sign (softKappa CL CR p X N) = SignType.sign κ := sign_of_mul_pos hsk
  -- the window sum
  set T : ℝ := ∑ n ∈ softWindow CL p X N,
    (CL.chain p X N).phi (Fz.step N) 0 2 n * (CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - n) with hT
  have hTpos := Hs p hp N hN hs1s X hXi j hδ
  have hsignT : SignType.sign ((-1 : ℝ) ^ j) = SignType.sign T := sign_of_mul_pos hTpos
  have hD : ∀ n ∈ softWindow CL p X N, CL.psiHatL p X N n * softSeqR CR p X N n =
      (CL.lamL p X N * CR.lamL p X N / kappaBal (CL.aOf p X N) ^ 2) *
        ((CL.chain p X N).phi (Fz.step N) 0 2 n * (CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - n)) := by
    intro n hn
    have hn' := (window_reflect hM hp X N n).mp hn
    obtain ⟨-, -, -, -, -, hgtL⟩ := win_row_pack CL hf 0 hp hXi hN1 ha0 hsA hn
    obtain ⟨-, -, -, -, -, hgtR⟩ := win_row_pack CR hf 0 hp hXR hNR haRle hsAR hn'
    have hκb := kappaBal_pos (CL.aOf p X N)
    unfold softSeqR
    rw [psiHatL_of_gt CL p X N hgtL, psiHatL_of_gt CR p X N hgtR, haR]
    field_simp
    rfl
  have hNn : ∑ n ∈ softWindow CL p X N, CL.psiHatL p X N n * softSeqR CR p X N n =
      (CL.lamL p X N * CR.lamL p X N / kappaBal (CL.aOf p X N) ^ 2) * T := by
    rw [hT, Finset.mul_sum]; exact Finset.sum_congr rfl hD
  have hκb2 : 0 < kappaBal (CL.aOf p X N) ^ 2 := by have := kappaBal_pos (CL.aOf p X N); positivity
  have hsignN : SignType.sign (∑ n ∈ softWindow CL p X N, CL.psiHatL p X N n * softSeqR CR p X N n) =
      SignType.sign (σ' * (-1) ^ j) := by
    rw [hNn, sign_mul, div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr hκb2), mul_one,
      hσs X (hmem X hXi), sign_mul, ← hsignT]
  -- `hat kappa = N / D` with `D > 0`
  have hkdef : softKappa CL CR p X N = (∑ n ∈ softWindow CL p X N, CL.psiHatL p X N n * softSeqR CR p X N n) /
      ∑ n ∈ softWindow CL p X N, softSeqR CR p X N n ^ 2 := rfl
  have hDnn : 0 ≤ ∑ n ∈ softWindow CL p X N, softSeqR CR p X N n ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hDpos : 0 < ∑ n ∈ softWindow CL p X N, softSeqR CR p X N n ^ 2 := by
    rcases hDnn.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [hkdef, ← h, div_zero, zero_mul] at hsk
      exact lt_irrefl _ hsk
  have hsignKN : SignType.sign (softKappa CL CR p X N) =
      SignType.sign (∑ n ∈ softWindow CL p X N, CL.psiHatL p X N n * softSeqR CR p X N n) := by
    rw [hkdef, div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr hDpos), mul_one]
  rw [hsignκ, ← hsignK, hsignKN, hsignN]

/-- **The sign hypotheses (ii), (iii) of `lem:tha-count` on the soft chart** (app_thmA Step 6): `SoftCountHyps CL CR Cs0`, from `soft_sign_D` and `soft_sign_kappa`. -/
theorem softCountHyps_proved (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (Cs0 : ℝ) : SoftCountHyps CL CR Cs0 := by
  obtain ⟨h1a, h1ap, Ha⟩ := soft_sign_D CL CR hM hf hm hLm
  obtain ⟨h1b, h1bp, Hb⟩ := soft_sign_kappa CL CR hM hf hm hLm Cs0
  refine ⟨min h1a h1b, lt_min h1ap h1bp, ?_⟩
  intro p hp N hN hstep
  exact ⟨Ha p hp N hN (hstep.trans (min_le_left _ _)), Hb p hp N hN (hstep.trans (min_le_right _ _))⟩

end Win


/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.reflect_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reflect_prod

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.uw_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uw_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.win_row_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_row_pack

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_win_u2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_win_u2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.row_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_alg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_sum_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_sum_sign

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_sign_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_sign_kappa

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softCountHyps_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms softCountHyps_proved

end FormalResearch.JacobiEigenvectors.TheoremA

end
