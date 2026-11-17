module

public import FormalResearch.Special.DiscreteLgBulk
public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.DiscreteAiryOscBi

/-!
# Discrete Liouville-Green matched to the Airy turning layer: Maslov offset `π/4` and `R = h^{1/6} |κ| / √π`

**Setting.**  A solution `Y` of the Jacobi rows has, near a simple turn, the Airy form `Y ≈ κ g Ai(X) + μ g Bi(X)` (`X = h^{-2/3} ζ`, `g` the Langer amplitude; this is
`DaiFull.pointwise`/`discrete_airy_full_unif`), and in the bulk the Liouville-Green form of `DiscreteLgBulk`.  This module identifies the two on an overlap.

**Chart relations** (abstract hypotheses at the two matching sites; for the Langer chart of `u = cos θ` they follow from `langerZeta_integral` and
`langerAmp_of_coeff`):
* `y = -X > 0`, `g y^{-1/4} = h^{1/6} w` (the Langer amplitude `g = w |ζ|^{1/4}`);
* `(2/3) y^{3/2} = Θ*/h - Θ(q)/h` (the Langer phase is the Liouville-Green phase measured from the turn: `(2/3)(-ζ)^{3/2} = ∫_q^c θ`);
* `Θ* - Θ(q) ≥ Φ_min > 0` (the overlap is at macroscopic phase distance from the turn).

**Results.**
* `dlgm_site`: at one site, `|Y - h^{1/6} π^{-1/2} w (κ cos χ + μ sin χ)| ≤ (|κ| + |μ|)(1/(12 Φ_min) + C_a/g_min) h^{1/6} h w`, with the phase
  `χ = Θ(q)/h - Θ*/h + π/4`.  I.e. `g Ai(X) ≈ h^{1/6} π^{-1/2} w cos χ`, `g Bi(X) ≈ h^{1/6} π^{-1/2} w sin χ` (`Ai(-y) ~ π^{-1/2} y^{-1/4} cos(ξ - π/4)`).
* `dlg_airy_match`: transported across the whole bulk window `[J, N+1]`:
  `|Y_k - h^{1/6} π^{-1/2} w_k (κ cos χ_k + μ sin χ_k)| ≤ C h^{1/6} h (|κ| + |μ|) w_k`.  For `μ = 0`: `Y_k = h^{1/6} κ π^{-1/2} w_k [cos(Θ_k/h - Θ*/h + π/4) + O(h)]`,
  i.e. amplitude `R = h^{1/6} |κ|/√π` and phase offset **exactly `π/4`** (the Maslov index of a simple turn); the sign of `κ` is the sign of the cosine factor.

**Claim class: proved** (the chart relations are hypotheses).  **Not formalised here:** `κ`, `μ` themselves (`κ ≠ 0` is `hahn_chain_kappa`, the sharp value is open here).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

lemma dlgm_rpow_split {y : ℝ} (hy : 0 < y) :
    y ^ (-(7 / 4) : ℝ) = y ^ (-(1 / 4) : ℝ) * (y ^ (3 / 2 : ℝ))⁻¹ := by
  rw [← Real.rpow_neg hy.le, ← Real.rpow_add hy]; norm_num

/-- **One-site matching** of the Airy form with the cos/sin pair (see the module docstring). -/
theorem dlgm_site {κ μ g y w h Ts P Φmin Ca gmin Y : ℝ} (hh : 0 < h) (hy : 0 < y)
    (hM2 : g * y ^ (-(1 / 4) : ℝ) = h ^ (1 / 6 : ℝ) * w) (hM3 : 2 / 3 * y ^ (3 / 2 : ℝ) = Ts / h - P)
    (hM4 : Φmin ≤ Ts - h * P) (hΦ : 0 < Φmin) (hg : gmin ≤ g) (hgmin : 0 < gmin) (hw : 0 ≤ w) (hCa : 0 ≤ Ca)
    (hY : |Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y)))| ≤ Ca * h * ((|κ| + |μ|) * y ^ (-(1 / 4) : ℝ))) :
    |Y - h ^ (1 / 6 : ℝ) * (1 / √π) * w * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4))| ≤
      (|κ| + |μ|) * (1 / (12 * Φmin) + Ca / gmin) * (h ^ (1 / 6 : ℝ) * h) * w := by
  have hr : 0 < y ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hy _
  have ht : 0 < y ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hy _
  have hg0 : 0 < g := hgmin.trans_le hg
  have hh6 : 0 < h ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hh _
  have hAi := airyAi_neg_asymptotic hy
  have hBi := airyBi_neg_asymptotic hy
  rw [hM3] at hAi hBi
  have hcos : Real.cos (Ts / h - P - π / 4) = Real.cos (P - Ts / h + π / 4) := by
    rw [← Real.cos_neg]; congr 1; ring
  have hsin : Real.sin (Ts / h - P - π / 4) = -Real.sin (P - Ts / h + π / 4) := by
    rw [← Real.sin_neg]; congr 1; ring
  rw [hcos] at hAi
  rw [hsin] at hBi
  -- the remainder
  have hrem : g * y ^ (-(7 / 4) : ℝ) ≤ h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin)) := by
    rw [dlgm_rpow_split hy, ← mul_assoc, hM2]
    have hinv : (y ^ (3 / 2 : ℝ))⁻¹ ≤ 2 / 3 * h / Φmin := by
      have h1 : 3 / 2 * (Φmin / h) ≤ y ^ (3 / 2 : ℝ) := by
        have : Ts / h - P = (Ts - h * P) / h := by field_simp
        have h2 : y ^ (3 / 2 : ℝ) = 3 / 2 * (Ts / h - P) := by linarith
        rw [h2, this]
        have : Φmin / h ≤ (Ts - h * P) / h := div_le_div_of_nonneg_right hM4 hh.le
        linarith
      have hpos : 0 < 3 / 2 * (Φmin / h) := by positivity
      calc (y ^ (3 / 2 : ℝ))⁻¹ ≤ (3 / 2 * (Φmin / h))⁻¹ := inv_anti₀ hpos h1
        _ = 2 / 3 * h / Φmin := by field_simp
    calc h ^ (1 / 6 : ℝ) * w * (y ^ (3 / 2 : ℝ))⁻¹ ≤ h ^ (1 / 6 : ℝ) * w * (2 / 3 * h / Φmin) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin)) := by field_simp
  -- decomposition
  set T : ℝ := h ^ (1 / 6 : ℝ) * (1 / √π) * w with hT
  have hT' : T = 1 / √π * (g * y ^ (-(1 / 4) : ℝ)) := by rw [hM2, hT]; ring
  have e1 : g * airyAi (-y) = T * Real.cos (P - Ts / h + π / 4) +
      g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4)) := by
    rw [hT']; ring
  have e2 : g * airyBi (-y) = T * Real.sin (P - Ts / h + π / 4) +
      g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4))) := by
    rw [hT']; ring
  have b1 : |g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))| ≤
      h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin)) := by
    rw [abs_mul, abs_of_pos hg0]
    calc _ ≤ g * (1 / 8 * y ^ (-(7 / 4) : ℝ)) := mul_le_mul_of_nonneg_left hAi hg0.le
      _ = 1 / 8 * (g * y ^ (-(7 / 4) : ℝ)) := by ring
      _ ≤ 1 / 8 * (h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin))) := by linarith
      _ = _ := by field_simp; ring
  have b2 : |g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4)))| ≤
      h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin)) := by
    rw [abs_mul, abs_of_pos hg0]
    calc _ ≤ g * (1 / 8 * y ^ (-(7 / 4) : ℝ)) := mul_le_mul_of_nonneg_left hBi hg0.le
      _ = 1 / 8 * (g * y ^ (-(7 / 4) : ℝ)) := by ring
      _ ≤ 1 / 8 * (h ^ (1 / 6 : ℝ) * h * w * (2 / (3 * Φmin))) := by linarith
      _ = _ := by field_simp; ring
  have hrg : y ^ (-(1 / 4) : ℝ) ≤ h ^ (1 / 6 : ℝ) * w / gmin := by
    rw [le_div_iff₀ hgmin]
    calc y ^ (-(1 / 4) : ℝ) * gmin ≤ y ^ (-(1 / 4) : ℝ) * g := mul_le_mul_of_nonneg_left hg hr.le
      _ = h ^ (1 / 6 : ℝ) * w := by rw [mul_comm]; exact hM2
  have e3 : Y - T * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4)) =
      (Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y)))) +
        κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))) +
        μ * (g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4)))) := by
    rw [e1, e2]; ring
  have e4 : h ^ (1 / 6 : ℝ) * (1 / √π) * w * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4)) =
      T * (κ * Real.cos (P - Ts / h + π / 4) + μ * Real.sin (P - Ts / h + π / 4)) := by rw [hT]
  rw [e4, e3]
  have t1 : |Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y)))| ≤
      Ca * h * ((|κ| + |μ|) * (h ^ (1 / 6 : ℝ) * w / gmin)) :=
    hY.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrg (by positivity)) (by positivity))
  have t2 : |κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4)))| ≤
      |κ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left b1 (abs_nonneg _)
  have t3 : |μ * (g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4))))| ≤
      |μ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left b2 (abs_nonneg _)
  have s1 := abs_add_le (Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y))) +
    κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))))
    (μ * (g * (airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * (-Real.sin (P - Ts / h + π / 4)))))
  have s2 := abs_add_le (Y - (κ * (g * airyAi (-y)) + μ * (g * airyBi (-y))))
    (κ * (g * (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (P - Ts / h + π / 4))))
  have key : Ca * h * ((|κ| + |μ|) * (h ^ (1 / 6 : ℝ) * w / gmin)) +
      |κ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) + |μ| * (h ^ (1 / 6 : ℝ) * h * w * (1 / (12 * Φmin))) =
      (|κ| + |μ|) * (1 / (12 * Φmin) + Ca / gmin) * (h ^ (1 / 6 : ℝ) * h) * w := by
    ring
  linarith


lemma dlgm_vocA_sub (a Y Z φ ψ : ℤ → ℝ) (m : ℤ) :
    vocA a (fun i => Y i - Z i) φ ψ m = vocA a Y φ ψ m - vocA a Z φ ψ m := by
  unfold vocA cas; rw [← sub_div]; congr 1; ring

lemma dlgm_vocB_sub (a Y Z φ ψ : ℤ → ℝ) (m : ℤ) :
    vocB a (fun i => Y i - Z i) φ ψ m = vocB a Y φ ψ m - vocB a Z φ ψ m := by
  unfold vocB cas; rw [← sub_div]; congr 1; ring

lemma dlgm_vocA_comb (a φ ψ : ℤ → ℝ) (x y : ℝ) (m : ℤ) (hd : cas a φ ψ m ≠ 0) :
    vocA a (fun i => x * φ i + y * ψ i) φ ψ m = x := by
  unfold vocA
  rw [div_eq_iff hd]; unfold cas; ring

lemma dlgm_vocB_comb (a φ ψ : ℤ → ℝ) (x y : ℝ) (m : ℤ) (hd : cas a φ ψ m ≠ 0) :
    vocB a (fun i => x * φ i + y * ψ i) φ ψ m = y := by
  unfold vocB
  rw [div_eq_iff hd]; unfold cas; ring

lemma dlgm_phi_le (w Θ : ℝ → ℝ) (q0 h : ℝ) (k : ℤ) (hw : 0 ≤ w (dlgQ q0 h k)) :
    |dlgPhi w Θ q0 h k| ≤ w (dlgQ q0 h k) := by
  unfold dlgPhi
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw (Real.abs_cos_le_one _)

lemma dlgm_psi_le (w Θ : ℝ → ℝ) (q0 h : ℝ) (k : ℤ) (hw : 0 ≤ w (dlgQ q0 h k)) :
    |dlgPsi w Θ q0 h k| ≤ w (dlgQ q0 h k) := by
  unfold dlgPsi
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw (Real.abs_sin_le_one _)


lemma dlgm_arith {C1 K h X nα Dq e : ℝ} (hC1 : 0 < C1) (hK0 : 0 ≤ K) (hh : 0 < h) (hh1 : h ≤ 1) (hX : 0 ≤ X)
    (hn : nα ≤ X + 2 * Dq) (hDq : Dq = 4 * K * e) (he : 0 ≤ e) :
    C1 * (h * nα) + 2 * Dq ≤ (C1 * (1 + 8 * K) + 8 * K + 1) * (h * X + e) := by
  have hD0 : 0 ≤ Dq := by rw [hDq]; positivity
  have h1 : h * nα ≤ h * X + 2 * Dq := by
    have a := mul_le_mul_of_nonneg_left hn hh.le
    have b : h * (2 * Dq) ≤ 2 * Dq := mul_le_of_le_one_left (by positivity) hh1
    linarith
  have h2 : C1 * (h * nα) ≤ C1 * (h * X) + C1 * (2 * Dq) := by
    have := mul_le_mul_of_nonneg_left h1 hC1.le; linarith
  have hP : 0 ≤ h * X := by positivity
  have e1 : (C1 * (1 + 8 * K) + 8 * K + 1) * (h * X + e) - (C1 * (h * X) + C1 * (2 * Dq) + 2 * Dq) =
      C1 * e + 8 * C1 * K * (h * X) + 8 * K * (h * X) + h * X + e := by rw [hDq]; ring
  have e2 : 0 ≤ C1 * e + 8 * C1 * K * (h * X) + 8 * K * (h * X) + h * X + e := by positivity
  linarith

/-- **Matching core.**  If an exact solution `Y` agrees with the LG combination `x φ + y ψ` at the two sites `m, m+1` up to `ε w`, then it agrees on the
whole bulk window up to `C (h (|x| + |y|) + ε) w`. -/
theorem dlg_match_core (lo hi M E L : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hM : 0 ≤ M) (hE : 0 ≤ E) (hL : 0 ≤ L) :
    ∃ h0 C : ℝ, 0 < h0 ∧ h0 ≤ 1 ∧ 0 < C ∧
      ∀ {A θ w Θ : ℝ → ℝ} {U : Set ℝ}, DlgData A θ w Θ U lo hi M →
      ∀ (q0 h : ℝ) (a c Y : ℤ → ℝ) (J N m : ℤ) (x y ε : ℝ), 0 < h → h ≤ h0 → J ≤ m → m ≤ N → ((N - J : ℤ) : ℝ) * h ≤ L →
        (∀ k ∈ Icc J (N + 1), dlgQ q0 h k ∈ U) →
        (∀ k ∈ Icc (J + 1) (N + 1), |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, |c k - 2 * A (dlgQ q0 h k) * Real.cos (θ (dlgQ q0 h k))| ≤ E * h ^ 2) →
        (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) →
        |Y m - (x * dlgPhi w Θ q0 h m + y * dlgPsi w Θ q0 h m)| ≤ ε * w (dlgQ q0 h m) →
        |Y (m + 1) - (x * dlgPhi w Θ q0 h (m + 1) + y * dlgPsi w Θ q0 h (m + 1))| ≤ ε * w (dlgQ q0 h (m + 1)) →
        ∀ k ∈ Icc J (N + 1),
          |Y k - (x * dlgPhi w Θ q0 h k + y * dlgPsi w Θ q0 h k)| ≤ C * (h * (|x| + |y|) + |ε|) * w (dlgQ q0 h k) := by
  obtain ⟨h1, C1, hh1, hh11, hC1, H1⟩ := dlg_bulk_cart lo hi M E L hlo hhi hM hE hL
  obtain ⟨h2, C2, hh2, hh21, hC2, hCa, hCb, hCd, H2⟩ := dlg_bulk_core lo hi M E L hlo hhi hM hE hL
  have hpe : 0 ≤ (hi + E) * hi := mul_nonneg (by linarith) hhi
  refine ⟨min h1 h2, C1 * (1 + 8 * (hi + E) * hi ^ 2) + 8 * (hi + E) * hi ^ 2 + 1, lt_min hh1 hh2,
    (min_le_left _ _).trans hh11, by positivity, ?_⟩
  intro A θ w Θ U D q0 h a c Y J N m x y ε hh hhm hJm hmN hlen hU hA hCc hY e0 e1 k hk
  have hh1' : h ≤ h1 := hhm.trans (min_le_left _ _)
  have hh2' : h ≤ h2 := hhm.trans (min_le_right _ _)
  obtain ⟨hc1, hc2, hc3⟩ := H1 D q0 h a c Y J N m hh hh1' hJm hmN hlen hU hA hCc hY
  obtain ⟨hcas, ham, -⟩ := H2 D q0 h a c Y J N m hh hh2' hJm hmN hlen hU hA hCc hY
  have hmI : m ∈ Icc J N := by rw [Finset.mem_Icc]; omega
  have hwk : ∀ k ∈ Icc J (N + 1), 0 ≤ w (dlgQ q0 h k) ∧ w (dlgQ q0 h k) ≤ hi := fun k hk =>
    ⟨(D.lo_pos.trans_le (D.wb _ (hU k hk)).1).le, (D.wb _ (hU k hk)).2⟩
  have hm0 := hwk m (by rw [Finset.mem_Icc]; omega)
  have hm1 := hwk (m + 1) (by rw [Finset.mem_Icc]; omega)
  have hc : 1 / 2 ≤ cas a (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m := hcas m hmI
  have hne : cas a (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m ≠ 0 := by intro h0; rw [h0] at hc; norm_num at hc
  -- Cramer coefficients of the defect
  have hφ0 := (dlgm_phi_le w Θ q0 h m hm0.1).trans hm0.2
  have hφ1 := (dlgm_phi_le w Θ q0 h (m + 1) hm1.1).trans hm1.2
  have hψ0 := (dlgm_psi_le w Θ q0 h m hm0.1).trans hm0.2
  have hψ1 := (dlgm_psi_le w Θ q0 h (m + 1) hm1.1).trans hm1.2
  have hε : 0 ≤ |ε| := abs_nonneg _
  have hD0 : |Y m - (x * dlgPhi w Θ q0 h m + y * dlgPsi w Θ q0 h m)| ≤ |ε| * hi :=
    e0.trans (mul_le_mul (le_abs_self ε) hm0.2 hm0.1 hε)
  have hD1 : |Y (m + 1) - (x * dlgPhi w Θ q0 h (m + 1) + y * dlgPsi w Θ q0 h (m + 1))| ≤ |ε| * hi :=
    e1.trans (mul_le_mul (le_abs_self ε) hm1.2 hm1.1 hε)
  obtain ⟨cA, cB⟩ := dlg_cramer_size (a := a)
    (Y := fun i => Y i - (x * dlgPhi w Θ q0 h i + y * dlgPsi w Θ q0 h i)) (φ := dlgPhi w Θ q0 h) (ψ := dlgPsi w Θ q0 h)
    (m := m) (hi := hi) (E := E) hc ham hφ0 hφ1 hψ0 hψ1
  rw [dlgm_vocA_sub, dlgm_vocA_comb a _ _ x y m hne] at cA
  rw [dlgm_vocB_sub, dlgm_vocB_comb a _ _ x y m hne] at cB
  set α := vocA a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m with hα
  set β := vocB a Y (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) m with hβ
  set Dq : ℝ := 2 * ((hi + E) * (hi * (|ε| * hi + |ε| * hi))) with hDq
  have hDn : 0 ≤ Dq := by positivity
  have hs : |Y m - (x * dlgPhi w Θ q0 h m + y * dlgPsi w Θ q0 h m)| +
      |Y (m + 1) - (x * dlgPhi w Θ q0 h (m + 1) + y * dlgPsi w Θ q0 h (m + 1))| ≤ |ε| * hi + |ε| * hi :=
    add_le_add hD0 hD1
  have hpe' : 0 ≤ hi + E := by linarith
  have hDle : 2 * ((hi + E) * (hi * (|Y m - (x * dlgPhi w Θ q0 h m + y * dlgPsi w Θ q0 h m)| +
      |Y (m + 1) - (x * dlgPhi w Θ q0 h (m + 1) + y * dlgPsi w Θ q0 h (m + 1))|))) ≤ Dq :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hhi) hpe') (by norm_num)
  have cA' : |α - x| ≤ Dq := cA.trans hDle
  have cB' : |β - y| ≤ Dq := cB.trans hDle
  have hwk0 := hwk k hk
  have hα' : |α| + |β| ≤ |x| + |y| + 2 * Dq := by
    have h1 : |α| ≤ |x| + |α - x| := by
      have := abs_add_le x (α - x); rwa [show x + (α - x) = α by ring] at this
    have h2 : |β| ≤ |y| + |β - y| := by
      have := abs_add_le y (β - y); rwa [show y + (β - y) = β by ring] at this
    linarith
  have P1 := hc1 k hk
  have P2 : |(α - x) * dlgPhi w Θ q0 h k| ≤ Dq * w (dlgQ q0 h k) := by
    rw [abs_mul]; exact mul_le_mul cA' (dlgm_phi_le w Θ q0 h k hwk0.1) (abs_nonneg _) hDn
  have P3 : |(β - y) * dlgPsi w Θ q0 h k| ≤ Dq * w (dlgQ q0 h k) := by
    rw [abs_mul]; exact mul_le_mul cB' (dlgm_psi_le w Θ q0 h k hwk0.1) (abs_nonneg _) hDn
  have hsplit : Y k - (x * dlgPhi w Θ q0 h k + y * dlgPsi w Θ q0 h k) =
      (Y k - (α * dlgPhi w Θ q0 h k + β * dlgPsi w Θ q0 h k)) + (α - x) * dlgPhi w Θ q0 h k +
        (β - y) * dlgPsi w Θ q0 h k := by ring
  have T1 : |Y k - (x * dlgPhi w Θ q0 h k + y * dlgPsi w Θ q0 h k)| ≤
      C1 * h * (|α| + |β|) * w (dlgQ q0 h k) + Dq * w (dlgQ q0 h k) + Dq * w (dlgQ q0 h k) := by
    rw [hsplit]
    have s1 := abs_add_le (Y k - (α * dlgPhi w Θ q0 h k + β * dlgPsi w Θ q0 h k) + (α - x) * dlgPhi w Θ q0 h k)
      ((β - y) * dlgPsi w Θ q0 h k)
    have s2 := abs_add_le (Y k - (α * dlgPhi w Θ q0 h k + β * dlgPsi w Θ q0 h k)) ((α - x) * dlgPhi w Θ q0 h k)
    linarith
  have hK : Dq = 4 * ((hi + E) * hi ^ 2) * |ε| := by rw [hDq]; ring
  have hK0 : 0 ≤ (hi + E) * hi ^ 2 := by positivity
  have step := dlgm_arith hC1 hK0 hh (hh1'.trans hh11) (by positivity : 0 ≤ |x| + |y|) hα' hK hε
  rw [show 8 * (hi + E) * hi ^ 2 = 8 * ((hi + E) * hi ^ 2) by ring]
  calc _ ≤ _ := T1
    _ = (C1 * (h * (|α| + |β|)) + 2 * Dq) * w (dlgQ q0 h k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right step hwk0.1

end FormalResearch.Special
