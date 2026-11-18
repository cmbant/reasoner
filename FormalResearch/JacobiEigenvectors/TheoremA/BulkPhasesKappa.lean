module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkPhases
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkPhase
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkProof
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkConj1
public import FormalResearch.JacobiEigenvectors.TheoremA.Count

/-!
# Paper J, Layer 2: the sign of `kappa'` at an eigenvalue of a bulk window (`lem:smo-bulkphase` (3) (iii), L2.S1)

Source: Paper J `app_thmA.tex`, proof of `lem:smo-bulkphase` (3) (iii) ("the sign of `kappa'` at an eigenvalue").  The ingredients of the argument, in the form used by
`bulk_kappa_sign` (`TheoremA/BulkWindows.lean`):

* `thetaL_add_mirror`: `Theta_L(u) + Theta_R(L - u) = S_0` (the right phase is the left phase of the mirror chart; `actInt_mirror`).
* `thetaL_incr`: under the uniform margin `|X - B_0| <= (1 - eps) 2 sqrt(E_0)` on `[c', c]`, `Theta_L` advances by an angle in `[h theta_1, h (pi - theta_1)]` over a step `h`, `theta_1 = arccos(1 - eps) > 0`.
* `cos_sq_pair`: `cos^2 alpha + cos^2 (alpha + theta) >= 1 - cos theta_1` for `theta in [theta_1, pi - theta_1]`: of two consecutive rows one has `cos^2 >= eps/2`.
* `exact_phase_row`: the exact edge solution seeded by `psi-hat_0` has the phase `Theta_L/h - pi/4` on every overlap row with a positive amplitude (`bulk_phase_left` plus `prop:tha-W` (1)).
* `cos_beta_rel`, `row_product_pos`: the arithmetic: `alpha + beta = pi k + delta` gives `cos beta = (-1)^k cos alpha + O(h)`, and then `(-1)^k f g > 0` when `cos^2 alpha >= kappa_0 > O(h)`.
* `stdAssump_hyp_C2`: `StdAssump` gives `(H1)`--`(H3)` and `C^2` principal symbols.

## Differences from the paper

The paper argues with `sin theta` (`rho` varies slowly); here two consecutive rows and the uniform step margin `theta_margin` are used instead, which needs no regularity of `rho` in `n`.

## Not formalised

The identification of the window label `k` with the eigenvalue index (soft-edge window `0`, `L2.C7`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set MeasureTheory FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

/-! ### Phases of the action: the mirror and the increment over one step -/

section Action

variable {L g : ℝ} {G0 B0 : ℝ → ℝ}

lemma actInt_mirror (X v : ℝ) :
    Real.arccos ((X - (fun s => B0 (L - s)) v) / (2 * Real.sqrt (E0 L (fun s => G0 (L - s)) v)))
      = actInt L G0 B0 X (L - v) := by
  unfold actInt
  have : E0 L (fun s => G0 (L - s)) v = E0 L G0 (L - v) := by
    unfold E0; ring_nf
  rw [this]

/-- `Theta_L(u) + Theta_R(u) = S_0` (`Theta_R` is the mirror chart's `Theta` at `L - u`). -/
lemma thetaL_add_mirror (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (X : ℝ) {u : ℝ} (hu : u ∈ Icc 0 L) :
    thetaL L G0 B0 X u + thetaL L (fun s => G0 (L - s)) (fun s => B0 (L - s)) X (L - u)
      = ∫ v in (0 : ℝ)..L, actInt L G0 B0 X v := by
  have hi := intervalIntegrable_arccos_action hL hyp hG2 hB2 X
  have h1 : thetaL L G0 B0 X u = ∫ v in (0 : ℝ)..u, actInt L G0 B0 X v := rfl
  have h2 : thetaL L (fun s => G0 (L - s)) (fun s => B0 (L - s)) X (L - u)
      = ∫ v in (0 : ℝ)..(L - u), actInt L G0 B0 X (L - v) := by
    unfold thetaL
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    exact actInt_mirror X v
  have h3 : ∫ v in (0 : ℝ)..(L - u), actInt L G0 B0 X (L - v) = ∫ v in u..L, actInt L G0 B0 X v := by
    have := intervalIntegral.integral_comp_sub_left (fun x => actInt L G0 B0 X x) (a := 0) (b := L - u) L
    simpa using this
  have hi1 : IntervalIntegrable (actInt L G0 B0 X) volume 0 u :=
    hi.mono_set (by rw [uIcc_of_le hu.1, uIcc_of_le hL.le]; exact Icc_subset_Icc le_rfl hu.2)
  have hi2 : IntervalIntegrable (actInt L G0 B0 X) volume u L :=
    hi.mono_set (by rw [uIcc_of_le hu.2, uIcc_of_le hL.le]; exact Icc_subset_Icc hu.1 le_rfl)
  rw [h1, h2, h3]
  exact intervalIntegral.integral_add_adjacent_intervals hi1 hi2

/-- With the uniform margin `|X - B_0| <= (1 - eps) 2 sqrt E_0` on `[c', c]`, the phase `Theta_L` advances by an amount in `[h theta_1, h (pi - theta_1)]`,
`theta_1 = arccos(1 - eps) > 0`, over a step `h` inside `[c', c]`. -/
lemma thetaL_incr (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L)) (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L))
    (X : ℝ) {c' c ε : ℝ} (hc'pos : 0 < c') (hcL : c < L) (hε : ε < 1)
    (hmargin : ∀ v ∈ Icc c' c, |X - B0 v| ≤ (1 - ε) * (2 * Real.sqrt (E0 L G0 v)))
    {u u' : ℝ} (hu : c' ≤ u) (huu' : u ≤ u') (hu' : u' ≤ c) :
    (u' - u) * Real.arccos (1 - ε) ≤ thetaL L G0 B0 X u' - thetaL L G0 B0 X u ∧
      thetaL L G0 B0 X u' - thetaL L G0 B0 X u ≤ (u' - u) * (Real.pi - Real.arccos (1 - ε)) := by
  have hi := intervalIntegrable_arccos_action hL hyp hG2 hB2 X
  have hu0 : 0 ≤ u := by linarith
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ L → IntervalIntegrable (actInt L G0 B0 X) volume a b := fun a b ha hab hb =>
    hi.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hL.le]; exact Icc_subset_Icc ha hb)
  have hdiff : thetaL L G0 B0 X u' - thetaL L G0 B0 X u = ∫ v in u..u', actInt L G0 B0 X v := by
    have e1 : thetaL L G0 B0 X u' = ∫ v in (0 : ℝ)..u', actInt L G0 B0 X v := rfl
    have e2 : thetaL L G0 B0 X u = ∫ v in (0 : ℝ)..u, actInt L G0 B0 X v := rfl
    rw [e1, e2, ← intervalIntegral.integral_add_adjacent_intervals (hsub 0 u le_rfl hu0 (by linarith))
      (hsub u u' hu0 huu' (by linarith))]
    ring
  have hbd : ∀ v ∈ Icc u u', Real.arccos (1 - ε) ≤ actInt L G0 B0 X v ∧ actInt L G0 B0 X v ≤ Real.pi - Real.arccos (1 - ε) := by
    intro v hv
    have hvc : v ∈ Icc c' c := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hvmem : v ∈ Ioo 0 L := ⟨by linarith [hvc.1], by linarith [hvc.2]⟩
    have hE := HypMorse.E0_pos hyp.G0_lb hyp.gstar_pos hvmem
    have hs := Real.sqrt_pos.mpr hE
    have hm := hmargin v hvc
    have hden : 0 < 2 * Real.sqrt (E0 L G0 v) := by positivity
    have ha := abs_le.mp hm
    unfold actInt
    set a := (X - B0 v) / (2 * Real.sqrt (E0 L G0 v)) with ha_def
    have h1 : a ≤ 1 - ε := by rw [ha_def, div_le_iff₀ hden]; linarith [ha.2]
    have h2 : -(1 - ε) ≤ a := by rw [ha_def, le_div_iff₀ hden]; linarith [ha.1]
    refine ⟨Real.arccos_le_arccos h1, ?_⟩
    have := Real.arccos_le_arccos h2
    rw [Real.arccos_neg] at this
    exact this
  rw [hdiff]
  have hint := hsub u u' hu0 huu' (by linarith)
  constructor
  · have := intervalIntegral.integral_mono_on huu' (intervalIntegrable_const (c := Real.arccos (1 - ε))) hint
      (fun v hv => (hbd v hv).1)
    simpa using this
  · have := intervalIntegral.integral_mono_on huu' hint (intervalIntegrable_const (c := Real.pi - Real.arccos (1 - ε)))
      (fun v hv => (hbd v hv).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith

/-- `cos^2 alpha + cos^2 (alpha + theta) >= 1 - cos(theta_1)` for `theta in [theta_1, pi - theta_1]`, `0 < theta_1 <= pi/2`. -/
lemma cos_sq_pair (α θ θ1 : ℝ) (h1 : 0 < θ1) (h2 : θ1 ≤ Real.pi / 2) (hθ1 : θ1 ≤ θ) (hθ2 : θ ≤ Real.pi - θ1) :
    1 - Real.cos θ1 ≤ Real.cos α ^ 2 + Real.cos (α + θ) ^ 2 := by
  have hcos : |Real.cos θ| ≤ Real.cos θ1 := by
    have hpi := Real.pi_pos
    have ha : Real.cos θ ≤ Real.cos θ1 :=
      Real.cos_le_cos_of_nonneg_of_le_pi h1.le (by linarith) hθ1
    have hb : Real.cos (Real.pi - θ1) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hθ2
    rw [Real.cos_pi_sub] at hb
    exact abs_le.mpr ⟨by linarith, ha⟩
  have e : Real.cos α ^ 2 + Real.cos (α + θ) ^ 2 = 1 + Real.cos (2 * α + θ) * Real.cos θ := by
    have h1 := Real.cos_sq α
    have h2 := Real.cos_sq (α + θ)
    have h2' : Real.cos (2 * (α + θ)) = Real.cos (2 * α + 2 * θ) := by congr 1; ring
    have a1 : Real.cos (2 * α) = Real.cos ((2 * α + θ) - θ) := by congr 1; ring
    have a2 : Real.cos (2 * α + 2 * θ) = Real.cos ((2 * α + θ) + θ) := by congr 1; ring
    have h3 : Real.cos (2 * α) + Real.cos (2 * α + 2 * θ) = 2 * (Real.cos (2 * α + θ) * Real.cos θ) := by
      have key : ∀ x : ℝ, Real.cos (x - θ) + Real.cos (x + θ) = 2 * (Real.cos x * Real.cos θ) := fun x => by
        rw [Real.cos_sub, Real.cos_add]; ring
      rw [a1, a2]; exact key _
    rw [h2'] at h2
    linarith
  rw [e]
  have := abs_le.mp (show |Real.cos (2 * α + θ) * Real.cos θ| ≤ Real.cos θ1 by
    rw [abs_mul]
    calc |Real.cos (2 * α + θ)| * |Real.cos θ| ≤ 1 * Real.cos θ1 :=
          mul_le_mul (Real.abs_cos_le_one _) hcos (abs_nonneg _) zero_le_one
      _ = Real.cos θ1 := one_mul _)
  linarith [this.1]

end Action

/-! ### The sign of a product of two near-cosine values -/

/-- Pure arithmetic of the sign argument: `f = rho_L (x + a)`, `g = rho_R (y + b)`, `y = s x + c` (`s = (-1)^k`), `x^2 >= kappa0`, all errors `O(h)`; then `s f g > 0`. -/
lemma row_product_pos {s x y f g ρL ρR EL ER Cw κ0 h : ℝ} (hs : s ^ 2 = 1) (hρL : 0 < ρL) (hρR : 0 < ρR)
    (hf : |f - ρL * x| ≤ EL * h * ρL) (hg : |g - ρR * y| ≤ ER * h * ρR) (hy : |y - s * x| ≤ Cw * h)
    (hx1 : |x| ≤ 1) (hx2 : κ0 ≤ x ^ 2) (hh0 : 0 < h) (hh1 : h ≤ 1) (hEL : 0 ≤ EL) (hER : 0 ≤ ER) (hCw : 0 ≤ Cw)
    (hsmall : h * (EL + ER + Cw + EL * (Cw + ER)) < κ0) : 0 < s * (f * g) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (f - ρL * x) / ρL := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (g - ρR * y) / ρR := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = y - s * x := ⟨_, rfl⟩
  have hfa : f = ρL * (x + a) := by rw [ha]; field_simp; ring
  have hgb : g = ρR * (y + b) := by rw [hb]; field_simp; ring
  have haa : |a| ≤ EL * h := by
    rw [ha, abs_div, abs_of_pos hρL, div_le_iff₀ hρL]; linarith
  have hbb : |b| ≤ ER * h := by
    rw [hb, abs_div, abs_of_pos hρR, div_le_iff₀ hρR]; linarith
  have hcc : |c| ≤ Cw * h := by rw [hc]; exact hy
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = s * (c + b) := ⟨_, rfl⟩
  have hs1 : |s| = 1 := by
    have : |s| ^ 2 = 1 := by rw [sq_abs]; exact hs
    nlinarith [abs_nonneg s]
  have hdd : |d| ≤ (Cw + ER) * h := by
    rw [hd, abs_mul, hs1, one_mul]
    calc |c + b| ≤ |c| + |b| := abs_add_le _ _
      _ ≤ Cw * h + ER * h := add_le_add hcc hbb
      _ = (Cw + ER) * h := by ring
  have hyx : y + b = s * x + c + b := by rw [hc]; ring
  have hprod : s * (f * g) = ρL * ρR * ((x + a) * (x + d)) := by
    rw [hfa, hgb, hyx, hd]
    have : s * (ρL * (x + a) * (ρR * (s * x + c + b))) = ρL * ρR * ((x + a) * (s * (s * x + c + b))) := by ring
    rw [this]
    congr 2
    have : s * (s * x + c + b) = s ^ 2 * x + s * (c + b) := by ring
    rw [this, hs, one_mul]
  rw [hprod]
  refine mul_pos (mul_pos hρL hρR) ?_
  have hex : (x + a) * (x + d) = x ^ 2 + (x * d + a * x + a * d) := by ring
  rw [hex]
  have hxd : |x * d| ≤ (Cw + ER) * h := by
    rw [abs_mul]
    calc |x| * |d| ≤ 1 * ((Cw + ER) * h) := mul_le_mul hx1 hdd (abs_nonneg _) zero_le_one
      _ = (Cw + ER) * h := one_mul _
  have hax : |a * x| ≤ EL * h := by
    rw [abs_mul]
    calc |a| * |x| ≤ (EL * h) * 1 := mul_le_mul haa hx1 (abs_nonneg _) (by positivity)
      _ = EL * h := mul_one _
  have had : |a * d| ≤ EL * (Cw + ER) * h := by
    rw [abs_mul]
    calc |a| * |d| ≤ (EL * h) * ((Cw + ER) * h) := mul_le_mul haa hdd (abs_nonneg _) (by positivity)
      _ = EL * (Cw + ER) * h * h := by ring
      _ ≤ EL * (Cw + ER) * h * 1 := mul_le_mul_of_nonneg_left hh1 (by positivity)
      _ = EL * (Cw + ER) * h := mul_one _
  have h1 := (abs_le.mp hxd).1
  have h2 := (abs_le.mp hax).1
  have h3 := (abs_le.mp had).1
  nlinarith [hx2, hsmall]

/-! ### The exact edge solution has the same phase -/

section Chart

variable {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily Par} {P : Set Par} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}

/-- **The exact edge solution on the overlap**: with `prop:tha-W` (1) (`bulkSolutionBound_of_one_le`) and `bulk_phase_left`: for the exact solution `psi` of the recurrence on the rows of the chart, seeded by `psi-hat_0`,
`|psi_n - rho cos(Theta_L(u_n)/h - pi/4)| <= E h rho` on every overlap row, with an amplitude `rho > 0` (`rho >= c1 h^{1/4}`, so the `O(h^m)` envelope error is `O(h) rho`). -/
theorem exact_phase_row {Gz : SymbolFamily (Par × ℝ)} {Pz : Set (Par × ℝ)} (C : BulkWeberChart Gz Pz Jlo Jhi m U V) (hm : 1 ≤ m)
    {cPC CPC : ℝ} (PC : ParabolicCylinderFacts U V cPC CPC) :
    ∃ E h0 : ℝ, 0 ≤ E ∧ 0 < h0 ∧ ∀ p ∈ Pz, ∀ X ∈ Icc Jlo Jhi, ∀ N : ℕ, C.N0 ≤ N → Gz.step N ≤ h0 → ∀ ψ : ℤ → ℝ,
      JacSol Gz p N X (C.NRL p X N) ψ → ψ 0 = C.psiHatL p X N 0 →
      ∀ n : ℤ, 0 ≤ n → n ≤ (C.chain p X N).NR → C.c' ≤ uNode (Gz.step N) n →
      ∃ ρ : ℝ, 0 < ρ ∧
        |ψ n - ρ * Real.cos (thetaL Gz.L (Gz.G 0 p) (Gz.B 0 p) X (uNode (Gz.step N) n) / Gz.step N - Real.pi / 4)|
          ≤ E * Gz.step N * ρ := by
  obtain ⟨c1, C1, h0a, hc1, hC1, hh0a, hphase⟩ := bulk_phase_left C PC
  obtain ⟨Cc, h0b, hh0b, hbound⟩ := bulkSolutionBound_of_one_le C hm
  obtain ⟨hc'pos, -, -, -, -, hcM, hcMCM, -, -, -⟩ := C.consts_pos
  have hCM0 : 0 ≤ C.CM := by linarith
  refine ⟨C1 + |Cc| * C.CM / c1, min (min h0a h0b) 1,
    add_nonneg hC1 (div_nonneg (mul_nonneg (abs_nonneg _) hCM0) hc1.le), lt_min (lt_min hh0a hh0b) one_pos, ?_⟩
  intro p hp X hX N hN hstep ψ hJ hseed n hn0 hnNR hov
  have hst : 0 < Gz.step N := FormalResearch.JB.stepSize_pos Gz.L_pos N
  have hha : Gz.step N ≤ h0a := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhb : Gz.step N ≤ h0b := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh1 : Gz.step N ≤ 1 := hstep.trans (min_le_right _ _)
  obtain ⟨ρ, hρ, hph⟩ := hphase p hp X hX N hN hha n hn0 hnNR hov
  have hq4 : 0 < Gz.step N ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hst _
  have hρpos : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  refine ⟨ρ, hρpos, ?_⟩
  have hnm : n ∈ Finset.Icc (0 : ℤ) (C.NRL p X N) := Finset.mem_Icc.mpr ⟨hn0, hnNR⟩
  have h1 := hbound p hp X hX N hN hhb ψ hJ hseed n hnm
  obtain ⟨-, henv⟩ := chart_overlap_row C p hp X hX N hN n hn0 hnNR hov
  -- `|psi - psi-hat| <= |Cc| h^m CM h^{1/4} <= (|Cc| CM / c1) h rho`
  have hE0 : 0 ≤ C.envL p X N n := by
    unfold BulkWeberChart.envL
    exact mul_nonneg ((C.valid p hp X hX N hN).W_pos n hnm).le ((C.valid p hp X hX N hN).M_pos n hnm).le
  have hpm : Gz.step N ^ m ≤ Gz.step N := pow_le_of_le_one hst.le hh1 (by omega)
  have h2 : |ψ n - C.psiHatL p X N n| ≤ |Cc| * C.CM / c1 * Gz.step N * ρ := by
    refine h1.trans ?_
    have hCcm : Cc * Gz.step N ^ m * C.envL p X N n ≤ |Cc| * Gz.step N ^ m * (C.CM * Gz.step N ^ ((1 : ℝ) / 4)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _)) henv hE0
        (mul_nonneg (abs_nonneg _) (pow_nonneg hst.le _))
    refine hCcm.trans ?_
    have h3 : Gz.step N ^ ((1 : ℝ) / 4) ≤ ρ / c1 := by rw [le_div_iff₀ hc1]; linarith
    calc |Cc| * Gz.step N ^ m * (C.CM * Gz.step N ^ ((1 : ℝ) / 4))
        ≤ |Cc| * Gz.step N * (C.CM * (ρ / c1)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpm (abs_nonneg _)) _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 hCM0
      _ = |Cc| * C.CM / c1 * Gz.step N * ρ := by ring
  calc |ψ n - ρ * Real.cos (thetaL Gz.L (Gz.G 0 p) (Gz.B 0 p) X (uNode (Gz.step N) n) / Gz.step N - Real.pi / 4)|
      = |(ψ n - C.psiHatL p X N n) + (C.psiHatL p X N n - ρ * Real.cos (thetaL Gz.L (Gz.G 0 p) (Gz.B 0 p) X (uNode (Gz.step N) n) / Gz.step N - Real.pi / 4))| := by ring_nf
    _ ≤ |ψ n - C.psiHatL p X N n| + |C.psiHatL p X N n - ρ * Real.cos (thetaL Gz.L (Gz.G 0 p) (Gz.B 0 p) X (uNode (Gz.step N) n) / Gz.step N - Real.pi / 4)| := abs_add_le _ _
    _ ≤ |Cc| * C.CM / c1 * Gz.step N * ρ + C1 * Gz.step N * ρ := add_le_add h2 hph
    _ = (C1 + |Cc| * C.CM / c1) * Gz.step N * ρ := by ring

end Chart

/-- `alpha + beta = pi k + delta` gives `|cos beta - (-1)^k cos alpha| <= |delta|`. -/
lemma cos_beta_rel (α β δ : ℝ) (k : ℕ) (h : α + β = Real.pi * k + δ) :
    |Real.cos β - (-1 : ℝ) ^ k * Real.cos α| ≤ |δ| := by
  have hβ : β = (δ - α) + k * Real.pi := by linarith
  rw [hβ, Real.cos_add_nat_mul_pi]
  have : (-1 : ℝ) ^ k * Real.cos (δ - α) - (-1 : ℝ) ^ k * Real.cos α
      = (-1 : ℝ) ^ k * (Real.cos (α - δ) - Real.cos α) := by
    rw [show δ - α = -(α - δ) by ring, Real.cos_neg]; ring
  rw [this, abs_mul]
  have h1 : |(-1 : ℝ) ^ k| = 1 := by simp
  rw [h1, one_mul]
  have := Real.abs_cos_sub_cos_le (α - δ) α
  have e : α - δ - α = -δ := by ring
  rw [e, abs_neg] at this
  exact this

/-- The standing assumptions give `(H1)`--`(H3)` and `C^2` principal symbols at every parameter of `P`. -/
lemma stdAssump_hyp_C2 {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {Kd r : ℕ}
    (hr : StdAssump F P Kd r) {p : Par} (hp : p ∈ P) :
    ∃ g : ℝ, Hyp F.L (F.G 0 p) (F.B 0 p) g ∧ ContDiffOn ℝ 2 (F.G 0 p) (Icc 0 F.L) ∧ ContDiffOn ℝ 2 (F.B 0 p) (Icc 0 F.L) := by
  obtain ⟨-, hEK, g, hg⟩ := hr
  have hbud : regBudget (max (2 * Kd - 1) 0) ≤ r := hEK.budget
  have hr2 : (2 : ℕ) ≤ r := le_trans (by unfold regBudget; omega) hbud
  refine ⟨g, hg p hp, ?_, ?_⟩
  · have := (hEK.reg 0 (Nat.zero_le _)).1.1 p hp
    simp only [Nat.mul_zero, Nat.sub_zero] at this
    exact this.of_le (by exact_mod_cast hr2)
  · have := (hEK.reg 0 (Nat.zero_le _)).2.1 p hp
    simp only [Nat.mul_zero, Nat.sub_zero] at this
    exact this.of_le (by exact_mod_cast hr2)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thetaL_add_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thetaL_add_mirror

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thetaL_incr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thetaL_incr

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.row_product_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.row_product_pos

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.exact_phase_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.exact_phase_row

end FormalResearch.JacobiEigenvectors.TheoremA
