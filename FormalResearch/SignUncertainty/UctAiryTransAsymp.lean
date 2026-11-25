module

public import FormalResearch.SignUncertainty.UctAiryTransOde

/-!
# Asymptotics of `f̃₁`, `g̃₁` on the right half plane and derivative bounds (`uct:airy-trans` (2), F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:airy-trans` (2), `(uct:Fstar-asym)`, `(uct:phicd-bnds)`.

The estimate `∂_w^r (w^{5/2} F̃_*(i c_s w) - C_Ai) = O_r(|w|^{-2-r})` on `Re w ≥ 0`, `|w| ≥ 2` is proved as follows (not by the contour
rotation of the TeX proof): the zeroth-order estimate on `Re w > 0` is `airyTwistedLaplaceC_ceF1_asymp`; the first-order ODE of the
holomorphic extension (`hasDerivAt_uctF1Ext`, `hasDerivAt_uctG1Ext`) is damped in the direction of decreasing `Re w` near the imaginary
axis, so a first-exit (barrier) argument along horizontal segments (`norm_le_max_of_damped`, `wedge_bound`) extends the estimate to the
wedge `-|Im w|/8 ≤ Re w ≤ 0`; Cauchy estimates on discs of radius `|w|/20` then give all derivatives.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- Barrier (first-exit) lemma for a damped differential inequality. -/
lemma norm_le_max_of_damped {z z' : ℝ → ℂ} {S μ G : ℝ} (hμ : 0 < μ)
    (hz : ∀ s ∈ Icc (0 : ℝ) S, HasDerivAt z (z' s) s)
    (hineq : ∀ s ∈ Icc (0 : ℝ) S, @inner ℝ ℂ _ (z s) (z' s) ≤ -μ * ‖z s‖ ^ 2 + G * ‖z s‖) :
    ∀ s ∈ Icc (0 : ℝ) S, ‖z s‖ ≤ max ‖z 0‖ (G / μ) := by
  intro s hs
  set M : ℝ := max ‖z 0‖ (G / μ) with hM
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (le_max_left _ _)
  have hGM : G ≤ μ * M := by
    have := le_max_right ‖z 0‖ (G / μ)
    rw [div_le_iff₀ hμ] at this
    linarith
  -- for every L > M^2, ‖z‖^2 ≤ L
  have key : ∀ L : ℝ, M ^ 2 < L → ‖z s‖ ^ 2 ≤ L := by
    intro L hL
    have hLpos : 0 < L := lt_of_le_of_lt (sq_nonneg M) hL
    have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => ‖z s‖ ^ 2)
      (f' := fun s => 2 * @inner ℝ ℂ _ (z s) (z' s)) (a := 0) (b := S) (B := fun _ => L) (B' := fun _ => 0)
      ?_ ?_ ?_ ?_ ?_ ?_ hs
    · exact this
    · exact fun s hs => (hz s hs).continuousAt.norm.pow 2 |>.continuousWithinAt
    · intro s hs
      exact ((hz s ⟨hs.1, hs.2.le⟩).norm_sq).hasDerivWithinAt
    · have h0 : ‖z 0‖ ≤ M := le_max_left _ _
      have : ‖z 0‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
      linarith
    · exact continuousOn_const
    · exact fun s hs => hasDerivWithinAt_const _ _ _
    · intro s hs heq
      have hs' : s ∈ Icc (0 : ℝ) S := ⟨hs.1, hs.2.le⟩
      have h1 := hineq s hs'
      have hn : M < ‖z s‖ := by
        by_contra hcon
        have hcon := not_lt.mp hcon
        have : ‖z s‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcon 2
        linarith
      have h3 : G * ‖z s‖ ≤ μ * M * ‖z s‖ := by
        exact mul_le_mul_of_nonneg_right hGM (norm_nonneg _)
      have h4 : μ * M * ‖z s‖ < μ * ‖z s‖ * ‖z s‖ := by
        have : μ * M < μ * ‖z s‖ := mul_lt_mul_of_pos_left hn hμ
        exact mul_lt_mul_of_pos_right this (lt_of_le_of_lt hM0 hn)
      have h5 : -μ * ‖z s‖ ^ 2 + G * ‖z s‖ < 0 := by
        have : μ * ‖z s‖ * ‖z s‖ = μ * ‖z s‖ ^ 2 := by ring
        linarith
      linarith
  by_contra hcon
  have hcon := not_le.mp hcon
  have h2 : M ^ 2 < ‖z s‖ ^ 2 := pow_lt_pow_left₀ hcon hM0 (two_ne_zero)
  have := key ((‖z s‖ ^ 2 + M ^ 2) / 2) (by linarith)
  linarith

lemma airyZero_one_abs : |airyZero 1| < 2.35 := by
  have := airyZero_one
  rw [abs_of_neg (by linarith [this.2])]; linarith [this.1]

lemma re_Dtilde_le {w : ℂ} {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 9 / 2) (hy : 5 ≤ |w.im|)
    (hx1 : -(|w.im| / 8) ≤ w.re) (hx2 : w.re ≤ 0) :
    (w ^ 2 / 4 - (airyZero 1 : ℂ) - (q : ℂ) / w).re ≤ -(w.im ^ 2 / 8) := by
  set y := w.im with hyd
  set x := w.re with hxd
  have hy2 : 25 ≤ y ^ 2 := by
    have : (5 : ℝ) ^ 2 ≤ |y| ^ 2 := pow_le_pow_left₀ (by norm_num) hy 2
    rw [sq_abs] at this
    linarith
  have hyy : 5 * |y| ≤ y ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg y]
  have hx2' : x ^ 2 ≤ y ^ 2 / 64 := by
    have h1 : -(|y| / 8) ≤ x := hx1
    have h2 : |x| ≤ |y| / 8 := by rw [abs_le]; exact ⟨h1, by linarith [abs_nonneg y]⟩
    have : |x| ^ 2 ≤ (|y| / 8) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs, div_pow, sq_abs] at this
    linarith
  have hre : (w ^ 2 / 4 - (airyZero 1 : ℂ) - (q : ℂ) / w).re = (x ^ 2 - y ^ 2) / 4 - airyZero 1 - q * x / (x ^ 2 + y ^ 2) := by
    simp [Complex.div_re, Complex.normSq_apply, pow_two, Complex.mul_re, hxd, hyd]
  rw [hre]
  have hden : 0 < x ^ 2 + y ^ 2 := by positivity
  have hT : -(q * x / (x ^ 2 + y ^ 2)) ≤ 9 / 80 := by
    rw [← neg_div, div_le_iff₀ hden]
    have h1 : -x ≤ |y| / 8 := by linarith
    have h2 : -(q * x) ≤ q * (|y| / 8) := by nlinarith
    have h3 : q * (|y| / 8) ≤ 9 / 2 * (|y| / 8) := mul_le_mul_of_nonneg_right hq (by positivity)
    nlinarith [sq_nonneg x]
  have ha := airyZero_one_abs
  have ha' : -airyZero 1 ≤ 2.35 := by linarith [neg_abs_le (airyZero 1), abs_nonneg (airyZero 1)]
  have : -(q * x / (x ^ 2 + y ^ 2)) = - (q * x / (x ^ 2 + y ^ 2)) := rfl
  nlinarith [hT, ha', hx2', hy2]


/-- Wedge estimate (horizontal barrier): if `Z' = -(w²/4 - a₁ - q/w) Z + f` with `‖f‖ ≤ G` on the wedge
`W = {5 ≤ |Im w|, -|Im w|/8 ≤ Re w ≤ 0}`, then `‖Z w‖ ≤ max ‖Z(i Im w)‖ (8 G/(Im w)²)` on `W`. -/
lemma wedge_bound {Z f : ℂ → ℂ} {q : ℝ} {Gf : ℝ → ℝ} (hq : 0 ≤ q) (hq9 : q ≤ 9 / 2)
    (hf : ∀ w : ℂ, 5 ≤ |w.im| → -(|w.im| / 8) ≤ w.re → w.re ≤ 0 → ‖f w‖ ≤ Gf w.im)
    (hZ : ∀ w : ℂ, 5 ≤ |w.im| → -(|w.im| / 8) ≤ w.re → w.re ≤ 0 →
      HasDerivAt Z (-(w ^ 2 / 4 - (airyZero 1 : ℂ) - (q : ℂ) / w) * Z w + f w) w)
    {w : ℂ} (hy : 5 ≤ |w.im|) (hx1 : -(|w.im| / 8) ≤ w.re) (hx2 : w.re ≤ 0) :
    ‖Z w‖ ≤ max ‖Z (Complex.I * (w.im : ℂ))‖ (8 * Gf w.im / w.im ^ 2) := by
  set y : ℝ := w.im with hy_def
  set S : ℝ := |y| / 8 with hS
  have hS0 : 0 ≤ S := by positivity
  let pt : ℝ → ℂ := fun s => Complex.I * (y : ℂ) - (s : ℂ)
  have hpt_re : ∀ s : ℝ, (pt s).re = -s := fun s => by simp [pt]
  have hpt_im : ∀ s : ℝ, (pt s).im = y := fun s => by simp [pt]
  have hpt_d : ∀ s : ℝ, HasDerivAt pt (-1) s := by
    intro s
    have : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    simpa [pt] using this.const_sub (Complex.I * (y : ℂ))
  let z : ℝ → ℂ := fun s => Z (pt s)
  let z' : ℝ → ℂ := fun s => -(-(pt s ^ 2 / 4 - (airyZero 1 : ℂ) - (q : ℂ) / pt s) * Z (pt s) + f (pt s))
  have hmem : ∀ s ∈ Icc (0 : ℝ) S, 5 ≤ |(pt s).im| ∧ -(|(pt s).im| / 8) ≤ (pt s).re ∧ (pt s).re ≤ 0 := by
    intro s hs
    rw [hpt_re, hpt_im]
    exact ⟨hy, by linarith [hs.2], by linarith [hs.1]⟩
  have hzd : ∀ s ∈ Icc (0 : ℝ) S, HasDerivAt z (z' s) s := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hmem s hs
    have := (hZ (pt s) h1 h2 h3).scomp s (hpt_d s)
    refine this.congr_deriv ?_
    simp only [z', smul_eq_mul]; ring
  have hineq : ∀ s ∈ Icc (0 : ℝ) S, @inner ℝ ℂ _ (z s) (z' s) ≤ -(y ^ 2 / 8) * ‖z s‖ ^ 2 + Gf y * ‖z s‖ := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hmem s hs
    have hre := re_Dtilde_le (w := pt s) hq hq9 h1 h2 h3
    rw [hpt_im] at hre
    have hfG0 := hf (pt s) h1 h2 h3
    rw [hpt_im] at hfG0
    have hfG : ‖f (pt s)‖ ≤ Gf y := hfG0
    set D : ℂ := (pt s) ^ 2 / 4 - (airyZero 1 : ℂ) - (q : ℂ) / pt s with hDdef
    set Zs : ℂ := Z (pt s) with hZs
    set fs : ℂ := f (pt s) with hfs
    have hz' : z' s = D * Zs - fs := by simp only [z', hDdef, hZs, hfs]; ring
    have hzs : z s = Zs := rfl
    rw [hz', hzs, Complex.inner]
    have e1 : (D * Zs - fs) * (starRingEnd ℂ) Zs = D * (((‖Zs‖ ^ 2 : ℝ)) : ℂ) - fs * (starRingEnd ℂ) Zs := by
      have := Complex.mul_conj' Zs
      push_cast
      rw [← this]; ring
    rw [e1, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h4 : -(fs * (starRingEnd ℂ) Zs).re ≤ Gf y * ‖Zs‖ := by
      have h0 := Complex.abs_re_le_norm (fs * (starRingEnd ℂ) Zs)
      rw [norm_mul, Complex.norm_conj] at h0
      have h5 : ‖fs‖ * ‖Zs‖ ≤ Gf y * ‖Zs‖ := mul_le_mul_of_nonneg_right hfG (norm_nonneg _)
      have h7 := neg_abs_le (fs * (starRingEnd ℂ) Zs).re
      linarith
    have h6 : D.re * ‖Zs‖ ^ 2 ≤ -(y ^ 2 / 8) * ‖Zs‖ ^ 2 := mul_le_mul_of_nonneg_right hre (by positivity)
    linarith
  have hy0 : 0 < y ^ 2 / 8 := by
    have : (25 : ℝ) ≤ y ^ 2 := by
      have : (5 : ℝ) ^ 2 ≤ |y| ^ 2 := pow_le_pow_left₀ (by norm_num) hy 2
      rw [sq_abs] at this; linarith
    linarith
  have hmain := norm_le_max_of_damped hy0 hzd hineq (-w.re) ⟨by linarith, by linarith⟩
  have hw : pt (-w.re) = w := by
    apply Complex.ext <;> simp [pt, hy_def]
  have h0 : z 0 = Z (Complex.I * (y : ℂ)) := by simp [z, pt]
  simp only [z, hw, h0] at hmain
  have : Gf y / (y ^ 2 / 8) = 8 * Gf y / y ^ 2 := by field_simp
  rw [this] at hmain
  exact hmain

theorem uctF1Ext_eq {w : ℂ} (hw : 0 ≤ w.re) : airyTwistedLaplaceC ceF1 w = uctF1Ext w := by
  rw [airyTwistedLaplaceC_ceF1_closed hw]; rfl

theorem uctG1Ext_eq {w : ℂ} (hw : 0 ≤ w.re) : airyTwistedLaplaceC (ceG1 (airyZero 1)) w = uctG1Ext w := by
  rw [airyTwistedLaplaceC_ceG1_closed hw]; rfl

lemma uctC_eq : uctC = (ceK : ℂ) / (Real.sqrt π : ℂ) := rfl

/-- `Z₁ = w^{5/2} Φ - 2c`. -/
noncomputable def uctZ1 (w : ℂ) : ℂ := w ^ 2 * (w ^ (1 / 2 : ℂ) * uctF1Ext w) - 2 * uctC

/-- `W₂ = w^{9/2} Ψ`. -/
noncomputable def uctW2 (w : ℂ) : ℂ := w ^ 4 * (w ^ (1 / 2 : ℂ) * uctG1Ext w)

lemma cpow_half_sq {w : ℂ} : w ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ) = w := by
  by_cases hw : w = 0
  · subst hw; simp [Complex.zero_cpow]
  · rw [← Complex.cpow_add _ _ hw]; norm_num

lemma cpow_half_ne_zero {w : ℂ} (hw : w ≠ 0) : w ^ (1 / 2 : ℂ) ≠ 0 :=
  (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hw

lemma cpow_five_half {w : ℂ} : w ^ (5 / 2 : ℂ) = w ^ 2 * w ^ (1 / 2 : ℂ) := by
  by_cases hw : w = 0
  · subst hw; simp [Complex.zero_cpow]
  · rw [show (5 / 2 : ℂ) = ((2 : ℕ) : ℂ) + 1 / 2 by norm_num, Complex.cpow_add _ _ hw, Complex.cpow_natCast]

lemma cpow_nine_half {w : ℂ} : w ^ (9 / 2 : ℂ) = w ^ 4 * w ^ (1 / 2 : ℂ) := by
  by_cases hw : w = 0
  · subst hw; simp [Complex.zero_cpow]
  · rw [show (9 / 2 : ℂ) = ((4 : ℕ) : ℂ) + 1 / 2 by norm_num, Complex.cpow_add _ _ hw, Complex.cpow_natCast]

lemma norm_cpow_five_half {w : ℂ} (hw : w ≠ 0) : ‖w ^ (5 / 2 : ℂ)‖ = ‖w‖ ^ (5 / 2 : ℝ) := by
  have := norm_cpow_ofReal_exponent hw (5 / 2)
  simpa using this

lemma norm_cpow_nine_half {w : ℂ} (hw : w ≠ 0) : ‖w ^ (9 / 2 : ℂ)‖ = ‖w‖ ^ (9 / 2 : ℝ) := by
  have := norm_cpow_ofReal_exponent hw (9 / 2)
  simpa using this

lemma uctZ1_bound_rhp : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 0 < w.re → 1 ≤ ‖w‖ → ‖uctZ1 w‖ ≤ C * ‖w‖ ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := airyTwistedLaplaceC_ceF1_asymp
  refine ⟨C, hC, fun w hw hw1 => ?_⟩
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  have hasy := h hw hw1
  have h1 : w ^ (5 / 2 : ℂ) * w ^ (-(5 / 2 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ hw0]; simp
  have h2 : (2 * ceK / Real.sqrt π : ℂ) = 2 * uctC := by unfold uctC; ring
  have hkey : uctZ1 w = w ^ (5 / 2 : ℂ) * (airyTwistedLaplaceC ceF1 w - (2 * ceK / Real.sqrt π : ℂ) * w ^ (-(5 / 2 : ℂ))) := by
    have e : uctZ1 w = w ^ (5 / 2 : ℂ) * airyTwistedLaplaceC ceF1 w - 2 * uctC := by
      unfold uctZ1; rw [← uctF1Ext_eq hw.le, cpow_five_half]; ring
    rw [e, h2]
    linear_combination (2 * uctC) * h1
  rw [hkey, norm_mul, norm_cpow_five_half hw0]
  calc ‖w‖ ^ (5 / 2 : ℝ) * ‖airyTwistedLaplaceC ceF1 w - (2 * ceK / Real.sqrt π : ℂ) * w ^ (-(5 / 2 : ℂ))‖
      ≤ ‖w‖ ^ (5 / 2 : ℝ) * (C * ‖w‖ ^ (-(9 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hasy (by positivity)
    _ = C * ‖w‖ ^ (-(2 : ℝ)) := by
      have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      rw [show (-(2 : ℝ)) = (5 / 2 : ℝ) + (-(9 / 2 : ℝ)) by norm_num, Real.rpow_add hpos]; ring

lemma uctW2_bound_rhp : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 0 < w.re → 1 ≤ ‖w‖ → ‖uctW2 w‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := airyTwistedLaplaceC_ceG1_bound
  refine ⟨C, hC, fun w hw hw1 => ?_⟩
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  have hasy := h hw hw1
  have e : uctW2 w = w ^ (9 / 2 : ℂ) * airyTwistedLaplaceC (ceG1 (airyZero 1)) w := by
    unfold uctW2; rw [uctG1Ext_eq hw.le |>.symm, cpow_nine_half]; ring
  rw [e, norm_mul, norm_cpow_nine_half hw0]
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  calc ‖w‖ ^ (9 / 2 : ℝ) * ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) w‖ ≤ ‖w‖ ^ (9 / 2 : ℝ) * (C * ‖w‖ ^ (-(9 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hasy (by positivity)
    _ = C := by
      rw [← mul_assoc, mul_comm (‖w‖ ^ (9 / 2 : ℝ)) C, mul_assoc, ← Real.rpow_add hpos]; norm_num

theorem hasDerivAt_uctZ1 {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt uctZ1 (-(w ^ 2 / 4 - (airyZero 1 : ℂ) - (((5 / 2 : ℝ) : ℂ)) / w) * uctZ1 w +
      (5 * uctC / w + 2 * uctC * (airyZero 1 : ℂ))) w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have hs := hasDerivAt_cpow_half hw
  have hΦ := hasDerivAt_uctF1Ext hw
  have h := (((hasDerivAt_pow 2 w).mul (hs.mul hΦ)).sub_const (2 * uctC))
  simp only [Pi.mul_apply] at h
  refine h.congr_deriv ?_
  have hs2 := cpow_half_sq (w := w)
  have hs0 := cpow_half_ne_zero hw0
  unfold uctZ1
  rw [Complex.cpow_neg] at hs hΦ ⊢
  have hA1 : uctA1 = (airyZero 1 : ℂ) := rfl
  rw [hA1]
  generalize w ^ (1 / 2 : ℂ) = s at *
  generalize uctF1Ext w = Φ at *
  subst hs2
  have hs1 : s ≠ 0 := hs0
  push_cast
  field_simp
  ring

theorem hasDerivAt_uctW2 {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt uctW2 (-(w ^ 2 / 4 - (airyZero 1 : ℂ) - (((9 / 2 : ℝ) : ℂ)) / w) * uctW2 w +
      w ^ 2 * (uctZ1 w + 2 * uctC)) w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have hs := hasDerivAt_cpow_half hw
  have hΨ := hasDerivAt_uctG1Ext hw
  have h := ((hasDerivAt_pow 4 w).mul (hs.mul hΨ))
  simp only [Pi.mul_apply] at h
  rw [Complex.cpow_neg] at h
  refine h.congr_deriv ?_
  have hs2 := cpow_half_sq (w := w)
  have hs0 := cpow_half_ne_zero hw0
  unfold uctW2 uctZ1
  have hA1 : uctA1 = (airyZero 1 : ℂ) := rfl
  rw [hA1]
  generalize w ^ (1 / 2 : ℂ) = s at *
  generalize uctF1Ext w = Φ at *
  generalize uctG1Ext w = Ψ at *
  subst hs2
  have hs1 : s ≠ 0 := hs0
  push_cast
  field_simp
  ring

/-! ### The wedge estimates and the sector bounds -/

lemma imag_axis_bound {F : ℂ → ℂ} {g : ℂ → ℝ} (hF : ∀ y : ℝ, y ≠ 0 → ContinuousAt F (Complex.I * (y : ℂ)))
    (hg : ∀ y : ℝ, y ≠ 0 → ContinuousAt g (Complex.I * (y : ℂ)))
    (h : ∀ w : ℂ, 0 < w.re → 1 ≤ ‖w‖ → ‖F w‖ ≤ g w) {y : ℝ} (hy : 1 ≤ |y|) :
    ‖F (Complex.I * (y : ℂ))‖ ≤ g (Complex.I * (y : ℂ)) := by
  have hy0 : y ≠ 0 := fun h0 => by rw [h0, abs_zero] at hy; norm_num at hy
  set w₀ : ℂ := Complex.I * (y : ℂ) with hw₀
  let wn : ℕ → ℂ := fun n => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) + w₀
  have hwn : Tendsto wn atTop (𝓝 w₀) := by
    have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    have h3 := h2.add_const w₀
    simpa [wn] using h3
  have hbd : ∀ n : ℕ, ‖F (wn n)‖ ≤ g (wn n) := by
    intro n
    apply h
    · have : (wn n).re = 1 / ((n : ℝ) + 1) := by
        simp only [wn, w₀, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      rw [this]; positivity
    · have : |(wn n).im| ≤ ‖wn n‖ := Complex.abs_im_le_norm _
      have him : (wn n).im = y := by
        simp only [wn, w₀, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, one_mul, mul_zero, zero_add]
      rw [him] at this; linarith
  exact le_of_tendsto_of_tendsto' ((hF y hy0).norm.tendsto.comp hwn) ((hg y hy0).tendsto.comp hwn) hbd

lemma slit_of_im {w : ℂ} (h : 5 ≤ |w.im|) : w ∈ Complex.slitPlane := by
  right
  intro h0; rw [h0, abs_zero] at h; norm_num at h

lemma continuousAt_uctZ1 {w : ℂ} (hw : w ∈ Complex.slitPlane) : ContinuousAt uctZ1 w :=
  (hasDerivAt_uctZ1 hw).continuousAt

lemma continuousAt_uctW2 {w : ℂ} (hw : w ∈ Complex.slitPlane) : ContinuousAt uctW2 w :=
  (hasDerivAt_uctW2 hw).continuousAt

lemma continuousAt_norm_rpow_neg {w : ℂ} (hw : w ≠ 0) (p : ℝ) : ContinuousAt (fun w : ℂ => ‖w‖ ^ (-p)) w :=
  (continuous_norm.continuousAt).rpow_const (Or.inl (norm_ne_zero_iff.mpr hw))

/-- Boundary values of `Z₁` on the imaginary axis. -/
lemma uctZ1_imag_bound : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ |y| → ‖uctZ1 (Complex.I * (y : ℂ))‖ ≤ C * ‖Complex.I * (y : ℂ)‖ ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := uctZ1_bound_rhp
  refine ⟨C, hC, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := fun h0 => by rw [h0, abs_zero] at hy; norm_num at hy
  have hsl : Complex.I * (y : ℂ) ∈ Complex.slitPlane := by
    right; simpa using hy0
  have hne : Complex.I * (y : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hsl
  refine imag_axis_bound (g := fun w : ℂ => C * ‖w‖ ^ (-(2 : ℝ))) (fun y hy0 => ?_) (fun y hy0 => ?_) h hy
  · exact continuousAt_uctZ1 (by right; simpa using hy0)
  · have hne' : Complex.I * (y : ℂ) ≠ 0 := by simpa using hy0
    exact (continuousAt_norm_rpow_neg hne' 2).const_mul C

lemma uctW2_imag_bound : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ |y| → ‖uctW2 (Complex.I * (y : ℂ))‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := uctW2_bound_rhp
  refine ⟨C, hC, fun y hy => ?_⟩
  refine imag_axis_bound (g := fun _ : ℂ => C) (fun y hy0 => ?_) (fun y hy0 => continuousAt_const) h hy
  exact continuousAt_uctW2 (by right; simpa using hy0)

lemma norm_I_mul_real (y : ℝ) : ‖Complex.I * (y : ℂ)‖ = |y| := by
  simp

lemma rpow_neg_two_abs (y : ℝ) (_hy : y ≠ 0) : |y| ^ (-(2 : ℝ)) = 1 / y ^ 2 := by
  rw [Real.rpow_neg (abs_nonneg y), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]; simp

lemma norm_uctC_nonneg : 0 ≤ ‖uctC‖ := norm_nonneg _

lemma uctZ1_wedge : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 5 ≤ |w.im| → -(|w.im| / 8) ≤ w.re → w.re ≤ 0 →
    ‖uctZ1 w‖ ≤ C / w.im ^ 2 := by
  obtain ⟨C₀, hC₀, h0⟩ := uctZ1_imag_bound
  set G : ℝ := ‖uctC‖ * 6 with hG
  have hG0 : 0 ≤ G := by positivity
  refine ⟨C₀ + 8 * G, by positivity, fun w hy hx1 hx2 => ?_⟩
  have hwb := wedge_bound (Z := uctZ1) (f := fun w => 5 * uctC / w + 2 * uctC * (airyZero 1 : ℂ)) (q := 5 / 2) (Gf := fun _ => G)
    (by norm_num) (by norm_num) (fun w hy hx1 hx2 => ?_) (fun w hy hx1 hx2 => hasDerivAt_uctZ1 (slit_of_im hy)) hy hx1 hx2
  · have hy0 : w.im ≠ 0 := fun h => by rw [h, abs_zero] at hy; norm_num at hy
    have hst := h0 w.im (by linarith)
    rw [norm_I_mul_real, rpow_neg_two_abs _ hy0] at hst
    have hy2 : 0 < w.im ^ 2 := by positivity
    calc ‖uctZ1 w‖ ≤ max ‖uctZ1 (Complex.I * (w.im : ℂ))‖ (8 * G / w.im ^ 2) := hwb
      _ ≤ (C₀ + 8 * G) / w.im ^ 2 := by
        apply max_le
        · calc ‖uctZ1 (Complex.I * (w.im : ℂ))‖ ≤ C₀ * (1 / w.im ^ 2) := hst
            _ = C₀ / w.im ^ 2 := by ring
            _ ≤ (C₀ + 8 * G) / w.im ^ 2 := by gcongr; linarith
        · gcongr; linarith
  · -- the forcing term
    have hwn : 5 ≤ ‖w‖ := le_trans hy (Complex.abs_im_le_norm w)
    have hw0 : w ≠ 0 := fun h => by rw [h] at hwn; simp at hwn; linarith
    have ha := airyZero_one_abs
    calc ‖5 * uctC / w + 2 * uctC * (airyZero 1 : ℂ)‖ ≤ ‖5 * uctC / w‖ + ‖2 * uctC * (airyZero 1 : ℂ)‖ := norm_add_le _ _
      _ = 5 * ‖uctC‖ / ‖w‖ + 2 * ‖uctC‖ * |airyZero 1| := by
          rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]; norm_num
      _ ≤ 5 * ‖uctC‖ / 5 + 2 * ‖uctC‖ * 2.35 := by
          gcongr
      _ ≤ G := by rw [hG]; nlinarith [norm_uctC_nonneg]

lemma norm_sq_le_wedge {w : ℂ} (hx1 : -(|w.im| / 8) ≤ w.re) (hx2 : w.re ≤ 0) : ‖w‖ ^ 2 ≤ 65 / 64 * w.im ^ 2 := by
  have h2 : |w.re| ≤ |w.im| / 8 := by rw [abs_le]; exact ⟨hx1, by linarith [abs_nonneg w.im]⟩
  have h3 : |w.re| ^ 2 ≤ (|w.im| / 8) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [sq_abs, div_pow, sq_abs] at h3
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

lemma uctW2_wedge : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 5 ≤ |w.im| → -(|w.im| / 8) ≤ w.re → w.re ≤ 0 → ‖uctW2 w‖ ≤ C := by
  obtain ⟨C₁, hC₁, h1⟩ := uctZ1_wedge
  obtain ⟨C₂, hC₂, h2⟩ := uctW2_imag_bound
  set cc : ℝ := ‖uctC‖ with hcc
  set K : ℝ := 65 / 8 * (C₁ / 25 + 2 * cc) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C₂ + K, by positivity, fun w hy hx1 hx2 => ?_⟩
  have hwb := wedge_bound (Z := uctW2) (f := fun w => w ^ 2 * (uctZ1 w + 2 * uctC)) (q := 9 / 2)
    (Gf := fun y => 65 / 64 * (C₁ + 2 * cc * y ^ 2))
    (by norm_num) (by norm_num) (fun w hy hx1 hx2 => ?_) (fun w hy hx1 hx2 => hasDerivAt_uctW2 (slit_of_im hy)) hy hx1 hx2
  · have hy0 : w.im ≠ 0 := fun h => by rw [h, abs_zero] at hy; norm_num at hy
    have hy2 : (25 : ℝ) ≤ w.im ^ 2 := by
      have : (5 : ℝ) ^ 2 ≤ |w.im| ^ 2 := pow_le_pow_left₀ (by norm_num) hy 2
      rw [sq_abs] at this; linarith
    have hst := h2 w.im (by linarith)
    refine hwb.trans (max_le (hst.trans (by linarith)) ?_)
    have e : 8 * (65 / 64 * (C₁ + 2 * cc * w.im ^ 2)) / w.im ^ 2 = 65 / 8 * (C₁ / w.im ^ 2 + 2 * cc) := by
      field_simp; ring
    show 8 * (65 / 64 * (C₁ + 2 * cc * w.im ^ 2)) / w.im ^ 2 ≤ C₂ + K
    rw [e]
    have : C₁ / w.im ^ 2 ≤ C₁ / 25 := div_le_div_of_nonneg_left hC₁.le (by norm_num) hy2
    have : 65 / 8 * (C₁ / w.im ^ 2 + 2 * cc) ≤ K := by rw [hK]; gcongr
    linarith
  · have hy0 : w.im ≠ 0 := fun h => by rw [h, abs_zero] at hy; norm_num at hy
    have hy2 : (0 : ℝ) < w.im ^ 2 := by positivity
    have hZ1 := h1 w hy hx1 hx2
    have hn := norm_sq_le_wedge hx1 hx2
    rw [norm_mul, norm_pow]
    have h3 : ‖uctZ1 w + 2 * uctC‖ ≤ C₁ / w.im ^ 2 + 2 * cc := by
      calc ‖uctZ1 w + 2 * uctC‖ ≤ ‖uctZ1 w‖ + ‖2 * uctC‖ := norm_add_le _ _
        _ ≤ C₁ / w.im ^ 2 + 2 * cc := by rw [norm_mul]; simp only [RCLike.norm_ofNat]; linarith
    calc ‖w‖ ^ 2 * ‖uctZ1 w + 2 * uctC‖ ≤ (65 / 64 * w.im ^ 2) * (C₁ / w.im ^ 2 + 2 * cc) :=
          mul_le_mul hn h3 (norm_nonneg _) (by positivity)
      _ = 65 / 64 * (C₁ + 2 * cc * w.im ^ 2) := by field_simp

/-- The sector `{Re w ≥ 0} ∪ {5 ≤ |Im w|, Re w ≥ -|Im w|/8}`. -/
def InSector (w : ℂ) : Prop := 0 ≤ w.re ∨ (5 ≤ |w.im| ∧ -(|w.im| / 8) ≤ w.re)

lemma eq_I_mul_im {w : ℂ} (h : w.re = 0) : w = Complex.I * (w.im : ℂ) := by
  apply Complex.ext <;> simp [h]

lemma uctZ1_sector : ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, InSector w → 5 ≤ ‖w‖ → ‖uctZ1 w‖ ≤ K * ‖w‖ ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := uctZ1_bound_rhp
  obtain ⟨C₀, hC₀, h0⟩ := uctZ1_imag_bound
  obtain ⟨C₁, hC₁, h1⟩ := uctZ1_wedge
  refine ⟨max C (max C₀ (65 / 64 * C₁)), by positivity, fun w hs hw5 => ?_⟩
  have hwpos : 0 < ‖w‖ := by linarith
  have hKm : 0 ≤ ‖w‖ ^ (-(2 : ℝ)) := by positivity
  rcases hs with hre | ⟨hy, hx⟩
  · rcases hre.lt_or_eq with hpos | hzero
    · calc ‖uctZ1 w‖ ≤ C * ‖w‖ ^ (-(2 : ℝ)) := h w hpos (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hKm
    · have hw := eq_I_mul_im hzero.symm
      have hy1 : 1 ≤ |w.im| := by
        have : |w.im| = ‖w‖ := by rw [hw]; simp
        linarith
      have := h0 w.im hy1
      rw [← hw] at this
      calc ‖uctZ1 w‖ ≤ C₀ * ‖w‖ ^ (-(2 : ℝ)) := this
        _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hKm
  · by_cases hneg : w.re ≤ 0
    · have hb := h1 w hy hx hneg
      have hn := norm_sq_le_wedge hx hneg
      have hy0 : 0 < w.im ^ 2 := by
        have : w.im ≠ 0 := fun h => by rw [h, abs_zero] at hy; norm_num at hy
        positivity
      have hnn : ‖w‖ ^ (-(2 : ℝ)) = 1 / ‖w‖ ^ 2 := by
        rw [Real.rpow_neg hwpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; simp
      rw [hnn]
      calc ‖uctZ1 w‖ ≤ C₁ / w.im ^ 2 := hb
        _ ≤ 65 / 64 * C₁ / ‖w‖ ^ 2 := by
            rw [div_le_div_iff₀ hy0 (by positivity)]
            nlinarith [hC₁]
        _ = (65 / 64 * C₁) * (1 / ‖w‖ ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans' (le_max_right _ _)) (by positivity)
    · -- Re w > 0
      have hpos : 0 < w.re := not_le.mp hneg
      calc ‖uctZ1 w‖ ≤ C * ‖w‖ ^ (-(2 : ℝ)) := h w hpos (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hKm

lemma uctW2_sector : ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, InSector w → 5 ≤ ‖w‖ → ‖uctW2 w‖ ≤ K := by
  obtain ⟨C, hC, h⟩ := uctW2_bound_rhp
  obtain ⟨C₀, hC₀, h0⟩ := uctW2_imag_bound
  obtain ⟨C₁, hC₁, h1⟩ := uctW2_wedge
  refine ⟨max C (max C₀ C₁), by positivity, fun w hs hw5 => ?_⟩
  rcases hs with hre | ⟨hy, hx⟩
  · rcases hre.lt_or_eq with hpos | hzero
    · exact (h w hpos (by linarith)).trans (le_max_left _ _)
    · have hw := eq_I_mul_im hzero.symm
      have hy1 : 1 ≤ |w.im| := by
        have : |w.im| = ‖w‖ := by rw [hw]; simp
        linarith
      have := h0 w.im hy1
      rw [← hw] at this
      exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  · by_cases hneg : w.re ≤ 0
    · exact (h1 w hy hx hneg).trans ((le_max_right _ _).trans' (le_max_right _ _))
    · exact (h w (not_le.mp hneg) (by linarith)).trans (le_max_left _ _)

lemma slit_of_sector {z : ℂ} (hs : InSector z) (h5 : 5 ≤ ‖z‖) : z ∈ Complex.slitPlane := by
  rcases hs with hre | ⟨hy, _⟩
  · rcases hre.lt_or_eq with hpos | hzero
    · left; exact hpos
    · right
      intro him
      have : z = 0 := by apply Complex.ext <;> simp [← hzero, him]
      rw [this] at h5; simp at h5; linarith
  · exact slit_of_im hy

lemma disc_in_sector {w0 z : ℂ} (h0 : 0 ≤ w0.re) (hn : 6 ≤ ‖w0‖) (hz : ‖z - w0‖ ≤ ‖w0‖ / 20) :
    InSector z ∧ 5 ≤ ‖z‖ ∧ 19 / 20 * ‖w0‖ ≤ ‖z‖ := by
  set r := ‖w0‖ with hr
  have hr0 : 0 < r := by linarith
  have hzn : 19 / 20 * r ≤ ‖z‖ := by
    have h1 := norm_sub_norm_le w0 z
    have h2 : ‖w0 - z‖ = ‖z - w0‖ := norm_sub_rev _ _
    linarith
  refine ⟨?_, by linarith, hzn⟩
  by_cases hre : 0 ≤ z.re
  · exact Or.inl hre
  · right
    have hre' : z.re < 0 := not_le.mp hre
    have hrz : |z.re - w0.re| ≤ r / 20 := by
      have := Complex.abs_re_le_norm (z - w0); simp only [Complex.sub_re] at this; linarith
    have hiz : |z.im - w0.im| ≤ r / 20 := by
      have := Complex.abs_im_le_norm (z - w0); simp only [Complex.sub_im] at this; linarith
    have hx0 : w0.re < r / 20 := by
      have := (abs_le.mp hrz).1; linarith
    have hr2 : r ^ 2 = w0.re ^ 2 + w0.im ^ 2 := by
      rw [hr, Complex.sq_norm, Complex.normSq_apply]; ring
    have hx02 : w0.re ^ 2 ≤ r ^ 2 / 400 := by nlinarith
    have hy0 : 99 / 100 * r ≤ |w0.im| := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have h1 : |w0.im| ^ 2 < (99 / 100 * r) ^ 2 := by
        exact pow_lt_pow_left₀ hcon (abs_nonneg _) (by norm_num)
      rw [sq_abs] at h1
      nlinarith
    have hzim : 94 / 100 * r ≤ |z.im| := by
      have := abs_sub_abs_le_abs_sub w0.im z.im
      rw [abs_sub_comm] at this
      linarith
    refine ⟨by linarith, ?_⟩
    have := (abs_le.mp hrz).1
    linarith

/-- Cauchy estimates on the sector: a bound `K |z|^{-p}` on the sector for a function holomorphic on the slit plane gives the
bound `C_r |w|^{-p-r}` for the `r`-th derivative at the points `Re w ≥ 0`, `|w| ≥ 6`. -/
lemma cauchy_sector {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane) {K p : ℝ} (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hbd : ∀ z : ℂ, InSector z → 5 ≤ ‖z‖ → ‖F z‖ ≤ K * ‖z‖ ^ (-p)) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w0 : ℂ, 0 ≤ w0.re → 6 ≤ ‖w0‖ → ‖iteratedDeriv r F w0‖ ≤ C * ‖w0‖ ^ (-(p + r)) := by
  refine ⟨(r.factorial : ℝ) * K * (19 / 20 : ℝ) ^ (-p) * 20 ^ r, by positivity, fun w0 h0 hn => ?_⟩
  set R := ‖w0‖ with hR
  have hR0 : 0 < R := by linarith
  have hsub : Metric.closedBall w0 (R / 20) ⊆ Complex.slitPlane := by
    intro z hz
    have := disc_in_sector h0 hn (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    exact slit_of_sector this.1 this.2.1
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := w0) (R := R / 20) (C := K * ((19 / 20 : ℝ) * R) ^ (-p)) r
    (by positivity) (hF.diffContOnCl_ball hsub) (fun z hz => by
      have hz' : ‖z - w0‖ = R / 20 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      obtain ⟨h1, h2, h3⟩ := disc_in_sector h0 hn hz'.le
      refine (hbd z h1 h2).trans (mul_le_mul_of_nonneg_left ?_ hK)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith))
  refine hcauchy.trans (le_of_eq ?_)
  have hRp : (19 / 20 : ℝ) * R = (19 / 20 : ℝ) * R := rfl
  rw [Real.mul_rpow (by norm_num) hR0.le, div_pow, ← Real.rpow_natCast R r, show (-(p + r) : ℝ) = -p + -(r : ℝ) by ring,
    Real.rpow_add hR0, Real.rpow_neg hR0.le (r : ℝ)]
  field_simp

lemma slit_of_halfplane {w : ℂ} (h0 : 0 ≤ w.re) (h2 : 2 ≤ ‖w‖) : w ∈ Complex.slitPlane := by
  rcases h0.lt_or_eq with hpos | hzero
  · left; exact hpos
  · right
    intro him
    have : w = 0 := by apply Complex.ext <;> simp [← hzero, him]
    rw [this] at h2; simp at h2; linarith

/-- Derivative bounds on the half plane from a sector bound. -/
lemma deriv_bound_halfplane {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane) {K p : ℝ} (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hbd : ∀ z : ℂ, InSector z → 5 ≤ ‖z‖ → ‖F z‖ ≤ K * ‖z‖ ^ (-p)) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 2 ≤ ‖w‖ → ‖iteratedDeriv r F w‖ ≤ C * ‖w‖ ^ (-(p + r)) := by
  obtain ⟨C₁, hC₁, h1⟩ := cauchy_sector hF hK hp hbd r
  -- compact part
  have hcd : ContDiffOn ℂ ⊤ F Complex.slitPlane := hF.contDiffOn Complex.isOpen_slitPlane
  have hcont : ContinuousOn (iteratedDeriv r F) Complex.slitPlane := by
    have := hcd.continuousOn_iteratedDerivWithin (m := r) (by exact_mod_cast le_top) (Complex.isOpen_slitPlane.uniqueDiffOn)
    exact this.congr (fun z hz => (iteratedDerivWithin_of_isOpen Complex.isOpen_slitPlane hz).symm)
  set Kc : Set ℂ := {w : ℂ | 0 ≤ w.re ∧ 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 6} with hKc
  have hKc_compact : IsCompact Kc := by
    have hclosed : IsClosed Kc := by
      refine IsClosed.inter (isClosed_le continuous_const Complex.continuous_re) (IsClosed.inter (isClosed_le continuous_const continuous_norm) (isClosed_le continuous_norm continuous_const))
    exact (isCompact_closedBall (0 : ℂ) 6).of_isClosed_subset hclosed (fun w hw => by simpa [Metric.mem_closedBall, dist_zero_right] using hw.2.2)
  obtain ⟨M, hM⟩ := hKc_compact.exists_bound_of_continuousOn (hcont.mono (fun w hw => slit_of_halfplane hw.1 hw.2.1))
  refine ⟨max C₁ (|M| * 6 ^ (p + r)), by positivity, fun w h0 h2 => ?_⟩
  rcases le_or_gt 6 ‖w‖ with h6 | h6
  · exact (h1 w h0 h6).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hw : w ∈ Kc := ⟨h0, h2, h6.le⟩
    have hb := (hM w hw).trans (le_abs_self M)
    have hwpos : 0 < ‖w‖ := by linarith
    have : (6 : ℝ) ^ (-(p + r)) ≤ ‖w‖ ^ (-(p + r)) :=
      Real.rpow_le_rpow_of_nonpos hwpos h6.le (by linarith [Nat.cast_nonneg (α := ℝ) r])
    calc ‖iteratedDeriv r F w‖ ≤ |M| := hb
      _ = |M| * 6 ^ (p + r) * 6 ^ (-(p + r)) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num)]; simp
      _ ≤ |M| * 6 ^ (p + r) * ‖w‖ ^ (-(p + r)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

lemma differentiableOn_uctZ1 : DifferentiableOn ℂ uctZ1 Complex.slitPlane :=
  fun _w hw => (hasDerivAt_uctZ1 hw).differentiableAt.differentiableWithinAt

lemma differentiableOn_uctG1Ext : DifferentiableOn ℂ uctG1Ext Complex.slitPlane :=
  fun _w hw => (hasDerivAt_uctG1Ext hw).differentiableAt.differentiableWithinAt

lemma uctG1Ext_sector : ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, InSector z → 5 ≤ ‖z‖ → ‖uctG1Ext z‖ ≤ K * ‖z‖ ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨K, hK, h⟩ := uctW2_sector
  refine ⟨K, hK, fun z hs hz5 => ?_⟩
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz5; simp at hz5; linarith
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have e : uctW2 z = z ^ (9 / 2 : ℂ) * uctG1Ext z := by
    unfold uctW2; rw [cpow_nine_half]; ring
  have hb := h z hs hz5
  rw [e, norm_mul, norm_cpow_nine_half hz0] at hb
  have hp : 0 < ‖z‖ ^ (9 / 2 : ℝ) := by positivity
  rw [Real.rpow_neg hpos.le]
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

theorem uctZ1_iteratedDeriv_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 2 ≤ ‖w‖ → ‖iteratedDeriv r uctZ1 w‖ ≤ C * ‖w‖ ^ (-((2 : ℝ) + r)) := by
  obtain ⟨K, hK, h⟩ := uctZ1_sector
  exact deriv_bound_halfplane differentiableOn_uctZ1 hK.le (by norm_num) (p := 2) h r

theorem uctG1Ext_iteratedDeriv_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 2 ≤ ‖w‖ → ‖iteratedDeriv r uctG1Ext w‖ ≤ C * ‖w‖ ^ (-((9 / 2 : ℝ) + r)) := by
  obtain ⟨K, hK, h⟩ := uctG1Ext_sector
  exact deriv_bound_halfplane differentiableOn_uctG1Ext hK.le (by norm_num) (p := 9 / 2) h r

end FormalResearch.SignUncertainty
