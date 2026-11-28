module

public import FormalResearch.ModularBootstrap.Mixtures.JetsOuter
public import FormalResearch.ModularBootstrap.Mixtures.JetsAmpIntegrals
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Main

/-!
# Linear jet `g₁(w, A)`, `σ`-involution ratio, and product additivity (`ctu:jets` (b)–(c))

Computes the slope integrals `h₁` of `lamLog` and `aW`, proves `g₁(w, A)` (`g1OutWA_eq`),
its `Q ≡ 1` specialization (`g1OutWA_one`), product additivity (`I1Amp_mul`, `I3Amp_mul`),
and the `σ`-involution ratio formula (`goutWA_sigma`, `goutWA_sigma_eq_one`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory Asymptotics
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.Mixtures

/-! ### 1. Linearity of `hbarA` for `aWA` and general `Jet` along `epsR` -/

/-- `log(lamT τ)` for the Virasoro descendant denominator `λ_T`. -/
noncomputable def lamLog (τ : ℝ) : ℝ := Real.log (lamT τ)

lemma lamLog_zero : lamLog 0 = 0 := by
  simp [lamLog, lamT_zero]

private lemma amp_add' {a b : ℝ → ℝ} (ha : Amp a) (hb : Amp b) :
    Amp (fun t => a t + b t) := by
  refine ⟨ha.cont.add hb.cont, fun t => by simp [ha.even t, hb.even t], ?_, fun y₀ => ?_⟩
  · obtain ⟨Ca, hCa⟩ := ha.bdd
    obtain ⟨Cb, hCb⟩ := hb.bdd
    refine ⟨max Ca 0 + max Cb 0, fun t => ?_⟩
    have ha1 := (hCa t).trans (mul_le_mul_of_nonneg_right (le_max_left Ca 0) (Real.exp_pos _).le)
    have hb1 := (hCb t).trans (mul_le_mul_of_nonneg_right (le_max_left Cb 0) (Real.exp_pos _).le)
    calc |a t + b t| ≤ |a t| + |b t| := abs_add_le _ _
      _ ≤ max Ca 0 * Real.exp |t| + max Cb 0 * Real.exp |t| := add_le_add ha1 hb1
      _ = (max Ca 0 + max Cb 0) * Real.exp |t| := by ring
  · obtain ⟨Ra, hRa, va, hva, hva_eq⟩ := ha.loc y₀
    obtain ⟨Rb, hRb, vb, hvb, hvb_eq⟩ := hb.loc y₀
    refine ⟨min Ra Rb, lt_min hRa hRb, fun ζ => va ζ + vb ζ, ?_, fun t ht => ?_⟩
    · exact (hva.mono (Metric.ball_subset_ball (min_le_left _ _))).add
        (hvb.mono (Metric.ball_subset_ball (min_le_right _ _)))
    · dsimp only
      rw [hva_eq t (lt_of_lt_of_le ht (min_le_left _ _)),
        hvb_eq t (lt_of_lt_of_le ht (min_le_right _ _))]
      push_cast; rfl

private lemma amp_smul' (c : ℝ) {a : ℝ → ℝ} (ha : Amp a) :
    Amp (fun t => c * a t) := by
  refine ⟨continuous_const.mul ha.cont, fun t => by simp [ha.even t], ?_, fun y₀ => ?_⟩
  · obtain ⟨C, hC⟩ := ha.bdd
    refine ⟨|c| * max C 0, fun t => ?_⟩
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hC t).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.exp_pos _).le)) (abs_nonneg c)
  · obtain ⟨R, hR, v, hv, hv_eq⟩ := ha.loc y₀
    refine ⟨R, hR, fun ζ => (c : ℂ) * v ζ, ?_, fun t ht => ?_⟩
    · exact (differentiableOn_const _).mul hv
    · dsimp only; rw [hv_eq t ht]; push_cast; rfl

lemma hbarA_aWA_eq (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    hbarA (aWA w A) ζ =
      hbarA aAmp ζ + (-2 : ℂ) * hbarA lamLog ζ +
        ((((w - 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) * hbarA aW ζ + hbarA (aRel A) ζ := by
  have hlam : Amp lamLog := amp_lamLog
  have h12 : Amp (fun τ => aAmp τ + (-2 : ℝ) * lamLog τ) := amp_add' amp_aAmp (amp_smul' (-2) hlam)
  have h34 : Amp (fun τ => (((w - 1 : ℕ) : ℝ) / 2) * aW τ + aRel A τ) :=
    amp_add' (amp_smul' _ amp_aW) (amp_aRel hA)
  have hfun : aWA w A = fun τ =>
      (aAmp τ + (-2 : ℝ) * lamLog τ) + ((((w - 1 : ℕ) : ℝ) / 2) * aW τ + aRel A τ) := by
    ext τ; unfold aWA lamLog; ring
  rw [hfun, hbarA_add h12 h34 hζ, hbarA_add amp_aAmp (amp_smul' (-2) hlam) hζ,
    hbarA_add (amp_smul' _ amp_aW) (amp_aRel hA) hζ,
    hbarA_smul (-2 : ℝ) hlam hζ, hbarA_smul (((w - 1 : ℕ) : ℝ) / 2) amp_aW hζ]
  push_cast
  ring

private lemma jet_eps_comp {l : Filter ℝ} {f : ℝ → ℝ} {c0 S1 b0 D1 : ℝ}
    (hpi : π ≠ 0)
    (hc : Jet l f c0 (S1 * (4 / π)) (S1 * 0 + -(π ^ 2 * b0) * (4 / π) ^ 2)
      (S1 * (-4 / (3 * π)) + 2 * -(π ^ 2 * b0) * (4 / π) * 0 + -(π ^ 2) * (S1 / 6 + D1) * (4 / π) ^ 3)) :
    Jet l f c0 ((4 / π) * S1) (-(π ^ 2 * b0) * (4 / π) ^ 2) (-(12 / π) * S1 - (64 / π) * D1) :=
  hc.of_eq rfl (by ring) (by ring) (by field_simp; ring)

/-- General cubic jet of `x ↦ Re h̄_a(ε(x))` at `0⁺` for any `a` with `Amp a` and slope `S1`. -/
lemma exists_jet_re_hbarA_epsR_of_h1 {a : ℝ → ℝ} (ha : Amp a) {S1 : ℝ}
    (hS1 : ∫ t : ℝ, (a t - a 0) * (π * kern t) = S1) :
    ∃ b : ℝ → ℝ, Amp b ∧ (∀ t : ℝ, t ≠ 0 → b t = (a t - a 0) / Real.sinh (π * t) ^ 2) ∧
    ∃ c2 : ℝ, Jet (𝓝[>] (0 : ℝ)) (fun x => (hbarA a (epsR x : ℂ)).re) (a 0)
      ((4 / π) * S1) c2 (-(12 / π) * S1 - (64 / π) * ∫ t : ℝ, (b t - b 0) * (π * kern t)) := by
  have hpi := Real.pi_pos.ne'
  obtain ⟨b, hb, hab⟩ := amp_quot ha
  have hJ := jet_re_hbarA ha hb hab
  rw [hS1] at hJ
  have hc := Jet.comp nhdsGT_le_nhds0 hJ jet_epsR tendsto_epsR
  exact ⟨b, hb, hab, _, jet_eps_comp hpi hc⟩

/-- Real-axis logarithm `log (Re GoutWA w A x)` on `(0, 1/4)`. -/
noncomputable def logGoutWAR (w : ℕ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log (GoutWA w A (x : ℂ)).re

lemma goutWA_real_eq {w : ℕ} {A : ℝ → ℝ} (hA : JetAmplitude A) {x : ℝ}
    (hx0 : 0 < x) (hx4 : x < 1 / 4) :
    GoutWA w A (x : ℂ) = (((GoutWA w A (x : ℂ)).re : ℝ) : ℂ) ∧
    0 < (GoutWA w A (x : ℂ)).re ∧
    logGoutWAR w A x =
      logGoutR x - 2 * (hbarA lamLog (epsR x : ℂ)).re +
        (((w - 1 : ℕ) : ℝ) / 2) * ((hbarA aW (epsR x : ℂ)).re - Real.log (tipR x)) +
        (hbarA (aRel A) (epsR x : ℂ)).re := by
  have hx1 : x < 1 := by linarith
  have hxc : (x : ℂ) ∈ closure halfDisc :=
    subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
  have hz4 : ‖(x : ℂ)‖ < 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx4
  have h1I : (x : ℂ) ≠ Complex.I := by intro h; have := congrArg Complex.im h; simp at this
  have h2I : (x : ℂ) ≠ -Complex.I := by intro h; have := congrArg Complex.im h; simp at this
  have hs : sInv (x : ℂ) ∈ closedStrip := sInv_mem_closedStrip hxc h1I h2I
  have hs_eq : sInv (x : ℂ) = (epsR x : ℂ) := sInv_real (x := x)
  have heps_cl : (epsR x : ℂ) ∈ closedStrip := by rwa [← hs_eq]
  have hq : qBd (x : ℂ) = (tipR x : ℂ) := by
    rw [qBd_eq_tipExt hxc hz4]
    exact tipExt_real hx0 hx4
  have htip_pos : 0 < tipR x := tipR_pos hx0 hx4
  have hb_re : ∀ {a : ℝ → ℝ}, Amp a →
      hbarA a (epsR x : ℂ) = (((hbarA a (epsR x : ℂ)).re : ℝ) : ℂ) := by
    intro a ha
    have hc := hbarA_conj ha heps_cl
    rw [Complex.conj_ofReal] at hc
    have him := congrArg Complex.im hc.symm
    simp only [Complex.conj_im] at him
    exact Complex.ext rfl (by simp only [Complex.ofReal_im]; linarith)
  have hqpow : ((tipR x : ℂ) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ))) =
      ((Real.exp (-((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 * Real.log (tipR x))) : ℝ) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast htip_pos.ne'),
      ← Complex.ofReal_log htip_pos.le, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp]
    congr 2; ring
  have hc1 : ((1 - (x : ℂ)) ^ (1 / 2 : ℂ)) = ((Real.exp (Real.log (1 - x) / 2) : ℝ) : ℂ) := by
    have h1x : 0 < 1 - x := by linarith
    have he1 : (1 - x) ^ (1 / 2 : ℝ) = Real.exp (Real.log (1 - x) / 2) := by
      rw [Real.rpow_def_of_pos h1x]; congr 1; ring
    calc (1 - (x : ℂ)) ^ (1 / 2 : ℂ)
        = ((1 - x : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
            rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; rfl,
              show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl]
      _ = (((1 - x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := (Complex.ofReal_cpow h1x.le (1 / 2 : ℝ)).symm
      _ = ((Real.exp (Real.log (1 - x) / 2) : ℝ) : ℂ) := by rw [he1]
  have hc2 : (1 + (x : ℂ)) ^ 2 = ((Real.exp (2 * Real.log (1 + x)) : ℝ) : ℂ) := by
    have h1x : 0 < 1 + x := by linarith
    have he2 : (1 + x) ^ 2 = Real.exp (2 * Real.log (1 + x)) := by
      rw [show (2 : ℝ) * Real.log (1 + x) = ((2 : ℕ) : ℝ) * Real.log (1 + x) by norm_num,
        Real.exp_nat_mul, Real.exp_log h1x]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_pow, he2]
  have hval : GoutWA w A (x : ℂ) =
      ((Real.exp ((hbarA (aWA w A) (epsR x : ℂ)).re + Real.log (1 - x) / 2 -
        2 * Real.log (1 + x) - (2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 * Real.log (tipR x)) : ℝ) : ℂ) := by
    unfold GoutWA
    rw [hs_eq, hb_re (amp_aWA w hA), ← Complex.ofReal_exp, hq, hqpow, hc1, hc2,
      ← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_mul,
      ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
    congr 1
  have hpos : 0 < (GoutWA w A (x : ℂ)).re := by
    rw [hval, Complex.ofReal_re]
    exact Real.exp_pos _
  refine ⟨by rw [hval, Complex.ofReal_re], hpos, ?_⟩
  unfold logGoutWAR
  rw [hval, Complex.ofReal_re, Real.log_exp]
  have hlin := congrArg Complex.re (hbarA_aWA_eq w hA hs)
  rw [hs_eq, Complex.add_re, Complex.add_re, Complex.add_re,
    show (((-2 : ℂ) * hbarA lamLog (epsR x : ℂ)).re) = -2 * (hbarA lamLog (epsR x : ℂ)).re by simp,
    show ((((((w - 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) * hbarA aW (epsR x : ℂ)).re) =
      (((w - 1 : ℕ) : ℝ) / 2) * (hbarA aW (epsR x : ℂ)).re by simp] at hlin
  unfold logGoutR
  rw [hlin, log_gout_real hx0 hx4]
  ring

/-! ### 2. First-order slope integrals `h₁(lamLog)` and `h₁(aW)` -/

lemma hasDerivAt_lamLog (τ : ℝ) : HasDerivAt lamLog (lD τ / lamT τ) τ :=
  (hasDerivAt_lamT τ).log (lamT_pos τ).ne'

lemma h1_lamLog_eq :
    ∫ τ : ℝ, (lamLog τ - lamLog 0) * (π * kern τ) = π / 2 + 1 - 2 * √2 * Real.arsinh 1 := by
  have hlam : Amp lamLog := amp_lamLog
  obtain ⟨iS, vS⟩ := int_sech
  obtain ⟨iH, vH⟩ := int_half
  obtain ⟨iQ, vQ⟩ := int_sqrt
  let rhs : ℝ → ℝ := fun τ => (1 / 2 : ℝ) * (π / Real.cosh (π * τ) +
    π / (1 + Real.cosh (π * τ)) - 2 * (π / √(Real.cosh (π * τ) * (1 + Real.cosh (π * τ)))))
  have hpt : ∀ τ : ℝ, τ ≠ 0 → (lD τ / lamT τ) / Real.sinh (π * τ) = rhs τ := fun τ hτ => by
    have hp := piece_lam hτ
    dsimp only [rhs]
    calc (lD τ / lamT τ) / Real.sinh (π * τ)
        = (2 * (lD τ / lamT τ) / Real.sinh (π * τ)) / 2 := by ring
      _ = rhs τ := by rw [hp]; ring
  have hint : IntegrableOn (fun τ : ℝ => (lD τ / lamT τ) / Real.sinh (π * τ)) (Ioi 0) := by
    have hi : IntegrableOn rhs (Ioi 0) := ((iS.add iH).sub (iQ.const_mul 2)).const_mul (1 / 2)
    exact hi.congr_fun (fun τ hτ => (hpt τ (ne_of_gt hτ)).symm) measurableSet_Ioi
  have hibp := slope_ibp hlam (fun τ _ => hasDerivAt_lamLog τ) hint
  have h_add : ∫ τ in Ioi (0 : ℝ), (π / Real.cosh (π * τ) + π / (1 + Real.cosh (π * τ))) =
      π / 2 + 1 := by
    calc ∫ τ in Ioi (0 : ℝ), (π / Real.cosh (π * τ) + π / (1 + Real.cosh (π * τ)))
        = (∫ τ in Ioi (0 : ℝ), π / Real.cosh (π * τ)) +
          ∫ τ in Ioi (0 : ℝ), π / (1 + Real.cosh (π * τ)) := integral_add iS iH
      _ = π / 2 + 1 := by rw [vS, vH]
  have h_sub : ∫ τ in Ioi (0 : ℝ), (π / Real.cosh (π * τ) + π / (1 + Real.cosh (π * τ)) -
      2 * (π / √(Real.cosh (π * τ) * (1 + Real.cosh (π * τ))))) =
      π / 2 + 1 - 2 * (√2 * Real.arsinh 1) := by
    calc ∫ τ in Ioi (0 : ℝ), (π / Real.cosh (π * τ) + π / (1 + Real.cosh (π * τ)) -
          2 * (π / √(Real.cosh (π * τ) * (1 + Real.cosh (π * τ)))))
        = (∫ τ in Ioi (0 : ℝ), (π / Real.cosh (π * τ) + π / (1 + Real.cosh (π * τ)))) -
          ∫ τ in Ioi (0 : ℝ), 2 * (π / √(Real.cosh (π * τ) * (1 + Real.cosh (π * τ)))) :=
          integral_sub (iS.add iH) (iQ.const_mul 2)
      _ = (π / 2 + 1) - 2 * (√2 * Real.arsinh 1) := by
          rw [h_add, integral_const_mul, vQ]
  have heq : ∫ τ in Ioi (0 : ℝ), (lD τ / lamT τ) / Real.sinh (π * τ) =
      (π / 2 + 1 - 2 * (√2 * Real.arsinh 1)) / 2 := by
    have hcon : ∫ τ in Ioi (0 : ℝ), (lD τ / lamT τ) / Real.sinh (π * τ) = ∫ τ in Ioi (0 : ℝ), rhs τ :=
      setIntegral_congr_fun measurableSet_Ioi fun τ hτ => hpt τ (ne_of_gt hτ)
    rw [hcon]
    show ∫ τ in Ioi (0 : ℝ), (1 / 2 : ℝ) * _ = _
    rw [integral_const_mul, h_sub]
    ring
  rw [hibp, heq]
  ring

lemma hasDerivAt_aW (τ : ℝ) : HasDerivAt aW (xD τ / xT τ + (vT τ * vD τ / bT τ) / bT τ) τ := by
  have hx := ((hasDerivAt_xT τ).div_const xiStar).log (div_pos (xT_pos τ) xiStar_pos).ne'
  have hb := ((hasDerivAt_bT τ).div_const xiStar).log (div_pos (bT_pos τ) xiStar_pos).ne'
  have hadd : HasDerivAt aW (xD τ / xiStar / (xT τ / xiStar) + (vT τ * vD τ / bT τ / xiStar) / (bT τ / xiStar)) τ :=
    hx.add hb
  refine hadd.congr_deriv ?_
  have hxi := xiStar_pos.ne'
  have hx0 := (xT_pos τ).ne'
  have hb0 := (bT_pos τ).ne'
  field_simp

lemma h1_aW_eq : ∫ τ : ℝ, (aW τ - aW 0) * (π * kern τ) = π - √2 := by
  obtain ⟨hxi, hvi, -⟩ := xb_cauchy_identity
  have hpt : ∀ τ : ℝ, τ ≠ 0 →
      (xD τ / xT τ + (vT τ * vD τ / bT τ) / bT τ) / Real.sinh (π * τ) = (xA τ + vA τ) / 2 :=
    fun τ hτ => by
      have hpx := piece_x hτ
      have hpb := piece_b hτ
      linear_combination 4 * hpx + 4 * hpb
  have hint : IntegrableOn (fun τ : ℝ => (xD τ / xT τ + (vT τ * vD τ / bT τ) / bT τ) / Real.sinh (π * τ))
      (Ioi 0) := by
    have hi : IntegrableOn (fun τ : ℝ => (xA τ + vA τ) / 2) (Ioi 0) :=
      (hxi.integrableOn.add hvi.integrableOn).div_const 2
    exact hi.congr_fun (fun τ hτ => (hpt τ (ne_of_gt hτ)).symm) measurableSet_Ioi
  have hibp := slope_ibp amp_aW (fun τ _ => hasDerivAt_aW τ) hint
  have heq : ∫ τ in Ioi (0 : ℝ), (xD τ / xT τ + (vT τ * vD τ / bT τ) / bT τ) / Real.sinh (π * τ) =
      (π - √2) / 2 := by
    have hcon : ∫ τ in Ioi (0 : ℝ),
          (xD τ / xT τ + (vT τ * vD τ / bT τ) / bT τ) / Real.sinh (π * τ) =
        ∫ τ in Ioi (0 : ℝ), (xA τ + vA τ) / 2 :=
      setIntegral_congr_fun measurableSet_Ioi fun τ hτ => hpt τ (ne_of_gt hτ)
    rw [hcon, integral_div, integral_xA_vA_Ioi]
  rw [hibp, heq]
  ring

/-! ### 3. Cubic jet of `logGoutWAR`, `g₁(w, A)`, `Q ≡ 1`, and product additivity (`ctu:jets` (b)) -/

/-- The cubic jet of `logGoutWAR w A` along `𝓝[>] 0`, exposing the first and third coefficients. -/
lemma exists_jet_logGoutWAR_raw {w : ℕ} (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ (bLam bW bA : ℝ → ℝ),
      Amp bLam ∧ (∀ t : ℝ, t ≠ 0 → bLam t = (lamLog t - lamLog 0) / Real.sinh (π * t) ^ 2) ∧
      Amp bW ∧ (∀ t : ℝ, t ≠ 0 → bW t = (aW t - aW 0) / Real.sinh (π * t) ^ 2) ∧
      Amp bA ∧ (∀ t : ℝ, t ≠ 0 → bA t = (aRel A t - aRel A 0) / Real.sinh (π * t) ^ 2) ∧
      ∃ c2 : ℝ, Jet (𝓝[>] (0 : ℝ)) (logGoutWAR w A) 0
        (2 * (w : ℝ) - 3 - 2 / π + 8 * I1Amp A / π) c2
        (g3Vir - 2 * (-(12 / π) * (π / 2 + 1 - 2 * √2 * Real.arsinh 1) -
            (64 / π) * (∫ t : ℝ, (bLam t - bLam 0) * (π * kern t))) +
          (((w - 1 : ℕ) : ℝ) / 2) * ((-(12 / π) * (π - √2) -
            (64 / π) * (∫ t : ℝ, (bW t - bW 0) * (π * kern t))) -
            (-(4 * √2) / (3 * π) - 128 * √2 / (3 * π ^ 3))) +
          (-(12 / π) * (2 * I1Amp A) - (64 / π) * ((2 / 3) * I3Amp A))) := by
  have hpi := Real.pi_pos.ne'
  have h1lam : ∫ t : ℝ, (lamLog t - lamLog 0) * (π * kern t) = π / 2 + 1 - 2 * √2 * Real.arsinh 1 :=
    h1_lamLog_eq
  have hlam : Amp lamLog := amp_lamLog
  obtain ⟨bLam, hbLam, habLam, _, hJlam⟩ := exists_jet_re_hbarA_epsR_of_h1 hlam h1lam
  obtain ⟨bW, hbW, habW, _, hJW⟩ := exists_jet_re_hbarA_epsR_of_h1 amp_aW h1_aW_eq
  obtain ⟨bA, hbA, habA, _, hJA⟩ := exists_jet_re_hbarA_epsR_of_h1 (amp_aRel hA) (h1_aRel_eq hA)
  obtain ⟨c2V, hJV⟩ := exists_jet_logGout_vir
  obtain ⟨t0, t2, hT⟩ := jet_log_tipR
  have hsum := ((hJV.sub (hJlam.const_mul 2)).add ((hJW.sub hT).const_mul (((w - 1 : ℕ) : ℝ) / 2))).add hJA
  have hev : (fun x => logGoutR x - 2 * (hbarA lamLog (epsR x : ℂ)).re +
      (((w - 1 : ℕ) : ℝ) / 2) * ((hbarA aW (epsR x : ℂ)).re - Real.log (tipR x)) +
      (hbarA (aRel A) (epsR x : ℂ)).re) =ᶠ[𝓝[>] (0 : ℝ)] logGoutWAR w A := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with x hx
    exact (goutWA_real_eq hA hx.1 hx.2).2.2.symm
  have hJet := hsum.congr_ev hev
  have htend_log : Tendsto (logGoutWAR w A) (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨C, r, hr, hjet⟩ := (goutWA_outerDatum_g1OutWA w hw hA).jet
    have hb : Tendsto (fun x : ℝ => (|g1OutWA w hw hA| + |C| * x) * x) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => (|g1OutWA w hw hA| + |C| * x) * x) (𝓝 0)
          (𝓝 ((|g1OutWA w hw hA| + |C| * 0) * 0)) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hG : Tendsto (fun x : ℝ => GoutWA w A (x : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r 1 by positivity)] with x hx
      have hx0 : 0 < x := hx.1
      have hxr : x < r := lt_of_lt_of_le hx.2 (min_le_left _ _)
      have hx1 : x < 1 := lt_of_lt_of_le hx.2 (min_le_right _ _)
      have hxc : (x : ℂ) ∈ closure halfDisc :=
        subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
      have hbd := hjet (x : ℂ) hxc (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxr)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hbd
      have e : ‖GoutWA w A (x : ℂ) - 1‖ ≤
          ‖GoutWA w A (x : ℂ) - 1 - g1OutWA w hw hA * (x : ℂ)‖ + ‖g1OutWA w hw hA * (x : ℂ)‖ := by
        simpa using norm_add_le (GoutWA w A (x : ℂ) - 1 - g1OutWA w hw hA * (x : ℂ))
          (g1OutWA w hw hA * (x : ℂ))
      have e2 : ‖g1OutWA w hw hA * (x : ℂ)‖ = |g1OutWA w hw hA| * x := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hx0]
      calc ‖GoutWA w A (x : ℂ) - 1‖ ≤ C * x ^ 2 + |g1OutWA w hw hA| * x := by linarith
        _ ≤ (|g1OutWA w hw hA| + |C| * x) * x := by nlinarith only [le_abs_self C, hx0]
    have hre_lim : Tendsto (fun x : ℝ => (GoutWA w A (x : ℂ)).re) (𝓝[>] 0) (𝓝 1) :=
      (Complex.continuous_re.tendsto 1).comp hG
    unfold logGoutWAR
    simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp hre_lim
  have h0 := tendsto_nhds_unique (hJet.tendsto nhdsGT_le_nhds0) htend_log
  have hw1 : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - 1 := by simp [Nat.cast_sub hw]
  have h1eq : g1Vir - 2 * ((4 / π) * (π / 2 + 1 - 2 * √2 * Real.arsinh 1)) +
      (((w - 1 : ℕ) : ℝ) / 2) * ((4 / π) * (π - √2) - (-(4 * √2 / π))) +
      (4 / π) * (2 * I1Amp A) = 2 * (w : ℝ) - 3 - 2 / π + 8 * I1Amp A / π := by
    rw [hw1]; unfold g1Vir xiStar; field_simp; ring
  rw [d1_aRel_eq hA hbA habA] at hJet
  refine ⟨bLam, bW, bA, hbLam, habLam, hbW, habW, hbA, habA, _,
    hJet.of_eq h0 h1eq rfl (by simp only [mul_assoc, sub_eq_add_neg])⟩

/-- Exact formula for `g₁(w, A)` (`ctu:g13A`, `ctu:jets` (b)):
`g₁(w, A) = 2w - 3 - 2/π + 8 I₁(A) / π` for every `w ≥ 1` and `JetAmplitude A`. -/
theorem g1OutWA_eq {w : ℕ} (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    g1OutWA w hw hA = 2 * (w : ℝ) - 3 - 2 / π + 8 * I1Amp A / π := by
  obtain ⟨bLam, bW, bA, _, _, _, _, _, _, c2, hJ⟩ := exists_jet_logGoutWAR_raw hw hA
  set g1' : ℝ := 2 * (w : ℝ) - 3 - 2 / π + 8 * I1Amp A / π
  set g3' : ℝ := g3Vir - 2 * (-(12 / π) * (π / 2 + 1 - 2 * √2 * Real.arsinh 1) -
      (64 / π) * (∫ t : ℝ, (bLam t - bLam 0) * (π * kern t))) +
    (((w - 1 : ℕ) : ℝ) / 2) * ((-(12 / π) * (π - √2) -
      (64 / π) * (∫ t : ℝ, (bW t - bW 0) * (π * kern t))) -
      (-(4 * √2) / (3 * π) - 128 * √2 / (3 * π ^ 3))) +
    (-(12 / π) * (2 * I1Amp A) - (64 / π) * ((2 / 3) * I3Amp A))
  have hlim1 : Tendsto (fun x : ℝ => logGoutWAR w A x / x) (𝓝[>] 0) (𝓝 g1') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbd := hJ.bound zero_lt_one
    have hlim0 : Tendsto (fun x : ℝ => x ^ 2 + |c2| * x + |g3'| * x ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x ^ 2 + |c2| * x + |g3'| * x ^ 2) (𝓝 0)
          (𝓝 (0 ^ 2 + |c2| * 0 + |g3'| * 0 ^ 2)) :=
        (((continuous_id.pow 2).add (continuous_const.mul continuous_id)).add
          (continuous_const.mul (continuous_id.pow 2))).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim0
    filter_upwards [hbd, self_mem_nhdsWithin] with x hxb hx0
    have hx : 0 < x := hx0
    simp only [Real.norm_eq_abs, one_mul, abs_of_nonneg (pow_nonneg hx.le 3)] at hxb
    have hxb' : |logGoutWAR w A x - 0 - g1' * x - c2 * x ^ 2 - g3' * x ^ 3| ≤ x ^ 3 := by
      simpa only [sub_add_eq_sub_sub, sub_zero] using hxb
    have htri : |logGoutWAR w A x - g1' * x| ≤
        |logGoutWAR w A x - 0 - g1' * x - c2 * x ^ 2 - g3' * x ^ 3| +
          (|c2| * x ^ 2 + |g3'| * x ^ 3) := by
      calc |logGoutWAR w A x - g1' * x|
          = |(logGoutWAR w A x - 0 - g1' * x - c2 * x ^ 2 - g3' * x ^ 3) +
              (c2 * x ^ 2 + g3' * x ^ 3)| := by ring_nf
        _ ≤ |logGoutWAR w A x - 0 - g1' * x - c2 * x ^ 2 - g3' * x ^ 3| +
              |c2 * x ^ 2 + g3' * x ^ 3| := abs_add_le _ _
        _ ≤ |logGoutWAR w A x - 0 - g1' * x - c2 * x ^ 2 - g3' * x ^ 3| +
              (|c2 * x ^ 2| + |g3' * x ^ 3|) :=
            add_le_add_right (abs_add_le (c2 * x ^ 2) (g3' * x ^ 3)) _
        _ = |logGoutWAR w A x - 0 - g1' * x - c2 * x ^ 2 - g3' * x ^ 3| +
              (|c2| * x ^ 2 + |g3'| * x ^ 3) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x), abs_of_nonneg (pow_nonneg hx.le 3)]
    rw [Real.norm_eq_abs, show logGoutWAR w A x / x - g1' = (logGoutWAR w A x - g1' * x) / x by
      field_simp, abs_div, abs_of_pos hx, div_le_iff₀ hx]
    calc |logGoutWAR w A x - g1' * x|
        ≤ x ^ 3 + (|c2| * x ^ 2 + |g3'| * x ^ 3) := by linarith [hxb', htri]
      _ = (x ^ 2 + |c2| * x + |g3'| * x ^ 2) * x := by ring
  have hlim2 : Tendsto (fun x : ℝ => logGoutWAR w A x / x) (𝓝[>] 0) (𝓝 (g1OutWA w hw hA)) := by
    obtain ⟨C, r, hr, hjet⟩ := (goutWA_outerDatum_g1OutWA w hw hA).jet
    have hG1 : Tendsto (fun x : ℝ => (GoutWA w A (x : ℂ)).re - 1) (𝓝[>] 0) (𝓝 0) := by
      have hb : Tendsto (fun x : ℝ => (|g1OutWA w hw hA| + |C| * x) * x) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun x : ℝ => (|g1OutWA w hw hA| + |C| * x) * x) (𝓝 0)
            (𝓝 ((|g1OutWA w hw hA| + |C| * 0) * 0)) :=
          ((continuous_const.add (continuous_const.mul continuous_id)).mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r 1 by positivity)] with x hx
      have hx0 : 0 < x := hx.1
      have hxr : x < r := lt_of_lt_of_le hx.2 (min_le_left _ _)
      have hx1 : x < 1 := lt_of_lt_of_le hx.2 (min_le_right _ _)
      have hxc : (x : ℂ) ∈ closure halfDisc :=
        subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
      have hbd := hjet (x : ℂ) hxc (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxr)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hbd
      have hre_le : |(GoutWA w A (x : ℂ)).re - 1 - g1OutWA w hw hA * x| ≤ C * x ^ 2 := by
        have h1 := Complex.abs_re_le_norm (GoutWA w A (x : ℂ) - 1 - g1OutWA w hw hA * (x : ℂ))
        simpa using h1.trans hbd
      have e : |(GoutWA w A (x : ℂ)).re - 1| ≤
          |(GoutWA w A (x : ℂ)).re - 1 - g1OutWA w hw hA * x| + |g1OutWA w hw hA * x| := by
        calc |(GoutWA w A (x : ℂ)).re - 1|
            = |((GoutWA w A (x : ℂ)).re - 1 - g1OutWA w hw hA * x) + g1OutWA w hw hA * x| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [abs_mul, abs_of_pos hx0] at e
      rw [sub_zero, Real.norm_eq_abs]
      nlinarith [le_abs_self C, hx0]
    have hy_small : ∀ᶠ x : ℝ in 𝓝[>] 0, |(GoutWA w A (x : ℂ)).re - 1| ≤ 1 / 2 :=
      (Metric.tendsto_nhds.mp hG1 (1 / 2) (by norm_num)).mono fun x hx => by
        simpa [Real.dist_eq] using hx.le
    have hlog_err : ∀ y : ℝ, |y| ≤ 1 / 2 → |Real.log (1 + y) - y| ≤ 2 * y ^ 2 := fun y hy => by
      have hy_lo : -1 / 2 ≤ y := by linarith [(abs_le.mp hy).1]
      have h1y : 1 / 2 ≤ 1 + y := by linarith
      have hup : Real.log (1 + y) ≤ y := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + y)]
      have hinv : Real.log ((1 + y)⁻¹) ≤ (1 + y)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith))
      rw [Real.log_inv] at hinv
      have hlo : -y ^ 2 / (1 + y) ≤ Real.log (1 + y) - y := by
        have : y / (1 + y) ≤ Real.log (1 + y) := by
          have : (1 + y)⁻¹ - 1 = -(y / (1 + y)) := by
            field_simp [show (1 + y) ≠ 0 by linarith]; ring
          linarith
        have : -y ^ 2 / (1 + y) = y / (1 + y) - y := by
          field_simp [show (1 + y) ≠ 0 by linarith]; ring
        linarith
      have hlo2 : -(2 * y ^ 2) ≤ Real.log (1 + y) - y := by
        have h1 : y ^ 2 / (1 + y) ≤ 2 * y ^ 2 := by
          rw [div_le_iff₀ (by linarith : 0 < 1 + y)]
          nlinarith [sq_nonneg y]
        linarith [show -y ^ 2 / (1 + y) = -(y ^ 2 / (1 + y)) by ring]
      exact abs_le.mpr ⟨hlo2, by linarith [sq_nonneg y]⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    let C0 : ℝ := 2 * (|g1OutWA w hw hA| + |C|) ^ 2 + |C|
    have hlim0 : Tendsto (fun x : ℝ => C0 * x) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => C0 * x) (𝓝 0) (𝓝 (C0 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim0
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (min r (1 / 4)) 1 by positivity), hy_small]
      with x hx hy
    have hx0 : 0 < x := hx.1
    have hxr : x < r := lt_of_lt_of_le hx.2 ((min_le_left _ _).trans (min_le_left _ _))
    have hx4 : x < 1 / 4 := lt_of_lt_of_le hx.2 ((min_le_left _ _).trans (min_le_right _ _))
    have hx1 : x < 1 := lt_of_lt_of_le hx.2 (min_le_right _ _)
    have hxc : (x : ℂ) ∈ closure halfDisc :=
      subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
    have hbd := hjet (x : ℂ) hxc (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxr)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hbd
    have hre_le : |(GoutWA w A (x : ℂ)).re - 1 - g1OutWA w hw hA * x| ≤ C * x ^ 2 := by
      have h1 := Complex.abs_re_le_norm (GoutWA w A (x : ℂ) - 1 - g1OutWA w hw hA * (x : ℂ))
      simpa using h1.trans hbd
    let y := (GoutWA w A (x : ℂ)).re - 1
    have hy_le : |y| ≤ (|g1OutWA w hw hA| + |C|) * x := by
      have e : |y| ≤ |y - g1OutWA w hw hA * x| + |g1OutWA w hw hA * x| := by
        calc |y| = |(y - g1OutWA w hw hA * x) + g1OutWA w hw hA * x| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [abs_mul, abs_of_pos hx0] at e
      have hx_le : x ^ 2 ≤ x := by nlinarith
      have hCx : C * x ^ 2 ≤ |C| * x :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg x)).trans
          (mul_le_mul_of_nonneg_left hx_le (abs_nonneg C))
      have hre' : |y - g1OutWA w hw hA * x| ≤ |C| * x := hre_le.trans hCx
      linarith
    have herr := hlog_err y hy
    have h1y_eq : 1 + y = (GoutWA w A (x : ℂ)).re := by dsimp only [y]; ring
    rw [h1y_eq] at herr
    have hnum : |logGoutWAR w A x - g1OutWA w hw hA * x| ≤ C0 * x ^ 2 := by
      calc |logGoutWAR w A x - g1OutWA w hw hA * x|
          = |(Real.log (GoutWA w A (x : ℂ)).re - y) + (y - g1OutWA w hw hA * x)| := by
              unfold logGoutWAR; ring_nf
        _ ≤ |Real.log (GoutWA w A (x : ℂ)).re - y| + |y - g1OutWA w hw hA * x| := abs_add_le _ _
        _ ≤ 2 * y ^ 2 + |C| * x ^ 2 := by
              refine add_le_add herr (hre_le.trans ?_)
              exact mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg x)
        _ ≤ 2 * ((|g1OutWA w hw hA| + |C|) * x) ^ 2 + |C| * x ^ 2 := by
              have hsq : y ^ 2 ≤ ((|g1OutWA w hw hA| + |C|) * x) ^ 2 := by
                rw [← sq_abs y]
                exact pow_le_pow_left₀ (abs_nonneg y) hy_le 2
              linarith
        _ = C0 * x ^ 2 := by dsimp only [C0]; ring
    rw [Real.norm_eq_abs, show logGoutWAR w A x / x - g1OutWA w hw hA =
        (logGoutWAR w A x - g1OutWA w hw hA * x) / x by field_simp, abs_div, abs_of_pos hx0,
      div_le_iff₀ hx0]
    linarith [hnum, show (C0 * x) * x = C0 * x ^ 2 by ring]
  exact tendsto_nhds_unique hlim2 hlim1

/-- Unit amplitude `A ≡ 1` satisfies `JetAmplitude`. -/
lemma jetAmplitude_one : JetAmplitude (fun _ : ℝ => (1 : ℝ)) where
  analytic := fun x _ => analyticAt_const
  lower := ⟨1, one_pos, fun _ _ => le_rfl⟩
  upper := ⟨1, fun _ _ => le_rfl⟩
  deriv_bdd := ⟨0, fun x _ => by simp⟩

lemma I1Amp_one : I1Amp (fun _ : ℝ => (1 : ℝ)) = 0 := by
  have he : ∀ t : ℝ, ellAmp (fun _ : ℝ => (1 : ℝ)) t = 0 := fun t => by
    unfold ellAmp
    simp
  simp [I1Amp, he]

lemma I3Amp_one : I3Amp (fun _ : ℝ => (1 : ℝ)) = 0 := by
  have he : ∀ t : ℝ, ellAmp (fun _ : ℝ => (1 : ℝ)) t = 0 := fun t => by
    unfold ellAmp
    simp
  simp [I3Amp, he]

/-- `Q ≡ 1` specialization (`ctu:jets` (b)): `g₁(w, 1) = 2w - 3 - 2/π`. -/
theorem g1OutWA_one {w : ℕ} (hw : 1 ≤ w) :
    g1OutWA w hw jetAmplitude_one = 2 * (w : ℝ) - 3 - 2 / π := by
  rw [g1OutWA_eq hw jetAmplitude_one, I1Amp_one]
  ring

/-- Product of two `JetAmplitude` functions is a `JetAmplitude`. -/
lemma JetAmplitude.mul {A B : ℝ → ℝ} (hA : JetAmplitude A) (hB : JetAmplitude B) :
    JetAmplitude (fun x => A x * B x) := by
  obtain ⟨loA, hloA, hAlo⟩ := hA.lower
  obtain ⟨loB, hloB, hBlo⟩ := hB.lower
  obtain ⟨hiA, hAhi⟩ := hA.upper
  obtain ⟨hiB, hBhi⟩ := hB.upper
  obtain ⟨DA, hDA⟩ := hA.deriv_bdd
  obtain ⟨DB, hDB⟩ := hB.deriv_bdd
  refine ⟨fun x hx => (hA.analytic x hx).mul (hB.analytic x hx),
    ⟨loA * loB, mul_pos hloA hloB, fun x hx =>
      mul_le_mul (hAlo x hx) (hBlo x hx) hloB.le (lt_of_lt_of_le hloA (hAlo x hx)).le⟩,
    ⟨hiA * hiB, fun x hx =>
      mul_le_mul (hAhi x hx) (hBhi x hx) (lt_of_lt_of_le hloB (hBlo x hx)).le
        ((lt_of_lt_of_le hloA (hAlo x hx)).le.trans (hAhi x hx))⟩,
    ⟨max hiA 0 * max DB 0 + max hiB 0 * max DA 0, fun x hx => ?_⟩⟩
  have hdA : HasDerivAt A (deriv A x) x := (hA.analytic x hx).differentiableAt.hasDerivAt
  have hdB : HasDerivAt B (deriv B x) x := (hB.analytic x hx).differentiableAt.hasDerivAt
  have hmul := (hdA.fun_mul hdB).deriv
  rw [hmul]
  have hAp : 0 ≤ A x := (lt_of_lt_of_le hloA (hAlo x hx)).le
  have hBp : 0 ≤ B x := (lt_of_lt_of_le hloB (hBlo x hx)).le
  calc |deriv A x * B x + A x * deriv B x|
      ≤ |deriv A x * B x| + |A x * deriv B x| := abs_add_le _ _
    _ = |deriv A x| * B x + A x * |deriv B x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hBp, abs_of_nonneg hAp]
    _ ≤ max DA 0 * max hiB 0 + max hiA 0 * max DB 0 := by
        exact add_le_add
          (mul_le_mul ((hDA x hx).trans (le_max_left _ _)) ((hBhi x hx).trans (le_max_left _ _)) hBp
            (le_max_right _ _))
          (mul_le_mul ((hAhi x hx).trans (le_max_left _ _)) ((hDB x hx).trans (le_max_left _ _))
            (abs_nonneg _) (le_max_right _ _))
    _ = max hiA 0 * max DB 0 + max hiB 0 * max DA 0 := by ring

lemma ellAmp_mul {A B : ℝ → ℝ} (hA : JetAmplitude A) (hB : JetAmplitude B) (t : ℝ) :
    ellAmp (fun x => A x * B x) t = ellAmp A t + ellAmp B t := by
  obtain ⟨loA, hloA, hAlo⟩ := hA.lower
  obtain ⟨loB, hloB, hBlo⟩ := hB.lower
  have hxA : A (xChart t) ≠ 0 := (lt_of_lt_of_le hloA (hAlo _ (xiStar_le_xChart t))).ne'
  have hxB : B (xChart t) ≠ 0 := (lt_of_lt_of_le hloB (hBlo _ (xiStar_le_xChart t))).ne'
  have hdA : HasDerivAt A (deriv A (xChart t)) (xChart t) :=
    (hA.analytic _ (xiStar_le_xChart t)).differentiableAt.hasDerivAt
  have hdB : HasDerivAt B (deriv B (xChart t)) (xChart t) :=
    (hB.analytic _ (xiStar_le_xChart t)).differentiableAt.hasDerivAt
  unfold ellAmp
  rw [(hdA.fun_mul hdB).deriv]
  field_simp

/-- Product additivity for `I₁(A B) = I₁(A) + I₁(B)` (`ctu:jets` (b), `ctu:g13`). -/
theorem I1Amp_mul {A B : ℝ → ℝ} (hA : JetAmplitude A) (hB : JetAmplitude B) :
    I1Amp (fun x => A x * B x) = I1Amp A + I1Amp B := by
  unfold I1Amp
  rw [← integral_add (integrableOn_ellAmp hA) (integrableOn_ellAmp hB)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ellAmp_mul hA hB t

/-- Product additivity for `I₃(A B) = I₃(A) + I₃(B)` (`ctu:jets` (b), `ctu:g13`). -/
theorem I3Amp_mul {A B : ℝ → ℝ} (hA : JetAmplitude A) (hB : JetAmplitude B) :
    I3Amp (fun x => A x * B x) = I3Amp A + I3Amp B := by
  unfold I3Amp
  rw [← integral_add (integrableOn_ellAmp_sub hA) (integrableOn_ellAmp_sub hB)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [ellAmp_mul hA hB t, ellAmp_mul hA hB 0]
  ring

/-! ### 4. `σ`-involution quotient independence (`ctu:jets` (c)) -/

/-- `G_outer^{(w,A)} = G_outer^{(w,1)} · G_{A,4}` on `closure Ω ∖ {±i, 1}` (`ctu:jets`). -/
lemma goutWA_factor (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) {z : ℂ}
    (hz : z ∈ closure halfDisc \ singPts) :
    GoutWA w A z = GoutWA w (fun _ => 1) z * GA4 A z := by
  have hs : sInv z ∈ closedStrip := sInv_mem_closedStrip' hz
  have hfun : aWA w A = fun τ => aWA w (fun _ => 1) τ + aRel A τ := by
    ext τ
    unfold aWA aRel
    simp
  have h1 := amp_aWA w jetAmplitude_one
  have h2 := amp_aRel hA
  unfold GoutWA GA4
  rw [hfun, hbarA_add h1 h2 hs, Complex.exp_add]
  ring

/-- `G_outer^{(w,A)}(σ z) / G_outer^{(w,A)}(z)` is independent of the amplitude `A` on `Ω` (`ctu:jets` (c)). -/
theorem goutWA_sigma_eq_one (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) {z : ℂ} (hz : z ∈ halfDisc) :
    GoutWA w A (sigmaHD z) / GoutWA w A z =
      GoutWA w (fun _ => 1) (sigmaHD z) / GoutWA w (fun _ => 1) z := by
  have hz_cl : z ∈ closure halfDisc \ singPts := ⟨subset_closure hz, not_mem_singPts_of_halfDisc hz⟩
  have hσ_cl : sigmaHD z ∈ closure halfDisc \ singPts :=
    ⟨subset_closure (sigmaHD_mem hz), not_mem_singPts_of_halfDisc (sigmaHD_mem hz)⟩
  rw [goutWA_factor w hA hz_cl, goutWA_factor w hA hσ_cl, GA4_sigma hA hz]
  have hGne : GA4 A z ≠ 0 := by unfold GA4; exact Complex.exp_ne_zero _
  field_simp

private lemma c_log_mul_re_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Complex.log (u * v) = Complex.log u + Complex.log v := by
  have hu_ne : u ≠ 0 := fun h => by rw [h] at hu; simp at hu
  have hv_ne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have harg_u : |u.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have harg_v : |v.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  have hpi := Real.pi_pos
  have him : (Complex.log u + Complex.log v).im ∈ Ioc (-π) π := by
    rw [Complex.add_im, Complex.log_im, Complex.log_im]
    obtain ⟨h1, h2⟩ := abs_lt.mp harg_u
    obtain ⟨h3, h4⟩ := abs_lt.mp harg_v
    exact ⟨by linarith, by linarith⟩
  rw [← Complex.log_exp him.1 him.2, Complex.exp_add, Complex.exp_log hu_ne, Complex.exp_log hv_ne]

/-- Closed form of the `σ`-involution quotient on `Ω` (`ctu:jets` (c)):
`G_outer^{(w,A)}(σ z) / G_outer^{(w,A)}(z) = (2√2)⁻¹ z^{1/2} (1+z)^{7/2} (1-z)^{-1/2} q̂(z)^{(2w-1)/2}`. -/
theorem goutWA_sigma_formula {w : ℕ} (_hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) {z : ℂ}
    (hz : z ∈ halfDisc) :
    GoutWA w A (sigmaHD z) / GoutWA w A z =
      (1 / (2 * (√2 : ℝ) : ℂ)) * z ^ (1 / 2 : ℂ) * (1 + z) ^ (7 / 2 : ℂ) *
        (1 - z) ^ (-1 / 2 : ℂ) * (qHat z) ^ (((2 * ((w - 1 : ℕ) : ℝ) + 1) / 2 : ℝ) : ℂ) := by
  rw [goutWA_sigma_eq_one w hA hz]
  have hz_mem := halfDisc_ne_special hz
  have hσ := sigmaHD_mem hz
  have hσ_mem := halfDisc_ne_special hσ
  have hz_cl : z ∈ closure halfDisc := subset_closure hz
  have hσ_cl : sigmaHD z ∈ closure halfDisc := subset_closure hσ
  have hs : sInv z ∈ closedStrip := strip_subset_closedStrip (sInv_mem_strip hz)
  have hhbar : hbarA (aWA w (fun _ => 1)) (sInv (sigmaHD z)) = hbarA (aWA w (fun _ => 1)) (sInv z) := by
    rw [sInv_sigma hz, hbarA_oneSub (amp_aWA w jetAmplitude_one) hs]
  have hq : qBd z = qHat z := qBd_of_mem hz
  have hqσ : qBd (sigmaHD z) = (qHat z)⁻¹ := by
    rw [qBd_of_mem hσ, sigmaHD, qHat_sigma hz]
  have hqz_slit : qHat z ∈ Complex.slitPlane := by
    rw [← hq]; exact qBd_mem_slit ⟨hz_cl, not_mem_singPts_of_halfDisc hz⟩
  have hqz_ne : qHat z ≠ 0 := Complex.slitPlane_ne_zero hqz_slit
  have hz_re : 0 < z.re := hz.2
  have h1pz_re : 0 < (1 + z).re := by simp; linarith
  have h1mz_re : 0 < (1 - z).re := re_one_sub_pos_cl hz_cl hz_mem.2.2
  have hz_ne : z ≠ 0 := fun h => by rw [h] at hz_re; simp at hz_re
  have h1pz_ne : 1 + z ≠ 0 := fun h => by rw [h] at h1pz_re; simp at h1pz_re
  have h1mz_ne : 1 - z ≠ 0 := fun h => by rw [h] at h1mz_re; simp at h1mz_re
  let p : ℝ := (2 * ((w - 1 : ℕ) : ℝ) + 1) / 4
  have hq_ratio : (qBd (sigmaHD z)) ^ (-(p : ℂ)) / (qBd z) ^ (-(p : ℂ)) =
      (qHat z) ^ (((2 * ((w - 1 : ℕ) : ℝ) + 1) / 2 : ℝ) : ℂ) := by
    rw [hq, hqσ, Complex.cpow_def_of_ne_zero (inv_ne_zero hqz_ne),
      Complex.cpow_def_of_ne_zero hqz_ne, Complex.cpow_def_of_ne_zero hqz_ne,
      Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hqz_slit), ← Complex.exp_sub]
    congr 1
    have hp : ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 2 : ℝ) = 2 * p := by dsimp only [p]; ring
    rw [hp]
    push_cast; ring
  have h1mσ : 1 - sigmaHD z = 2 * z * (1 + z)⁻¹ := by unfold sigmaHD; field_simp; ring
  have h1pσ : 1 + sigmaHD z = 2 / (1 + z) := by unfold sigmaHD; field_simp; ring
  have h2z_re : 0 < ((2 : ℂ) * z).re := by simp; linarith
  have h1pz_inv_re : 0 < (1 + z)⁻¹.re := by
    rw [Complex.inv_re]
    exact div_pos h1pz_re (Complex.normSq_pos.mpr h1pz_ne)
  have h1pz_slit : 1 + z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl h1pz_re)
  have hlog_1mσ : Complex.log (1 - sigmaHD z) = Complex.log 2 + Complex.log z - Complex.log (1 + z) := by
    rw [h1mσ, c_log_mul_re_pos h2z_re h1pz_inv_re,
      c_log_mul_re_pos (by simp : 0 < ((2 : ℂ)).re) hz_re,
      Complex.log_inv _ (Complex.slitPlane_arg_ne_pi h1pz_slit)]
    ring
  have h1mσ_ne : 1 - sigmaHD z ≠ 0 := by
    rw [h1mσ]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz_ne) (inv_ne_zero h1pz_ne)
  have hpow_part : ((1 - sigmaHD z) ^ (1 / 2 : ℂ) / (1 + sigmaHD z) ^ 2) /
      ((1 - z) ^ (1 / 2 : ℂ) / (1 + z) ^ 2) =
      (1 / (2 * (√2 : ℝ) : ℂ)) * z ^ (1 / 2 : ℂ) * (1 + z) ^ (7 / 2 : ℂ) * (1 - z) ^ (-1 / 2 : ℂ) := by
    have hsq2 : (Complex.exp (Complex.log 2 * (1 / 2 : ℂ))) = (√2 : ℝ) := by
      calc Complex.exp (Complex.log 2 * (1 / 2 : ℂ))
          = ((2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
              rw [← Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]; norm_num
        _ = (((2 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
              (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (1 / 2 : ℝ)).symm
        _ = (√2 : ℝ) := by rw [← Real.sqrt_eq_rpow]
    have h4 : (2 : ℂ) ^ 2 = 4 := by norm_num
    have hsqrt2_sq : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    have h1p_pow : (1 + z) ^ 2 = Complex.exp (2 * Complex.log (1 + z)) := by
      rw [show (2 : ℂ) * Complex.log (1 + z) = ((2 : ℕ) : ℂ) * Complex.log (1 + z) by norm_num,
        Complex.exp_nat_mul, Complex.exp_log h1pz_ne]
    rw [h1pσ, Complex.cpow_def_of_ne_zero h1mσ_ne, hlog_1mσ,
      Complex.cpow_def_of_ne_zero h1mz_ne, Complex.cpow_def_of_ne_zero hz_ne,
      Complex.cpow_def_of_ne_zero h1pz_ne, Complex.cpow_def_of_ne_zero h1mz_ne,
      div_pow, h4, h1p_pow]
    have hlhs : Complex.exp ((Complex.log 2 + Complex.log z - Complex.log (1 + z)) * (1 / 2 : ℂ)) /
          (4 / Complex.exp (2 * Complex.log (1 + z))) /
          (Complex.exp (Complex.log (1 - z) * (1 / 2 : ℂ)) / Complex.exp (2 * Complex.log (1 + z))) =
        (Complex.exp (Complex.log 2 * (1 / 2 : ℂ)) / 4) *
          Complex.exp (Complex.log z * (1 / 2 : ℂ) + Complex.log (1 + z) * (7 / 2 : ℂ) +
            Complex.log (1 - z) * (-1 / 2 : ℂ)) := by
      have hex1 : Complex.exp (2 * Complex.log (1 + z)) ≠ 0 := Complex.exp_ne_zero _
      have hex2 : Complex.exp (Complex.log (1 - z) * (1 / 2 : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      field_simp
      rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hlhs, hsq2, Complex.exp_add, Complex.exp_add]
    have hcoeff : ((√2 : ℝ) : ℂ) / 4 = 1 / (2 * ((√2 : ℝ) : ℂ)) := by
      field_simp
      rw [sq, hsqrt2_sq]; norm_num
    rw [hcoeff]
    ring
  unfold GoutWA
  rw [hhbar]
  have hexp_ne : Complex.exp (hbarA (aWA w (fun _ => 1)) (sInv z)) ≠ 0 := Complex.exp_ne_zero _
  calc (Complex.exp (hbarA (aWA w (fun _ => 1)) (sInv z)) * (1 - sigmaHD z) ^ (1 / 2 : ℂ) /
          (1 + sigmaHD z) ^ 2 * qBd (sigmaHD z) ^ (-(p : ℂ))) /
        (Complex.exp (hbarA (aWA w (fun _ => 1)) (sInv z)) * (1 - z) ^ (1 / 2 : ℂ) /
          (1 + z) ^ 2 * qBd z ^ (-(p : ℂ)))
      = (((1 - sigmaHD z) ^ (1 / 2 : ℂ) / (1 + sigmaHD z) ^ 2) /
          ((1 - z) ^ (1 / 2 : ℂ) / (1 + z) ^ 2)) * (qBd (sigmaHD z) ^ (-(p : ℂ)) / qBd z ^ (-(p : ℂ))) := by
          field_simp
    _ = _ := by rw [hpow_part, hq_ratio]

end FormalResearch.ModularBootstrap.Mixtures

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.g1OutWA_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.g1OutWA_eq

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.I1Amp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.I1Amp_mul

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.goutWA_sigma_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.goutWA_sigma_formula
