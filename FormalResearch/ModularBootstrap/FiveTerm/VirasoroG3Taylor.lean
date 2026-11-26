module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Main
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# `g₃ = (1/6)(log Gout)'''(0)` as a complex Taylor coefficient (FIVE-0b, `cts:g3-gamma0`)

`Gout = exp ∘ L` near the tip with `L` holomorphic on a disc around `0`, `L(x) = log Gout(x) ∈ ℝ` on the real segment
(`gout_eq_exp_L`).  The real cubic jet of `log Gout` (`jet_logGout`) then identifies the Taylor coefficients of `L`:
`L(0) = 0`, `L'(0) = g₁`, `L''(0)/2 = g₂`, `L'''(0)/6 = g₃` (`g3Out_taylor`), i.e. `g3Out` is the paper's
`g₃ = (1/6)(log G_outer)'''(0)`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory Asymptotics
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The real part of a holomorphic function on the real axis has the Taylor jet given by its complex derivatives. -/
lemma jet_re_holo {G : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hG : DifferentiableOn ℂ G (ball (0 : ℂ) ρ)) :
    Jet (𝓝 0) (fun x : ℝ => (G (x : ℂ)).re) (G 0).re (deriv G 0).re ((deriv (deriv G) 0).re / 2)
      ((deriv (deriv (deriv G)) 0).re / 6) := by
  have hG1 : DifferentiableOn ℂ (deriv G) (ball (0 : ℂ) ρ) := hG.deriv isOpen_ball
  have hG2 : DifferentiableOn ℂ (deriv (deriv G)) (ball (0 : ℂ) ρ) := hG1.deriv isOpen_ball
  have hmem : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), (x : ℂ) ∈ ball (0 : ℂ) ρ := by
    filter_upwards [eventually_abs_lt (l := 𝓝 (0 : ℝ)) le_rfl hρ] with x hx
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have hd0 : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), HasDerivAt (fun x : ℝ => (G (x : ℂ)).re) (deriv G (x : ℂ)).re x := by
    filter_upwards [hmem] with x hx
    exact ((hG.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt).real_of_complex
  have hd1 : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), HasDerivAt (fun x : ℝ => (deriv G (x : ℂ)).re)
      (deriv (deriv G) (x : ℂ)).re x := by
    filter_upwards [hmem] with x hx
    exact ((hG1.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt).real_of_complex
  have hd2 : HasDerivAt (fun x : ℝ => (deriv (deriv G) (x : ℂ)).re) (deriv (deriv (deriv G)) 0).re 0 := by
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ
    have h1 : HasDerivAt (deriv (deriv G)) (deriv (deriv (deriv G)) 0) (((0 : ℝ)) : ℂ) := by
      simpa using (hG2.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    simpa using h1.real_of_complex
  have hj : (fun x : ℝ => (deriv (deriv G) (x : ℂ)).re -
      ((deriv (deriv G) 0).re + (deriv (deriv (deriv G)) 0).re * x)) =o[𝓝 0] fun x => x := by
    have := hd2.isLittleO
    simp only [sub_zero, smul_eq_mul, Complex.ofReal_zero] at this
    refine this.congr_left (fun x => ?_)
    ring
  have h2 := Jet2.of_deriv hd1 hj
  have h3 := Jet.of_deriv hd0 h2
  simpa using h3.of_eq rfl rfl rfl (by ring)

/-- A holomorphic function which is real on a segment `(0, ρ)` with real cubic jet `c` there has Taylor coefficients `c`. -/
lemma taylor_of_real_segment {G : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hG : DifferentiableOn ℂ G (ball (0 : ℂ) ρ))
    {f : ℝ → ℝ} (hreal : ∀ x : ℝ, 0 < x → x < ρ → G (x : ℂ) = (f x : ℂ)) {c0 c1 c2 c3 : ℝ}
    (hf : Jet (𝓝[>] (0 : ℝ)) f c0 c1 c2 c3) :
    G 0 = c0 ∧ deriv G 0 = c1 ∧ deriv (deriv G) 0 / 2 = c2 ∧ deriv (deriv (deriv G)) 0 / 6 = c3 := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < ρ ∧ 0 < x := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with x hx using ⟨hx.2, hx.1⟩
  -- real parts
  have hre := (jet_re_holo hρ hG).mono (l' := 𝓝[>] (0 : ℝ)) nhdsGT_le_nhds0
  have hre' := hre.congr_ev (g := f) (by
    filter_upwards [hev] with x hx
    simp [hreal x hx.2 hx.1])
  obtain ⟨r0, r1, r2, r3⟩ := Jet.unique hre' hf
  -- imaginary parts, through `-I * G`
  set K : ℂ → ℂ := fun z => -Complex.I * G z with hK
  have hK1 : DifferentiableOn ℂ K (ball (0 : ℂ) ρ) := (differentiableOn_const _).mul hG
  have e1 : deriv K = fun z => -Complex.I * deriv G z := deriv_const_mul_field' _
  have e2 : deriv (deriv K) = fun z => -Complex.I * deriv (deriv G) z := by
    rw [e1]; exact deriv_const_mul_field' _
  have e3 : deriv (deriv (deriv K)) = fun z => -Complex.I * deriv (deriv (deriv G)) z := by
    rw [e2]; exact deriv_const_mul_field' _
  have him := (jet_re_holo hρ hK1).mono (l' := 𝓝[>] (0 : ℝ)) nhdsGT_le_nhds0
  have him' := him.congr_ev (g := fun _ => 0) (by
    filter_upwards [hev] with x hx
    simp [hK, hreal x hx.2 hx.1])
  obtain ⟨i0, i1, i2, i3⟩ := Jet.unique him' (Jet.const (l := 𝓝[>] (0 : ℝ)) 0)
  rw [e1] at i1
  rw [e2] at i2
  rw [e3] at i3
  simp only [hK, neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, neg_neg] at i0 i1 i2 i3
  refine ⟨Complex.ext (by simpa using r0) (by simpa using i0), Complex.ext (by simpa using r1) (by simpa using i1),
    Complex.ext ?_ ?_, Complex.ext ?_ ?_⟩
  · simpa using r2
  · simp; linarith
  · simpa using r3
  · simp; linarith


/-- **`g₃` is the cubic Taylor coefficient of the holomorphic logarithm of `Gout`**: near the tip there are `ρ > 0` and
`L` holomorphic on `|z| < ρ` with `Gout = exp ∘ L` on `closure halfDisc ∩ {|z| < ρ}`, `L(0) = 0`, `L'(0) = g₁`,
`L''(0)/2 = g₂` and `L'''(0)/6 = g₃`, where `g₁ g₂ g₃` are `g1Out g2Out g3Out`.  So `g3Out = (1/6)(log Gout)'''(0)`. -/
theorem g3Out_taylor : ∃ ρ : ℝ, 0 < ρ ∧ ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball (0 : ℂ) ρ) ∧
    (∀ z ∈ closure halfDisc, ‖z‖ < ρ → Gout z = Complex.exp (L z)) ∧ L 0 = 0 ∧ deriv L 0 = g1Out ∧
    deriv (deriv L) 0 / 2 = g2Out ∧ deriv (deriv (deriv L)) 0 / 6 = g3Out := by
  obtain ⟨δ, hδ, H, hH0, heq0, -⟩ := exists_edge_dataA amp_aAmp 0
  obtain ⟨ρ, hρ, hρ4, hsI, hT⟩ := exists_local_radius hδ
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  have hL := gout_eq_exp_Lloc hH0 heq0 hρ4 hsI hT
  have hH0' : DifferentiableOn ℂ H (ball (0 : ℂ) δ) := by rw [hc] at hH0; exact hH0
  have hdiff : DifferentiableOn ℂ (Lloc H) (ball (0 : ℂ) ρ) := by
    intro z hz
    have hzn : ‖z‖ < ρ := by simpa using hz
    have hz4 : ‖z‖ < 1 / 4 := by linarith
    have hz1 : ‖z‖ < 1 := by linarith
    have h1 : DifferentiableAt ℂ (fun z => H (sInv z)) z := by
      have hs : DifferentiableAt ℂ sInv z := differentiableAt_sInv_ball hz1
      exact DifferentiableAt.comp (g := H) z
        (hH0'.differentiableAt (isOpen_ball.mem_nhds (hsI z hzn))) hs
    have hre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (1 + w).re := by
      intro w hw
      have := Complex.abs_re_le_norm w
      simp only [Complex.add_re, Complex.one_re]
      linarith [(abs_lt.mp (lt_of_le_of_lt this hw)).1]
    have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.log (1 - z)) z := by
      have hs : 1 - z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        have := hre (-z) (by simpa using hz1)
        simpa [sub_eq_add_neg] using this
      exact (DifferentiableAt.clog (by fun_prop) hs)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => Complex.log (1 + z)) z := by
      have hs : 1 + z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left; exact hre z hz1
      exact (DifferentiableAt.clog (by fun_prop) hs)
    have h4 : DifferentiableAt ℂ (fun z : ℂ => Complex.log (tipExt z)) z := by
      have hts : tipExt z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left; exact hT z hzn
      exact DifferentiableAt.clog (differentiableOn_tipExt.differentiableAt
        (isOpen_ball.mem_nhds (by simpa using hz4))) hts
    unfold Lloc
    exact (((h1.add (h2.div_const 2)).sub (h3.const_mul 2)).sub (h4.div_const 4)).differentiableWithinAt
  -- `L` is real on the segment
  have hreal : ∀ x : ℝ, 0 < x → x < ρ → Lloc H (x : ℂ) = ((logGoutR x : ℝ) : ℂ) := by
    intro x hx0 hxρ
    have hx4 : x < 1 / 4 := by linarith
    obtain ⟨he0, he1⟩ := epsR_mem hx0 hx4
    have hxn : ‖(x : ℂ)‖ < ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxρ
    have hxc : (x : ℂ) ∈ closure halfDisc :=
      subset_closure ⟨by simpa [abs_of_pos hx0] using (by linarith : x < 1), by simpa using hx0⟩
    have hI : (x : ℂ) ≠ Complex.I := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [Complex.I_re]
    have hI' : (x : ℂ) ≠ -Complex.I := by
      intro h; have := congrArg Complex.im h; simp at this
    have hs : sInv (x : ℂ) ∈ closedStrip := sInv_mem_closedStrip hxc hI hI'
    have hb : hbarA aAmp (sInv (x : ℂ)) = H (sInv (x : ℂ)) := by
      refine hbarA_eq_local hH0 heq0 ?_ hs
      rw [hc]; exact hsI _ hxn
    have e1 : H (sInv (x : ℂ)) = (((hbarA aAmp (epsR x : ℂ)).re : ℝ) : ℂ) := by
      rw [← hb, sInv_real, ← hbarA_real_im amp_aAmp he0 he1]
    have e2 : Complex.log (1 - (x : ℂ)) = ((Real.log (1 - x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by linarith)]; push_cast; rfl
    have e3 : Complex.log (1 + (x : ℂ)) = ((Real.log (1 + x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by linarith)]; push_cast; rfl
    have e4 : Complex.log (tipExt (x : ℂ)) = ((Real.log (tipR x) : ℝ) : ℂ) := by
      rw [tipExt_real hx0 hx4, Complex.ofReal_log (tipR_pos hx0 hx4).le]
    unfold Lloc logGoutR
    rw [e1, e2, e3, e4, log_gout_real hx0 hx4]
    push_cast
    ring
  obtain ⟨t0, t1, t2, t3⟩ := taylor_of_real_segment hρ hdiff hreal jet_logGout
  exact ⟨ρ, hρ, Lloc H, hdiff, hL, t0, t1, t2, t3⟩

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.g3Out_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.g3Out_taylor
