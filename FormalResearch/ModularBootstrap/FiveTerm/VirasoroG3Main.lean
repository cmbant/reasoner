module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3RealJets
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3D1
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG1Main

/-!
# `g₃ = 7 - 18/π - (16√2/3) ξ_*` (FIVE-0b, `ctu:jets` / `cts:g3-gamma0`)

`g3Out` is the cubic Taylor coefficient of `log Gout` at `0` along the real segment, `g₃ = (1/6)(log Gout)'''(0)`:
`log Gout(x) = g₁x + g₂x² + g₃x³ + o(x³)` as `x → 0⁺` (`jet_logGout`).  Its value is computed from
`poisson_third`, `d1_exists` (the slope of the quotient amplitude) and the jets of the elementary pieces
(`g3Out_eq_g3Vir`); with `gamma0_eq_gamma0Of` this gives `gamma0 = gamma0Of g1Out g3Out`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory Asymptotics
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The logarithm of `Gout` along the real segment `(0, 1/4)`. -/
noncomputable def logGoutR (x : ℝ) : ℝ := Real.log (Gout (x : ℂ)).re

/-- A jet has the limit `c₀`. -/
lemma Jet.tendsto {l : Filter ℝ} (hl : l ≤ 𝓝 0) {f : ℝ → ℝ} {c0 c1 c2 c3 : ℝ} (hf : Jet l f c0 c1 c2 c3) :
    Tendsto f l (𝓝 c0) := by
  have hg : Jet l (fun x => f x - c0) 0 c1 c2 c3 :=
    (hf.sub (Jet.const (l := l) c0)).of_eq (by ring) (by ring) (by ring) (by ring)
  have := (hg.tendsto_zero hl).add_const c0
  simpa using this

lemma tendsto_gout_real : Tendsto (fun x : ℝ => Gout (x : ℂ)) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨C, r, hr, hjet⟩ := gout_outerDatum_g1Out.jet
  have hb : Tendsto (fun x : ℝ => (|g1Out| + |C| * x) * x) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => (|g1Out| + |C| * x) * x) (𝓝 0) (𝓝 ((|g1Out| + |C| * 0) * 0)) :=
      (((continuous_const.add (continuous_const.mul continuous_id))).mul continuous_id).tendsto 0
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
  have e : ‖Gout (x : ℂ) - 1‖ ≤ ‖Gout (x : ℂ) - 1 - g1Out * (x : ℂ)‖ + ‖g1Out * (x : ℂ)‖ := by
    have := norm_add_le (Gout (x : ℂ) - 1 - g1Out * (x : ℂ)) (g1Out * (x : ℂ))
    simpa using this
  have e2 : ‖g1Out * (x : ℂ)‖ = |g1Out| * x := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
  calc ‖Gout (x : ℂ) - 1‖ ≤ C * x ^ 2 + |g1Out| * x := by linarith
    _ ≤ (|g1Out| + |C| * x) * x := by nlinarith only [le_abs_self C, hx0]

lemma tendsto_logGoutR : Tendsto logGoutR (𝓝[>] 0) (𝓝 0) := by
  have h1 := (Complex.continuous_re.tendsto 1).comp tendsto_gout_real
  have h2 := (Real.continuousAt_log (one_ne_zero)).tendsto.comp h1
  show Tendsto (fun x : ℝ => Real.log (Gout (x : ℂ)).re) _ _
  simpa [Function.comp_def] using h2

/-- The jet of `log Gout` with the Virasoro values of the first and third coefficients. -/
theorem exists_jet_logGout_vir : ∃ c2 : ℝ, Jet (𝓝[>] (0 : ℝ)) logGoutR 0 g1Vir c2 g3Vir := by
  have hpi := Real.pi_pos
  obtain ⟨b, hb, hab, hd1⟩ := d1_exists
  have hJ := jet_re_hbarA amp_aAmp hb hab
  have hS1 : (∫ t : ℝ, (aAmp t - aAmp 0) * (π * kern t)) =
      11 * π / 8 + 3 / 2 - √2 / 4 - 4 * √2 * Real.arsinh 1 := by
    obtain ⟨hint, hval⟩ := aD_integral
    have hibp := slope_ibp amp_aAmp (fun t _ => hasDerivAt_aAmp t) hint
    rw [hibp, hval]; ring
  rw [hd1, hS1] at hJ
  have hcomp := Jet.comp nhdsGT_le_nhds0 hJ jet_epsR tendsto_epsR
  obtain ⟨t0, t2, hT⟩ := jet_log_tipR
  have hsum := (hcomp.add ((jet_log_one_sub.const_mul (1 / 2)).sub (jet_log_one_add.const_mul 2))).sub
    (hT.const_mul (1 / 4))
  have hev : (fun x => (hbarA aAmp (epsR x : ℂ)).re + (1 / 2 * Real.log (1 - x) - 2 * Real.log (1 + x)) -
      1 / 4 * Real.log (tipR x)) =ᶠ[𝓝[>] 0] logGoutR := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with x hx
    unfold logGoutR
    rw [log_gout_real hx.1 hx.2]; ring
  have hJet := hsum.congr_ev hev
  have h0 := tendsto_nhds_unique (hJet.tendsto nhdsGT_le_nhds0) tendsto_logGoutR
  refine ⟨_, hJet.of_eq h0 ?_ rfl ?_⟩
  · unfold g1Vir xiStar
    field_simp
    ring
  · unfold g3Vir xiStar S0
    field_simp
    ring

/-- Existence of the cubic expansion of `log Gout`. -/
lemma exists_jet_logGout : ∃ c : ℝ × ℝ, Jet (𝓝[>] (0 : ℝ)) logGoutR 0 g1Out c.1 c.2 := by
  obtain ⟨c2, h⟩ := exists_jet_logGout_vir
  exact ⟨(c2, g3Vir), by rw [g1Out_eq_g1Vir]; exact h⟩

/-- The second odd-even jet `g₂ = (1/2)(log Gout)''(0)`: the quadratic coefficient of `log Gout` at `0`. -/
noncomputable def g2Out : ℝ := (Classical.choose exists_jet_logGout).1

/-- **The third jet** `g₃ = (1/6)(log Gout)'''(0)`: the cubic Taylor coefficient of `log Gout` at `0`. -/
noncomputable def g3Out : ℝ := (Classical.choose exists_jet_logGout).2

/-- `log Gout(x) = g₁ x + g₂ x² + g₃ x³ + o(x³)` as `x → 0⁺`. -/
theorem jet_logGout : Jet (𝓝[>] (0 : ℝ)) logGoutR 0 g1Out g2Out g3Out :=
  Classical.choose_spec exists_jet_logGout

/-- **`g₃ = 7 - 18/π - (16√2/3) ξ_*`** (`cts:g3-gamma0`): the third odd jet of the Virasoro outer function. -/
theorem g3Out_eq_g3Vir : g3Out = g3Vir := by
  obtain ⟨c2, h⟩ := exists_jet_logGout_vir
  have := Jet.unique jet_logGout (h.of_eq rfl g1Out_eq_g1Vir.symm rfl rfl)
  exact this.2.2.2

/-- **`γ₀ = (3π/32)(g₃ - (7/15)g₁)` at the outer jets** (`cts:g3-gamma0`, `ctu:jets`). -/
theorem gamma0_eq_gamma0Of_out : gamma0 = gamma0Of g1Out g3Out := by
  rw [g1Out_eq_g1Vir, g3Out_eq_g3Vir]; exact gamma0_eq_gamma0Of

/-- `γ₀ = (21π - 78 + 8√2 π ξ_*)/40` in terms of the outer jets. -/
theorem gamma0Of_out_closed : gamma0Of g1Out g3Out = (21 * π - 78 + 8 * √2 * π * xiStar) / 40 :=
  gamma0_eq_gamma0Of_out.symm

/-- `c₀* = α_tip g₁` at the outer jet. -/
theorem c0Star_eq_c0StarOf_out : c0Star = c0StarOf g1Out := by
  rw [g1Out_eq_g1Vir]; exact c0Star_eq_c0StarOf

/-- `d₂* = (2c₀*/A_opt) c₁^Langer - A_opt γ₀` with both constants read off the outer jets. -/
theorem d2Star_eq_d2StarOf_out : d2Star = d2StarOf g1Out g3Out := by
  rw [g1Out_eq_g1Vir, g3Out_eq_g3Vir]; exact d2Star_eq_d2StarOf

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.g3Out_eq_g3Vir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.g3Out_eq_g3Vir

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.jet_logGout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.jet_logGout

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gamma0_eq_gamma0Of_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gamma0_eq_gamma0Of_out

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.d2Star_eq_d2StarOf_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.d2Star_eq_d2StarOf_out
