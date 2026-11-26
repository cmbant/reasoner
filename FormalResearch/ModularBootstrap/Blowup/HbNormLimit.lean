module

public import FormalResearch.ModularBootstrap.Blowup.NormLimitIdentify
public import FormalResearch.SignUncertainty.HermiteBiehlerData

/-!
# `bl:norm` for a general Hermite–Biehler profile (abstract layer, any `m₀`)

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma BL-N (`bl:norm`), general `(P, Q_HB)`.

For any `D : HermiteBiehlerData` (`G_N = D.G`, node set `S`, terminal node `t_m = D.tm`), the
extremal `D.G` is an `ExtremalProfile`, obeys the equality principle of `NormLimitIdentify` with the
prescribed nodes `S \ {t_m}` (this is `hb_uniqueness`, packaged in `D.uniqueness`) and is negative just
to the right of `t_m` (from `D.G_deriv_ne_zero` and `D.G_nonneg_left`).  The abstract limit theorems of
`NormLimitIdentify` therefore apply to sequences of densities `DensitySeq` with prescribed-node data
`ũ_{n,i} → t_i`, `Re Ψ_n(ũ_{n,i}) ≥ 0`, giving

* (a) `limsup uT_n ≤ t_m`;
* (b) if `liminf uT_n ≥ t_m`, `Ψ_n → G_N/‖G_N‖₁` locally uniformly and in `L¹`, `∫ Re Ψ_n → 0`.

The Airy (`m₀ = 1`) and Clark (`m₀ = 2`) cases are in `AiryNormLimit`, `ClarkNormLimit`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.Special FormalResearch.SignUncertainty

/-- The nodes `S \ {t_m}` of a Hermite–Biehler datum. -/
abbrev HbNodes (D : HermiteBiehlerData) : Type := {t : ℝ // t ∈ D.S ∧ t ≠ D.tm}

/-- The Hermite–Biehler extremal is an extremal profile. -/
theorem hbExtremalProfile (D : HermiteBiehlerData) : ExtremalProfile D.G where
  diff := D.G_diff
  integrable := D.G_int
  real := D.G_real
  mass_pos := D.G_l1_pos
  integral_re := by
    have hre : ∫ u : ℝ, (D.G (u : ℂ)).re = (∫ u : ℝ, D.G (u : ℂ)).re := integral_re D.G_int
    rw [hre, D.G_integral_zero, Complex.zero_re]

/-- Equality principle for a Hermite–Biehler datum (`lem:hb-uniqueness`). -/
theorem hbEqualityPrinciple (D : HermiteBiehlerData) :
    EqualityPrinciple (κ := HbNodes D) D.G D.tm (fun t => t.1) := by
  intro Φ hd hi ⟨C, ν, hC, hb⟩ hreal hpos hnode hint hne
  have hint' : 0 ≤ (∫ x : ℝ, (fun z => -Φ z) (x : ℂ)).re := by
    have hre : ∫ x : ℝ, (Φ (x : ℂ)).re = (∫ x : ℝ, Φ (x : ℂ)).re := integral_re hi
    simp only [integral_neg, Complex.neg_re]
    linarith
  obtain ⟨b, hb0, hH, hnz⟩ := D.uniqueness (H := fun z => -Φ z) (C := C) (ν := ν) hd.neg hi.neg hC
    (fun u => by simpa using hb u) (fun x => by simp [hreal x]) hint'
    (fun t ht hne' => by
      have := hnode ⟨t, ht, hne'⟩
      simp only [Complex.neg_re]; linarith)
    (fun x hx => by
      have := hpos x hx
      simp only [Complex.neg_re]; linarith)
  obtain ⟨z, hz⟩ := hne
  have hb_pos := (hnz ⟨z, neg_ne_zero.mpr hz⟩).1
  exact ⟨b, hb_pos, fun u => by have := hH u; linear_combination -this⟩

/-- The Hermite–Biehler extremal is negative just to the right of `t_m`. -/
theorem hbExtremal_neg_right (D : HermiteBiehlerData) : ∀ ε : ℝ, 0 < ε →
    ∃ x : ℝ, D.tm < x ∧ x ≤ D.tm + ε ∧ (D.G (x : ℂ)).re < 0 := by
  intro ε hε
  have hdG : HasDerivAt (fun x : ℝ => D.G (x : ℂ)) (deriv D.G (D.tm : ℂ)) D.tm := by
    simpa only [mul_one] using (D.G_diff (D.tm : ℂ)).hasDerivAt.comp_ofReal
  set f : ℝ → ℝ := fun x => (D.G (x : ℂ)).re with hf
  have hdf : HasDerivAt f (deriv D.G (D.tm : ℂ)).re D.tm :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt D.tm hdG
  have hdim : HasDerivAt (fun x : ℝ => (D.G (x : ℂ)).im) (deriv D.G (D.tm : ℂ)).im D.tm :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt D.tm hdG
  have hdim0 : (deriv D.G (D.tm : ℂ)).im = 0 := by
    have hconst : (fun x : ℝ => (D.G (x : ℂ)).im) = fun _ => (0 : ℝ) := funext D.G_real
    rw [hconst] at hdim
    exact hdim.unique (hasDerivAt_const _ _)
  have hne : (deriv D.G (D.tm : ℂ)).re ≠ 0 := fun h0 =>
    D.G_deriv_ne_zero D.tm D.tm_mem (Complex.ext h0 hdim0)
  have hf0 : f D.tm = 0 := by simp [hf, D.G_eq_zero_on_S D.tm D.tm_mem]
  have hslope := hasDerivAt_iff_tendsto_slope.mp hdf
  have hle : (deriv D.G (D.tm : ℂ)).re ≤ 0 := by
    have hlt : Tendsto (slope f D.tm) (𝓝[<] D.tm) (𝓝 (deriv D.G (D.tm : ℂ)).re) :=
      hslope.mono_left (nhdsWithin_mono _ fun x (hx : x < D.tm) => ne_of_lt hx)
    refine le_of_tendsto hlt ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x < D.tm := hx
    rw [slope_def_field, hf0, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos (D.G_nonneg_left x hx'.le) (by linarith)
  have hneg : (deriv D.G (D.tm : ℂ)).re < 0 := lt_of_le_of_ne hle hne
  have hev : ∀ᶠ x in 𝓝[>] D.tm, f x < 0 := by
    have hlt : Tendsto (slope f D.tm) (𝓝[>] D.tm) (𝓝 (deriv D.G (D.tm : ℂ)).re) :=
      hslope.mono_left (nhdsWithin_mono _ fun x (hx : D.tm < x) => ne_of_gt hx)
    filter_upwards [hlt.eventually (gt_mem_nhds hneg), self_mem_nhdsWithin] with x hx hx'
    have hx'' : D.tm < x := hx'
    rw [slope_def_field, hf0, sub_zero] at hx
    by_contra hcon
    push Not at hcon
    have := div_nonneg hcon (sub_nonneg.mpr hx''.le)
    linarith
  obtain ⟨x, hx1, hx2⟩ := (hev.and (Ioo_mem_nhdsGT (show D.tm < D.tm + ε by linarith))).exists
  exact ⟨x, hx2.1, hx2.2.le, hx1⟩

variable {C₀ : ℝ} {R ς δ : ℕ → ℝ} {Ψ : ℕ → ℂ → ℂ} {uT : ℕ → ℝ}

/-- **`bl:norm`(a), general `m₀`**: `limsup uT_n ≤ t_m`. -/
theorem hb_threshold_le (D : HermiteBiehlerData) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (hnodes : ∀ i : HbNodes D, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, uT n ≤ D.tm + ε :=
  threshold_le_of_negative S hbd (hbExtremalProfile D) (hbEqualityPrinciple D) hnodes
    (hbExtremal_neg_right D) ε hε

/-- **`bl:norm`(b), general `m₀`**: locally uniform convergence to `G_N/‖G_N‖₁`. -/
theorem hb_norm_limit (D : HermiteBiehlerData) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (huT : ∀ x < D.tm, ∀ᶠ n in atTop, x ≤ uT n)
    (hnodes : ∀ i : HbNodes D, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re) :
    LocUnif Ψ id (normProfile D.G) :=
  norm_limit S hbd (hbExtremalProfile D) (hbEqualityPrinciple D) huT hnodes

/-- `L¹(ℝ)` convergence (densities extended by zero); no mass escapes. -/
theorem hb_norm_limit_l1 (D : HermiteBiehlerData) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (huT : ∀ x < D.tm, ∀ᶠ n in atTop, x ≤ uT n)
    (hnodes : ∀ i : HbNodes D, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re) :
    Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x -
      normProfile D.G (x : ℂ)‖) atTop (𝓝 0) :=
  norm_limit_l1 S hbd (hbExtremalProfile D) (hbEqualityPrinciple D) huT hnodes

/-- The truncated total mass tends to `0` (the vacuum slack). -/
theorem hb_norm_limit_integral (D : HermiteBiehlerData) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (huT : ∀ x < D.tm, ∀ᶠ n in atTop, x ≤ uT n)
    (hnodes : ∀ i : HbNodes D, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re) :
    Tendsto (fun n => ∫ x in (-(R n))..(R n), (Ψ n (x : ℂ)).re) atTop (𝓝 0) :=
  norm_limit_integral_re S hbd (hbExtremalProfile D) (hbEqualityPrinciple D) huT hnodes

/-- The thresholds converge to `t_m` once `liminf uT_n ≥ t_m`. -/
theorem hb_threshold_tendsto (D : HermiteBiehlerData) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (huT : ∀ x < D.tm, ∀ᶠ n in atTop, x ≤ uT n)
    (hnodes : ∀ i : HbNodes D, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re) :
    Tendsto uT atTop (𝓝 D.tm) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hb_threshold_le D S hbd hnodes (ε / 2) (half_pos hε),
    huT (D.tm - ε / 2) (by linarith)] with n h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- info: 'FormalResearch.ModularBootstrap.Blowup.hb_norm_limit_l1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hb_norm_limit_l1

/-- info: 'FormalResearch.ModularBootstrap.Blowup.hb_threshold_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hb_threshold_le

end FormalResearch.ModularBootstrap.Blowup
