module

public import FormalResearch.ModularBootstrap.Stability.AiryStabilityBase
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# Stability at the terminal node: abstract theorem (`se:terminal-stability`)

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem
`se:terminal-stability`; the Airy and Clark instances are `AiryStability` (`rem:thmBstab`) and
`ClarkStability` (`se:3.1`).

`TerminalData κ` packages what the proof uses: an extremal profile `G` with the equality principle
at its terminal node `zT` and prescribed nodes `nodes : κ → ℝ` (`EqualityPrinciple`, i.e. Hermite–Biehler
uniqueness), `G'(zT) = -γ` with `γ > 0`, and the quadrature inequality
`∫ f ≥ w f(zT)` for `f ∈ 𝒢` that is `≥ 0` on `(-∞, zT]` and at the nodes (Theorem Q; `w` is the weight
at `zT`).

`termI T δ = inf { ∫ f/‖f‖₁ : f ∈ 𝒢 \ 0, f(nodes) ≥ 0, f ≥ 0 on (-∞, zT + δ] }`.

* `term_lower`: for `θ < w γ/‖G‖₁`, `θ δ ≤ ∫ f/‖f‖₁` for all admissible `f` and all small `δ`.
* `terminal_stability`: given a trial family `G + δ W` (`W ∈ 𝒢`, `∫ W = w γ`, admissible for small
  `δ`) and nonemptiness of the admissible sets, `termI T δ > 0` for all `δ > 0` and
  `termI T δ/δ → w γ/‖G‖₁` as `δ ↓ 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.SignUncertainty

namespace AiryG

variable {f g : ℂ → ℂ}

lemma add (hf : AiryG f) (hg : AiryG g) : AiryG (fun u => f u + g u) where
  diff := hf.diff.add hg.diff
  integrable := hf.integrable.add hg.integrable
  growth := by
    obtain ⟨C₁, ν₁, hC₁, hb₁⟩ := hf.growth
    obtain ⟨C₂, ν₂, hC₂, hb₂⟩ := hg.growth
    refine ⟨C₁ + C₂, max ν₁ ν₂, add_nonneg hC₁ hC₂, fun u => ?_⟩
    have h1 : (1 + ‖u‖) ^ ν₁ ≤ (1 + ‖u‖) ^ max ν₁ ν₂ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg u]) (le_max_left _ _)
    have h2 : (1 + ‖u‖) ^ ν₂ ≤ (1 + ‖u‖) ^ max ν₁ ν₂ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg u]) (le_max_right _ _)
    have he := airyEnv_pos u
    calc ‖f u + g u‖ ≤ ‖f u‖ + ‖g u‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖u‖) ^ ν₁ * airyEnv u + C₂ * (1 + ‖u‖) ^ ν₂ * airyEnv u := add_le_add (hb₁ u) (hb₂ u)
      _ ≤ C₁ * (1 + ‖u‖) ^ max ν₁ ν₂ * airyEnv u + C₂ * (1 + ‖u‖) ^ max ν₁ ν₂ * airyEnv u := by
          gcongr
      _ = _ := by ring
  real := fun x => by simp [hf.real x, hg.real x]

end AiryG

/-- Data of the terminal-node stability theorem. -/
structure TerminalData (κ : Type) where
  G : ℂ → ℂ
  zT : ℝ
  nodes : κ → ℝ
  w : ℝ
  γ : ℝ
  hG : ExtremalProfile G
  hGgrowth : ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖G u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u
  hP : EqualityPrinciple G zT nodes
  hw : 0 < w
  hγ : 0 < γ
  hderiv : (deriv G (zT : ℂ)).re = -γ
  quad : ∀ f : ℂ → ℂ, AiryG f → (∀ x : ℝ, x ≤ zT → 0 ≤ (f (x : ℂ)).re) →
    (∀ i, 0 ≤ (f (nodes i : ℂ)).re) →
    0 ≤ ∫ x : ℝ, (f (x : ℂ)).re ∧ w * (f (zT : ℂ)).re ≤ ∫ x : ℝ, (f (x : ℂ)).re

variable {κ : Type}

/-- The admissible ratios at threshold `zT + δ`. -/
def termSet (T : TerminalData κ) (δ : ℝ) : Set ℝ :=
  {r | ∃ f : ℂ → ℂ, AiryG f ∧ (∃ x : ℝ, f (x : ℂ) ≠ 0) ∧ (∀ i, 0 ≤ (f (T.nodes i : ℂ)).re) ∧
    (∀ x : ℝ, x ≤ T.zT + δ → 0 ≤ (f (x : ℂ)).re) ∧
    r = (∫ x : ℝ, (f (x : ℂ)).re) / ∫ x : ℝ, ‖f (x : ℂ)‖}

/-- `I_N(δ)`. -/
noncomputable def termI (T : TerminalData κ) (δ : ℝ) : ℝ := sInf (termSet T δ)

/-- The value of `(G/‖G‖₁)'` at `zT`. -/
lemma TerminalData.profile_deriv_re (T : TerminalData κ) :
    (deriv (normProfile T.G) (T.zT : ℂ)).re = -T.γ / profileMass T.G := by
  have hd : HasDerivAt (normProfile T.G) ((((profileMass T.G)⁻¹ : ℝ) : ℂ) *
      deriv T.G (T.zT : ℂ)) (T.zT : ℂ) :=
    (T.hG.diff (T.zT : ℂ)).hasDerivAt.const_mul _
  rw [hd.deriv, Complex.re_ofReal_mul, T.hderiv]
  ring

/-- **Lower bound** (the compactness half of `se:terminal-stability`). -/
theorem term_lower (T : TerminalData κ) {θ : ℝ} (hθ : θ < T.w * T.γ / profileMass T.G) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ f : ℂ → ℂ, AiryG f →
      (∃ x : ℝ, f (x : ℂ) ≠ 0) → (∀ i, 0 ≤ (f (T.nodes i : ℂ)).re) →
      (∀ x : ℝ, x ≤ T.zT + δ → 0 ≤ (f (x : ℂ)).re) →
      θ * δ ≤ (∫ x : ℝ, (f (x : ℂ)).re) / ∫ x : ℝ, ‖f (x : ℂ)‖ := by
  set M := profileMass T.G with hM
  have hMpos : 0 < M := T.hG.mass_pos
  have hwγ : 0 < T.w * T.γ / M := by have := T.hw; have := T.hγ; positivity
  by_cases hθ0 : θ ≤ 0
  · refine ⟨1, one_pos, fun δ hδ _ f hf hne hnodes hnn => ?_⟩
    have h1 := (T.quad f hf (fun x hx => hnn x (by linarith)) hnodes).1
    have h2 : 0 ≤ ∫ x : ℝ, ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
    have : θ * δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hθ0 hδ.le
    exact this.trans (div_nonneg h1 h2)
  push Not at hθ0
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 / ((n : ℝ) + 1) ∧ ∃ f : ℂ → ℂ, AiryG f ∧
      (∃ x : ℝ, f (x : ℂ) ≠ 0) ∧ (∀ i, 0 ≤ (f (T.nodes i : ℂ)).re) ∧
      (∀ x : ℝ, x ≤ T.zT + δ → 0 ≤ (f (x : ℂ)).re) ∧
      (∫ x : ℝ, (f (x : ℂ)).re) / (∫ x : ℝ, ‖f (x : ℂ)‖) < θ * δ := by
    intro n
    obtain ⟨δ, h1, h2, f, hf, hne, hnode, hnn, hlt⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨δ, h1, h2, f, hf, hne, hnode, hnn, hlt⟩
  choose δ hδ0 hδlt f hf hne hnode hnn hlt using hseq
  set N : ℕ → ℝ := fun n => ∫ x : ℝ, ‖f n (x : ℂ)‖ with hN
  have hNpos : ∀ n, 0 < N n := fun n => by
    obtain ⟨x, hx⟩ := hne n
    exact integral_norm_pos_of_ne_zero (hf n).diff (hf n).integrable hx
  set g : ℕ → ℂ → ℂ := fun n u => (((N n)⁻¹ : ℝ) : ℂ) * f n u with hg
  have hgG : ∀ n, AiryG (g n) := fun n => (hf n).smul _
  have hgn : ∀ n, ∫ x : ℝ, ‖g n (x : ℂ)‖ = 1 := by
    intro n
    simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hNpos n))]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (hNpos n).ne'
  have hgnn : ∀ n x, x ≤ T.zT + δ n → 0 ≤ (g n (x : ℂ)).re := by
    intro n x hx
    simp only [hg, Complex.re_ofReal_mul]
    exact mul_nonneg (inv_nonneg.mpr (hNpos n).le) (hnn n x hx)
  have hgnode : ∀ n i, 0 ≤ (g n (T.nodes i : ℂ)).re := by
    intro n i
    simp only [hg, Complex.re_ofReal_mul]
    exact mul_nonneg (inv_nonneg.mpr (hNpos n).le) (hnode n i)
  have hgint : ∀ n, ∫ x : ℝ, (g n (x : ℂ)).re = (N n)⁻¹ * ∫ x : ℝ, (f n (x : ℂ)).re := by
    intro n
    simp only [hg, Complex.re_ofReal_mul]
    exact integral_const_mul _ _
  have hquad := fun n => T.quad (g n) (hgG n) (fun x hx => hgnn n x (by linarith [hδ0 n])) (hgnode n)
  have hε0 : ∀ n, 0 ≤ ∫ x : ℝ, (g n (x : ℂ)).re := fun n => (hquad n).1
  have hεlt : ∀ n, ∫ x : ℝ, (g n (x : ℂ)).re < θ * δ n := fun n => by
    rw [hgint n, ← div_eq_inv_mul]; exact hlt n
  have hδtend : Tendsto δ atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hδ0 n).le) (fun n => (hδlt n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set R : ℕ → ℝ := fun n => (n : ℝ) + 1 + |T.zT| with hR
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have := abs_nonneg T.zT; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); simp only [hR]; linarith
  have hRtend : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have := abs_nonneg T.zT; simp only [hR]; linarith
  have hε_tend : Tendsto (fun n => ∫ x : ℝ, (g n (x : ℂ)).re) atTop (𝓝 0) := by
    refine squeeze_zero hε0 (fun n => (hεlt n).le) ?_
    simpa using hδtend.const_mul θ
  have hτ_tend : Tendsto (fun n => tailBound (4 * π)⁻¹ (R n)) atTop (𝓝 0) :=
    (tailBound_tendsto_real _).comp hRtend
  have hS : DensitySeq (4 * π)⁻¹ R (fun _ => 0)
      (fun n => (∫ x : ℝ, (g n (x : ℂ)).re) + tailBound (4 * π)⁻¹ (R n)) g
      (fun n => T.zT + δ n) :=
    { hC0 := by positivity
      hR := hRtend
      hς0 := Eventually.of_forall fun _ => le_rfl
      hς := tendsto_const_nhds
      hδ := by simpa using hε_tend.add hτ_tend
      hspec := fun n => (hgG n).densityHyp (hgn n) (hR1 n)
        (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
            have := hδ0 n
            have hle := neg_abs_le T.zT
            simp only [hR]; linarith) (hgnn n) (hε0 n) }
  have hbd : ∃ x₀, ∀ n, x₀ ≤ T.zT + δ n := ⟨T.zT, fun n => by linarith [hδ0 n]⟩
  have huT : ∀ x < T.zT, ∀ᶠ n in atTop, x ≤ T.zT + δ n := fun x hx =>
    Eventually.of_forall fun n => by linarith [hδ0 n]
  have hnodes : ∀ i, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 (T.nodes i)) ∧
      ∀ n, 0 ≤ (g n (ũ n : ℂ)).re := fun i => ⟨fun _ => T.nodes i, tendsto_const_nhds,
    fun n => hgnode n i⟩
  -- derivative convergence on a compact interval around `zT`
  set m : ℕ := ⌈|T.zT|⌉₊ + 2 with hm
  have hmball : ∀ x ∈ Icc T.zT (T.zT + 1), ((x : ℝ) : ℂ) ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
    intro x hx
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |T.zT| ≤ (⌈|T.zT|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : |x| ≤ |T.zT| + 1 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, neg_abs_le T.zT, le_abs_self T.zT]
    simp only [hm, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hderiv := norm_limit_deriv hS hbd T.hG T.hP huT hnodes m
  have hK : IsCompact ((fun x : ℝ => (x : ℂ)) '' Icc T.zT (T.zT + 1)) :=
    isCompact_Icc.image continuous_ofReal
  have hKsub : ((fun x : ℝ => (x : ℂ)) '' Icc T.zT (T.zT + 1)) ⊆ ball (0 : ℂ) ((m : ℝ) + 1) := by
    rintro _ ⟨x, hx, rfl⟩; exact hmball x hx
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hderiv _ hKsub hK
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have hPd : Differentiable ℂ (normProfile T.G) := normProfile_differentiable T.hG
  have hPcont : ContinuousAt (fun x : ℝ => (deriv (normProfile T.G) (x : ℂ)).re) T.zT :=
    (Complex.continuous_re.comp (hPd.deriv.continuous.comp continuous_ofReal)).continuousAt
  have hw := T.hw
  have hγ := T.hγ
  set ε' : ℝ := (T.w * T.γ / M - θ) / (4 * T.w) with hε'
  have hε'pos : 0 < ε' := by
    have : 0 < T.w * T.γ / M - θ := by linarith
    positivity
  obtain ⟨ρ, hρ, hρP⟩ := Metric.continuousAt_iff.mp hPcont ε' hε'pos
  have hev1 := hunif ε' hε'pos
  have hev2 : ∀ᶠ n in atTop, δ n < min ρ 1 := hδtend.eventually (gt_mem_nhds (lt_min hρ one_pos))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hδn := hδ0 n
  have hδρ : δ n < ρ := lt_of_lt_of_le hn2 (min_le_left _ _)
  have hδ1 : δ n < 1 := lt_of_lt_of_le hn2 (min_le_right _ _)
  set φ : ℝ → ℝ := fun t => (g n (t : ℂ)).re with hφ
  have hφd : ∀ x : ℝ, HasDerivAt φ ((deriv (g n) (x : ℂ)).re) x := fun x =>
    hasDerivAt_re_ofReal (hgG n).diff x
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope φ (fun x => (deriv (g n) (x : ℂ)).re)
    (show T.zT < T.zT + δ n by linarith)
    (fun x _ => (hφd x).continuousAt.continuousWithinAt) (fun x _ => hφd x)
  have hξK : ξ ∈ Icc T.zT (T.zT + 1) := ⟨hξ.1.le, by linarith [hξ.2]⟩
  have hξdist : dist (deriv (g n) (ξ : ℂ)) (deriv (normProfile T.G) (ξ : ℂ)) < ε' := by
    have := hn1 (ξ : ℂ) ⟨ξ, hξK, rfl⟩
    rwa [dist_comm] at this
  have hξre : (deriv (g n) (ξ : ℂ)).re ≤ (deriv (normProfile T.G) (T.zT : ℂ)).re + 2 * ε' := by
    have h1 : |(deriv (g n) (ξ : ℂ)).re - (deriv (normProfile T.G) (ξ : ℂ)).re| < ε' := by
      have hre : |(deriv (g n) (ξ : ℂ) - deriv (normProfile T.G) (ξ : ℂ)).re| ≤
          ‖deriv (g n) (ξ : ℂ) - deriv (normProfile T.G) (ξ : ℂ)‖ := Complex.abs_re_le_norm _
      have hlt' : ‖deriv (g n) (ξ : ℂ) - deriv (normProfile T.G) (ξ : ℂ)‖ < ε' := by
        simpa [dist_eq_norm] using hξdist
      simpa [Complex.sub_re] using lt_of_le_of_lt hre hlt'
    have h2 : |(deriv (normProfile T.G) (ξ : ℂ)).re - (deriv (normProfile T.G) (T.zT : ℂ)).re| < ε' := by
      have := hρP (x := ξ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hξ.1, hξ.2])
      simpa [Real.dist_eq] using this
    rw [abs_lt] at h1 h2
    linarith [h1.2, h2.2]
  have hφtop : 0 ≤ φ (T.zT + δ n) := hgnn n _ le_rfl
  have hslope : (φ (T.zT + δ n) - φ T.zT) = δ n * (deriv (g n) (ξ : ℂ)).re := by
    rw [hξeq, show T.zT + δ n - T.zT = δ n by ring]
    field_simp
  have hφa : -(δ n * ((deriv (normProfile T.G) (T.zT : ℂ)).re + 2 * ε')) ≤ φ T.zT := by
    have := mul_le_mul_of_nonneg_left hξre hδn.le
    linarith
  rw [T.profile_deriv_re] at hφa
  have hquad' := (hquad n).2
  have hφa' : δ n * (T.γ / M - 2 * ε') ≤ φ T.zT := by
    refine le_trans (le_of_eq ?_) hφa
    ring
  have hint_lb : T.w * (δ n * (T.γ / M - 2 * ε')) ≤ ∫ x : ℝ, (g n (x : ℂ)).re :=
    le_trans (mul_le_mul_of_nonneg_left hφa' hw.le) hquad'
  have hfin := lt_of_le_of_lt hint_lb (hεlt n)
  have hcancel : T.w * (T.γ / M - 2 * ε') < θ := by
    have h := (mul_lt_mul_iff_of_pos_left hδn).mp
      (by nlinarith [hfin] : δ n * (T.w * (T.γ / M - 2 * ε')) < δ n * θ)
    exact h
  have hcalc : T.w * (T.γ / M - 2 * ε') = T.w * T.γ / M - (T.w * T.γ / M - θ) / 2 := by
    rw [hε']; field_simp; ring
  rw [hcalc] at hcancel
  linarith

lemma termSet_bdd (T : TerminalData κ) {δ : ℝ} (hδ : 0 ≤ δ) : BddBelow (termSet T δ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, hf, -, hnode, hnn, rfl⟩
  exact div_nonneg (T.quad f hf (fun x hx => hnn x (by linarith)) hnode).1
    (integral_nonneg fun x => norm_nonneg _)

lemma le_termI (T : TerminalData κ) {δ θ : ℝ} (hne : (termSet T δ).Nonempty)
    (h : ∀ f : ℂ → ℂ, AiryG f → (∃ x : ℝ, f (x : ℂ) ≠ 0) → (∀ i, 0 ≤ (f (T.nodes i : ℂ)).re) →
      (∀ x : ℝ, x ≤ T.zT + δ → 0 ≤ (f (x : ℂ)).re) →
      θ * δ ≤ (∫ x : ℝ, (f (x : ℂ)).re) / ∫ x : ℝ, ‖f (x : ℂ)‖) : θ * δ ≤ termI T δ := by
  refine le_csInf hne ?_
  rintro r ⟨f, hf, hne', hnode, hnn, rfl⟩
  exact h f hf hne' hnode hnn

lemma termI_mono (T : TerminalData κ) {δ δ' : ℝ} (hδ' : 0 < δ') (hle : δ' ≤ δ)
    (hne : (termSet T δ).Nonempty) : termI T δ' ≤ termI T δ := by
  refine csInf_le_csInf (termSet_bdd T hδ'.le) hne ?_
  rintro r ⟨f, hf, hne', hnode, hnn, rfl⟩
  exact ⟨f, hf, hne', hnode, fun x hx => hnn x (by linarith), rfl⟩

/-- **Terminal-node stability** (`se:terminal-stability`), abstract form.

Assume the admissible sets are nonempty for all `δ > 0`, and a trial family `G + δ W` with
`W ∈ 𝒢`, `∫ W = w γ`, admissible for `0 < δ < δ₁`.  Then `I_N(δ) > 0` for all `δ > 0` and
`I_N(δ)/δ → w γ/‖G‖₁` as `δ ↓ 0`. -/
theorem terminal_stability (T : TerminalData κ)
    (hne : ∀ δ : ℝ, 0 < δ → (termSet T δ).Nonempty)
    (W : ℂ → ℂ) (hW : AiryG W) (hWint : ∫ x : ℝ, (W (x : ℂ)).re = T.w * T.γ)
    {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hnn : ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ x : ℝ, x ≤ T.zT + δ →
      0 ≤ (T.G (x : ℂ) + (δ : ℂ) * W (x : ℂ)).re)
    (hnode : ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ i,
      0 ≤ (T.G (T.nodes i : ℂ) + (δ : ℂ) * W (T.nodes i : ℂ)).re) :
    (∀ δ : ℝ, 0 < δ → 0 < termI T δ) ∧
      Tendsto (fun δ : ℝ => termI T δ / δ) (𝓝[>] 0) (𝓝 (T.w * T.γ / profileMass T.G)) := by
  set M := profileMass T.G with hM
  have hMpos : 0 < M := T.hG.mass_pos
  have hw := T.hw
  have hγ := T.hγ
  have hwγ : 0 < T.w * T.γ / M := by positivity
  have hGG : AiryG T.G :=
    { diff := T.hG.diff, integrable := T.hG.integrable, real := T.hG.real, growth := T.hGgrowth }
  set Tf : ℝ → ℂ → ℂ := fun δ u => T.G u + (δ : ℂ) * W u with hTf
  have hTfG : ∀ δ, AiryG (Tf δ) := fun δ => hGG.add (hW.smul δ)
  have hTfint : ∀ δ, ∫ x : ℝ, (Tf δ (x : ℂ)).re = δ * (T.w * T.γ) := by
    intro δ
    have h1 : ∀ x : ℝ, (Tf δ (x : ℂ)).re = (T.G (x : ℂ)).re + δ * (W (x : ℂ)).re := fun x => by
      simp [hTf, Complex.add_re]
    simp_rw [h1]
    rw [integral_add hGG.integrable_re (hW.integrable_re.const_mul δ), integral_const_mul,
      hWint, T.hG.integral_re, zero_add]
  have hTfne : ∀ δ, 0 < δ → ∃ x : ℝ, Tf δ (x : ℂ) ≠ 0 := by
    intro δ hδ
    by_contra h
    push Not at h
    have : ∫ x : ℝ, (Tf δ (x : ℂ)).re = 0 := by simp [h]
    rw [hTfint] at this
    have : 0 < δ * (T.w * T.γ) := by positivity
    linarith
  have hmem : ∀ δ : ℝ, 0 < δ → δ < δ₁ → (δ * (T.w * T.γ)) / (∫ x : ℝ, ‖Tf δ (x : ℂ)‖) ∈ termSet T δ :=
    fun δ hδ hδ1 => ⟨Tf δ, hTfG δ, hTfne δ hδ, fun i => hnode δ hδ hδ1 i,
      fun x hx => hnn δ hδ hδ1 x hx, by rw [hTfint]⟩
  have hupper : ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      termI T δ ≤ (δ * (T.w * T.γ)) / (∫ x : ℝ, ‖Tf δ (x : ℂ)‖) := fun δ hδ hδ1 =>
    csInf_le (termSet_bdd T hδ.le) (hmem δ hδ hδ1)
  -- mass of the trial family
  set w₁ : ℝ := ∫ x : ℝ, ‖W (x : ℂ)‖ with hw₁
  have hmass_up : ∀ δ : ℝ, 0 ≤ δ → ∫ x : ℝ, ‖Tf δ (x : ℂ)‖ ≤ M + δ * w₁ := by
    intro δ hδ
    have hint : Integrable (fun x : ℝ => ‖T.G (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) :=
      hGG.integrable_norm.add (hW.integrable_norm.const_mul δ)
    calc ∫ x : ℝ, ‖Tf δ (x : ℂ)‖ ≤ ∫ x : ℝ, (‖T.G (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) := by
          refine integral_mono (hTfG δ).integrable_norm hint fun x => ?_
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
      _ = M + δ * w₁ := by
          rw [integral_add hGG.integrable_norm (hW.integrable_norm.const_mul δ), integral_const_mul]; rfl
  have hmass_lo : ∀ δ : ℝ, 0 ≤ δ → M - δ * w₁ ≤ ∫ x : ℝ, ‖Tf δ (x : ℂ)‖ := by
    intro δ hδ
    have hint : Integrable (fun x : ℝ => ‖Tf δ (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) :=
      (hTfG δ).integrable_norm.add (hW.integrable_norm.const_mul δ)
    have h1 : ∫ x : ℝ, ‖T.G (x : ℂ)‖ ≤ ∫ x : ℝ, (‖Tf δ (x : ℂ)‖ + δ * ‖W (x : ℂ)‖) := by
      refine integral_mono hGG.integrable_norm hint fun x => ?_
      have : T.G (x : ℂ) = Tf δ (x : ℂ) - (δ : ℂ) * W (x : ℂ) := by simp [hTf]
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
    rw [integral_add (hTfG δ).integrable_norm (hW.integrable_norm.const_mul δ),
      integral_const_mul] at h1
    have : M = ∫ x : ℝ, ‖T.G (x : ℂ)‖ := rfl
    linarith
  have hlim : ∀ s : ℝ, Tendsto (fun δ : ℝ => M + s * δ * w₁) (𝓝[>] 0) (𝓝 M) := by
    intro s
    have hc : Continuous (fun δ : ℝ => M + s * δ * w₁) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hmass : Tendsto (fun δ : ℝ => ∫ x : ℝ, ‖Tf δ (x : ℂ)‖) (𝓝[>] 0) (𝓝 M) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun δ => M + (-1) * δ * w₁)
      (h := fun δ => M + 1 * δ * w₁) (hlim (-1)) (hlim 1) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have := hmass_lo δ (le_of_lt hδ)
      linarith
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have := hmass_up δ (le_of_lt hδ)
      linarith
  refine ⟨?_, ?_⟩
  · intro δ hδ
    obtain ⟨δ₀, hδ₀, hlow⟩ := term_lower T (θ := T.w * T.γ / M / 2) (by linarith)
    set δ' := min δ (δ₀ / 2) with hδ'
    have hδ'pos : 0 < δ' := lt_min hδ (half_pos hδ₀)
    have hδ'lt : δ' < δ₀ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ₀)
    have h1 : T.w * T.γ / M / 2 * δ' ≤ termI T δ' :=
      le_termI T (hne δ' hδ'pos) fun f hf hne' hnode' hnn' =>
        hlow δ' hδ'pos hδ'lt f hf hne' hnode' hnn'
    have h2 : termI T δ' ≤ termI T δ := termI_mono T hδ'pos (min_le_left _ _) (hne δ hδ)
    have : 0 < T.w * T.γ / M / 2 * δ' := by positivity
    linarith
  · rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨δ₀, hδ₀, hlow⟩ := term_lower T (θ := (a + T.w * T.γ / M) / 2) (by linarith)
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < δ₀ := by
        filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hδ₀] with δ h1 h2
        exact ⟨h1, h2.2⟩
      filter_upwards [hev] with δ ⟨hδ, hδlt⟩
      have h1 : (a + T.w * T.γ / M) / 2 * δ ≤ termI T δ :=
        le_termI T (hne δ hδ) fun f hf hne' hnode' hnn' =>
          hlow δ hδ hδlt f hf hne' hnode' hnn'
      rw [lt_div_iff₀ hδ]
      nlinarith
    · intro b hb
      have hinv : Tendsto (fun δ : ℝ => (T.w * T.γ) / (∫ x : ℝ, ‖Tf δ (x : ℂ)‖)) (𝓝[>] 0)
          (𝓝 (T.w * T.γ / M)) := tendsto_const_nhds.div hmass hMpos.ne'
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < δ₁ := by
        filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hδ₁] with δ h1 h2
        exact ⟨h1, h2.2⟩
      filter_upwards [hinv.eventually (gt_mem_nhds hb), hev] with δ hlt ⟨hδ, hδ1⟩
      calc termI T δ / δ ≤ ((δ * (T.w * T.γ)) / (∫ x : ℝ, ‖Tf δ (x : ℂ)‖)) / δ :=
            div_le_div_of_nonneg_right (hupper δ hδ hδ1) hδ.le
        _ = (T.w * T.γ) / (∫ x : ℝ, ‖Tf δ (x : ℂ)‖) := by field_simp
        _ < b := hlt

/-- info: 'FormalResearch.ModularBootstrap.Stability.terminal_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminal_stability

end FormalResearch.ModularBootstrap.Stability
