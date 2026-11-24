module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkOfBlowupLimit

/-!
# Pinned first level: the abstract two-level lower bound (`virasoro_two_level.tex`, Theorem 2.1)

For a `BlowupFamilyPackage` `F` (the packaged output of Proposition T) and a pinned point
`σ n → s_1^* = -u₁/β` (`u₁ > a₁`) with `Φ_n(σ n) ≥ 0` eventually:

* `clarkProfile α c`: the profile `s ↦ c · g_α(-β s)` of the equality case;
* `tendsto_s₁_of_tendsto_excess`: `excess → A` forces `s₁ → A / ((2/3) ξ_*)`
  (the general form of `att_tendsto_s1`, which is the case `A = A_opt`);
* `pinned_limit`: along a subsequence with `s₁` bounded above, a Proposition T limit `Ψ` has
  `-β s₁^* ≤ z₂(α(u₁))`, and equality forces `Ψ = clarkProfile α c`, `γ → 0`, `‖Ψ‖₁ = 1`;
* `twoLevel_eventually`, `twoLevel_liminf`: `liminf (t₁ - ξ̄ c')/c'^{1/3} ≥ c_* |z₂(α(u₁))|`
  (the `EReal` form is the analogue of `theorem_C`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.Analysis

/-- The profile `s ↦ c · g_α(-β s)` of the two-level equality case. -/
noncomputable def clarkProfile (α c : ℝ) (s : ℂ) : ℂ :=
  (c : ℂ) * clarkExtremal α (-(betaTip : ℂ) * s)

/-- `N_α = ∫ ‖g_α(-β s)‖ ds`. -/
noncomputable def clarkProfileNorm (α : ℝ) : ℝ :=
  ∫ s : ℝ, ‖clarkExtremal α (-(betaTip : ℂ) * (s : ℂ))‖

lemma clarkProfile_ofReal (α c s : ℝ) :
    clarkProfile α c (s : ℂ) = (c : ℂ) * clarkExtremal α (((-betaTip * s : ℝ)) : ℂ) := by
  unfold clarkProfile; push_cast; ring_nf

lemma clarkProfile_integrable {α : ℝ} (hα : Real.sin α ≠ 0) (c : ℝ) :
    Integrable (fun s : ℝ => clarkProfile α c (s : ℂ)) := by
  simp_rw [clarkProfile_ofReal]
  exact ((clarkExtremal_integrable hα).comp_mul_left' (neg_ne_zero.mpr betaTip_pos.ne')).const_mul _

lemma clarkProfile_integral_re {α : ℝ} (hα : Real.sin α ≠ 0) (c : ℝ) :
    ∫ s : ℝ, (clarkProfile α c (s : ℂ)).re = 0 := by
  have h0 := (clarkExtremal_attains hα).2.2.2.2.2.2.2.2.2.1
  have : ∀ s : ℝ, (clarkProfile α c (s : ℂ)).re = c * (clarkExtremal α (((-betaTip * s : ℝ)) : ℂ)).re := by
    intro s; rw [clarkProfile_ofReal]; simp [Complex.mul_re]
  simp_rw [this]
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ => (clarkExtremal α (x : ℂ)).re) (-betaTip)]
  simp [h0]

lemma clarkProfile_norm_integral (α : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ s : ℝ, ‖clarkProfile α c (s : ℂ)‖ = c * clarkProfileNorm α := by
  unfold clarkProfileNorm
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [clarkProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

lemma cStar_mul_abs_of_neg {z : ℝ} (hz : z < 0) :
    cStar * |z| = (2 / 3 : ℝ) * xiStar * (-z / betaTip) := by
  unfold cStar
  rw [abs_of_neg hz]
  field_simp [betaTip_pos.ne']

lemma clarkNode_two_neg {u₁ : ℝ} (hu₁ : airyZero 1 < u₁) : clarkNode (clarkAngle u₁) 2 < 0 :=
  ((airyZero_two_lt_clarkNode_two hu₁).2).trans (airyZero_neg 1)

/-- **Pinned limit.** Let `F` be a `BlowupFamilyPackage`, `u₁ > a₁` and `σ n → -u₁/β` with
`Φ_n(σ n) ≥ 0`. Along a subsequence `ns` with `s₁` bounded above and the pin at every term, a
Proposition T limit `Ψ` has `-β s₁^* ≤ z₂(α(u₁))`; equality forces `Ψ = clarkProfile α c`
with `c > 0`, `γ → 0` and `‖Ψ‖₁ = 1`. -/
theorem pinned_limit {ι : Type*} {p : Filter ι} (F : BlowupFamilyPackage ι p)
    {u₁ : ℝ} (hu₁ : airyZero 1 < u₁) {σ : ι → ℝ} (hσ : Tendsto σ p (nhds (-u₁ / betaTip)))
    (ns : ℕ → ι) (hns : Tendsto ns atTop p)
    (hpin : ∀ k, 0 ≤ (F.Φ (ns k) (σ (ns k) : ℂ)).re)
    (hB : ∃ B : ℝ, ∀ k : ℕ, F.s₁ (ns k) ≤ B) :
    ∃ (ms : ℕ → ℕ) (s₁Star : ℝ) (Ψ : ℂ → ℂ) (γLim : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => F.s₁ (ns (ms k))) atTop (nhds s₁Star) ∧
      TendstoLocallyUniformlyOn (fun k => F.Φ (ns (ms k))) Ψ atTop univ ∧
      Tendsto (fun k => F.γ (ns (ms k))) atTop (nhds γLim) ∧
      Differentiable ℂ Ψ ∧ Integrable (fun s : ℝ => Ψ (s : ℂ)) ∧
      -betaTip * s₁Star ≤ clarkNode (clarkAngle u₁) 2 ∧
      (-betaTip * s₁Star = clarkNode (clarkAngle u₁) 2 →
        ∃ c : ℝ, 0 < c ∧ (∀ s : ℂ, Ψ s = clarkProfile (clarkAngle u₁) c s) ∧ γLim = 0 ∧
          ∫ s : ℝ, ‖Ψ (s : ℂ)‖ = 1) := by
  obtain ⟨ms, s₁Star, Ψ, γLim, mEsc, hms, hs₁, hΦ, hγ, hΨd, hΨi, ⟨C, hC, hΨb⟩, hΨne, hΨreal,
    hΨnn, hΨnorm, hγnn, hmEscnn, hΨint, hΨneg⟩ := F.propT_subseq ns hns hB
  have hint0 : (∫ s : ℝ, (Ψ (s : ℂ)).re) ≤ 0 := by rw [hΨint]; linarith
  have hσlim : Tendsto (fun k => ((σ (ns (ms k)) : ℝ) : ℂ)) atTop
      (nhds ((( -u₁ / betaTip : ℝ)) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hσ.comp (hns.comp hms.tendsto_atTop))
  have hΦσ := hΦ.tendsto_comp hΨd.continuous.continuousWithinAt (mem_univ _)
    (by simpa [nhdsWithin_univ] using hσlim)
  have hcast : (((-u₁ / betaTip : ℝ)) : ℂ) = -(u₁ : ℂ) / (betaTip : ℂ) := by push_cast; ring
  have hΦσ' : Tendsto (fun k => F.Φ (ns (ms k)) ((σ (ns (ms k)) : ℝ) : ℂ)) atTop
      (nhds (Ψ ((-u₁ / betaTip : ℝ) : ℂ))) := by rw [hcast]; exact hΦσ
  have hpin_lim : 0 ≤ (Ψ ((-u₁ / betaTip : ℝ) : ℂ)).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hΦσ')
      (Eventually.of_forall fun k => hpin (ms k))
  obtain ⟨hle, heq⟩ := clark_of_blowup_limit hΨd hΨi hC hΨb hΨreal hΨnn hint0 hΨne hu₁ hpin_lim
  refine ⟨ms, s₁Star, Ψ, γLim, hms, hs₁, hΦ, hγ, hΨd, hΨi, hle, fun hEq => ?_⟩
  obtain ⟨c, hc, hΨc⟩ := heq hEq
  have hΨc' : ∀ s : ℂ, Ψ s = clarkProfile (clarkAngle u₁) c s := hΨc
  have hα := sin_clarkAngle_ne_zero hu₁
  have hre0 : (∫ s : ℝ, (Ψ (s : ℂ)).re) = 0 := by
    simp_rw [hΨc']
    exact clarkProfile_integral_re hα c
  have hγ0 : γLim = 0 := by linarith
  refine ⟨c, hc, hΨc', hγ0, ?_⟩
  exact norm_integral_eq_one (Φ := fun s : ℝ => Ψ (s : ℂ)) hΨi hΨreal hre0 hΨnorm hΨneg

/-- **Two-level lower bound, eventual form** (`virasoro_two_level.tex`, Theorem 2.1): if
`σ n → -u₁/β` (`u₁ > a₁`) and `Φ_n(σ n) ≥ 0` eventually, then for every `ε > 0`, eventually
`c_* |z₂(α(u₁))| - ε ≤ (t₁ - ξ̄ c')/c'^{1/3}`. -/
theorem twoLevel_eventually {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : BlowupFamilyPackage ι p) {u₁ : ℝ} (hu₁ : airyZero 1 < u₁)
    {σ : ι → ℝ} (hσ : Tendsto σ p (nhds (-u₁ / betaTip)))
    (hpin : ∀ᶠ n in p, 0 ≤ (F.Φ n (σ n : ℂ)).re) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in p,
      cStar * |clarkNode (clarkAngle u₁) 2| - ε ≤
        (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) := by
  intro ε hε
  have hz := clarkNode_two_neg hu₁
  have h := eventually_excess_ge_of_limit F (fun n => 0 ≤ (F.Φ n (σ n : ℂ)).re) hpin
    (-clarkNode (clarkAngle u₁) 2 / betaTip) (fun ns hns hpinns hB => by
      obtain ⟨ms, s₁Star, Ψ, γLim, hms, hs₁lim, -, -, -, -, hle, -⟩ :=
        pinned_limit F hu₁ hσ ns hns hpinns hB
      exact ⟨ms, s₁Star, hms, hs₁lim, by rw [div_le_iff₀ betaTip_pos]; linarith⟩) ε hε
  rwa [← cStar_mul_abs_of_neg hz] at h

/-- **Two-level lower bound, `EReal` `liminf` form** (`virasoro_two_level.tex`, Theorem 2.1). -/
theorem twoLevel_liminf {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : BlowupFamilyPackage ι p) {u₁ : ℝ} (hu₁ : airyZero 1 < u₁)
    {σ : ι → ℝ} (hσ : Tendsto σ p (nhds (-u₁ / betaTip)))
    (hpin : ∀ᶠ n in p, 0 ≤ (F.Φ n (σ n : ℂ)).re) :
    ((cStar * |clarkNode (clarkAngle u₁) 2| : ℝ) : EReal) ≤
      Filter.liminf (fun n => (((F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) : ℝ) : EReal)) p := by
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hxL, hxA⟩ := EReal.exists_between_coe_real hlt
  have hev := twoLevel_eventually F hu₁ hσ hpin
    (cStar * |clarkNode (clarkAngle u₁) 2| - x) (sub_pos.mpr (EReal.coe_lt_coe_iff.mp hxA))
  have hle : (x : EReal) ≤ _ := le_liminf_of_le (by isBoundedDefault)
    (hev.mono fun _ hn => EReal.coe_le_coe_iff.mpr (by linarith))
  exact absurd (hle.trans_lt hxL) (lt_irrefl _)

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.pinned_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pinned_limit

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoLevel_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoLevel_eventually

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoLevel_liminf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoLevel_liminf

end FormalResearch.ModularBootstrap.TwoLevel
