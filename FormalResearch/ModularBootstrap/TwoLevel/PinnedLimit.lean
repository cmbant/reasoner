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

/-- `‖Ψ‖₁ = 1` from `∫ Re Ψ = 0`, `‖Ψ‖₁ ≤ 1` and half-mass `1/2 ≤ ∫ Ψ₋`. -/
lemma norm_integral_eq_one {Ψ : ℝ → ℂ}
    (hΨ_int : Integrable Ψ) (hΨ_real : ∀ s : ℝ, (Ψ s).im = 0)
    (hΨ_zero : (∫ s : ℝ, (Ψ s).re) = 0) (hle : ∫ s : ℝ, ‖Ψ s‖ ≤ 1)
    (hneg : (1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ s).re)) :
    ∫ s : ℝ, ‖Ψ s‖ = 1 := by
  have hre_int : Integrable (fun s : ℝ => (Ψ s).re) := hΨ_int.re
  let Ψp : ℝ → ℝ := fun s => max 0 ((Ψ s).re)
  let Ψm : ℝ → ℝ := fun s => max 0 (-(Ψ s).re)
  have hp_int : Integrable Ψp := by
    refine Integrable.mono' hΨ_int.norm
      (((continuous_const.max continuous_id).comp_aestronglyMeasurable hre_int.aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_of_nonneg (le_max_left _ _)]
    exact max_le (norm_nonneg _) (Complex.re_le_norm _)
  have hm_int : Integrable Ψm := by
    refine Integrable.mono' hΨ_int.norm
      (((continuous_const.max continuous_id).comp_aestronglyMeasurable hre_int.neg.aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_of_nonneg (le_max_left _ _)]
    exact max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm (Ψ s)))
  have hsplit_re : (fun s : ℝ => (Ψ s).re) = fun s => Ψp s - Ψm s := by
    ext s; dsimp [Ψp, Ψm]
    rcases le_total 0 (Ψ s).re with h | h
    · simp [h]
    · simp [h]
  have hsplit_norm : (fun s : ℝ => ‖Ψ s‖) = fun s => Ψp s + Ψm s := by
    ext s; dsimp [Ψp, Ψm]
    have hΨc : Ψ s = ((Ψ s).re : ℂ) := Complex.ext (by simp) (by simp [hΨ_real s])
    have hnorm : ‖Ψ s‖ = |(Ψ s).re| := by
      conv_lhs => rw [hΨc]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    rcases le_total 0 (Ψ s).re with h | h
    · rw [abs_of_nonneg h, max_eq_right h, max_eq_left (by linarith), add_zero]
    · rw [abs_of_nonpos h, max_eq_left h, max_eq_right (by linarith), zero_add]
  have hp_eq_hm : ∫ s : ℝ, Ψp s = ∫ s : ℝ, Ψm s := by
    have h0 : ∫ s : ℝ, (Ψp s - Ψm s) = 0 := by rw [← hsplit_re]; exact hΨ_zero
    rw [integral_sub hp_int hm_int] at h0; linarith
  have hnorm_two : ∫ s : ℝ, ‖Ψ s‖ = 2 * ∫ s : ℝ, Ψm s := by
    rw [hsplit_norm, integral_add hp_int hm_int, hp_eq_hm]; ring
  linarith

/-- `excess → A` forces `s₁ → A / ((2/3) ξ_*)` (the general form of `att_tendsto_s1`). -/
theorem tendsto_s₁_of_tendsto_excess {ι : Type*} {p : Filter ι}
    (F : BlowupFamilyPackage ι p) {A : ℝ}
    (hA : Tendsto (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ)) p (nhds A)) :
    Tendsto F.s₁ p (nhds (A / ((2 / 3 : ℝ) * xiStar))) := by
  obtain ⟨C₀, hC₀⟩ := F.theorem_A_lower
  let B₀ : ℝ := max C₀ ((A + 1) / ((2 / 3 : ℝ) * xiStar))
  have hs₁_bdd : ∀ᶠ n in p, |F.s₁ n| ≤ B₀ := by
    have hq_ub := hA.eventually (eventually_le_nhds (by linarith : A < A + 1))
    filter_upwards [hC₀, hq_ub, F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
      F.scaled_excess_eq] with n hnC₀ hnq hc'1 hex
    have hnn : 0 ≤ (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2 := by
      have : 0 ≤ (F.c' n) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _; positivity
    have hub : F.s₁ n ≤ (A + 1) / ((2 / 3 : ℝ) * xiStar) := by
      rw [le_div_iff₀' two_thirds_xiStar_pos]; linarith
    exact abs_le.mpr ⟨by linarith [le_max_left C₀ ((A + 1) / ((2 / 3 : ℝ) * xiStar))],
      hub.trans (le_max_right _ _)⟩
  have hc'neg : Tendsto (fun n => (F.c' n) ^ (-(2 / 3 : ℝ))) p (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp F.hc'_tendsto
  have hquad : Tendsto (fun n => (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2) p (nhds 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (hc'neg.const_mul ((1 / 3 : ℝ) * B₀ ^ 2)))
    filter_upwards [hs₁_bdd, F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hc'1
    have hpow_nn : 0 ≤ (F.c' n) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hsq : (F.s₁ n) ^ 2 ≤ B₀ ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg (le_trans (abs_nonneg _) hn)])
    rw [Real.norm_of_nonneg (by positivity)]; nlinarith
  have hlin : Tendsto (fun n => (2 / 3 : ℝ) * xiStar * F.s₁ n) p (nhds A) := by
    have hdiff : Tendsto (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) -
        (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2) p (nhds A) := by
      simpa using hA.sub hquad
    refine hdiff.congr' (F.scaled_excess_eq.mono fun n hex => by linarith)
  have hdiv := hlin.const_mul (((2 / 3 : ℝ) * xiStar)⁻¹)
  rw [inv_mul_eq_div] at hdiv
  exact hdiv.congr fun n => by field_simp [xiStar_pos.ne']

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
  exact norm_integral_eq_one (Ψ := fun s : ℝ => Ψ (s : ℂ)) hΨi hΨreal hre0 hΨnorm hΨneg

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
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  simp only [not_le] at hnot
  have hev : ∀ᶠ n in p, (1 ≤ F.c' n ∧
      (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) =
        (2 / 3 : ℝ) * xiStar * F.s₁ n + (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2) ∧
      0 ≤ (F.Φ n (σ n : ℂ)).re :=
    ((F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))).and F.scaled_excess_eq).and hpin
  obtain ⟨ns, hns, hprops⟩ := exists_seq_forall_of_frequently (hnot.and_eventually hev)
  have hB : ∀ k : ℕ, F.s₁ (ns k) ≤
      (cStar * |clarkNode (clarkAngle u₁) 2| - ε) / ((2 / 3 : ℝ) * xiStar) := fun k => by
    obtain ⟨hlt, ⟨hc'1, hex⟩, -⟩ := hprops k
    have hnn : 0 ≤ (1 / 3 : ℝ) * (F.c' (ns k)) ^ (-(2 / 3 : ℝ)) * (F.s₁ (ns k)) ^ 2 := by
      have : 0 ≤ (F.c' (ns k)) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      positivity
    rw [hex] at hlt; rw [le_div_iff₀' two_thirds_xiStar_pos]; linarith
  obtain ⟨ms, s₁Star, Ψ, γLim, hms, hs₁lim, -, -, -, -, hle, -⟩ :=
    pinned_limit F hu₁ hσ ns hns (fun k => (hprops k).2.2) ⟨_, hB⟩
  have hlim_le := le_of_tendsto hs₁lim (Eventually.of_forall fun k => hB (ms k))
  have hz := clarkNode_two_neg hu₁
  have h1 : -clarkNode (clarkAngle u₁) 2 / betaTip ≤ s₁Star := by
    rw [div_le_iff₀ betaTip_pos]; linarith
  have h2 := mul_le_mul_of_nonneg_left (h1.trans hlim_le) two_thirds_xiStar_pos.le
  rw [mul_div_cancel₀ _ two_thirds_xiStar_pos.ne', ← cStar_mul_abs_of_neg hz] at h2
  linarith

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

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_s₁_of_tendsto_excess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_s₁_of_tendsto_excess

end FormalResearch.ModularBootstrap.TwoLevel
