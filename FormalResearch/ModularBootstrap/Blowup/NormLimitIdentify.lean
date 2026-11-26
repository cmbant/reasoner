module

public import FormalResearch.ModularBootstrap.Blowup.NormLimitCore
public import FormalResearch.Analysis.Scheffe

/-!
# Identification of the limit and `L¹` convergence (generic part of `bl:norm`)

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma BL-N (`bl:norm`), proof.

`NormLimitCore` gives a subsequence limit `Φ` of a density sequence.  If the extremal `G` of the
terminal node `zT` (with the prescribed nodes `nodes`) obeys the *equality principle* (`EqualityPrinciple`:
every entire real function of Airy growth, nonnegative below `zT` and at the nodes, with `∫ Re ≤ 0`,
is a positive multiple of `G`), then every subsequence limit is `c G`, and the mass conditions
`‖Φ‖₁ ≤ 1`, `∫ max 0 (-Re Φ) ≥ 1/2` force `c = 1/‖G‖₁`.  Hence the whole sequence converges, locally
uniformly with derivatives, and (Scheffé) in `L¹(ℝ)` with the sequence extended by zero.

* `norm_limit_subseq`, `norm_limit`: subsequence and whole-sequence locally uniform limit `G/‖G‖₁`.
* `norm_limit_deriv`: locally uniform convergence of the derivatives.
* `norm_limit_l1`: `∫ ‖1_{[-R_n,R_n]} Ψ_n - G/‖G‖₁‖ → 0`, and `∫_{-R_n}^{R_n} Re Ψ_n → 0`.
* `threshold_le_of_negative`: if `G` is negative just right of `zT` and the sequence has the node
  data, then `uT_n ≤ zT + ε` eventually, for every `ε > 0` (the bound (a) of `bl:norm`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.Special

variable {C₀ : ℝ} {R ς δ : ℕ → ℝ} {Ψ : ℕ → ℂ → ℂ} {uT : ℕ → ℝ}

/-- A normalised real extremal profile. -/
structure ExtremalProfile (G : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ G
  integrable : Integrable (fun x : ℝ => G (x : ℂ))
  real : ∀ x : ℝ, (G (x : ℂ)).im = 0
  mass_pos : 0 < ∫ x : ℝ, ‖G (x : ℂ)‖
  integral_re : ∫ x : ℝ, (G (x : ℂ)).re = 0

/-- `L¹` norm of the profile. -/
noncomputable def profileMass (G : ℂ → ℂ) : ℝ := ∫ x : ℝ, ‖G (x : ℂ)‖

/-- The equality principle of the terminal node `zT` with prescribed nodes `nodes`: every entire
function in the class `𝒢` that is nonnegative on `(-∞, zT]` and at the nodes and has `∫ Re ≤ 0` is
a positive multiple of `G`. -/
def EqualityPrinciple {κ : Type} (G : ℂ → ℂ) (zT : ℝ) (nodes : κ → ℝ) : Prop :=
  ∀ Φ : ℂ → ℂ, Differentiable ℂ Φ → Integrable (fun x : ℝ => Φ (x : ℂ)) →
    (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖Φ u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) →
    (∀ x : ℝ, (Φ (x : ℂ)).im = 0) → (∀ x : ℝ, x ≤ zT → 0 ≤ (Φ (x : ℂ)).re) →
    (∀ i, 0 ≤ (Φ (nodes i : ℂ)).re) → ∫ x : ℝ, (Φ (x : ℂ)).re ≤ 0 → (∃ z : ℂ, Φ z ≠ 0) →
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℂ, Φ u = (c : ℂ) * G u

lemma ExtremalProfile.neg_half {G : ℂ → ℂ} (hG : ExtremalProfile G) :
    ∫ x : ℝ, max 0 (-(G (x : ℂ)).re) = profileMass G / 2 := by
  have hre : Integrable (fun x : ℝ => (G (x : ℂ)).re) := hG.integrable.re
  have hpos : Integrable (fun x : ℝ => max 0 ((G (x : ℂ)).re)) :=
    hre.pos_part.congr (Eventually.of_forall fun x => max_comm _ _)
  have hneg : Integrable (fun x : ℝ => max 0 (-(G (x : ℂ)).re)) :=
    hre.neg_part.congr (Eventually.of_forall fun x => max_comm _ _)
  have hnorm : ∀ x : ℝ, ‖G (x : ℂ)‖ = max 0 ((G (x : ℂ)).re) + max 0 (-(G (x : ℂ)).re) := by
    intro x
    have heq : G (x : ℂ) = (((G (x : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (hG.real x)
    conv_lhs => rw [heq]
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases le_total 0 ((G (x : ℂ)).re) with h | h
    · rw [abs_of_nonneg h, max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_left h, max_eq_right (by linarith)]; ring
  have hsub : ∀ x : ℝ, (G (x : ℂ)).re = max 0 ((G (x : ℂ)).re) - max 0 (-(G (x : ℂ)).re) := by
    intro x
    rcases le_total 0 ((G (x : ℂ)).re) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have h1 : profileMass G = (∫ x : ℝ, max 0 ((G (x : ℂ)).re)) + ∫ x : ℝ, max 0 (-(G (x : ℂ)).re) := by
    unfold profileMass
    rw [← integral_add hpos hneg]
    exact integral_congr_ae (Eventually.of_forall hnorm)
  have h2 : (∫ x : ℝ, (G (x : ℂ)).re) =
      (∫ x : ℝ, max 0 ((G (x : ℂ)).re)) - ∫ x : ℝ, max 0 (-(G (x : ℂ)).re) := by
    rw [← integral_sub hpos hneg]
    exact integral_congr_ae (Eventually.of_forall hsub)
  linarith [hG.integral_re]

/-- Subsequences of a density sequence are density sequences. -/
lemma DensitySeq.comp (S : DensitySeq C₀ R ς δ Ψ uT) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    DensitySeq C₀ (R ∘ ψ) (ς ∘ ψ) (δ ∘ ψ) (Ψ ∘ ψ) (uT ∘ ψ) where
  hC0 := S.hC0
  hR := S.hR.comp hψ.tendsto_atTop
  hς0 := hψ.tendsto_atTop.eventually S.hς0
  hς := S.hς.comp hψ.tendsto_atTop
  hδ := S.hδ.comp hψ.tendsto_atTop
  hspec := fun n => S.hspec (ψ n)

/-- From every subsequence extract a further subsequence converging uniformly on `K`. -/
lemma tendstoUniformlyOn_of_subseq {F : ℕ → ℂ → ℂ} {Φ : ℂ → ℂ} {K : Set ℂ}
    (h : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun k => F (ψ (φ k))) Φ atTop K) :
    TendstoUniformlyOn F Φ atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ¬ ∀ x ∈ K, dist (Φ x) (F n x) < ε := by
    rw [Filter.not_eventually] at hcon
    exact hcon
  obtain ⟨ψ, hψ, hψp⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨φ, hφ, hU⟩ := h ψ hψ
  have := (Metric.tendstoUniformlyOn_iff.mp hU ε hε).exists
  obtain ⟨k, hk⟩ := this
  exact hψp (φ k) hk

variable {κ : Type} {G : ℂ → ℂ} {zT : ℝ} {nodes : κ → ℝ}

/-- **Subsequence limit.** Under the equality principle, every density sequence whose thresholds
are asymptotically at least `zT` and which carries the nodal data has a subsequence converging
locally uniformly to `G / ‖G‖₁`. -/
theorem norm_limit_subseq (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (hG : ExtremalProfile G) (hP : EqualityPrinciple G zT nodes)
    (huT : ∀ x < zT, ∀ᶠ n in atTop, x ≤ uT n)
    (hnodes : ∀ i, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 (nodes i)) ∧ ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      LocUnif Ψ φ (fun u => (((profileMass G)⁻¹ : ℝ) : ℂ) * G u) := by
  obtain ⟨x₀, hx₀⟩ := hbd
  obtain ⟨φ, Φ, hφ, hU, hΦd, hgrow⟩ := density_exists_subseq S
  have hreal := limit_real S hφ hU
  have hint := limit_integrable S hφ hU hΦd
  have hre0 := limit_re_le_zero S hφ hU hΦd hx₀
  have hneg := limit_neg_ge S hφ hU hΦd hx₀
  have hnorm1 := limit_norm_le_one S hφ hU hΦd
  have hpos_lt : ∀ x : ℝ, x < zT → 0 ≤ (Φ (x : ℂ)).re := fun x hx =>
    limit_nonneg S hφ hU x ((hφ.tendsto_atTop.eventually (huT x hx)))
  have hpos : ∀ x : ℝ, x ≤ zT → 0 ≤ (Φ (x : ℂ)).re := by
    intro x hx
    have hcl : x ∈ closure (Iio zT) := by rw [closure_Iio]; exact hx
    have hclosed : IsClosed {y : ℝ | 0 ≤ (Φ (y : ℂ)).re} :=
      isClosed_le continuous_const (Complex.continuous_re.comp (limit_continuous hΦd))
    exact hclosed.closure_subset_iff.mpr (fun y hy => hpos_lt y hy) hcl
  have hnode : ∀ i, 0 ≤ (Φ (nodes i : ℂ)).re := by
    intro i
    obtain ⟨ũ, hũ, hũn⟩ := hnodes i
    have hũφ : Tendsto (fun k => ũ (φ k)) atTop (𝓝 (nodes i)) := hũ.comp hφ.tendsto_atTop
    have hw : Tendsto (fun k => ((ũ (φ k) : ℝ) : ℂ)) atTop (𝓝 ((nodes i : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hũφ
    have ht := Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_comp_of_unifLocUnif (F := Ψ) hU hΦd.continuous hw)
    exact ge_of_tendsto ht (Eventually.of_forall fun k => hũn (φ k))
  have hne : ∃ z : ℂ, Φ z ≠ 0 := by
    by_contra hall
    push Not at hall
    have : ∫ x : ℝ, max 0 (-(Φ (x : ℂ)).re) = 0 := by simp [hall]
    linarith
  obtain ⟨c, hc, hΦc⟩ := hP Φ hΦd hint ⟨_, 1 / 2, by unfold limitGrowthConst; have := S.hC0; positivity,
    hgrow⟩ hreal hpos hnode hre0 hne
  have hfun : Φ = fun u => (c : ℂ) * G u := funext hΦc
  have hmass := hG.mass_pos
  have hn1 : ∫ x : ℝ, ‖Φ (x : ℂ)‖ = c * profileMass G := by
    rw [hfun]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [integral_const_mul]; rfl
  have hn2 : ∫ x : ℝ, max 0 (-(Φ (x : ℂ)).re) = c * (profileMass G / 2) := by
    rw [← hG.neg_half, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hfun, Complex.re_ofReal_mul]
    rw [show -(c * (G (x : ℂ)).re) = c * (-(G (x : ℂ)).re) by ring]
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero]
  have hcle : c * profileMass G ≤ 1 := hn1 ▸ hnorm1
  have hcge : 1 ≤ c * profileMass G := by rw [hn2] at hneg; linarith
  have hceq : c = (profileMass G)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (le_antisymm hcle hcge)
  refine ⟨φ, hφ, ?_⟩
  have : Φ = fun u => (((profileMass G)⁻¹ : ℝ) : ℂ) * G u := by rw [hfun, hceq]
  rw [← this]; exact hU

/-- The normalised limit profile `G / ‖G‖₁`. -/
noncomputable def normProfile (G : ℂ → ℂ) (u : ℂ) : ℂ := (((profileMass G)⁻¹ : ℝ) : ℂ) * G u

lemma normProfile_differentiable (hG : ExtremalProfile G) : Differentiable ℂ (normProfile G) :=
  (differentiable_const _).mul hG.diff

lemma normProfile_integral_norm (hG : ExtremalProfile G) :
    ∫ x : ℝ, ‖normProfile G (x : ℂ)‖ = 1 := by
  have hm : 0 < profileMass G := hG.mass_pos
  simp only [normProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr hm), integral_const_mul]
  exact inv_mul_cancel₀ hm.ne'

lemma normProfile_integrable (hG : ExtremalProfile G) :
    Integrable (fun x : ℝ => normProfile G (x : ℂ)) :=
  hG.integrable.const_mul _

lemma normProfile_integral_re (hG : ExtremalProfile G) :
    ∫ x : ℝ, (normProfile G (x : ℂ)).re = 0 := by
  simp only [normProfile, Complex.re_ofReal_mul]
  rw [integral_const_mul, hG.integral_re, mul_zero]

variable (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
  (hG : ExtremalProfile G) (hP : EqualityPrinciple G zT nodes)
  (huT : ∀ x < zT, ∀ᶠ n in atTop, x ≤ uT n)
  (hnodes : ∀ i, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 (nodes i)) ∧ ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re)

include S hbd hG hP huT hnodes in
/-- **Whole-sequence limit** `Ψ_n → G/‖G‖₁`, uniformly on every ball. -/
theorem norm_limit :
    LocUnif Ψ id (normProfile G) := by
  intro m
  refine tendstoUniformlyOn_of_subseq fun ψ hψ => ?_
  obtain ⟨x₀, hx₀⟩ := hbd
  obtain ⟨φ, hφ, hU⟩ := norm_limit_subseq (S.comp hψ) ⟨x₀, fun n => hx₀ (ψ n)⟩ hG hP
    (fun x hx => hψ.tendsto_atTop.eventually (huT x hx))
    (fun i => by
      obtain ⟨ũ, hũ, hũn⟩ := hnodes i
      exact ⟨ũ ∘ ψ, hũ.comp hψ.tendsto_atTop, fun n => hũn (ψ n)⟩)
  exact ⟨φ, hφ, hU m⟩

include S hbd hG hP huT hnodes in
/-- Locally uniform convergence of the derivatives. -/
theorem norm_limit_deriv (m : ℕ) :
    TendstoLocallyUniformlyOn (fun n => deriv (Ψ n)) (deriv (normProfile G)) atTop
      (ball (0 : ℂ) ((m : ℝ) + 1)) := by
  have hU := norm_limit S hbd hG hP huT hnodes m
  have hloc : TendstoLocallyUniformlyOn Ψ (normProfile G) atTop (ball (0 : ℂ) ((m : ℝ) + 1)) :=
    hU.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  refine hloc.deriv ?_ isOpen_ball
  filter_upwards [S.hR (eventually_ge_atTop ((m : ℝ) + 1))] with n hn
  exact ((S.hspec n).analytic.differentiableOn).mono
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hn))

include S hbd hG hP huT hnodes in
/-- `∫_{-R_n}^{R_n} ‖Ψ_n‖ → 1`. -/
theorem norm_limit_norm_integral :
    Tendsto (fun n => ∫ x in (-(R n))..(R n), ‖Ψ n (x : ℂ)‖) atTop (𝓝 1) := by
  have hU := norm_limit S hbd hG hP huT hnodes
  have hΦ := normProfile_differentiable hG
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hT := tendsto_symm_integral (normProfile_integrable hG).norm
    rw [normProfile_integral_norm hG] at hT
    obtain ⟨N, hN⟩ := (hT.eventually (Ioi_mem_nhds ha)).exists
    have hlim := limit_integral_norm (Ψ := Ψ) (φ := id) S strictMono_id hU hΦ N
    filter_upwards [hlim.eventually (Ioi_mem_nhds hN), S.hR (eventually_ge_atTop (N : ℝ))] with
      n h1 h2
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h2 : (N : ℝ) ≤ R n := h2
    refine lt_of_lt_of_le h1 ?_
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) h2
      (Eventually.of_forall fun x => norm_nonneg _) ?_
    exact (S.hspec n).norm_cont.intervalIntegrable_of_Icc (μ := volume) (by linarith)
  · exact Eventually.of_forall fun n => lt_of_le_of_lt (S.hspec n).l1 hb

include S hbd hG hP huT hnodes in
/-- **`L¹` convergence** (Scheffé): the sequence extended by zero converges to `G/‖G‖₁` in
`L¹(ℝ)`; in particular no mass escapes and `∫_{-R_n}^{R_n} Re Ψ_n → 0`. -/
theorem norm_limit_l1 :
    Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x -
      normProfile G (x : ℂ)‖) atTop (𝓝 0) := by
  have hU := norm_limit S hbd hG hP huT hnodes
  have hΦ := normProfile_differentiable hG
  refine FormalResearch.Analysis.tendsto_integral_norm_sub_of_tendsto_ae (μ := volume) (p := atTop)
    ?_ (normProfile_integrable hG) (Eventually.of_forall fun x => ?_) ?_
  · exact Eventually.of_forall fun n =>
      ((S.hspec n).cont_real.integrableOn_Icc).integrable_indicator measurableSet_Icc
  · have hpt : Tendsto (fun n => Ψ n (x : ℂ)) atTop (𝓝 (normProfile G (x : ℂ))) :=
      tendsto_comp_of_unifLocUnif (F := Ψ) (φ := id) hU hΦ.continuous
        (w := fun _ => (x : ℂ)) tendsto_const_nhds
    refine hpt.congr' ?_
    filter_upwards [S.hR (eventually_ge_atTop (|x|))] with n hn
    rw [indicator_of_mem (abs_le.mp hn)]
  · have heq : ∀ n, 0 ≤ R n → ∫ x : ℝ, ‖(Icc (-(R n)) (R n)).indicator
        (fun x : ℝ => Ψ n (x : ℂ)) x‖ = ∫ x in (-(R n))..(R n), ‖Ψ n (x : ℂ)‖ := by
      intro n hn
      simp_rw [norm_indicator_eq_indicator_norm]
      rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by linarith)]
    rw [normProfile_integral_norm hG]
    refine (norm_limit_norm_integral S hbd hG hP huT hnodes).congr' ?_
    filter_upwards [S.hR (eventually_ge_atTop (0 : ℝ))] with n hn
    exact (heq n (by exact hn)).symm

include S hbd hG hP huT hnodes in
/-- The truncated total mass tends to zero. -/
theorem norm_limit_integral_re :
    Tendsto (fun n => ∫ x in (-(R n))..(R n), (Ψ n (x : ℂ)).re) atTop (𝓝 0) := by
  have hl1 := norm_limit_l1 S hbd hG hP huT hnodes
  have hg := normProfile_integrable hG
  have hfi : ∀ n, Integrable ((Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ))) := fun n =>
    ((S.hspec n).cont_real.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hbound : ∀ᶠ n in atTop, ‖∫ x in (-(R n))..(R n), (Ψ n (x : ℂ)).re‖ ≤
      ∫ x : ℝ, ‖(Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x -
        normProfile G (x : ℂ)‖ := by
    filter_upwards [S.hR (eventually_ge_atTop (0 : ℝ))] with n hn
    have hn : 0 ≤ R n := hn
    have h1 : ∫ x in (-(R n))..(R n), (Ψ n (x : ℂ)).re =
        ∫ x : ℝ, (((Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x -
          normProfile G (x : ℂ))).re := by
      have hre0 := normProfile_integral_re hG
      have e1 : ∫ x : ℝ, ((Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x -
          normProfile G (x : ℂ)).re =
          (∫ x : ℝ, ((Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x).re) -
            ∫ x : ℝ, (normProfile G (x : ℂ)).re := by
        simp_rw [Complex.sub_re]
        exact integral_sub (hfi n).re hg.re
      rw [e1, hre0, sub_zero]
      have e2 : ∀ x : ℝ, ((Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x).re =
          (Icc (-(R n)) (R n)).indicator (fun x : ℝ => (Ψ n (x : ℂ)).re) x := by
        intro x
        by_cases hx : x ∈ Icc (-(R n)) (R n) <;> simp [hx]
      simp_rw [e2]
      rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by linarith)]
    rw [h1]
    refine norm_integral_le_of_norm_le ((hfi n).sub hg).norm (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  exact squeeze_zero_norm' hbound hl1

include S hbd hG hP hnodes in
/-- **Upper bound for the threshold** (part (a) of `bl:norm`): if the extremal profile is negative
somewhere in every interval `(zT, zT + ε]`, the thresholds satisfy `uT_n ≤ zT + ε` eventually, for
every `ε > 0`. No assumption on the position of `uT_n` other than a lower bound. -/
theorem threshold_le_of_negative
    (hGneg : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, zT < x ∧ x ≤ zT + ε ∧ (G (x : ℂ)).re < 0)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop, uT n ≤ zT + ε := by
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, zT + ε < uT n := by
    rw [Filter.not_eventually] at hcon
    exact hcon.mono fun n hn => not_le.mp hn
  obtain ⟨ψ, hψ, hψp⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨x₀, hx₀⟩ := hbd
  obtain ⟨φ, hφ, hU⟩ := norm_limit_subseq (S.comp hψ) ⟨x₀, fun n => hx₀ (ψ n)⟩ hG hP
    (fun x hx => Eventually.of_forall fun n => by
      have := hψp n; simp only [Function.comp]; linarith)
    (fun i => by
      obtain ⟨ũ, hũ, hũn⟩ := hnodes i
      exact ⟨ũ ∘ ψ, hũ.comp hψ.tendsto_atTop, fun n => hũn (ψ n)⟩)
  obtain ⟨x, hx1, hx2, hx3⟩ := hGneg ε hε
  have hnn := limit_nonneg (S.comp hψ) hφ hU x
    (Eventually.of_forall fun k => by have := hψp (φ k); simp only [Function.comp]; linarith)
  have hmass := hG.mass_pos
  simp only [Complex.re_ofReal_mul] at hnn
  have : (0 : ℝ) < (profileMass G)⁻¹ := inv_pos.mpr hmass
  nlinarith

end FormalResearch.ModularBootstrap.Blowup
