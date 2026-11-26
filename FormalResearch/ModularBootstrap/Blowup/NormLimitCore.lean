module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1ClarkHelpers
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.AiryDiscBounds
public import FormalResearch.Special.AiryEnvelope
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Normal-families limit of slack-feasible transported densities (core of `bl:norm`)

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma BL-N (`bl:norm`), proof, and the
local-stability argument of Proposition TE.0' (`teb:quant_c1_hb`, `CFT/common/two_edge_bootstrap.tex`).

`DensityHyp C₀ R ς δ Ψ uT` is the list of properties that the transported density
`F(ũ) = -g V Δ'(ũ)/M[g]` of a test `g` with vacuum slack and threshold chart value `uT`
has on the Langer disc `|ũ| ≤ R`: holomorphy, reality, the type-(II) envelope with exponent
`ς`, `ũ`-positivity up to `uT`, `∫|F| ≤ 1`, the left-lobe mass `1/2 - δ` of the negative part and
the truncated total mass `∫_{-R'}^R Re F ≤ δ` (`δ` = slack plus far-lobe mass).

`density_subseq_limit` is the compactness step: a sequence with `R_n → ∞`, `ς_n → 0`, `δ_n → 0`
and `uT_n` bounded below has a subsequence converging locally uniformly on `ℂ` to an entire `Φ`
with the Airy growth, real on `ℝ`, `‖Φ‖₁ ≤ 1`, `∫ Re Φ ≤ 0`, negative mass `∫ max 0 (-Re Φ) ≥ 1/2`
and `Φ ≥ 0` on every `x` that is eventually below the thresholds.  Nothing in this file is specific
to the Airy node (`m₀ = 1`) or to the Clark nodes; the identification of the limit is in the
files that import it.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- Properties of a transported density `Ψ` on the Langer disc `|u| ≤ R` (see the module docstring). -/
structure DensityHyp (C₀ R ς δ : ℝ) (Ψ : ℂ → ℂ) (uT : ℝ) : Prop where
  analytic : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R)
  real : ∀ x ∈ Icc (-R) R, (Ψ (x : ℂ)).im = 0
  env : ∀ u ∈ closedBall (0 : ℂ) R, ¬ (u.im = 0 ∧ u.re ≤ 0) →
    ‖Ψ u‖ ≤ C₀ * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
      ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹
  nonneg : ∀ x ∈ Icc (-R) R, x ≤ uT → 0 ≤ (Ψ (x : ℂ)).re
  l1 : ∫ x in (-R)..R, ‖Ψ (x : ℂ)‖ ≤ 1
  neg : (1 / 2 : ℝ) - δ ≤ ∫ x in (-R)..R, max 0 (-(Ψ (x : ℂ)).re)
  top : ∀ R' ∈ Icc (0 : ℝ) R, -R' ≤ uT → ∫ x in (-R')..R, (Ψ (x : ℂ)).re ≤ δ

/-- Standing assumptions of a sequence of densities. -/
structure DensitySeq (C₀ : ℝ) (R ς δ : ℕ → ℝ) (Ψ : ℕ → ℂ → ℂ) (uT : ℕ → ℝ) : Prop where
  hC0 : 0 < C₀
  hR : Tendsto R atTop atTop
  hς0 : ∀ᶠ n in atTop, 0 ≤ ς n
  hς : Tendsto ς atTop (𝓝 0)
  hδ : Tendsto δ atTop (𝓝 0)
  hspec : ∀ n, DensityHyp C₀ (R n) (ς n) (δ n) (Ψ n) (uT n)

/-- Constant of the growth bound of the limit. -/
noncomputable def limitGrowthConst (C₀ : ℝ) : ℝ := 8 * Real.exp (5 / 2) * C₀ * Real.exp 1

namespace DensityHyp

variable {C₀ R ς δ : ℝ} {Ψ : ℂ → ℂ} {uT : ℝ}

lemma mem_ball_of_real {R x : ℝ} (hx : x ∈ Icc (-R) R) : (x : ℂ) ∈ closedBall (0 : ℂ) R := by
  rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hx

lemma cont_real (h : DensityHyp C₀ R ς δ Ψ uT) :
    ContinuousOn (fun x : ℝ => Ψ (x : ℂ)) (Icc (-R) R) :=
  h.analytic.continuousOn.comp continuous_ofReal.continuousOn fun _ hx => mem_ball_of_real hx

lemma env_pos (h : DensityHyp C₀ R ς δ Ψ uT) {x : ℝ} (hx0 : 0 < x) (hxR : x ≤ R) :
    ‖Ψ (x : ℂ)‖ ≤ C₀ * airyEnv (x : ℂ) * Real.exp (ς * √x) * x⁻¹ := by
  have hu : (x : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxR
  have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := by
    intro h0; simp only [Complex.ofReal_re] at h0; linarith [h0.2]
  have h1 := h.env (x : ℂ) hu hcut
  have hcp : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hx0.le, Complex.ofReal_re, Real.sqrt_eq_rpow]
  have hnorm_inv : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ = x⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hcp,
      Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hx0.le]
  calc ‖Ψ (x : ℂ)‖
      ≤ C₀ * airyEnv (x : ℂ) * Real.exp (ς * ((x : ℂ) ^ (1 / 2 : ℂ)).re) *
          (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹) := by
        simpa only [mul_assoc] using h1
    _ = C₀ * airyEnv (x : ℂ) * Real.exp (ς * √x) * x⁻¹ := by rw [hnorm_inv, hcp]

/-- Tail of the norm on the positive axis. -/
lemma tail_norm (h : DensityHyp C₀ R ς δ Ψ uT) (hC0 : 0 < C₀) (hς : 0 ≤ ς) (hς2 : ς ≤ 1 / 2)
    {A : ℝ} (hA : 1 ≤ A) (hAR : A ≤ R) :
    ∫ x in A..R, ‖Ψ (x : ℂ)‖ ≤ (6 / 5 : ℝ) * C₀ * Real.exp (-(5 / 6 : ℝ) * A) :=
  clarkTail_norm_le hC0 hς hς2 hA hAR
    (h.cont_real.mono (Icc_subset_Icc (by linarith) le_rfl))
    fun x hx0 hxR => h.env_pos hx0 hxR

end DensityHyp

/-- Integral of a Lipschitz function of a locally uniformly convergent family. -/
lemma tendsto_intervalIntegral_lip {F : ℕ → ℂ → ℂ} {Φ : ℂ → ℂ} {φ : ℕ → ℕ} {g : ℂ → ℝ}
    (hg : ∀ a b, |g a - g b| ≤ ‖a - b‖) (hg0 : Continuous g) {N : ℕ}
    (hU : TendstoUniformlyOn (fun k => F (φ k)) Φ atTop (closedBall (0 : ℂ) ((N : ℝ) + 1)))
    (hcont : ∀ᶠ k in atTop, ContinuousOn (F (φ k)) (closedBall (0 : ℂ) ((N : ℝ) + 1)))
    (hΦ : Continuous Φ) :
    Tendsto (fun k => ∫ x in (-(N : ℝ))..N, g (F (φ k) (x : ℂ))) atTop
      (𝓝 (∫ x in (-(N : ℝ))..N, g (Φ (x : ℂ)))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hN : (0 : ℝ) ≤ 2 * N := by positivity
  have hε' : 0 < ε / (2 * N + 1) := div_pos hε (by positivity)
  have hev := (Metric.tendstoUniformlyOn_iff.mp hU (ε / (2 * N + 1)) hε').and hcont
  filter_upwards [hev] with k ⟨hk, hkc⟩
  have hle : (-(N : ℝ)) ≤ N := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hmem : ∀ x ∈ Icc (-(N : ℝ)) N, (x : ℂ) ∈ closedBall (0 : ℂ) ((N : ℝ) + 1) := fun x hx => by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [abs_le.mpr hx]
  have hc1 : ContinuousOn (fun x : ℝ => g (F (φ k) (x : ℂ))) (Icc (-(N : ℝ)) N) :=
    hg0.comp_continuousOn (hkc.comp continuous_ofReal.continuousOn hmem)
  have hc2 : Continuous fun x : ℝ => g (Φ (x : ℂ)) := hg0.comp (hΦ.comp continuous_ofReal)
  have hi1 := hc1.intervalIntegrable_of_Icc (μ := volume) hle
  have hi2 := hc2.intervalIntegrable (μ := volume) (-(N : ℝ)) N
  rw [dist_eq_norm, ← intervalIntegral.integral_sub hi1 hi2]
  have hb : ∀ x ∈ Ι (-(N : ℝ)) N, ‖g (F (φ k) (x : ℂ)) - g (Φ (x : ℂ))‖ ≤ ε / (2 * N + 1) := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have hx' : x ∈ Icc (-(N : ℝ)) N := Ioc_subset_Icc_self hx
    have := hk (x : ℂ) (hmem x hx')
    rw [dist_eq_norm] at this
    rw [Real.norm_eq_abs]
    exact (hg _ _).trans (by rw [norm_sub_rev]; exact this.le)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have h2 : |(N : ℝ) - -(N : ℝ)| * (ε / (2 * N + 1)) < ε := by
    rw [show (N : ℝ) - -(N : ℝ) = 2 * N by ring, abs_of_nonneg hN, mul_div_assoc',
      div_lt_iff₀ (by positivity)]
    nlinarith
  exact this.trans_lt h2

section Extraction

variable {C₀ : ℝ} {R ς δ : ℕ → ℝ} {Ψ : ℕ → ℂ → ℂ} {uT : ℕ → ℝ}

/-- **Compactness.** A subsequence of a density sequence converges locally uniformly on `ℂ` to an
entire function with the Airy growth bound. -/
theorem density_exists_subseq (S : DensitySeq C₀ R ς δ Ψ uT) :
    ∃ (φ : ℕ → ℕ) (Φ : ℂ → ℂ), StrictMono φ ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun k => Ψ (φ k)) Φ atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Differentiable ℂ Φ ∧
      ∀ u : ℂ, ‖Φ u‖ ≤ limitGrowthConst C₀ * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
  have hC0 := S.hC0
  let M_seq : ℕ → ℝ := fun m =>
    8 * Real.exp (7 / 2) * C₀ * (1 + ((m : ℝ) + 2)) ^ (1 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * ((m : ℝ) + 2) ^ (3 / 2 : ℝ))
  have hM_nn : ∀ m, 0 ≤ M_seq m := fun m => by dsimp [M_seq]; positivity
  have hK_ex : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ((m : ℝ) + 4) ≤ R n ∧ 0 ≤ ς n ∧ ς n ≤ 1 / 2 ∧ ς n * √((m : ℝ) + 4) ≤ 1 := by
    intro m
    have h1 : ∀ᶠ n in atTop, ((m : ℝ) + 4) ≤ R n := S.hR (eventually_ge_atTop _)
    have h2 : ∀ᶠ n in atTop, ς n ≤ 1 / 2 := S.hς (Iic_mem_nhds (by norm_num))
    have h3 : ∀ᶠ n in atTop, ς n * √((m : ℝ) + 4) ≤ 1 := by
      have ht : Tendsto (fun n => ς n * √((m : ℝ) + 4)) atTop (𝓝 (0 * √((m : ℝ) + 4))) :=
        S.hς.mul_const _
      rw [zero_mul] at ht
      exact ht (Iic_mem_nhds one_pos)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h1.and (S.hς0.and (h2.and h3)))
    exact ⟨N, fun n hn => by obtain ⟨a, b, c, d⟩ := hN n hn; exact ⟨a, b, c, d⟩⟩
  choose K hK using hK_ex
  have hAn : ∀ m, ∀ n ≥ K m,
      AnalyticOnNhd ℂ (Ψ n) (closedBall (0 : ℂ) ((m : ℝ) + 2)) := fun m n hn =>
    (S.hspec n).analytic.mono (closedBall_subset_closedBall (by linarith [(hK m n hn).1]))
  have hBd : ∀ m, ∀ n ≥ K m, ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 2), ‖Ψ n z‖ ≤ M_seq m := by
    intro m n hn z hz
    have hsp := hK m n hn
    exact typeII_cut_bound (by positivity) (by linarith [hsp.1]) hC0 hsp.2.1
      (S.hspec n).analytic (S.hspec n).env
      (by simpa [show ((m : ℝ) + 2) + 2 = (m : ℝ) + 4 by ring] using hsp.2.2.2) hz
  obtain ⟨φ, Φ, hφ, hU⟩ := clarkArzelaDiagonal hM_nn hAn hBd
  have hφ' : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hev_K : ∀ m : ℕ, ∀ᶠ k in atTop, K m ≤ φ k := fun m =>
    hφ'.eventually (eventually_ge_atTop _)
  have hΦd : Differentiable ℂ Φ := by
    intro z
    let m : ℕ := ⌈‖z‖⌉₊ + 1
    have h_open : IsOpen (ball (0 : ℂ) ((m : ℝ) + 1)) := isOpen_ball
    have hz_ball : z ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_ball_zero_iff]
      have : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
      dsimp [m]; push_cast; linarith
    have h_loc : TendstoLocallyUniformlyOn (fun k => Ψ (φ k)) Φ atTop
        (ball (0 : ℂ) ((m : ℝ) + 1)) :=
      (hU m).tendstoLocallyUniformlyOn.mono ball_subset_closedBall
    have h_ev_diff : ∀ᶠ k in atTop, DifferentiableOn ℂ (Ψ (φ k)) (ball (0 : ℂ) ((m : ℝ) + 1)) := by
      filter_upwards [hev_K m] with k hk
      exact (hAn m (φ k) hk).differentiableOn.mono
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    exact ((h_loc.differentiableOn h_ev_diff h_open) z hz_ball).differentiableAt
      (h_open.mem_nhds hz_ball)
  refine ⟨φ, Φ, hφ, hU, hΦd, fun u => ?_⟩
  let m : ℕ := ⌈‖u‖⌉₊
  have hu_m : u ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
    rw [mem_closedBall_zero_iff]; linarith [Nat.le_ceil ‖u‖]
  have ht_pt : Tendsto (fun k => ‖Ψ (φ k) u‖) atTop (𝓝 ‖Φ u‖) :=
    ((hU m).tendsto_at hu_m).norm
  have hev_bd : ∀ᶠ k in atTop,
      ‖Ψ (φ k) u‖ ≤ limitGrowthConst C₀ * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
    filter_upwards [hev_K m] with k hk
    have hsp := hK m (φ k) hk
    have hu_norm : u ∈ closedBall (0 : ℂ) ‖u‖ := mem_closedBall_zero_iff.mpr le_rfl
    have hR_dom : ‖u‖ + 2 ≤ R (φ k) := by
      have := Nat.le_ceil ‖u‖
      linarith [hsp.1]
    have hdisc := (typeII_disc_avg_bound (norm_nonneg u) hR_dom hC0 hsp.2.1
      (S.hspec (φ k)).analytic (S.hspec (φ k)).env hu_norm).1
    have hςu : ς (φ k) * √(‖u‖ + 2) ≤ 1 := by
      have hsqrt : √(‖u‖ + 2) ≤ √((m : ℝ) + 4) :=
        Real.sqrt_le_sqrt (by linarith [Nat.le_ceil ‖u‖])
      calc ς (φ k) * √(‖u‖ + 2) ≤ ς (φ k) * √((m : ℝ) + 4) :=
            mul_le_mul_of_nonneg_left hsqrt hsp.2.1
        _ ≤ 1 := hsp.2.2.2
    have hexp1 : Real.exp (ς (φ k) * √(‖u‖ + 2)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hςu
    have henv_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
    calc ‖Ψ (φ k) u‖
        ≤ 8 * Real.exp (5 / 2) * C₀ * Real.exp (ς (φ k) * √(‖u‖ + 2)) *
            airyEnv u * (1 + ‖u‖) ^ (1 / 2 : ℝ) := hdisc
      _ ≤ 8 * Real.exp (5 / 2) * C₀ * Real.exp 1 * airyEnv u * (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = limitGrowthConst C₀ * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
          unfold limitGrowthConst; ring
  exact le_of_tendsto ht_pt hev_bd

variable {φ : ℕ → ℕ} {Φ : ℂ → ℂ}

/-- Locally uniform convergence of a subsequence along balls. -/
abbrev LocUnif (Ψ : ℕ → ℂ → ℂ) (φ : ℕ → ℕ) (Φ : ℂ → ℂ) : Prop :=
  ∀ m : ℕ, TendstoUniformlyOn (fun k => Ψ (φ k)) Φ atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))

lemma eventually_R_ge (S : DensitySeq C₀ R ς δ Ψ uT) (hφ : StrictMono φ) (N : ℝ) :
    ∀ᶠ k in atTop, N ≤ R (φ k) := (S.hR.comp hφ.tendsto_atTop) (eventually_ge_atTop N)

lemma eventually_cont (S : DensitySeq C₀ R ς δ Ψ uT) (hφ : StrictMono φ) (N : ℕ) :
    ∀ᶠ k in atTop, ContinuousOn (Ψ (φ k)) (closedBall (0 : ℂ) ((N : ℝ) + 1)) := by
  filter_upwards [eventually_R_ge S hφ ((N : ℝ) + 1)] with k hk
  exact (S.hspec (φ k)).analytic.continuousOn.mono (closedBall_subset_closedBall hk)

lemma limit_continuous (hΦ : Differentiable ℂ Φ) : Continuous fun x : ℝ => Φ (x : ℂ) :=
  hΦ.continuous.comp continuous_ofReal

lemma limit_real (S : DensitySeq C₀ R ς δ Ψ uT) (hφ : StrictMono φ) (hU : LocUnif Ψ φ Φ) (x : ℝ) :
    (Φ (x : ℂ)).im = 0 := by
  let m : ℕ := ⌈|x|⌉₊
  have hx_m : (x : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    linarith [Nat.le_ceil |x|]
  have ht_im : Tendsto (fun k => (Ψ (φ k) (x : ℂ)).im) atTop (𝓝 (Φ (x : ℂ)).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp ((hU m).tendsto_at hx_m)
  have hev0 : ∀ᶠ k in atTop, (Ψ (φ k) (x : ℂ)).im = 0 := by
    filter_upwards [eventually_R_ge S hφ (|x|)] with k hk
    exact (S.hspec (φ k)).real x (abs_le.mp hk)
  exact tendsto_nhds_unique ht_im (tendsto_const_nhds.congr' (hev0.mono fun _ hk => hk.symm))

/-- Norm and real-part integrals over `[-N, N]` pass to the limit; summary of the three Lipschitz
functions `‖·‖`, `Re`, `max 0 (-Re ·)`. -/
lemma limit_integral_norm (S : DensitySeq C₀ R ς δ Ψ uT) (hφ : StrictMono φ)
    (hU : LocUnif Ψ φ Φ) (hΦ : Differentiable ℂ Φ) (N : ℕ) :
    Tendsto (fun k => ∫ x in (-(N : ℝ))..N, ‖Ψ (φ k) (x : ℂ)‖) atTop
      (𝓝 (∫ x in (-(N : ℝ))..N, ‖Φ (x : ℂ)‖)) :=
  tendsto_intervalIntegral_lip (g := fun z : ℂ => ‖z‖)
    (fun a b => by simpa using abs_norm_sub_norm_le a b) continuous_norm (hU N)
    (eventually_cont S hφ N) hΦ.continuous

lemma limit_integral_re (S : DensitySeq C₀ R ς δ Ψ uT) (hφ : StrictMono φ)
    (hU : LocUnif Ψ φ Φ) (hΦ : Differentiable ℂ Φ) (N : ℕ) :
    Tendsto (fun k => ∫ x in (-(N : ℝ))..N, (Ψ (φ k) (x : ℂ)).re) atTop
      (𝓝 (∫ x in (-(N : ℝ))..N, (Φ (x : ℂ)).re)) :=
  tendsto_intervalIntegral_lip (g := fun z : ℂ => z.re)
    (fun a b => by simpa using Complex.abs_re_le_norm (a - b)) Complex.continuous_re (hU N)
    (eventually_cont S hφ N) hΦ.continuous

lemma limit_integral_neg (S : DensitySeq C₀ R ς δ Ψ uT) (hφ : StrictMono φ)
    (hU : LocUnif Ψ φ Φ) (hΦ : Differentiable ℂ Φ) (N : ℕ) :
    Tendsto (fun k => ∫ x in (-(N : ℝ))..N, max 0 (-(Ψ (φ k) (x : ℂ)).re)) atTop
      (𝓝 (∫ x in (-(N : ℝ))..N, max 0 (-(Φ (x : ℂ)).re))) := by
  refine tendsto_intervalIntegral_lip (g := fun z : ℂ => max 0 (-z.re)) (fun a b => ?_)
    (continuous_const.max Complex.continuous_re.neg) (hU N) (eventually_cont S hφ N) hΦ.continuous
  have h1 := Complex.abs_re_le_norm (a - b)
  have h2 : |max 0 (-a.re) - max 0 (-b.re)| ≤ |(-a.re) - (-b.re)| := by
    simpa using abs_max_sub_max_le_abs 0 (-a.re) (-b.re) |>.trans_eq' (by simp)
  refine h2.trans ?_
  rw [show (-a.re) - (-b.re) = -(a - b).re by simp]
  simpa using h1

end Extraction

end FormalResearch.ModularBootstrap.Blowup
