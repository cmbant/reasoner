module

public import FormalResearch.SignUncertainty.CtScaleArc
public import FormalResearch.SignUncertainty.HankelBootLine
public import FormalResearch.SignUncertainty.HankelBootTop
public import FormalResearch.SignUncertainty.HankelBootCount
public import FormalResearch.SignUncertainty.CtRoscAssembly
public import FormalResearch.SignUncertainty.CtBandTop

/-!
# Scale-`r` Hankel Bootstrap Step (`ct:dyadic` Part (1), Step 1b)

Proves the scale-`r` Airy bootstrap feedback inequality (`constant_terms_lower.tex`, `ct:L-fb` and Step 1b)
at every good circle `r ∈ [r_min(c), R_J]` (`r_min(c) ≍ (log c)^2`, `R_J ∈ [10⁻⁴ c^{2/3}, 10⁻⁴ c^{2/3}+1]`):
for every fixed `k ≥ 9` and sufficiently large `c ≥ c₀(k)`,

`hankelBootB1 c f r u_T + hankelBootB2 c f r ≤ C_step * (1 + k + exp (-k) * hankelScaleL c R_J r u_T f) * r ^ (-1/2)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.ModularBootstrap.ConcreteBootstrap
private lemma hankel_scale_line_step {c ε T u_T r ℓ : ℝ} {f : ℝ → ℝ}
    (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hr10 : 10 ≤ r) (hrA : r + 1 ≤ langerRadius c)
    (hru : -r ≤ u_T) (hℓ0 : 0 ≤ ℓ) (hℓh : ℓ ≤ 1 / 2)
    {k : ℕ} (hkr : (k : ℝ) ≤ r / 5) :
    (63 / 100 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r) ≤
      -(∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re) +
        (4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c) +
          120 * ((k : ℝ) + 1) / r + 72 * Real.exp (-(5 / 6 : ℝ) * r) +
          hankelLobe c + 2 * langerRadius c * hankelRinf c +
          (3 * r + 1) * hankelRinf c) := by
  have hc0 : 0 < c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr_pos : 0 < r := by linarith
  have hRA : r ≤ langerRadius c := by linarith
  have huA : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hmRA : |-r| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hr_pos]; exact hRA
  -- Shift integral identity:
  -- `∫ x in -r..r, Re(Ψ̃(x+ℓ)(1+x/r)^{k+1}) = ∫ v in (-r+ℓ)..(r+ℓ), (1+(v-ℓ)/r)^{k+1} Re Ψ̃(v)`
  have hψ_cont : ContinuousOn (hankelPsiR c f) (Icc (-langerRadius c) (langerRadius c)) := by
    have h_an := analyticOnNhd_hankelPsi hc0 hfe
    have hA_eq : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 :=
      hankelBoot_langerRadius_eq c
    intro x hx
    have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) (c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, ← hA_eq]
      exact abs_le.2 hx
    exact (Complex.continuous_re.continuousAt.comp
      (((h_an _ hx_ball).continuousAt).comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  let w : ℝ → ℝ := fun v => (1 + (v - ℓ) / r) ^ (k + 1)
  have hw_cont : Continuous w := by unfold w; fun_prop
  have h_integrand_cont : ∀ a b : ℝ, -langerRadius c ≤ a → a ≤ b → b ≤ langerRadius c →
      IntervalIntegrable (fun v => (1 - w v) * hankelPsiR c f v) volume a b := by
    intro a b ha hab hb
    refine ((continuousOn_const.sub hw_cont.continuousOn).mul
      (hψ_cont.mono (Icc_subset_Icc ha hb))).intervalIntegrable_of_Icc hab
  have hband := hankelBoot_line_band hc hf hε hmass hT hu0 hu3 hr10 hrA hℓ0 hℓh k
  have hmid := hankelBoot_line_mid hc hf hε hmass hT hu0 hu3 hr10 hrA hℓ0 hℓh k hkr
  have hright := hankelBoot_line_right hc hf hε hmass hT hu0 hu3 hr10 hrA hℓ0 hℓh k hkr
  have htail := hankelBoot_line_tail hc hf hε hmass hT hu0 hu3 hr10 hrA hℓ0 hℓh k
  have hT_le : T ≤ c * hankelXi c (-r) := by
    rw [← hT]
    exact hankel_phi_anti hc0 hmRA huA hru
  have htop := hankel_psi_total_upper_tail hc hf hε hmass hmRA hT_le
  have hB2_eq : hankelBootB2 c f r = ∫ u in Set.Ioi (c * hankelXi c (-r)), hankelRho0 c u * f u := by
    have hxi_pos : 0 < hankelXi c (-r) := hankelXi_pos hc0 hmRA
    have hf_pos : ∀ ξ : ℝ, hankelXi c (-r) ≤ ξ → 0 ≤ f (c * ξ) := fun ξ hξ =>
      hf.tail_nonneg (c * ξ) (hT_le.trans (mul_le_mul_of_nonneg_left hξ hc0.le))
    exact hankelBoot_B2_eq hc0 hfe hxi_pos hf_pos
  rw [← hB2_eq] at htop
  -- Split `∫_{-r}^{A} Ψ̃` and `∫_{-r+ℓ}^{r+ℓ} (1 - w) Ψ̃`
  have hu1 : u_T ≤ 1 := by linarith
  have h1r : 1 ≤ r + ℓ := by linarith
  have hmr_mrl : -r ≤ -r + ℓ := by linarith
  have hmrl_u : -r + ℓ ≤ u_T := by linarith
  have hrl_A : r + ℓ ≤ langerRadius c := by linarith
  have hmA_mr : -langerRadius c ≤ -r := by linarith
  have hmA_mrl : -langerRadius c ≤ -r + ℓ := by linarith
  have h_sum_omw :
      (∫ v in (-r + ℓ)..u_T, (1 - w v) * hankelPsiR c f v) +
        (∫ v in u_T..1, (1 - w v) * hankelPsiR c f v) +
        (∫ v in 1..(r + ℓ), (1 - w v) * hankelPsiR c f v) =
      ∫ v in (-r + ℓ)..(r + ℓ), (1 - w v) * hankelPsiR c f v := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals
      (h_integrand_cont (-r + ℓ) u_T hmA_mrl hmrl_u (by linarith))
      (h_integrand_cont u_T 1 (by linarith) hu1 (by linarith))
    have h123 := intervalIntegral.integral_add_adjacent_intervals
      (h_integrand_cont (-r + ℓ) 1 hmA_mrl (by linarith) (by linarith))
      (h_integrand_cont 1 (r + ℓ) (by linarith) h1r hrl_A)
    linarith
  have h_sum_psi :
      (∫ v in (-r)..(-r + ℓ), hankelPsiR c f v) +
        (∫ v in (-r + ℓ)..(r + ℓ), hankelPsiR c f v) +
        (∫ v in (r + ℓ)..langerRadius c, hankelPsiR c f v) =
      ∫ v in (-r)..langerRadius c, hankelPsiR c f v := by
    have i1 := (hψ_cont.mono (Icc_subset_Icc hmA_mr (by linarith))).intervalIntegrable_of_Icc (μ := volume) hmr_mrl
    have i2 := (hψ_cont.mono (Icc_subset_Icc hmA_mrl hrl_A)).intervalIntegrable_of_Icc (μ := volume) (by linarith)
    have i12 := (hψ_cont.mono (Icc_subset_Icc hmA_mr hrl_A)).intervalIntegrable_of_Icc (μ := volume) (by linarith)
    have i3 := (hψ_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (μ := volume) hrl_A
    have ha' := intervalIntegral.integral_add_adjacent_intervals i1 i2
    have hb' := intervalIntegral.integral_add_adjacent_intervals i12 i3
    linarith
  have h_omw_split :
      ∫ v in (-r + ℓ)..(r + ℓ), (1 - w v) * hankelPsiR c f v =
        (∫ v in (-r + ℓ)..(r + ℓ), hankelPsiR c f v) -
          ∫ v in (-r + ℓ)..(r + ℓ), w v * hankelPsiR c f v := by
    have iΨ : IntervalIntegrable (hankelPsiR c f) volume (-r + ℓ) (r + ℓ) :=
      (hψ_cont.mono (Icc_subset_Icc hmA_mrl hrl_A)).intervalIntegrable_of_Icc (μ := volume) (by linarith)
    have iwΨ : IntervalIntegrable (fun v => w v * hankelPsiR c f v) volume (-r + ℓ) (r + ℓ) :=
      (hw_cont.continuousOn.mul
        (hψ_cont.mono (Icc_subset_Icc hmA_mrl hrl_A))).intervalIntegrable_of_Icc (μ := volume) (by linarith)
    have hfun : (fun v => (1 - w v) * hankelPsiR c f v) =
        fun v => hankelPsiR c f v - w v * hankelPsiR c f v := by
      ext v; ring
    rw [hfun]
    exact intervalIntegral.integral_sub iΨ iwΨ
  have h_line_shift :
      ∫ v in (-r + ℓ)..(r + ℓ), w v * hankelPsiR c f v =
        ∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (fun v => w v * hankelPsiR c f v) ℓ (a := -r) (b := r)
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    have hxA : |x + ℓ| ≤ langerRadius c := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    dsimp only [w]
    unfold hankelBootShifted hankelPsiR
    have him : (hankelPsi c f ((x + ℓ : ℝ) : ℂ)).im = 0 := hankelPsi_real hc0 f hxA
    have harg : (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) := by push_cast; ring
    have hpow : (1 + (x : ℂ) / (r : ℂ)) ^ (k + 1) = (((1 + x / r) ^ (k + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [harg, hpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hsub : x + ℓ - ℓ = x := by ring
    rw [hsub]; ring
  have h_line_id :
      ((-∫ v in (-r + ℓ)..u_T, (1 - w v) * hankelPsiR c f v) -
          ∫ v in (-r)..(-r + ℓ), hankelPsiR c f v) +
        (-∫ v in u_T..1, (1 - w v) * hankelPsiR c f v) +
        (-∫ v in 1..(r + ℓ), (1 - w v) * hankelPsiR c f v) +
        (-∫ v in (r + ℓ)..langerRadius c, hankelPsiR c f v) +
        ((∫ x in (-r)..langerRadius c, hankelPsiR c f x) + hankelBootB2 c f r) =
      (∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re) + hankelBootB2 c f r := by
    linarith only [h_sum_omw, h_sum_psi, h_omw_split, h_line_shift]
  have hB1_le := hankelBootB1_le_B1k hc hf hε hmass hT hu0 hu3 hr_pos hru hRA k
  have hB2_nn : 0 ≤ hankelBootB2 c f r := hankelBootB2_nonneg c f r
  have hrinf_nn : 0 ≤ hankelRinf c := hankelRinf_nonneg (by linarith) hfe hε hmass
  have h_comb : (63 / 100 : ℝ) * hankelBootMoment c f r u_T k + hankelBootB2 c f r ≤
      -(∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re) +
        ((r + 1) * hankelRinf c +
          4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c) +
          120 * ((k : ℝ) + 1) / r + 72 * Real.exp (-(5 / 6 : ℝ) * r) +
          (hankelLobe c + 2 * langerRadius c * hankelRinf c)) := by
    have htail' : -∫ v in (r + ℓ)..langerRadius c, hankelPsiR c f v ≤ 72 * Real.exp (-(5 / 6 : ℝ) * r) := by
      linarith only [htail]
    have hsum_bd : (∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re) + hankelBootB2 c f r ≤
        (-(63 / 100 : ℝ) * hankelBootMoment c f r u_T k + (r + 1) * hankelRinf c) +
          4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c) +
          120 * ((k : ℝ) + 1) / r + 72 * Real.exp (-(5 / 6 : ℝ) * r) +
          (hankelLobe c + 2 * langerRadius c * hankelRinf c) := by
      rw [← h_line_id]
      exact add_le_add (add_le_add (add_le_add (add_le_add hband hmid) hright) htail') htop
    linarith only [hsum_bd]
  have hB1k_def : hankelBootB1k c f r u_T k = hankelBootMoment c f r u_T k + 2 * r * hankelRinf c := rfl
  rw [hB1k_def] at hB1_le
  have h63 : (63 / 100 : ℝ) * hankelBootB1 c f r u_T ≤
      (63 / 100 : ℝ) * hankelBootMoment c f r u_T k + 2 * r * hankelRinf c := by
    have h1 : (63 / 100 : ℝ) * hankelBootB1 c f r u_T ≤
        (63 / 100 : ℝ) * (hankelBootMoment c f r u_T k + 2 * r * hankelRinf c) :=
      mul_le_mul_of_nonneg_left hB1_le (by norm_num)
    have h2 : (63 / 100 : ℝ) * (2 * r * hankelRinf c) ≤ 2 * r * hankelRinf c := by
      have hrr : 0 ≤ r * hankelRinf c := mul_nonneg hr_pos.le hrinf_nn
      linarith only [hrr]
    linarith only [h1, h2]
  have hB2_63 : (63 / 100 : ℝ) * hankelBootB2 c f r ≤ hankelBootB2 c f r := by linarith only [hB2_nn]
  linarith only [h_comb, h63, hB2_63]


/-- **Scale-`r` Hankel bootstrap step (`constant_terms_lower.tex`, `ct:dyadic` Part (1), Step 1b)**:
there exist universal constants `C_step > 0` and `r_min_base ≥ 256` such that for every `k ≥ 9`,
for all sufficiently large `c ≥ c₀(k)`, any feasible normalized Hankel eigenfunction `(f, T)`
with `T < cξ(a₁)`, any top good circle `R_J ∈ [10⁻⁴ c^{2/3}, 10⁻⁴ c^{2/3} + 1]`, and any good circle
`r ∈ [r_min_base (log c)², R_J]`,
`B₁(r; f, u_T) + B₂(r; f) ≤ C_step * (1 + k + exp(-k) * L_r) * r^{-1/2}`. -/
private noncomputable def scaleCNode : ℝ := π * quantC1C1 / quantC1WStar
private noncomputable def scaleCLine : ℝ := 4 * Real.exp (6 / 5 : ℝ) * 2 + 120
private noncomputable def scaleCArc : ℝ :=
  4 * virasoroArcCovConst * (π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC
private noncomputable def scaleCUnc : ℝ := 1800 * π * 40 ^ (5 / 2 : ℝ)
private noncomputable def scaleCSlack : ℝ := 2 * (6 * π) ^ 2 + 11
private noncomputable def scaleCNum : ℝ := scaleCUnc + 90 + 1 + scaleCSlack + 2 * scaleCLine
private noncomputable def scaleCK : ℝ := scaleCNode + 2 * scaleCLine
private noncomputable def scaleCStep : ℝ := (100 / 63 : ℝ) * max (max scaleCNum scaleCK) scaleCArc

private lemma scale_step_alg (k L s : ℝ) :
    scaleCNode * k * s + 2 * (6 * π) ^ 2 * s +
      (scaleCArc * L * s + scaleCUnc * s) +
      ((2 * scaleCLine * k + 2 * scaleCLine) * s + 90 * s + 1 * s + 7 * s + 4 * s) =
    (scaleCNum + scaleCK * k + scaleCArc * L) * s := by
  unfold scaleCNum scaleCSlack scaleCK
  ring

private lemma scale_combine_63 {B12 I P k L s nrinf line_k tail_t lobe ar_t rrinf : ℝ}
    (hs : 0 ≤ s) (hk : 0 ≤ k) (hCLine : 0 ≤ scaleCLine)
    (hline : (63 / 100 : ℝ) * B12 ≤ -I + (line_k + tail_t + lobe + ar_t + rrinf))
    (hquad : P ≤ I + (scaleCArc * L * s + scaleCUnc * s))
    (hnodes : -(scaleCNode * k * s) - nrinf ≤ P)
    (hlinek : line_k ≤ scaleCLine * (k + 1) * s)
    (hnr : nrinf ≤ 2 * (6 * π) ^ 2 * s) (htail : tail_t ≤ 90 * s)
    (hlobe : lobe ≤ 1 * s) (har : ar_t ≤ 7 * s) (hrr : rrinf ≤ 4 * s) :
    (63 / 100 : ℝ) * B12 ≤ (scaleCNum + scaleCK * k + scaleCArc * L) * s := by
  have hk_lin : scaleCLine * (k + 1) ≤ 2 * scaleCLine * k + 2 * scaleCLine := by
    have h1 : 0 ≤ scaleCLine * k := mul_nonneg hCLine hk
    linarith only [h1, hCLine]
  have hlinek2 : line_k ≤ (2 * scaleCLine * k + 2 * scaleCLine) * s :=
    hlinek.trans (mul_le_mul_of_nonneg_right hk_lin hs)
  have h_sum1 := scale_step_alg k L s
  linarith only [hline, hquad, hnodes, hlinek2, hnr, htail, hlobe, har, hrr, h_sum1]

theorem hankel_scale_mass_step :
    ∃ C_step r_min_base : ℝ, 0 < C_step ∧ 256 ≤ r_min_base ∧
      ∀ (k : ℕ), 9 ≤ k → ∃ c₀ : ℝ, 1e14 ≤ c₀ ∧
        ∀ (c ε T u_T R_J r : ℝ) (f : ℝ → ℝ), c₀ ≤ c →
          IsHankelFeasible c ε T f → (ε = 1 ∨ ε = -1) → hankelMass c f = 1 →
          c * hankelXi c u_T = T → airyZero 1 < u_T →
          QuantC1B2Holds (hankelPsi c f) u_T →
          (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J →
          R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1 →
          r_min_base * (Real.log c) ^ 2 ≤ r → r ≤ R_J → ctGoodRadius r →
          hankelBootB1 c f r u_T + hankelBootB2 c f r ≤
            C_step * (1 + (k : ℝ) + Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) *
              r ^ (-(1 / 2 : ℝ)) := by
  have hC_node_nn : 0 ≤ scaleCNode := by
    unfold scaleCNode; exact div_nonneg (mul_nonneg Real.pi_pos.le quantC1C1_pos.le) quantC1WStar_pos.le
  have hC_line_nn : 0 ≤ scaleCLine := by unfold scaleCLine; positivity
  have hC_arc_pos : 0 < scaleCArc := by
    unfold scaleCArc
    exact mul_pos (mul_pos (mul_pos (by positivity) virasoroArcCovConst_pos) (by positivity))
      hankelScaleWindowC_pos
  have hC_step_pos : 0 < scaleCStep := by
    unfold scaleCStep
    exact mul_pos (by norm_num) (lt_max_of_lt_right hC_arc_pos)
  refine ⟨scaleCStep, 1e8, hC_step_pos, by norm_num, fun k hk9 => ?_⟩
  let η_min : ℝ := min quantC1DeltaStar (min quantC1Eta0 (1 / 2 : ℝ))
  have hη_min_pos : 0 < η_min :=
    lt_min quantC1DeltaStar_pos (lt_min quantC1Eta0_pos (by norm_num))
  -- Need `c₀` large enough so that `hankelRinf c ≤ c^(-4/3)`, `hankelLobe c ≤ c^(-1/3)`,
  -- and `(π / 2 * k) / (1e4 * log c) ≤ η_min`, `5 * k ≤ 1e8 * (log c)^2`, `256 ≤ 1e8 * (log c)^2`.
  have hev_rinf : ∀ᶠ c : ℝ in atTop, c ^ (4 / 3 : ℝ) * hankelRinf c ≤ 1 := hankelRinf_c43_small
  have hev_lobe : ∀ᶠ c : ℝ in atTop, c ^ (1 / 3 : ℝ) * hankelLobe c ≤ 1 := by
    have ht : Tendsto (fun c : ℝ => 16 * (c ^ (4 / 3 : ℝ) * Real.exp (-(1 / 600000 : ℝ) * c)))
        atTop (𝓝 0) := by
      have hmul := (tendsto_const_nhds (x := (16 : ℝ))).mul
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / 3 : ℝ) (1 / 600000 : ℝ) (by norm_num))
      simpa using hmul
    filter_upwards [eventually_ge_atTop (1 : ℝ), ht (Iic_mem_nhds (zero_lt_one))] with c hc1 hsm
    have hlo := hankelBoot_lobe_le hc1
    have hc0 : 0 < c := by linarith
    have hpow : c ^ (1 / 3 : ℝ) * (c * Real.exp (-(1 / 600000 : ℝ) * c)) =
        c ^ (4 / 3 : ℝ) * Real.exp (-(1 / 600000 : ℝ) * c) := by
      rw [← mul_assoc]; congr 1
      nth_rw 2 [← Real.rpow_one c]
      rw [← Real.rpow_add hc0]; norm_num
    calc c ^ (1 / 3 : ℝ) * hankelLobe c
        ≤ c ^ (1 / 3 : ℝ) * (16 * (c * Real.exp (-(1 / 600000 : ℝ) * c))) := by gcongr
      _ = 16 * (c ^ (4 / 3 : ℝ) * Real.exp (-(1 / 600000 : ℝ) * c)) := by
          rw [← hpow]; ring
      _ ≤ 1 := hsm
  let thresh : ℝ := max 32 (max ((π / 2 * (k : ℝ)) / (1e4 * η_min)) (max (k : ℝ) 1))
  have hev_log' : ∀ᶠ c : ℝ in atTop, thresh ≤ Real.log c :=
    Real.tendsto_log_atTop.eventually_ge_atTop thresh
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1
    (eventually_ge_atTop (1e14 : ℝ) |>.and (hev_rinf.and (hev_lobe.and hev_log')))
  refine ⟨c₀, (hc₀ c₀ le_rfl).1, ?_⟩
  intro c ε T u_T R_J r f hc_ge hf hε hmass hT ha1 hB2 hRJ_lb hRJ_ub hr_log hr_RJ hgood
  obtain ⟨hc14, hrinf_bd, hlobe_bd, hlog_bd⟩ := hc₀ c hc_ge
  have hc0 : 0 < c := by linarith
  have hc3 : 3e6 ≤ c := by linarith
  obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1 hB2
  have hlog_ge : thresh ≤ Real.log c := hlog_bd
  have hlog32 : 32 ≤ Real.log c := (le_max_left _ _).trans hlog_ge
  have hlog0 : 0 < Real.log c := by linarith
  have hr256 : 256 ≤ r := by
    have : 1e8 * (32 : ℝ) ^ 2 ≤ 1e8 * (Real.log c) ^ 2 := by gcongr
    linarith
  have hr_pos : 0 < r := by linarith
  have hk_le_log : (k : ℝ) ≤ Real.log c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hlog_ge
  have hkr : (k : ℝ) ≤ r / 5 := by
    have hk9r : (9 : ℝ) ≤ k := by exact_mod_cast hk9
    have h1 : (k : ℝ) ^ 2 ≤ (Real.log c) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le_log 2
    have hk_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hk9r]
    have h3 : 5 * (k : ℝ) ≤ 1e8 * (Real.log c) ^ 2 := by nlinarith [h1, hk_sq, hlog32]
    linarith
  -- Bounds on `R_J`, `langerRadius c`, and `r_∞`
  have h48_RJ : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have hc12 : (1e12 : ℝ) ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h1e8 : (1e12 : ℝ) ^ (2 / 3 : ℝ) = 1e8 := by
      have h1 : (1e12 : ℝ) = (1e4 : ℝ) ^ (3 : ℕ) := by norm_num
      rw [h1, ← Real.rpow_natCast (1e4 : ℝ) 3, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h1e8] at hc12
    linarith
  obtain ⟨_, hRJ_A, hA_RJ, hRJ_c⟩ := hankelBoot_radius_facts hc3 h48_RJ hRJ_lb hRJ_ub
  have hrA : r + 1 ≤ langerRadius c := by linarith
  have hru : -r ≤ u_T := by linarith
  -- `ℓ = (π / 2) * k / √r` bounds
  set ℓ : ℝ := (π / 2) * (k : ℝ) / √r
  have ha_pos : 0 < √r := Real.sqrt_pos.2 hr_pos
  have ha_ge : 1e4 * Real.log c ≤ √r := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1e4 * Real.log c)]
    exact Real.sqrt_le_sqrt (by calc (1e4 * Real.log c) ^ 2 = 1e8 * (Real.log c) ^ 2 := by ring
      _ ≤ r := hr_log)
  have hℓ0 : 0 ≤ ℓ := by dsimp [ℓ]; positivity
  have hℓ_eta : ℓ ≤ η_min := by
    have hthresh : (π / 2 * (k : ℝ)) / (1e4 * η_min) ≤ Real.log c :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hlog_ge
    have hdiv : (π / 2 * (k : ℝ)) / (1e4 * Real.log c) ≤ η_min := by
      rw [div_le_iff₀ (by positivity)] at hthresh ⊢
      linarith
    have hstep : ℓ ≤ (π / 2 * (k : ℝ)) / (1e4 * Real.log c) := by
      dsimp [ℓ]; gcongr
    exact hstep.trans hdiv
  have hℓh : ℓ ≤ 1 / 2 := hℓ_eta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hℓ_nodes : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1) :=
    hℓ_eta.trans (min_le_min le_rfl (min_le_min le_rfl (by norm_num)))
  -- Good circle data
  obtain ⟨N, hN, hD⟩ := airy_circleData hr_pos (ctGoodRadius_ne_zero hr_pos hgood)
  have hNle : (N : ℝ) ≤ r ^ (3 / 2 : ℝ) := hankelBoot_zero_count_le hr_pos hN
  -- Combine line, nodes, and arc
  have hline := hankel_scale_line_step hc3 hf hε hmass hT hu0 hu3 (by linarith) hrA hru hℓ0 hℓh hkr
  have hquad := hankel_scale_quad_arc hc14 hf hε hmass hT hu0 hu3 hRJ_lb hRJ_ub hr256 hr_RJ
    hr_log hrA rfl hℓh hk9 hgood hN hD
  have hnodes := hankelBoot_nodes_lb hc3 hf hε hmass hT ha1 hB2 hu0 hu3 (by linarith) hrA hN
    hℓ0 hℓ_nodes hkr
  -- Bound error terms by `r ^ (-1/2)`
  have hr12_pos : 0 < r ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr_pos _
  have hc13_r12 : c ^ (-(1 / 3 : ℝ)) ≤ r ^ (-(1 / 2 : ℝ)) := by
    have hrc : r ≤ c ^ (2 / 3 : ℝ) := hr_RJ.trans hRJ_c
    have hstep : r ^ (1 / 2 : ℝ) ≤ c ^ (1 / 3 : ℝ) := by
      calc r ^ (1 / 2 : ℝ) ≤ (c ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hr_pos.le hrc (by norm_num)
        _ = c ^ (1 / 3 : ℝ) := by rw [← Real.rpow_mul hc0.le]; norm_num
    rw [Real.rpow_neg hc0.le, Real.rpow_neg hr_pos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hr_pos _) hstep
  have hr_c : r ≤ c := by
    have h1 : c ^ (2 / 3 : ℝ) ≤ c ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at h1
    exact (hr_RJ.trans hRJ_c).trans h1
  have hA_c : langerRadius c ≤ 7 / 2 * c ^ (2 / 3 : ℝ) := by linarith
  have hrinf_nn : 0 ≤ hankelRinf c := hankelRinf_nonneg (by linarith) hf.toIsHankelEigenfn hε hmass
  have hrinf_le : hankelRinf c ≤ c ^ (-(4 / 3 : ℝ)) := by
    have hpos_r : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    calc hankelRinf c = (c ^ (4 / 3 : ℝ))⁻¹ * (c ^ (4 / 3 : ℝ) * hankelRinf c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos_r.ne', one_mul]
      _ ≤ (c ^ (4 / 3 : ℝ))⁻¹ * 1 := mul_le_mul_of_nonneg_left hrinf_bd (by positivity)
      _ = c ^ (-(4 / 3 : ℝ)) := by rw [mul_one, Real.rpow_neg hc0.le]
  have hlobe_le : hankelLobe c ≤ c ^ (-(1 / 3 : ℝ)) := by
    have hpos_r : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    calc hankelLobe c = (c ^ (1 / 3 : ℝ))⁻¹ * (c ^ (1 / 3 : ℝ) * hankelLobe c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos_r.ne', one_mul]
      _ ≤ (c ^ (1 / 3 : ℝ))⁻¹ * 1 := mul_le_mul_of_nonneg_left hlobe_bd (by positivity)
      _ = c ^ (-(1 / 3 : ℝ)) := by rw [mul_one, Real.rpow_neg hc0.le]
  have hArinf : 2 * langerRadius c * hankelRinf c ≤ 7 * c ^ (-(2 / 3 : ℝ)) := by
    have h1 : c ^ (2 / 3 : ℝ) * c ^ (-(4 / 3 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc 2 * langerRadius c * hankelRinf c
        ≤ 2 * (7 / 2 * c ^ (2 / 3 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by gcongr
      _ = 7 * c ^ (-(2 / 3 : ℝ)) := by rw [← h1]; ring
  have hc23_r12 : c ^ (-(2 / 3 : ℝ)) ≤ r ^ (-(1 / 2 : ℝ)) := by
    have h1 : c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact h1.trans hc13_r12
  have hArinf_one : 2 * langerRadius c * hankelRinf c ≤ 1 := by
    have h7c : 7 * c ^ (-(2 / 3 : ℝ)) ≤ 1 := by
      have : (7 : ℝ) ≤ c ^ (2 / 3 : ℝ) := by linarith [hRJ_c]
      rw [Real.rpow_neg hc0.le, mul_inv_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
      linarith
    exact hArinf.trans h7c
  have h_node_rinf : (6 * π) ^ 2 * ((N : ℝ) + 1) * hankelRinf c ≤ 2 * (6 * π) ^ 2 * r ^ (-(1 / 2 : ℝ)) := by
    have hN1 : (N : ℝ) + 1 ≤ 2 * c := by
      have hrc : r ^ (3 / 2 : ℝ) ≤ (c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hr_pos.le (hr_RJ.trans hRJ_c) (by norm_num)
      rw [← Real.rpow_mul hc0.le] at hrc
      norm_num at hrc
      linarith [hNle, hrc]
    have hcc : c * c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
    calc (6 * π) ^ 2 * ((N : ℝ) + 1) * hankelRinf c
        ≤ (6 * π) ^ 2 * (2 * c) * c ^ (-(4 / 3 : ℝ)) := by gcongr
      _ = 2 * (6 * π) ^ 2 * (c * c ^ (-(4 / 3 : ℝ))) := by ring
      _ = 2 * (6 * π) ^ 2 * c ^ (-(1 / 3 : ℝ)) := by rw [hcc]
      _ ≤ 2 * (6 * π) ^ 2 * r ^ (-(1 / 2 : ℝ)) := by gcongr
  have h_rrinf : (3 * r + 1) * hankelRinf c ≤ 4 * r ^ (-(1 / 2 : ℝ)) := by
    have h3r : 3 * r + 1 ≤ 4 * c := by linarith
    have hcc : c * c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
    calc (3 * r + 1) * hankelRinf c ≤ 4 * c * c ^ (-(4 / 3 : ℝ)) := by gcongr
      _ = 4 * c ^ (-(1 / 3 : ℝ)) := by rw [← hcc]; ring
      _ ≤ 4 * r ^ (-(1 / 2 : ℝ)) := by gcongr
  have h_invr_le : r⁻¹ ≤ r ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one r]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h_kr : ((k : ℝ) + 1) / r ≤ ((k : ℝ) + 1) * r ^ (-(1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h_invr_le (by positivity)
  have h_exp_tail : Real.exp (-(5 / 6 : ℝ) * r) ≤ (6 / 5 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
    have hadd : (5 / 6 : ℝ) * r ≤ Real.exp ((5 / 6 : ℝ) * r) := by
      linarith [Real.add_one_le_exp ((5 / 6 : ℝ) * r)]
    have hinv : Real.exp (-(5 / 6 : ℝ) * r) ≤ ((5 / 6 : ℝ) * r)⁻¹ := by
      rw [show -(5 / 6 : ℝ) * r = -((5 / 6 : ℝ) * r) by ring, Real.exp_neg]
      exact inv_anti₀ (by linarith [hr_pos]) hadd
    have hrew : ((5 / 6 : ℝ) * r)⁻¹ = (6 / 5 : ℝ) * r⁻¹ := by ring
    rw [hrew] at hinv
    exact hinv.trans (mul_le_mul_of_nonneg_left h_invr_le (by norm_num))
  -- Bound the node ℓ term
  have h_node_ell : 2 * quantC1C1 * (1 / quantC1WStar) * ℓ =
      scaleCNode * (k : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
    have hr12 : (√r)⁻¹ = r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hr_pos.le]
    unfold scaleCNode
    dsimp [ℓ]
    simp only [div_eq_mul_inv]
    rw [hr12]
    ring
  -- Bound the line `(k+1)/r` term
  have h_line_k_bd :
      4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c) +
        120 * ((k : ℝ) + 1) / r ≤
      scaleCLine * ((k : ℝ) + 1) * r ^ (-(1 / 2 : ℝ)) := by
    have h1 : 1 + 2 * langerRadius c * hankelRinf c ≤ 2 := by linarith [hArinf_one]
    have h2 : 4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c) ≤
        4 * Real.exp (6 / 5 : ℝ) * 2 * (((k : ℝ) + 1) / r) := by
      have hk_r : 0 ≤ 4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r := by positivity
      calc 4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c)
          ≤ 4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * 2 := by gcongr
        _ = 4 * Real.exp (6 / 5 : ℝ) * 2 * (((k : ℝ) + 1) / r) := by ring
    calc 4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c) +
          120 * ((k : ℝ) + 1) / r
        ≤ (4 * Real.exp (6 / 5 : ℝ) * 2 + 120) * (((k : ℝ) + 1) / r) := by
          linarith only [h2, show 120 * ((k : ℝ) + 1) / r = 120 * (((k : ℝ) + 1) / r) by ring]
      _ = scaleCLine * (((k : ℝ) + 1) / r) := rfl
      _ ≤ scaleCLine * (((k : ℝ) + 1) * r ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h_kr hC_line_nn
      _ = scaleCLine * ((k : ℝ) + 1) * r ^ (-(1 / 2 : ℝ)) := by ring
  -- Total bound on `(63/100) * (B1 + B2)`
  have hL_ge_1 : 1 ≤ hankelScaleL c R_J r u_T f :=
    hankelScaleL_ge_one (by linarith) hf hε hmass hT hu0 hu3 hr256 hr_RJ (by linarith : R_J ≤ langerRadius c)
  have h_tot_63 : (63 / 100 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r) ≤
      (scaleCNum + scaleCK * (k : ℝ) + scaleCArc * Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) *
        r ^ (-(1 / 2 : ℝ)) := by
    have hquad' : hankelBootNodes c f r ℓ k N ≤
        (∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re) +
          (scaleCArc * (Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) * r ^ (-(1 / 2 : ℝ)) +
            scaleCUnc * r ^ (-(1 / 2 : ℝ))) := by
      unfold scaleCArc scaleCUnc
      linarith only [hquad]
    have hnodes' : -(scaleCNode * (k : ℝ) * r ^ (-(1 / 2 : ℝ))) -
        (6 * π) ^ 2 * ((N : ℝ) + 1) * hankelRinf c ≤ hankelBootNodes c f r ℓ k N := by
      rw [← h_node_ell]
      linarith only [hnodes]
    have hline' : (63 / 100 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r) ≤
        -(∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re) +
          ((4 * Real.exp (6 / 5 : ℝ) * ((k : ℝ) + 1) / r * (1 + 2 * langerRadius c * hankelRinf c) +
            120 * ((k : ℝ) + 1) / r) + 72 * Real.exp (-(5 / 6 : ℝ) * r) +
            hankelLobe c + 2 * langerRadius c * hankelRinf c + (3 * r + 1) * hankelRinf c) := by
      linarith only [hline]
    have h_lobe_r : hankelLobe c ≤ 1 * r ^ (-(1 / 2 : ℝ)) := by linarith only [hlobe_le, hc13_r12]
    have h_Ar_r : 2 * langerRadius c * hankelRinf c ≤ 7 * r ^ (-(1 / 2 : ℝ)) := by linarith only [hArinf, hc23_r12]
    have h_tail_r : 72 * Real.exp (-(5 / 6 : ℝ) * r) ≤ 90 * r ^ (-(1 / 2 : ℝ)) := by
      calc 72 * Real.exp (-(5 / 6 : ℝ) * r) ≤ 72 * ((6 / 5 : ℝ) * r ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h_exp_tail (by norm_num)
        _ ≤ 90 * r ^ (-(1 / 2 : ℝ)) := by linarith only [hr12_pos]
    have hcomb := scale_combine_63 hr12_pos.le (Nat.cast_nonneg k) hC_line_nn
      hline' hquad' hnodes' h_line_k_bd h_node_rinf h_tail_r h_lobe_r h_Ar_r h_rrinf
    simpa only [mul_assoc] using hcomb
  have h_final_63 :
      (scaleCNum + scaleCK * (k : ℝ) + scaleCArc * Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) *
        r ^ (-(1 / 2 : ℝ)) ≤
      (max (max scaleCNum scaleCK) scaleCArc) *
        (1 + (k : ℝ) + Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) *
        r ^ (-(1 / 2 : ℝ)) := by
    have hm1 : scaleCNum ≤ max (max scaleCNum scaleCK) scaleCArc := (le_max_left _ _).trans (le_max_left _ _)
    have hm2 : scaleCK ≤ max (max scaleCNum scaleCK) scaleCArc := (le_max_right _ _).trans (le_max_left _ _)
    have hm3 : scaleCArc ≤ max (max scaleCNum scaleCK) scaleCArc := le_max_right _ _
    have hL_nn : 0 ≤ Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f :=
      mul_nonneg (Real.exp_pos _).le (by linarith only [hL_ge_1])
    have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h_inner : scaleCNum + scaleCK * (k : ℝ) + scaleCArc * Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f ≤
        max (max scaleCNum scaleCK) scaleCArc * (1 + (k : ℝ) + Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) := by
      have t1 : scaleCNum ≤ max (max scaleCNum scaleCK) scaleCArc * 1 := by linarith only [hm1]
      have t2 : scaleCK * (k : ℝ) ≤ max (max scaleCNum scaleCK) scaleCArc * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hm2 hk_nn
      have t3 : scaleCArc * Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f ≤
          max (max scaleCNum scaleCK) scaleCArc * (Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) := by
        rw [mul_assoc scaleCArc]
        exact mul_le_mul_of_nonneg_right hm3 hL_nn
      linarith only [t1, t2, t3]
    exact mul_le_mul_of_nonneg_right h_inner hr12_pos.le
  have h_mult : (hankelBootB1 c f r u_T + hankelBootB2 c f r) ≤
      (100 / 63 : ℝ) * ((63 / 100 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r)) := by
    have hsum_nn : 0 ≤ hankelBootB1 c f r u_T + hankelBootB2 c f r :=
      add_nonneg (hankelBootB1_nonneg hc3 hf hε hmass hT hu0 hu3 hr_pos hru (by linarith only [hr_RJ, hRJ_A]))
        (hankelBootB2_nonneg c f r)
    linarith only [hsum_nn]
  refine h_mult.trans ?_
  calc (100 / 63 : ℝ) * ((63 / 100 : ℝ) * (hankelBootB1 c f r u_T + hankelBootB2 c f r))
      ≤ (100 / 63 : ℝ) * ((max (max scaleCNum scaleCK) scaleCArc) *
          (1 + (k : ℝ) + Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) *
          r ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h_tot_63.trans h_final_63) (by norm_num)
    _ = scaleCStep * (1 + (k : ℝ) + Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f) *
          r ^ (-(1 / 2 : ℝ)) := by
        unfold scaleCStep
        simp only [mul_assoc]

/-- info: 'FormalResearch.SignUncertainty.hankel_scale_mass_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankel_scale_mass_step

end FormalResearch.SignUncertainty
