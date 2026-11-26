module

public import Mathlib
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.CtDyadicGReg
public import FormalResearch.SignUncertainty.CtDyadicStatement

/-!
# `ct:dyadic` (1) at the top scale `R_J`: the band moments `B₁ + B₂ = O(c^{-1/3})`

`constant_terms_lower.tex`, `ct:dyadic` (1), top scale `r = R_J`.  At a good radius `R ∈ [b²c^{2/3}, b²c^{2/3}+1]` (`b = 1/100`) the
Hankel bootstrap instance `hankelBootHBAt` (window lemma `hankel_yv_at`) and `teb_bootstrap_hb` give `L ≤ L♯` and hence
`B₁(R) + B₂(R) ≤ K c^{-1/3}` with `K` an absolute constant (`hankel_top_moments`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- **Top-scale band moments** (`ct:dyadic` (1) at `r = R_J`, `(ct:dyad)` at the top scale): there are `K, c₀` such that for `c ≥ c₀`, a
feasible `f` with `M[f] = 1`, `cξ(u_T) = T`, `a₁ < u_T`, `QuantC1B2Holds`, and a good radius `R ∈ [b²c^{2/3}, b²c^{2/3}+1]`,
`B₁(R) + B₂(R) ≤ K c^{-1/3}`. -/
theorem hankel_top_moments : ∃ K c₀ : ℝ, 0 ≤ K ∧ ∀ (c ε T u_T R : ℝ) (f : ℝ → ℝ), c₀ ≤ c →
    IsHankelFeasible c ε T f → (ε = 1 ∨ ε = -1) → hankelMass c f = 1 → c * hankelXi c u_T = T →
    airyZero 1 < u_T → QuantC1B2Holds (hankelPsi c f) u_T →
    (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1 →
    ctGoodRadius R →
    hankelBootB1 c f R u_T + hankelBootB2 c f R ≤ K * c ^ (-(1 / 3 : ℝ)) := by
  set P := hankelBootParams hankelWindowC one_le_hankelWindowC with hP
  obtain ⟨c₂, hc₂⟩ := Filter.eventually_atTop.1 hankel_small_eventually
  set Ls := tebLogSharp (tebCStarHB P 0) with hLs
  set K := tebCXHB P 0 * (1 + Real.log Ls) with hK
  have hCX : 0 < tebCXHB P 0 := tebCXOf_pos P (tebLambdaN_nonneg P (le_refl 0))
  have hLs1 : 1 ≤ Ls := one_le_tebLogSharp (le_max_left _ _)
  refine ⟨K, max (max 1e14 c₂) (tebC2 P), by
    have := Real.log_nonneg hLs1; rw [hK]; positivity, ?_⟩
  intro c ε T u_T R f hc hf hε hM hT ha1 hB2 hR1 hR2 hgood
  have hc14 : 1e14 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc2' : c₂ ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcT : tebC2 P ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hc3 : 3e6 ≤ c := by linarith
  have hc12 : (3 * π) ^ (12 : ℕ) ≤ c := by
    have : 3 * π ≤ 10 := by linarith [Real.pi_lt_d2]
    have h2 : (3 * π) ^ (12 : ℕ) ≤ (10 : ℝ) ^ 12 := pow_le_pow_left₀ (by positivity) this 12
    linarith
  have h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    obtain ⟨t, ht14, hct, hk4, hK8, -⟩ := hankel_window_cnum hc14
    rw [hK8]
    have : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
    norm_num at this ⊢
    linarith
  have hsm := hc₂ c hc2'
  let I := hankelBootHBAt one_le_hankelWindowC hankel_yv_at (c := c) hc14 hc3 hc12 h48 hR1 hR2 hgood hf hε hM hT ha1 hB2 hsm
  obtain ⟨hL, hIc, hIx, hIR, hIB1, hIB2⟩ := I.2
  have hcI : tebC2 P ≤ I.1.c := by rw [hIc]; exact hcT
  have hboot := teb_bootstrap_hb P I.1 hcI
  have h1 := hboot.1
  have h2 := (hboot.2 hL).1
  rw [hIc, hIB1, hIB2] at h1
  have hlog : Real.log I.1.L ≤ Real.log Ls :=
    Real.log_le_log (by linarith [I.1.hL_lb]) h2
  have hcm : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  calc _ ≤ tebCXHB P 0 * (1 + Real.log I.1.L) * c ^ (-(1 / 3 : ℝ)) := h1
    _ ≤ K * c ^ (-(1 / 3 : ℝ)) := by
      rw [hK]; gcongr

/-- info: 'FormalResearch.SignUncertainty.hankel_top_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_top_moments

/-- `‖Ψ̃(x)‖ = |Re Ψ̃(x)|` on the real axis of the Langer disc. -/
lemma hankelPsi_norm_real {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ langerRadius c) :
    ‖hankelPsi c f (x : ℂ)‖ = |hankelPsiR c f x| := by
  have him := hankelPsi_real hc f (x := x) hx
  have : hankelPsi c f (x : ℂ) = ((hankelPsiR c f x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hankelPsiR, him]
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-- **First `v`-moment of `|Ψ̃(-v)|`** (`(ct:half)`, second inequality, from the band moment): for `u_T ∈ [-3, 0]`, `0 < R ≤ r_c`,
`-R ≤ u_T`, `∫_0^R v ‖Ψ̃(-v)‖ dv ≤ R B₁(R) + 3 R² r_∞ + 3 (1 + 2 r_c r_∞)`. -/
theorem hankel_half_moment {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) :
    ∫ v in (0 : ℝ)..R, v * ‖hankelPsi c f (-(v : ℂ))‖ ≤
      R * hankelBootB1 c f R u_T + 3 * R ^ 2 * hankelRinf c + 3 * (1 + 2 * langerRadius c * hankelRinf c) := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hA := langerRadius_pos hc0
  have hmem : ∀ x ∈ Icc (-R) 0, |x| ≤ langerRadius c := fun x hx =>
    abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- change of variables
  have hcv : ∫ v in (0 : ℝ)..R, v * ‖hankelPsi c f (-(v : ℂ))‖ =
      ∫ x in (-R)..0, (-x) * |hankelPsiR c f x| := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun x : ℝ => (-x) * |hankelPsiR c f x|)
    simp only [neg_neg, neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun v hv => ?_)
    rw [uIcc_of_le hR0.le] at hv
    show v * ‖hankelPsi c f (-(v : ℂ))‖ = v * |hankelPsiR c f (-v)|
    have : -(v : ℂ) = ((-v : ℝ) : ℂ) := by push_cast; ring
    rw [this, hankelPsi_norm_real hc0 f (by rw [abs_neg, abs_of_nonneg hv.1]; linarith [hv.2])]
  rw [hcv]
  have hgc : ContinuousOn (hankelPsiR c f) (Icc (-R) 0) :=
    (continuousOn_hankelPsiR hc0 hfe).mono (fun x hx => abs_le.1 (hmem x hx))
  have habs : ContinuousOn (fun x => (-x) * |hankelPsiR c f x|) (Icc (-R) 0) :=
    (continuous_neg.continuousOn).mul hgc.abs
  have hI1 : IntervalIntegrable (fun x => (-x) * |hankelPsiR c f x|) volume (-R) u_T :=
    (habs.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩ : Icc (-R) u_T ⊆ Icc (-R) 0)).intervalIntegrable_of_Icc hRu
  have hI2 : IntervalIntegrable (fun x => (-x) * |hankelPsiR c f x|) volume u_T 0 :=
    (habs.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩ : Icc u_T 0 ⊆ Icc (-R) 0)).intervalIntegrable_of_Icc hu0
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  rw [← hsplit]
  -- band part
  have hQc : ContinuousOn (hankelPsiLead c f) (Icc (-R) u_T) :=
    (continuousOn_hankelQ hc0 hfe).mono (fun x hx => abs_le.1 (hmem x ⟨hx.1, by linarith [hx.2]⟩))
  have hint1 : IntervalIntegrable (fun x => (-x) * |hankelPsiR c f x|) volume (-R) u_T :=
    (habs.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩ : Icc (-R) u_T ⊆ Icc (-R) 0)).intervalIntegrable_of_Icc hRu
  have hint2 : IntervalIntegrable (fun x => (-x) * hankelPsiLead c f x + 3 * R * hankelRinf c) volume (-R) u_T :=
    (((continuous_neg.continuousOn).mul hQc).add continuousOn_const).intervalIntegrable_of_Icc hRu
  have hpt : ∀ x ∈ Icc (-R) u_T,
      (-x) * |hankelPsiR c f x| ≤ (-x) * hankelPsiLead c f x + 3 * R * hankelRinf c := by
    intro x hx
    have hx0 : 0 ≤ -x := by linarith [hx.2]
    have hxR : -x ≤ R := by linarith [hx.1]
    have hg := hankelBoot_psi_ge hc hf hε hM hT hu0 hu3 hR0 hRu hRA hx.1 hx.2
    have hxm : |x| ≤ langerRadius c := hmem x ⟨hx.1, by linarith [hx.2]⟩
    have hd := abs_le.1 (hankelPsiR_sub_Q_le hc5 hfe hε hM hxm)
    have habs' : |hankelPsiR c f x| ≤ hankelPsiLead c f x + 3 * hankelRinf c := by
      rw [abs_le]; constructor <;> linarith [hd.1, hd.2]
    calc (-x) * |hankelPsiR c f x| ≤ (-x) * (hankelPsiLead c f x + 3 * hankelRinf c) :=
          mul_le_mul_of_nonneg_left habs' hx0
      _ = (-x) * hankelPsiLead c f x + (-x) * (3 * hankelRinf c) := by ring
      _ ≤ (-x) * hankelPsiLead c f x + 3 * R * hankelRinf c := by
          have : (-x) * (3 * hankelRinf c) ≤ R * (3 * hankelRinf c) :=
            mul_le_mul_of_nonneg_right hxR (by positivity)
          linarith
  have hb1 := intervalIntegral.integral_mono_on hRu hint1 hint2 hpt
  have hRB1 := hankelBoot_R_mul_B1 hc0 hf hT hu hRA hR0 hRu
  have hconst : ∫ x in (-R)..u_T, ((-x) * hankelPsiLead c f x + 3 * R * hankelRinf c) =
      (∫ x in (-R)..u_T, (-x) * hankelPsiLead c f x) + (u_T - -R) * (3 * R * hankelRinf c) := by
    have hiQ : IntervalIntegrable (fun x => (-x) * hankelPsiLead c f x) volume (-R) u_T :=
      ((continuous_neg.continuousOn).mul hQc).intervalIntegrable_of_Icc hRu
    rw [intervalIntegral.integral_add hiQ intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  have hlen : (u_T - -R) * (3 * R * hankelRinf c) ≤ 3 * R ^ 2 * hankelRinf c := by
    have : u_T - -R ≤ R := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ 3 * R * hankelRinf c)]
  have hRB1' : ∫ x in (-R)..u_T, (-x) * hankelPsiLead c f x = R * hankelBootB1 c f R u_T := hRB1.symm
  -- core part
  have hbA : |(-(langerRadius c))| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hA]
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA]
  have hmass := hankel_psi_abs_mass hc5 hfe hε hM
  have hgcA : ContinuousOn (hankelPsiR c f) (Icc (-(langerRadius c)) (langerRadius c)) :=
    continuousOn_hankelPsiR hc0 hfe
  have hintA : IntervalIntegrable (fun x => |hankelPsiR c f x|) volume (-(langerRadius c)) (langerRadius c) :=
    hgcA.abs.intervalIntegrable_of_Icc (by linarith)
  have hint3 : IntervalIntegrable (fun x => |hankelPsiR c f x|) volume u_T 0 :=
    (hgcA.abs.mono (fun x hx => ⟨by linarith [hx.1, abs_le.1 hu |>.1, hR0], by linarith [hx.2, hA]⟩ :
      Icc u_T 0 ⊆ Icc (-(langerRadius c)) (langerRadius c))).intervalIntegrable_of_Icc hu0
  have hint4 : IntervalIntegrable (fun x => 3 * |hankelPsiR c f x|) volume u_T 0 := hint3.const_mul 3
  have hint5 : IntervalIntegrable (fun x => (-x) * |hankelPsiR c f x|) volume u_T 0 :=
    (habs.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩ : Icc u_T 0 ⊆ Icc (-R) 0)).intervalIntegrable_of_Icc hu0
  have hpt2 : ∀ x ∈ Icc u_T 0, (-x) * |hankelPsiR c f x| ≤ 3 * |hankelPsiR c f x| := fun x hx =>
    mul_le_mul_of_nonneg_right (by linarith [hx.1]) (abs_nonneg _)
  have hb2 := intervalIntegral.integral_mono_on hu0 hint5 hint4 hpt2
  rw [intervalIntegral.integral_const_mul] at hb2
  have hb3 : ∫ x in u_T..0, |hankelPsiR c f x| ≤
      ∫ x in (-(langerRadius c))..(langerRadius c), |hankelPsiR c f x| :=
    intervalIntegral.integral_mono_interval (by linarith [abs_le.1 hu |>.1]) hu0 (by linarith)
      (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hintA
  linarith [hb1, hconst, hRB1', hlen, hb2, hb3, hmass]

/-- info: 'FormalResearch.SignUncertainty.hankel_half_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_half_moment

/-- Eventually `c^{4/3} r_∞ ≤ 1`. -/
lemma hankelRinf_c43_small : ∀ᶠ c : ℝ in atTop, c ^ (4 / 3 : ℝ) * hankelRinf c ≤ 1 := by
  have e1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 3 : ℝ) (1 / 40000) (by norm_num)
  have := e1.const_mul (2 * |hankelTailI0|)
  rw [mul_zero] at this
  filter_upwards [this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 0] with c hc hc0
  have h1 : c ^ (4 / 3 : ℝ) * hankelRinf c ≤ 2 * |hankelTailI0| * (c ^ (5 / 3 : ℝ) * Real.exp (-(1 / 40000) * c)) := by
    unfold hankelRinf
    have e : c ^ (4 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (5 / 3 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
    have e2 : Real.exp (-(c / 40000)) = Real.exp (-(1 / 40000) * c) := by congr 1; ring
    rw [e2]
    calc c ^ (4 / 3 : ℝ) * (2 * hankelTailI0 * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 40000) * c))
        = 2 * hankelTailI0 * (c ^ (5 / 3 : ℝ) * Real.exp (-(1 / 40000) * c)) := by rw [← e]; ring
      _ ≤ _ := by
        have : 0 ≤ c ^ (5 / 3 : ℝ) * Real.exp (-(1 / 40000) * c) := by positivity
        exact mul_le_mul_of_nonneg_right (by nlinarith [le_abs_self hankelTailI0, abs_nonneg hankelTailI0]) this
  exact h1.trans hc

/-- Algebra of the `(ct:cov)` shape: `L e X^{-1/2} N^{-5/4} (X/√N)⁻¹ = L e X^{-3/2} N^{-3/4}`. -/
lemma cov_shape_eq {L e X N : ℝ} (hX : 0 < X) (hN : 0 < N) :
    L * e * X ^ (-(1 / 2 : ℝ)) * N ^ (-(5 / 4 : ℝ)) * (X / Real.sqrt N)⁻¹ =
      L * e * X ^ (-(3 / 2 : ℝ)) * N ^ (-(3 / 4 : ℝ)) := by
  have h1 : X ^ (-(3 / 2 : ℝ)) = X ^ (-(1 / 2 : ℝ)) * X⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hX]; norm_num
  have h2 : N ^ (-(3 / 4 : ℝ)) = N ^ (-(5 / 4 : ℝ)) * Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]; norm_num
  rw [h1, h2, inv_div]
  field_simp

/-- `R^{3/4} ≤ √c / 100` for `R ≤ 2·10⁻⁴ c^{2/3}`, `c ≥ 10¹⁴` (numerics of the angular range). -/
lemma rpow_three_quarters_le {c R : ℝ} (hc : 1e14 ≤ c) (hR0 : 0 ≤ R)
    (hR : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1) : R ^ (3 / 4 : ℝ) ≤ Real.sqrt c / 100 := by
  obtain ⟨t, ht14, hct, -, hK8, -⟩ := hankel_window_cnum hc
  have hsqc : Real.sqrt c = t ^ 6 := by
    rw [hct, show t ^ 12 = (t ^ 6) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have ht0 : 0 < t := by linarith
  have ht8 : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
  rw [hsqc]
  rw [hK8] at hR
  have hR3 : R ^ 3 ≤ (t ^ 6 / 100) ^ 4 := by
    have h1 : R ≤ t ^ 8 / 5000 := by norm_num at ht8; nlinarith
    have h2 : R ^ 3 ≤ (t ^ 8 / 5000) ^ 3 := pow_le_pow_left₀ hR0 h1 3
    have h3 : (t ^ 8 / 5000) ^ 3 ≤ (t ^ 6 / 100) ^ 4 := by
      have : (t ^ 6 / 100) ^ 4 - (t ^ 8 / 5000) ^ 3 = t ^ 24 * (1 / 1e8 - 1 / 1.25e11) := by ring
      have h24 : 0 < t ^ 24 := pow_pos ht0 24
      nlinarith
    exact h2.trans h3
  have hpow : (R ^ (3 / 4 : ℝ)) ^ 4 = R ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0]; norm_num
  have hnn : 0 ≤ R ^ (3 / 4 : ℝ) := Real.rpow_nonneg hR0 _
  exact le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) (by rw [hpow]; exact hR3)

/-- **`CtBandData c₁` for small `c₁`** (`ct:dyadic` (1), the two outputs at the top radius `R_J` used by (2)): for `0 < c₁ ≤ 1/900`, a
good radius `R_J ∈ [b²c^{2/3}, b²c^{2/3}+1]`, `A = √R_J`, satisfies `9c₁c^{1/3} ≤ A`, `A² < r_c`, `(ct:cov)` on `|ũ| = R_J` for
`sin φ ≥ 10³ R_J^{-3/4} (log c)^{1/2}` with `L♯♯ = C_fb (K + 1)` independent of `c`, and `∫_0^{R_J} v|Ψ̃(-v)| dv ≤ (K+8) c^{1/3}`.
Proof: window lemma `hankel_cov_window` (band reduction `hankel_band_reduction_pos` for all `cos ψ > 0`) with `L' = C_fb(c^{1/3}(B₁+B₂)+1)`,
and `B₁ + B₂ ≤ K c^{-1/3}` from the top-scale bootstrap (`hankel_top_moments`); half-moment from `hankel_half_moment`.  No multiscale
bootstrap is needed for these two outputs (the scale-`r` induction of `ct:dyadic` (1) is needed only for `(ct:dyad)` at `r < R_J` and the
first inequality of `(ct:half)`). -/
theorem ctBandData_small {c₁ : ℝ} (hc₁ : 0 < c₁) (hsmall : c₁ ≤ 1 / 900) : CtBandData c₁ := by
  obtain ⟨K, cK, hK0, hK⟩ := hankel_top_moments
  obtain ⟨c₁q, hc₁q, hquant⟩ := hankel_quantC1_of_feasible
  obtain ⟨c₂, hc₂⟩ := Filter.eventually_atTop.1 hankel_small_eventually
  obtain ⟨c₃, hc₃⟩ := Filter.eventually_atTop.1 hankelRinf_c43_small
  have hCw := one_le_hankelWindowC
  refine ⟨hankelWindowC * (K + 1), 1000, K + 8, max (max (max 1e14 cK) (max c₁q c₂)) c₃, by positivity,
    by norm_num, by linarith, ?_⟩
  intro ε hε c hc T f hf hmass hviol _hgap
  have hc14 : 1e14 ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hcK : cK ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hcq : c₁q ≤ c := ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))).trans hc
  have hc2' : c₂ ≤ c := ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))).trans hc
  have hc3' : c₃ ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hc3 : 3e6 ≤ c := by linarith
  obtain ⟨u_T, ha1, -, hT, hB2⟩ := hquant c ε T f hcq hf hε hmass hviol
  obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1 hB2
  have h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    obtain ⟨t, ht14, hct, hk4, hK8, -⟩ := hankel_window_cnum hc14
    rw [hK8]
    have : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
    norm_num at this ⊢
    linarith
  obtain ⟨R, hR1, hR2, hRlow⟩ := hankelBoot_good_circle_window ((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) (by linarith)
  have hgood : ctGoodRadius R := hRlow
  obtain ⟨hR48, hRA1, -, hRc⟩ := hankelBoot_radius_facts hc3 h48 hR1 hR2
  have hR0 : 0 < R := by linarith
  have hcs : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hBK := hK c ε T u_T R f hcK hf hε hmass hT ha1 hB2 hR1 hR2 hgood
  have hLL : hankelWindowC * (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + 1) ≤
      hankelWindowC * (K + 1) := by
    have : c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) ≤ K := by
      calc _ ≤ c ^ (1 / 3 : ℝ) * (K * c ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hBK hcs.le
        _ = K := by
          rw [← mul_assoc, mul_comm (c ^ (1 / 3 : ℝ)) K, mul_assoc, ← Real.rpow_add hc0]; norm_num
    gcongr
  refine ⟨Real.sqrt R, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (c ^ (1 / 3 : ℝ) / 100) ^ 2 ≤ R := by
      have : (c ^ (1 / 3 : ℝ) / 100) ^ 2 = (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num; ring
      rw [this]; exact hR1
    have h2 : c ^ (1 / 3 : ℝ) / 100 ≤ Real.sqrt R := Real.le_sqrt_of_sq_le h1
    nlinarith [mul_le_mul_of_nonneg_right hsmall hcs.le]
  · rw [Real.sq_sqrt hR0.le]; linarith
  · rw [Real.sq_sqrt hR0.le]; exact hgood
  · rw [Real.sq_sqrt hR0.le]
    intro u him hn hpos hang
    have hN : 0 < ‖u‖ := by rw [hn]; exact hR0
    have hsq : 0 < Real.sqrt ‖u‖ := Real.sqrt_pos.2 hN
    have hlog1 : 1 ≤ Real.log c := by
      have : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log c := Real.log_le_log (Real.exp_pos 1) (by linarith)
    set X := (u ^ (1 / 2 : ℂ)).re with hXd
    set θ := X / Real.sqrt ‖u‖ with hθd
    have hRp : 0 < R ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hR0 _
    have hR34 := rpow_three_quarters_le hc14 hR0.le hR2
    have hθge : 1000 * R ^ (-(3 / 4 : ℝ)) ≤ θ := by
      have h1 : 1 ≤ Real.sqrt (Real.log c) := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlog1
      have h2 : 0 ≤ 1000 * R ^ (-(3 / 4 : ℝ)) := by positivity
      calc 1000 * R ^ (-(3 / 4 : ℝ)) = 1000 * R ^ (-(3 / 4 : ℝ)) * 1 := by ring
        _ ≤ 1000 * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) := mul_le_mul_of_nonneg_left h1 h2
        _ ≤ θ := hang
    have hθ : 1e5 ≤ θ * Real.sqrt c := by
      have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
      have h1 : 100 ≤ R ^ (-(3 / 4 : ℝ)) * Real.sqrt c := by
        rw [Real.rpow_neg hR0.le, inv_mul_eq_div, le_div_iff₀ hRp]
        linarith
      calc (1e5 : ℝ) = 1000 * 100 := by norm_num
        _ ≤ 1000 * (R ^ (-(3 / 4 : ℝ)) * Real.sqrt c) := by linarith
        _ = (1000 * R ^ (-(3 / 4 : ℝ))) * Real.sqrt c := by ring
        _ ≤ θ * Real.sqrt c := mul_le_mul_of_nonneg_right hθge hsc.le
    have hX : θ * Real.sqrt ‖u‖ ≤ X := by rw [hθd]; field_simp; exact le_rfl
    have hw := hankel_cov_window hc14 hf hε hmass hT hu0 hu3 hR1 hR2 hθ him
      (by rw [hn]; linarith) (by rw [hn]; linarith) hX
    rw [cov_shape_eq hpos hN]
    refine hw.trans ?_
    have h0 : 0 ≤ airyEnv u * X ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
      have := airyEnv_pos u
      positivity
    calc _ = hankelWindowC * (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + 1) *
          (airyEnv u * X ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) := by ring
      _ ≤ hankelWindowC * (K + 1) * (airyEnv u * X ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_right hLL h0
      _ = _ := by ring
  · rw [Real.sq_sqrt hR0.le]
    have hRu : -R ≤ u_T := by linarith
    have hRA : R ≤ langerRadius c := by linarith
    have hh := hankel_half_moment hc3 hf hε hmass hT hu0 hu3 hR0 hRu hRA
    have hs3 := hc₃ c hc3'
    have hs2 := hc₂ c hc2'
    have hRsq : R ^ 2 ≤ c ^ (4 / 3 : ℝ) := by
      have e : (c ^ (2 / 3 : ℝ)) ^ 2 = c ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      exact (pow_le_pow_left₀ hR0.le hRc 2).trans_eq e
    have hr : 0 ≤ hankelRinf c := by
      have := hankelRinf_nonneg (by linarith : (5000 : ℝ) ≤ c) hf.toIsHankelEigenfn hε hmass
      exact this
    have h1 : R * hankelBootB1 c f R u_T ≤ K * c ^ (1 / 3 : ℝ) := by
      have hB1le : hankelBootB1 c f R u_T ≤ K * c ^ (-(1 / 3 : ℝ)) := by
        have := hankelBootB2_nonneg c f R
        linarith
      have hcc : R * (K * c ^ (-(1 / 3 : ℝ))) ≤ c ^ (2 / 3 : ℝ) * (K * c ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_right hRc (by positivity)
      have : c ^ (2 / 3 : ℝ) * (K * c ^ (-(1 / 3 : ℝ))) = K * c ^ (1 / 3 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hc0]; norm_num
      nlinarith [mul_le_mul_of_nonneg_left hB1le hR0.le]
    have h2 : 3 * R ^ 2 * hankelRinf c ≤ 3 := by
      nlinarith [mul_le_mul_of_nonneg_right hRsq hr]
    have h3 : 2 * langerRadius c * hankelRinf c ≤ 1 / 2 := by linarith
    have hc13 : 1 ≤ c ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    show ∫ v in (0 : ℝ)..R, v * ‖hankelPsi c f (-(v : ℂ))‖ ≤ (K + 8) * c ^ (1 / 3 : ℝ)
    have e : (K + 8) * c ^ (1 / 3 : ℝ) = K * c ^ (1 / 3 : ℝ) + 8 * c ^ (1 / 3 : ℝ) := by ring
    linarith [hh, h1, h2, h3, hc13]

/-- info: 'FormalResearch.SignUncertainty.ctBandData_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctBandData_small

/-- **`ct:dyadic` (2) without the band hypothesis** (`CtDyadicRadiusStatement` for every small `c₁`): `ct_dyadic_radius_small` with
`CtBandData c₁` discharged by `ctBandData_small` (and `CtChartComplex c₁` by `ct_chart_complex`). -/
theorem ct_dyadic_radius_proved : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtDyadicRadiusStatement c₁ := by
  obtain ⟨c₁₀, h0, h⟩ := ct_dyadic_radius_small
  exact ⟨min c₁₀ (1 / 900), lt_min h0 (by norm_num), fun c₁ hc₁ hle =>
    h c₁ hc₁ (hle.trans (min_le_left _ _)) (ctBandData_small hc₁ (hle.trans (min_le_right _ _)))⟩

/-- info: 'FormalResearch.SignUncertainty.ct_dyadic_radius_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_dyadic_radius_proved

end FormalResearch.SignUncertainty
