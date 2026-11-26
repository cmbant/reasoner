module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicChartReal
public import FormalResearch.SignUncertainty.CtDyadicUhat

/-!
# `ct:dyadic` (4), `ct:taper-harnack` (c): the chart facts `TaperChartInputs` for the concrete objects

`constant_terms_lower.tex`, `ct:dyadic` (4) and `ct:taper-harnack` (c): for the Lean Langer chart `hankelXi` and the concrete
`û = ctUhat`, `ctTaperV ε c L = -û(ũ(ξ(L)))`, `R' = -φ_c(-R)`, `Λ = L(ξ(-R'))`:

* `ctUtildeXi_band`: for `0 ≤ L ≤ log(π²ξ(-r))`, `r ≤ A`: `ũ(ξ(L)) = -K g(L)` with `K g(L) ≤ r` (`g(L) = -y(e^L - 1)`);
* `hankel_band_edge`: `Λ > 0`, `e^Λ - 1 ≤ 5·10⁻⁴`, `K g(Λ) = r`;
* `exists_deriv_ratio`: if `f > 0` on `(0, Λ]` has `f' ≥ 0` and `L f' ≤ 2f` then `f(L') ≤ (L'/L)² f(L)`;
* **`taperBand_of_window`**: `TaperBand` (`TaperChartInputs ε c R 2` and `v' ≤ v ≤ v' + 1/2`) from the `ψ_ε`-window (`PsiWin`), `c ≥ 3`, `2M ≤ c`, `λM ≤ 1/2`,
  `1 ≤ R`, `[-R, 0)` in the window and `R ≤ A`, and the named input `UhatInjOn` (bijectivity of `û`, `ct:cfu`);
* **`taperBand`, `taperChartInputs`**: the same, with the regime as `∃ ρ₁ c₀`: for `c ≥ c₀` and `1 ≤ R ≤ ρ₁ c^{2/3}`.

The logarithmic-derivative constant is `A_v = 2` (the chart gives `L g' ≤ 1.01 g`, `û' ≤ 3/2`); the paper's
`A_v = (1 + o(1))A_Φ ≤ 1.53` is for the larger band `L ≤ Λ₂`, here `L ≤ 5·10⁻⁴`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `v'(L) = -ũ(ξ(L)) = K g(L)`. -/
noncomputable def ctVprime (c L : ℝ) : ℝ := langerScale c * ctChartG L

/-- **`ũ(ξ(L)) = -K g(L)`** on the part of the band reached from `[-r, 0]`, and `K g(L) ≤ r`. -/
lemma ctUtildeXi_band {c r L : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr : r ≤ langerRadius c) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log (Real.pi ^ 2 * hankelXi c (-r))) :
    ctUtildeXi c (Real.exp L / π ^ 2) = -ctVprime c L ∧ ctVprime c L ≤ r := by
  obtain ⟨x, hx, hxe⟩ := exists_hankelXi_eq hc hr0 hr hL0 hL
  have hxA : x ∈ Icc (-(langerRadius c)) 0 := ⟨by linarith [hx.1], hx.2⟩
  have h1 := ctUtildeXi_eq_hankelBandU hc ⟨x, hxA, hxe⟩
  have hxabs : |x| ≤ langerRadius c := abs_le.2 ⟨hxA.1, by linarith [hxA.2, langerRadius_pos hc]⟩
  have h2 : hankelBandU c (Real.exp L / π ^ 2) = x := by
    rw [← hxe]; exact hankelBandU_hankelXi hc hxabs
  have h3 : hankelBandU c (Real.exp L / π ^ 2) = -ctVprime c L := by
    rw [hankelBandU_eq]
    have : Real.pi ^ 2 * (Real.exp L / π ^ 2) - 1 = Real.exp L - 1 := by
      have : Real.pi ^ 2 ≠ 0 := by positivity
      field_simp
    rw [this]
    unfold ctVprime ctChartG; ring
  refine ⟨by rw [h1, h3], ?_⟩
  have : -ctVprime c L = x := by rw [← h3, h2]
  linarith [hx.1]

/-- The edge of the band: for `0 < r ≤ A`, `Λ = log(π²ξ(-r)) > 0`, `e^Λ - 1 ≤ 5·10⁻⁴` and `K g(Λ) = r`. -/
lemma hankel_band_edge {c r : ℝ} (hc : 0 < c) (hr0 : 0 < r) (hr : r ≤ langerRadius c) :
    0 < Real.log (Real.pi ^ 2 * hankelXi c (-r)) ∧
      Real.exp (Real.log (Real.pi ^ 2 * hankelXi c (-r))) - 1 ≤ 5e-4 ∧
      ctVprime c (Real.log (Real.pi ^ 2 * hankelXi c (-r))) = r := by
  have habs : |(-r)| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hr0]; exact hr
  obtain ⟨hw0, hw1, -⟩ := hankelXi_w_bounds hc habs (by linarith)
  set w := Real.pi ^ 2 * hankelXi c (-r) - 1 with hw
  have hU := hankelBandU_hankelXi hc habs
  have hKpos := langerScale_pos hc
  have hUe : langerScale c * ctYR w = -r := by rw [← hU, hankelBandU_eq]
  have hwpos : 0 < w := by
    rcases hw0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ctYR 0 = 0 := by
        have := ctYR_add_le (le_refl (0 : ℝ)) (by norm_num)
        simpa using this
      rw [← h, h0] at hUe
      linarith
  have hpos : 0 < Real.pi ^ 2 * hankelXi c (-r) := by linarith
  have hexp : Real.exp (Real.log (Real.pi ^ 2 * hankelXi c (-r))) = 1 + w := by
    rw [Real.exp_log hpos]; linarith
  refine ⟨Real.log_pos (by linarith), by rw [hexp]; linarith, ?_⟩
  unfold ctVprime ctChartG
  rw [hexp, show 1 + w - 1 = w by ring]
  linarith

/-- If `f > 0` on `(0, Λ]` with `f' ≥ 0` and `L f'(L) ≤ 2 f(L)`, then `f` is monotone and `f(L') ≤ (L'/L)² f(L)`. -/
lemma exists_deriv_ratio {f f' : ℝ → ℝ} {Λ : ℝ} (hd : ∀ L ∈ Ioc 0 Λ, HasDerivAt f (f' L) L)
    (hnn : ∀ L ∈ Ioc 0 Λ, 0 ≤ f' L) (hlog : ∀ L ∈ Ioc 0 Λ, L * f' L ≤ 2 * f L) {L L' : ℝ} (hL : 0 < L)
    (hLL : L ≤ L') (hL' : L' ≤ Λ) : f L ≤ f L' ∧ f L' ≤ (L' / L) ^ (2 : ℝ) * f L := by
  have hsub : Icc L L' ⊆ Ioc 0 Λ := fun x hx => ⟨lt_of_lt_of_le hL hx.1, hx.2.trans hL'⟩
  have hcont : ContinuousOn f (Icc L L') := fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt
  have hint : interior (Icc L L') ⊆ Ioc 0 Λ := interior_subset.trans hsub
  constructor
  · exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc L L') hcont
      (fun x hx => (hd x (hint hx)).hasDerivWithinAt) (fun x hx => hnn x (hint hx))
      ⟨le_rfl, hLL⟩ ⟨hLL, le_rfl⟩ hLL
  · have hpos : ∀ x ∈ Icc L L', 0 < x := fun x hx => lt_of_lt_of_le hL hx.1
    have hcont2 : ContinuousOn (fun x => f x / x ^ 2) (Icc L L') :=
      hcont.div (continuousOn_pow 2) (fun x hx => (pow_pos (hpos x hx) 2).ne')
    have hanti : AntitoneOn (fun x => f x / x ^ 2) (Icc L L') := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc L L') hcont2
        (f' := fun x => (f' x * x ^ 2 - f x * (2 * x)) / (x ^ 2) ^ 2) (fun x hx => ?_) (fun x hx => ?_)
      · have hx' := hint hx
        have hxp : 0 < x := hx'.1
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
        exact ((hd x hx').div h2 (pow_pos hxp 2).ne').hasDerivWithinAt
      · have hx' := hint hx
        have hxp : 0 < x := hx'.1
        apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
        have := hlog x hx'
        nlinarith [mul_le_mul_of_nonneg_left this hxp.le]
    have h := hanti ⟨le_rfl, hLL⟩ ⟨hLL, le_rfl⟩ hLL
    simp only at h
    have hL'p : 0 < L' := lt_of_lt_of_le hL hLL
    rw [div_le_div_iff₀ (pow_pos hL'p 2) (pow_pos hL 2)] at h
    rw [Real.rpow_two, div_pow]
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hL 2)]
    linarith

/-- `1 ≤ log c` for `c ≥ 3`. -/
lemma one_le_log_of_three_le {c : ℝ} (hc : 3 ≤ c) : 1 ≤ Real.log c := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- **The taper band**: `TaperChartInputs` together with the comparison `v' ≤ v ≤ v' + 1/2` of the Langer band variable
`v'(L) = -ũ(ξ(L)) = K g(L)` (`ctVprime`) with `v(L) = -û(-v')` on `0 < L ≤ Λ` (`ψ_ε < 0` and `λM ≤ 1/2`), `v' ≤ R' ≤ R`, and
`R - 1/2 ≤ R' ≤ R`, `e^Λ - 1 ≤ 5·10⁻⁴` and `R' ≤ 1.0025 K Λ` (so `Λ ≳ R/c^{2/3}`).  This is what the pointwise estimates of `ct:Bj-pointwise` (f) use. -/
structure TaperBand (ε c R : ℝ) : Prop where
  inputs : TaperChartInputs ε c R 2
  vp_le_v : ∀ L, 0 < L → L ≤ ctTaperLam ε c R → ctVprime c L ≤ ctTaperV ε c L
  v_le : ∀ L, 0 < L → L ≤ ctTaperLam ε c R → ctTaperV ε c L ≤ ctVprime c L + 1 / 2
  vp_le_R : ∀ L, 0 < L → L ≤ ctTaperLam ε c R → ctVprime c L ≤ ctRprime ε c R
  Rprime_ge : R - 1 / 2 ≤ ctRprime ε c R
  Rprime_le : ctRprime ε c R ≤ R
  Lam_le_small : Real.exp (ctTaperLam ε c R) - 1 ≤ 5e-4
  Rprime_le_Lam : ctRprime ε c R ≤ 1.0025 * langerScale c * ctTaperLam ε c R

/-- **`TaperBand` from the `ψ_ε`-window** (`ct:dyadic` (4), `ct:taper-harnack` (c), first half), with `A_v = 2`.
Hypotheses: the window facts of `ctPsi_window` (`PsiWin ε ρ M`: `ψ_ε < 0`, `|ψ_ε|, |ψ_ε'| ≤ M` on `(-ρ, 0)`), `c ≥ 3`,
`2M ≤ c`, `λM ≤ 1/2` (`λ = 2^{-2/3}c^{-1/3}`), `1 ≤ R`, `[-R, 0)` inside the window (`μ R < ρ`, `μ = 2^{2/3}c^{-2/3}`) and in the
Langer disc (`R ≤ A`), and the named input `UhatInjOn ε c` (bijectivity of `û`, `ct:cfu`). -/
theorem taperBand_of_window {ε c R ρ M : ℝ} (hW : PsiWin ε ρ M) (hc3 : 3 ≤ c) (hcM : 2 * M ≤ c)
    (hlam : ctLam c * M ≤ 1 / 2) (hR1 : 1 ≤ R) (hRw : -ρ < ctMu c * (-R)) (hRA : R ≤ langerRadius c)
    (hinj : UhatInjOn ε c) : TaperBand ε c R := by
  have hc : 0 < c := by linarith
  have hK := langerScale_pos hc
  have hmu := ctMu_pos hc
  obtain ⟨u, hu, hv⟩ := exists_ctUhat_eq hW hc hlam hR1 hRw
  have hphi := ctPhi_eq hinj hRA hu hv
  have hr_eq : ctRprime ε c R = -u := by
    show -ctPhi ε c (-R) = -u
    rw [hphi]
  have hr0 : 0 < ctRprime ε c R := by rw [hr_eq]; linarith [hu.2]
  have hrR : ctRprime ε c R ≤ R := by rw [hr_eq]; linarith [hu.1]
  have hrA : ctRprime ε c R ≤ langerRadius c := hrR.trans hRA
  obtain ⟨hE1, hE2, hE3⟩ := hankel_band_edge hc hr0 hrA
  have hLam : ctTaperLam ε c R = Real.log (Real.pi ^ 2 * hankelXi c (-(ctRprime ε c R))) := rfl
  set r := ctRprime ε c R with hrdef
  set Λ := ctTaperLam ε c R with hΛ
  have hexpL : ∀ L ∈ Ioc 0 Λ, Real.exp L - 1 ≤ 5e-4 := by
    intro L hL
    have := Real.exp_le_exp.2 hL.2
    rw [hLam] at this
    linarith
  -- the band formulas on `(0, Λ]`
  have key : ∀ L ∈ Ioc 0 Λ, ctTaperV ε c L = -ctUhat ε c (-(ctVprime c L)) ∧ 0 < ctVprime c L ∧
      ctVprime c L ≤ r := by
    intro L hL
    obtain ⟨h1, h2⟩ := ctUtildeXi_band hc hr0.le hrA hL.1.le (by rw [← hLam]; exact hL.2)
    refine ⟨by unfold ctTaperV; rw [h1], ?_, h2⟩
    exact mul_pos hK (ctChartG_pos hL.1 (hexpL L hL))
  have hwin : ∀ L ∈ Ioc 0 Λ, -ρ < ctMu c * (-(ctVprime c L)) := by
    intro L hL
    have := (key L hL).2.2
    have h2 : ctMu c * (-R) ≤ ctMu c * (-(ctVprime c L)) :=
      mul_le_mul_of_nonneg_left (by linarith) hmu.le
    linarith
  let D : ℝ → ℝ := fun L => 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * (-(ctVprime c L)))
  let V' : ℝ → ℝ := fun L => langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L) * D L
  have hVd : ∀ L ∈ Ioc 0 Λ, HasDerivAt (fun L => -ctUhat ε c (-(ctVprime c L))) (V' L) L := by
    intro L hL
    have hg := ctChartG_hasDerivAt hL.1.le (hexpL L hL)
    have h1 : HasDerivAt (fun L => -(ctVprime c L)) (-(langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L))) L :=
      (hg.const_mul (langerScale c)).neg
    have hU := ctUhat_hasDerivAt hW hc (u := -(ctVprime c L)) (by linarith [(key L hL).2.1]) (hwin L hL)
    have h2 := (hU.comp L h1).neg
    refine h2.congr_deriv ?_
    simp only [V', D]; ring
  have hDb : ∀ L ∈ Ioc 0 Λ, 1 / 2 ≤ D L ∧ D L ≤ 3 / 2 := fun L hL =>
    ctUhat_deriv_bounds hW hc hcM (u := -(ctVprime c L)) (by linarith [(key L hL).2.1]) (hwin L hL)
  have hVge : ∀ L ∈ Ioc 0 Λ, ctVprime c L ≤ -ctUhat ε c (-(ctVprime c L)) := by
    intro L hL
    have := ctUhat_lt hW hc (u := -(ctVprime c L)) (by linarith [(key L hL).2.1]) (hwin L hL)
    linarith
  have hnn : ∀ L ∈ Ioc 0 Λ, 0 ≤ V' L := by
    intro L hL
    have hgd := (ctChartG_deriv_bounds hL.1.le (hexpL L hL)).1
    have he := Real.exp_pos L
    have : 0 ≤ langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L) := by
      apply mul_nonneg hK.le; nlinarith
    exact mul_nonneg this (by linarith [(hDb L hL).1])
  have hlog : ∀ L ∈ Ioc 0 Λ, L * V' L ≤ 2 * -ctUhat ε c (-(ctVprime c L)) := by
    intro L hL
    have h1 := ctChartG_log_deriv hL.1 (hexpL L hL)
    have h2 := hVge L hL
    have hgd := (ctChartG_deriv_bounds hL.1.le (hexpL L hL)).1
    have he := Real.exp_pos L
    have hD3 := (hDb L hL).2
    have hKg : L * (langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L)) ≤ 1.01 * ctVprime c L := by
      have := mul_le_mul_of_nonneg_left h1 hK.le
      unfold ctVprime
      nlinarith
    have hpos := (key L hL).2.1
    have hq : 0 ≤ L * (langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L)) := by
      apply mul_nonneg hL.1.le; apply mul_nonneg hK.le; nlinarith
    calc L * V' L = (L * (langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L))) * D L := by simp only [V']; ring
      _ ≤ (1.01 * ctVprime c L) * (3 / 2) := mul_le_mul hKg hD3 (by linarith [(hDb L hL).1]) (by positivity)
      _ ≤ 2 * -ctUhat ε c (-(ctVprime c L)) := by nlinarith
  have hrat := fun {L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') (hL' : L' ≤ Λ) =>
    exists_deriv_ratio (f := fun L => -ctUhat ε c (-(ctVprime c L))) (f' := V') (Λ := Λ) hVd hnn hlog hL hLL hL'
  rw [← hLam] at hE1 hE2 hE3
  have hMb : ∀ L ∈ Ioc 0 Λ, -ctUhat ε c (-(ctVprime c L)) ≤ ctVprime c L + 1 / 2 := by
    intro L hL
    have := abs_ctUhat_sub_le hW hc (u := -(ctVprime c L)) (by linarith [(key L hL).2.1]) (hwin L hL)
    have h2 := (abs_le.1 this).1
    linarith
  have hRr : R - 1 / 2 ≤ r := by
    rw [hr_eq]
    have := abs_ctUhat_sub_le hW hc (u := u) (by linarith [hu.2]) (by
      have := mul_le_mul_of_nonneg_left hu.1 hmu.le
      linarith)
    have h2 := (abs_le.1 this).1
    rw [hv] at h2
    linarith
  have hin : TaperChartInputs ε c R 2 := by
    refine ⟨by linarith, by norm_num, hE1, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : Λ ≤ Real.exp Λ - 1 := by linarith [Real.add_one_le_exp Λ]
      have h2 : (1 : ℝ) ≤ Real.log (Real.pi ^ 2 * Real.log c / 2) := by
        rw [Real.le_log_iff_exp_le (by have := one_le_log_of_three_le hc3; positivity)]
        have := one_le_log_of_three_le hc3
        have hp : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        nlinarith [Real.exp_one_lt_d9]
      linarith
    · intro L hL hLΛ
      obtain ⟨h1, h2, -⟩ := key L ⟨hL, hLΛ⟩
      rw [h1]
      linarith [hVge L ⟨hL, hLΛ⟩]
    · intro L L' hL hLL hL'
      obtain ⟨h1, -, -⟩ := key L ⟨hL, hLL.trans hL'⟩
      obtain ⟨h2, -, -⟩ := key L' ⟨hL.trans_le hLL, hL'⟩
      rw [h1, h2]
      exact (hrat hL hLL hL').1
    · intro L L' hL hLL hL'
      obtain ⟨h1, -, -⟩ := key L ⟨hL, hLL.trans hL'⟩
      obtain ⟨h2, -, -⟩ := key L' ⟨hL.trans_le hLL, hL'⟩
      rw [h1, h2]
      exact (hrat hL hLL hL').2
    · obtain ⟨h1, -, -⟩ := key Λ ⟨hE1, le_rfl⟩
      rw [h1, hE3]
      have : -r = u := by rw [hr_eq]; ring
      rw [this, hv]
      simp
  have hRL : r ≤ 1.0025 * langerScale c * Λ := by
    have hg := (ctChartG_bounds hE1.le hE2).2.1
    have : ctVprime c Λ ≤ langerScale c * (1.0025 * Λ) := mul_le_mul_of_nonneg_left hg hK.le
    rw [hE3] at this
    linarith
  exact ⟨hin, fun L hL hLΛ => by rw [(key L ⟨hL, hLΛ⟩).1]; exact hVge L ⟨hL, hLΛ⟩,
    fun L hL hLΛ => by rw [(key L ⟨hL, hLΛ⟩).1]; exact hMb L ⟨hL, hLΛ⟩,
    fun L hL hLΛ => (key L ⟨hL, hLΛ⟩).2.2, hRr, hrR, hE2, hRL⟩

lemma ctLam_le {c : ℝ} (hc : 0 < c) : ctLam c ≤ (c ^ (1 / 3 : ℝ))⁻¹ := by
  unfold ctLam
  have h2 : (2 : ℝ) ^ (-(2 / 3) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  rw [Real.rpow_neg hc.le]
  calc (2 : ℝ) ^ (-(2 / 3) : ℝ) * (c ^ (1 / 3 : ℝ))⁻¹ ≤ 1 * (c ^ (1 / 3 : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := one_mul _

lemma rpow_third_ge {c M : ℝ} (hM : 0 ≤ M) (hc : (2 * M + 1) ^ 3 ≤ c) : 2 * M + 1 ≤ c ^ (1 / 3 : ℝ) := by
  have hx : 0 ≤ 2 * M + 1 := by linarith
  have := Real.rpow_le_rpow (by positivity) hc (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have e : ((2 * M + 1) ^ 3) ^ (1 / 3 : ℝ) = 2 * M + 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  rwa [e] at this

/-- **`TaperBand` (hence `TaperChartInputs ε c R 2`) in the paper's regime** (`ct:dyadic` (4), `ct:cfu`): there are `ρ₁ > 0` and
`c₀ ≥ 3` (the paper's "`c` large" and "`c₁` small": `R ≤ 4c₁²c^{2/3}` with `4c₁² ≤ ρ₁`) such that for `c ≥ c₀` and every radius
`1 ≤ R ≤ ρ₁ c^{2/3}`, the concrete taper `v = -û∘ũ∘ξ` satisfies the chart inputs of `ct:taper-harnack` (c) with `A_v = 2`, given the
named input `UhatInjOn ε c` (bijectivity of `û` on the Langer disc, `ct:cfu`). -/
theorem taperBand {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ ρ₁ c₀ : ℝ, 0 < ρ₁ ∧ 3 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ R : ℝ, 1 ≤ R → R ≤ ρ₁ * c ^ (2 / 3 : ℝ) →
      UhatInjOn ε c → TaperBand ε c R := by
  obtain ⟨ρ, M, hρ, hM, hwin⟩ := ctPsi_window hε
  have hW : PsiWin ε ρ M := ⟨hρ, hM, hwin⟩
  have hκ := langerKappa_pos
  refine ⟨min (ρ / 4) (langerKappa * 4.94e-4), max 3 ((2 * M + 1) ^ 3),
    lt_min (by positivity) (by positivity), le_max_left _ _, ?_⟩
  intro c hcc R hR1 hR hinj
  have hc3 : 3 ≤ c := (le_max_left _ _).trans hcc
  have hcM3 : (2 * M + 1) ^ 3 ≤ c := (le_max_right _ _).trans hcc
  have hc : 0 < c := by linarith
  have hM1 : 2 * M + 1 ≤ c ^ (1 / 3 : ℝ) := rpow_third_ge hM hcM3
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hcM : 2 * M ≤ c := by
    have : 2 * M + 1 ≤ (2 * M + 1) ^ 3 := by
      have h1 : 1 ≤ 2 * M + 1 := by linarith
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * M) (by linarith : (0 : ℝ) ≤ 2 * M + 1)]
    linarith
  have hlam : ctLam c * M ≤ 1 / 2 := by
    have h1 := ctLam_le hc
    have h3 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
    calc ctLam c * M ≤ (c ^ (1 / 3 : ℝ))⁻¹ * M := mul_le_mul_of_nonneg_right h1 hM
      _ ≤ 1 / 2 := by
        rw [inv_mul_le_iff₀ h3]; linarith
  have hRA : R ≤ langerRadius c := by
    unfold langerRadius langerScale
    calc R ≤ min (ρ / 4) (langerKappa * 4.94e-4) * c ^ (2 / 3 : ℝ) := hR
      _ ≤ langerKappa * 4.94e-4 * c ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hc23.le
      _ = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by ring
  have hRw : -ρ < ctMu c * (-R) := by
    have hμ : ctMu c * c ^ (2 / 3 : ℝ) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
      unfold ctMu
      rw [mul_assoc, ← Real.rpow_add hc]; norm_num
    have h22 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hμ0 := ctMu_pos hc
    have h1 : ctMu c * R ≤ ctMu c * (ρ / 4 * c ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hR.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hc23.le)) hμ0.le
    have h2 : ctMu c * (ρ / 4 * c ^ (2 / 3 : ℝ)) = ρ / 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [← hμ]; ring
    have : ρ / 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ ρ / 4 * 2 := mul_le_mul_of_nonneg_left h22 (by positivity)
    nlinarith
  exact (taperBand_of_window hW hc3 hcM hlam hR1 hRw hRA hinj)

/-- **The chart inputs of the taper** (`ct:taper-harnack` (c)): `TaperChartInputs ε c R 2` for the concrete `ctTaperV`, `ctRprime`,
`ctTaperLam`, in the regime of `taperBand` and under the named input `UhatInjOn ε c` (bijectivity of `û`, `ct:cfu`). -/
theorem taperChartInputs {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ ρ₁ c₀ : ℝ, 0 < ρ₁ ∧ 3 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ R : ℝ, 1 ≤ R → R ≤ ρ₁ * c ^ (2 / 3 : ℝ) →
      UhatInjOn ε c → TaperChartInputs ε c R 2 := by
  obtain ⟨ρ₁, c₀, h1, h2, h⟩ := taperBand hε
  exact ⟨ρ₁, c₀, h1, h2, fun c hc R hR hRR hinj => (h c hc R hR hRR hinj).inputs⟩

/-- info: 'FormalResearch.SignUncertainty.taperBand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taperBand

/-- info: 'FormalResearch.SignUncertainty.taperChartInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taperChartInputs

end FormalResearch.SignUncertainty
