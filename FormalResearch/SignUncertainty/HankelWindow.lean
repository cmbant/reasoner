module

public import FormalResearch.SignUncertainty.HankelBootAssembly
public import FormalResearch.SignUncertainty.HankelWindowLocal
public import FormalResearch.SignUncertainty.HankelWindowGeom
public import FormalResearch.SignUncertainty.HankelWindowBand
public import FormalResearch.SignUncertainty.HankelWindowArith
public import FormalResearch.SignUncertainty.HankelWindowAux
public import FormalResearch.SignUncertainty.HankelWindowSaddle

/-!
# The Hankel window lemma `HankelYVAt` (`teb:mellin` (2)--(3), M5-S6b)

For `c ≥ 10¹⁴`, a feasible normalised `f`, a level `u_T ∈ [-3, 0]` and a radius `R ∈ [b² c^{2/3}, b² c^{2/3} + 1]`
(`b = 1/100`), on the annulus `R - 1 ≤ ‖ũ‖ ≤ R + 1`, `Im ũ ≥ 0`, `2 c^{-1/12} √‖ũ‖ ≤ Re ũ^{1/2}`:

`‖Ψ̃(ũ)‖ ≤ C_fb (c^{1/3}(B₁ + B₂) + 1) e(ũ) (Re ũ^{1/2})^{-3/2} ‖ũ‖^{-3/4}`, `C_fb = 6/5 C_Y + 17`

(`hankel_yv_window`; `hankel_yv_at : HankelYVAt hankelWindowC 10¹⁴`).  Proof: at the saddle `ζ₊ = σ + iτ₀`
of `ũ` the local integral `∫_{|τ|≤1/3} J(1/10 + iτ) dτ` is shifted to `Re ζ = σ`; inside the window
`|y - τ₀| ≤ h`, `h² = 5 log c/(cσ)`, `‖W̃_c‖` is bounded by the band reduction
(`hankel_window_Wt_bound`, `cos ψ ≥ c^{-1/12}` from the hypothesis `2 c^{-1/12} √‖ũ‖ ≤ Re ũ^{1/2}`), outside it the
Gaussian factor is `≤ c^{-2}` (`hankel_local_density_window`).  The constant `C_fb` differs from the paper's
(unspecified) `C_fb`; the threshold `c_YV = 10¹⁴` is a Lean artefact.
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand FormalResearch.CohnElkies FormalResearch.Special
  FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- The constant `C_fb = (6/5) C_Y + 17`. -/
noncomputable def hankelWindowC : ℝ := 6 / 5 * tebBandConst hankelBandParams + 17

lemma one_le_hankelWindowC : 1 ≤ hankelWindowC := by
  unfold hankelWindowC
  have := tebBandConst_pos hankelBandParams
  linarith

set_option maxHeartbeats 4000000 in
/-- **Window lemma** (proved). -/
theorem hankel_yv_window {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 1e14 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1) :
    YVEnvBound (hankelPsi c f) c R
      (hankelWindowC * (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + 1)) := by
  intro u hIm hlo hhi hX
  have hc3 : 3e6 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨t, ht14, hct, hk4, hK8, hτi, hc56, hlog⟩ := hankel_window_cnum hc
  have ht0 : 0 < t := by linarith
  set k : ℝ := c ^ (1 / 3 : ℝ) with hkdef
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hXorig := hX
  have ht8 : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
  have ht8' : (1.4e9 : ℝ) ≤ t ^ 8 := by norm_num at ht8; linarith
  have hRlb8 : (1 / 100 : ℝ) ^ 2 * t ^ 8 ≤ R := by rw [← hK8]; exact hRlb
  have hRub8 : R ≤ (1 / 100 : ℝ) ^ 2 * t ^ 8 + 1 := by rw [← hK8]; exact hRub
  have hR1 : 1e5 ≤ R := by nlinarith
  have hRc : R + 1 ≤ t ^ 8 := by nlinarith
  have hkap := hankelLangerKappa_bounds
  have hRdisc : R + 1 ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
    rw [hK8]; nlinarith
  have hRA : R ≤ langerRadius c := by
    have : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
    rw [this]; linarith
  set N : ℝ := ‖u‖ with hNdef
  have hN1 : 9e4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hNdef; linarith
  set s : ℝ := N ^ (1 / 2 : ℝ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN0 _
  have hsqrtN : Real.sqrt N = s := by rw [hsdef, Real.sqrt_eq_rpow]
  set X : ℝ := (u ^ (1 / 2 : ℂ)).re with hXdef
  rw [hτi, hsqrtN] at hX
  have hτi0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hX0 : 0 < X := by
    have : 0 < 2 * t⁻¹ * s := by positivity
    linarith
  have hcut := hankel_window_slit hu_ne hX0
  set K : ℝ := c ^ (2 / 3 : ℝ) * langerKappa with hK
  have hK0 : 0 < K := mul_pos (Real.rpow_pos_of_pos hc0 _) langerKappa_pos
  set y : ℂ := u / (K : ℂ) with hy
  have hKne : (K : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
  have huy : (K : ℂ) * y = u := by rw [hy]; field_simp
  have hyn : ‖y‖ ≤ 4.94e-4 := by
    rw [hy, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0, div_le_iff₀ hK0]
    have : N ≤ R + 1 := hhi
    linarith
  obtain ⟨q, hq, hqn, hqu, hqg⟩ := chart_saddle_data langerEta_etaC hc0 hyn (by rw [huy]; exact hcut)
  rw [huy] at hqu
  obtain ⟨σ, τ0, h, hζeq, hσpos, hσle, hτ0, hh0, hhsq, hζlo, hζhi, hhle, hcz, hnzσ, hXk, hkσ⟩ :=
    hankel_window_saddle hc hRlb hRub hlo hhi hXorig hq hqn hqu
  set ζ := saddleRoot q with hζdef
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hqn
  have hσ1 : σ < 1 := by linarith
  have hζ0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have hcσ0 : 0 < c * σ := by positivity
  have hnzσ' : ‖ζ‖ / σ ≤ 1.002 * s / X := by rw [hζeq]; exact hnzσ
  have hμ := langerMu_lt
  have hμ0 := langerMu_pos
  have hB12 : 0 ≤ hankelBootB1 c f R u_T + hankelBootB2 c f R := by
    have h1 := hankelBootB1_nonneg hc3 hf hε hM hT hu0 hu3 (by linarith) (by linarith) hRA
    have h2 := hankelBootB2_nonneg c f R
    linarith
  set Bs : ℝ := hankelBootB1 c f R u_T + hankelBootB2 c f R with hBs
  set Q : ℝ := tebBandConst hankelBandParams * c ^ (-(5 / 6 : ℝ)) *
    (k * Bs + c ^ (-(1 / 6 : ℝ))) with hQdef
  have hCy := tebBandConst_pos hankelBandParams
  have hc56' : 0 < c ^ (-(5 / 6 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hc16 : 0 < c ^ (-(1 / 6 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  set W : ℝ := Q * (11 / 10 * ‖ζ‖ / σ) with hWdef
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hW : ∀ y : ℝ, |y| ≤ 1 / 3 → |y - τ0| ≤ h →
      ‖hankelWt c f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ W := fun y _ hy => by
    have := hankel_window_Wt_bound hc3 hf hε hM hT hu0 hu3 hRlb hRub hB12 hσpos hσ1 hζlo hζhi
      hhle hcz hy
    rw [← hζeq] at this
    exact this
  set ℓ : ℂ := -(gSer etaC ζ) with hℓ
  have hl : ℓ.re ≤ 1 / 200 := by
    have h1 := Complex.re_le_norm (-(gSer etaC ζ))
    rw [norm_neg] at h1
    exact h1.trans (norm_gSer_small hζn)
  have hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0 := by rw [← hζeq, hℓ]; ring
  have hwin := hankel_local_density_window (by linarith) hf.toIsHankelEigenfn hε hM ℓ hl hσpos hσle hτ0
    hcrit hh0 hW0 hW
  rw [← hζeq] at hwin
  have hph : (c : ℂ) * hankelLocPhi ℓ ζ = -(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ) := by
    rw [← hqu, ← phase_at_saddle langerEta_etaC hc0 hq hqn]
    unfold hankelLocPhi; ring
  have hexp : Real.exp (c * (hankelLocPhi ℓ ζ).re) = airyEnv u := by
    have h2 := congrArg Complex.re hph
    rw [Complex.re_ofReal_mul] at h2
    unfold airyEnv
    rw [h2]
    simp [Complex.mul_re]
  rw [hexp] at hwin
  have hlocal_eq : Complex.log (1 + chartYinv etaC y) = ℓ := hqg.symm
  -- the prefactor
  have hwn := norm_chartYinv_le langerEta_etaC hyn
  have h1w : 0.9995 ≤ ‖1 + chartYinv etaC y‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(chartYinv etaC y))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this; linarith
  have hder := norm_deriv_chartYinv_le hyn
  have hpref : k / (2 * π * langerKappa) ≤ k * 0.27 := hankel_pref_le hk0.le
  have hnorm : ‖hankelPsi c f u‖ = (k / (2 * π * langerKappa)) *
      ‖deriv (chartYinv etaC) y‖ / ‖1 + chartYinv etaC y‖ *
      ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by
    show ‖hankelPsiY c f y‖ = _
    unfold hankelPsiY
    rw [norm_mul, norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := langerKappa_pos; positivity)]
  have hL0 := norm_nonneg (hankelLocal c f (Complex.log (1 + chartYinv etaC y)))
  have hD0 := norm_nonneg (deriv (chartYinv etaC) y)
  have hpref0 : 0 ≤ k / (2 * π * langerKappa) := by
    have := langerKappa_pos; positivity
  have hΨ : ‖hankelPsi c f u‖ ≤ 0.272 * k *
      ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by
    rw [hnorm]
    calc (k / (2 * π * langerKappa)) * ‖deriv (chartYinv etaC) y‖ / ‖1 + chartYinv etaC y‖ *
          ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖
        ≤ (k * 0.27) * (1 / 0.996) / 0.9995 *
          ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by gcongr
      _ ≤ 0.272 * k * ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by
        have h1 : (0.27 : ℝ) * (1 / 0.996) / 0.9995 ≤ 0.272 := by norm_num
        have h2 : (k * 0.27) * (1 / 0.996) / 0.9995 ≤ 0.272 * k := by
          calc (k * 0.27) * (1 / 0.996) / 0.9995 = (0.27 * (1 / 0.996) / 0.9995) * k := by ring
            _ ≤ 0.272 * k := by gcongr
        gcongr
  -- the final arithmetic
  have hXs0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hk3 : k ^ 3 = c := by
    rw [hkdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  set G : ℝ := Real.sqrt (c * σ) with hGdef
  have hG0 : 0 < G := Real.sqrt_pos.2 hcσ0
  have hGk : k * Real.sqrt X ≤ G := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [mul_pow, Real.sq_sqrt hX0.le, ← hk3]
    have h1 : k ^ 2 * X ≤ k ^ 2 * (k * σ) := by gcongr
    have e : k ^ 2 * (k * σ) = k ^ 3 * σ := by ring
    linarith
  have hsqrt3 : Real.sqrt (π / ((2 / 5) * c * σ)) ≤ 3 / G := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_pow, hGdef, Real.sq_sqrt hcσ0.le]
    have : π / ((2 / 5) * c * σ) = (5 / 2 * π) / (c * σ) := by field_simp
    rw [this, div_le_div_iff_of_pos_right hcσ0]
    nlinarith [Real.pi_lt_d2]
  have hNc : N ≤ c ^ (2 / 3 : ℝ) := by rw [hK8]; have : N ≤ R + 1 := hhi; linarith
  have hQs : Q * s ≤ tebBandConst hankelBandParams * (k * Bs + 1) * N ^ (-(3 / 4 : ℝ)) := by
    have hL1 := hankel_window_L1 hc0 hN0 hNc
    have hc16' : c ^ (-(1 / 6 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hBs0 : 0 ≤ k * Bs := mul_nonneg hk0.le hB12
    calc Q * s = tebBandConst hankelBandParams * (k * Bs + c ^ (-(1 / 6 : ℝ))) *
          (s * c ^ (-(5 / 6 : ℝ))) := by rw [hQdef]; ring
      _ ≤ tebBandConst hankelBandParams * (k * Bs + 1) * N ^ (-(3 / 4 : ℝ)) := by
        have h1 : k * Bs + c ^ (-(1 / 6 : ℝ)) ≤ k * Bs + 1 := by linarith
        have h2 : 0 ≤ s * c ^ (-(5 / 6 : ℝ)) := by positivity
        gcongr
  have hXN : X ≤ N ^ (1 / 2 : ℝ) := by
    have := Complex.re_le_norm (u ^ (1 / 2 : ℂ))
    have e : ‖u ^ (1 / 2 : ℂ)‖ = N ^ (1 / 2 : ℝ) := norm_saddleRoot u
    linarith
  have hci := hankel_window_L2 hc0 hN0 hNc hX0 hXN
  have hkc : k * c⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hc0, one_mul, hk4, hct]
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have hek : Real.exp (-(0.035 * c * σ)) * k ≤ 1 := by
    have h1 : Real.exp (-(0.035 * c * σ)) ≤ Real.exp (-k) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-k) * k ≤ 1 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos k), mul_one]
      linarith [Real.add_one_le_exp k]
    nlinarith [Real.exp_pos (-k)]
  have hE : Real.exp (-((2 / 5) * c * σ * h ^ 2)) = (c⁻¹) ^ 2 := by
    have : (2 / 5) * c * σ * h ^ 2 = 2 * Real.log c := by rw [hhsq]; field_simp
    rw [this]
    have h2 : Real.exp (2 * Real.log c) = c ^ 2 := by
      rw [show (2 : ℝ) * Real.log c = ((2 : ℕ) : ℝ) * Real.log c by norm_num, Real.exp_nat_mul,
        Real.exp_log hc0]
    rw [Real.exp_neg, h2, inv_pow]
  have hCc : 2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c)) =
      2 * (2 * Real.exp (-(0.035 * c * σ)) * c⁻¹ / 0.07) := by field_simp
  have hΛ : 1 ≤ k * Bs + 1 := by
    have := mul_nonneg hk0.le hB12; linarith
  have harith := hankel_window_arith (k := k) (X := X) (Xs := Real.sqrt X) (s := s) (σ := σ) (nz := ‖ζ‖)
    (G := G) (W := W) (Q := Q) (Λ := k * Bs + 1) (Cy := tebBandConst hankelBandParams)
    (N34 := N ^ (-(3 / 4 : ℝ))) (ci := c⁻¹) (e := Real.exp (-(0.035 * c * σ)))
    hk0 hX0 hXs0 hs0 hσpos hζ0 hG0 hQ0 hΛ hCy (Real.rpow_nonneg hN0.le _) (inv_pos.2 hc0)
    (Real.exp_pos _).le (le_of_eq hWdef) hnzσ' hQs hGk hci hkc hek
    (A := (100 / 81) * W * Real.sqrt (π / ((2 / 5) * c * σ)))
    (by gcongr)
  have hX32 : X ^ (-(3 / 2 : ℝ)) = (X * Real.sqrt X)⁻¹ := by
    rw [Real.rpow_neg hX0.le]
    congr 1
    rw [Real.sqrt_eq_rpow]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hX0, Real.rpow_one]
  have hair := (airyEnv_pos u).le
  rw [hlocal_eq] at hΨ
  calc ‖hankelPsi c f u‖ ≤ 0.272 * k * ‖hankelLocal c f ℓ‖ := hΨ
    _ ≤ 0.272 * k * (airyEnv u * ((100 / 81 * W * Real.sqrt (π / (2 / 5 * c * σ)) +
          4 / 3 * Real.exp (-(2 / 5 * c * σ * h ^ 2)) +
          2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c))))) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
    _ = airyEnv u * (0.272 * k * ((100 / 81) * W * Real.sqrt (π / ((2 / 5) * c * σ)) +
          (4 / 3) * (c⁻¹) ^ 2 + 2 * (2 * Real.exp (-(0.035 * c * σ)) * c⁻¹ / 0.07))) := by
        rw [hE, hCc]; ring
    _ ≤ airyEnv u * ((1.2 * tebBandConst hankelBandParams * (k * Bs + 1) + 17) *
          (N ^ (-(3 / 4 : ℝ)) / (X * Real.sqrt X))) := by gcongr
    _ ≤ airyEnv u * (hankelWindowC * (k * Bs + 1) * (N ^ (-(3 / 4 : ℝ)) / (X * Real.sqrt X))) := by
        have h1 : 1.2 * tebBandConst hankelBandParams * (k * Bs + 1) + 17 ≤
            hankelWindowC * (k * Bs + 1) := by
          unfold hankelWindowC; nlinarith
        have h2 : 0 ≤ N ^ (-(3 / 4 : ℝ)) / (X * Real.sqrt X) := by positivity
        gcongr
    _ = _ := by rw [hX32]; field_simp

/-- info: 'FormalResearch.SignUncertainty.hankel_yv_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_yv_window

/-- **Hankel band-feedback hypothesis** (S6b): `HankelYVAt C_fb c_YV` holds with `C_fb = hankelWindowC` and
`c_YV = 10¹⁴`. -/
theorem hankel_yv_at : HankelYVAt hankelWindowC 1e14 := by
  intro c ε T u_T R f hc hf hε hM hT hu0 hu3 hRlb hRub
  exact hankel_yv_window hc hf hε hM hT hu0 hu3 hRlb hRub

/-- info: 'FormalResearch.SignUncertainty.hankel_yv_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_yv_at

end FormalResearch.SignUncertainty
