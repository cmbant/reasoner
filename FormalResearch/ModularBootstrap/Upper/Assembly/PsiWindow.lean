module

public import FormalResearch.ModularBootstrap.Upper.Assembly.PsiBounds

/-!
# (P3) and (P4) for the designs: the window limit and the vacuum bound of `Ψ_g`

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` ((P3), (P4) of Property `sr:P`),
`upper_transfer.tex` (`ut:W`, `ut:ID`, `ut:G`, `ut:Vac` (i)).

With `Ψ_c = (2 / (C_* FK_c)) Ψ_g` (`Ψ_g = psiAiry`, `g = designG N η d c`), for the design `D(N, η_*, d)`:

* `design_psi_uniform` ((P3)): `Ψ_c → W_D = Re W` uniformly on `[-R, R]` as `c → ∞`.  The proof
  puts `u = -κσ`, `t = c x²/3`, `J κ = dt/dσ` (`Assembly.Chart`) and writes
  `(2/(C_* FK)) g V J = (1/(C_* κ FK)) (h₀ - ĥ₀) V (dt/dσ)`: the `h₀` part converges by
  `design_part1` (Lemma `W` and `ID`), the `ĥ₀` part is `O(λ c^{1/2}/ FK_c · FK_c/c^{1/2}) → 0`
  by `hat_window_bound` and `FK_c ≥ c^{1/2}`;
* `design_psi_limsup` ((P4)): `∫ Ψ_c du ≤ V_D + ε` (`∫ Ψ_g = -g_vac/(2π)`, Proposition V (i)).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity

/-- The scaling `2 / (C_* FK_c)` of `Ψ_g`. -/
noncomputable def psiScale (c : ℝ) : ℝ := 2 / (CStar * FKc 1 1 c)

lemma psiScale_pos {c : ℝ} (hc : 0 < c) : 0 < psiScale c := by
  have := FKc_pos (q := 1) one_pos 1 hc
  have := CStar_pos
  unfold psiScale; positivity

/-- Pointwise form of `Ψ_c`: `(2/(C_* FK)) g V J = (1/(C_* κ FK)) (h₀ - ĥ₀) V (dt/dσ)` at `u = -κσ`. -/
lemma psi_eq_sig {c : ℝ} (hc : 0 < c) (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (u σ : ℝ) (hσ : σ = -u / kappaAiry)
    (hx : 0 ≤ xiStar + lambdaComb c * σ) :
    psiScale c * psiAiry virasoroProblem c (sigG N η σs c) u =
      (1 / (CStar * kappaAiry * FKc 1 1 c)) *
        ((combProfile c (sigBc N η σs c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) -
          hankelTransform 1 (combProfile c (sigBc N η σs c))
            (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)) *
          virasoroProblem.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) := by
  have hκ := kappaAiry_pos
  have hCs := CStar_pos
  have hFK := FKc_pos (q := 1) one_pos 1 hc
  subst hσ
  unfold psiScale psiAiry sigG pairOdd
  rw [tAiry_eq hc hx, jAiry_eq hc hx]
  field_simp

/-- Pointwise form of `Ψ_c`: `(2/(C_* FK)) g V J = (1/(C_* κ FK)) (h₀ - ĥ₀) V (dt/dσ)` at `u = -κσ`. -/
lemma psi_eq {c : ℝ} (hc : 0 < c) (N : ℕ) (η d u σ : ℝ) (hσ : σ = -u / kappaAiry)
    (hx : 0 ≤ xiStar + lambdaComb c * σ) :
    psiScale c * psiAiry virasoroProblem c (designG N η d c) u =
      (1 / (CStar * kappaAiry * FKc 1 1 c)) *
        ((combProfile c (designBc N η d c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) -
          hankelTransform 1 (combProfile c (designBc N η d c))
            (c * (xiStar + lambdaComb c * σ) ^ 2 / 3)) *
          virasoroProblem.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) :=
  psi_eq_sig hc N η (designSigma1 d) u σ hσ hx

/-- **(P3): the window limit of `Ψ_g`** for the finite modifications with arbitrary offsets `σs`: see
`design_psi_uniform`, the case `σs = designSigma1 d`. -/
theorem sig_psi_uniform (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ)
    {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ u ∈ Icc (-R) R,
      |psiScale c * psiAiry virasoroProblem c (sigG N η σs c) u - sigWinW N η σs u| ≤ ε := by
  have hκ := kappaAiry_pos
  have hCs := CStar_pos
  have hP : 0 < CStar * kappaAiry := mul_pos hCs hκ
  set S : ℝ := R / kappaAiry with hS
  have hS0 : 0 ≤ S := by positivity
  have hSκ : S * kappaAiry = R := by rw [hS]; field_simp
  obtain ⟨n1, hn1⟩ := (phiWKB_succ_tendsto.eventually_ge_atTop S).exists
  obtain ⟨K, hK0, hKev⟩ := sig_hat_window_bound N hN hη0.le hη1 σs
  set ε' : ℝ := ε * (CStar * kappaAiry) / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  set δ₂ : ℝ := ε * (CStar * kappaAiry) / (2 * (K + 1)) with hδ₂
  have hδ₂0 : 0 < δ₂ := by positivity
  have hlsq : ∀ᶠ c : ℝ in atTop, lambdaComb c * c ^ (1 / 2 : ℝ) ≤ δ₂ :=
    lambdaComb_mul_sqrt_tendsto.eventually_le_const hδ₂0
  filter_upwards [sig_part1 N hN hη0.le hη1 σs hS0 n1 hε'0, hKev, hlsq,
    lambda_mul_le S (half_pos xiStar_pos), FKc_ge_mul_sqrt 1, eventually_gt_atTop (1 : ℝ)]
    with c h1 hK hl hlS hFK hc1 u hu
  have hc0 : 0 < c := lt_trans one_pos hc1
  have hlam := lambdaComb_pos' hc0
  have hFKpos := FKc_pos (q := 1) one_pos 1 hc0
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = -u / kappaAiry := ⟨_, rfl⟩
  have hσκ : σ * kappaAiry = -u := by rw [hσ]; field_simp
  have hlo : -S ≤ σ := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h hκ, hu.2]
  have hhi : σ ≤ S := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h hκ, hu.1]
  have hσS : σ ∈ Icc (-S) (phiWKB (n1 + 1)) := ⟨hlo, hhi.trans hn1⟩
  have hx : xiStar / 2 ≤ xiStar + lambdaComb c * σ := by
    have := mul_le_mul_of_nonneg_left hlo hlam.le
    nlinarith
  have hx0 : 0 ≤ xiStar + lambdaComb c * σ := le_trans (by have := xiStar_pos; positivity) hx
  have hWu : -kappaAiry * σ = u := by rw [hσ]; field_simp
  have hp1 := h1 σ hσS
  rw [hWu] at hp1
  have hp2 := hK _ hx
  rw [psi_eq_sig hc0 N η σs u σ hσ hx0]
  set x : ℝ := xiStar + lambdaComb c * σ with hxdef
  set t : ℝ := c * x ^ 2 / 3 with htdef
  set h : ℝ := combProfile c (sigBc N η σs c) t with hhdef
  set ĥ : ℝ := hankelTransform 1 (combProfile c (sigBc N η σs c)) t with hĥdef
  set V : ℝ := virasoroProblem.cardyV (c / 12) t with hVdef
  set Dt : ℝ := (2 * c * x / 3) * lambdaComb c with hDt
  set P : ℝ := CStar * kappaAiry with hPdef
  set FK : ℝ := FKc 1 1 c with hFKdef
  set Wu : ℝ := sigWinW N η σs u with hWudef
  have hB : |ĥ * V * Dt| ≤ ε / 2 * (P * FK) := by
    have e1 : ĥ * V * Dt = (ĥ * V * (2 * c * x / 3)) * lambdaComb c := by rw [hDt]; ring
    rw [e1, abs_mul, abs_of_pos hlam]
    have hc2 : c = √c * √c := (Real.mul_self_sqrt hc0.le).symm
    have hsq : lambdaComb c * √c ≤ δ₂ := by rw [Real.sqrt_eq_rpow]; exact hl
    have hsqp : 0 < √c := Real.sqrt_pos.mpr hc0
    have hFK' : √c ≤ FK := by simpa using hFK
    calc |ĥ * V * (2 * c * x / 3)| * lambdaComb c ≤ (K * c) * lambdaComb c :=
          mul_le_mul_of_nonneg_right hp2 hlam.le
      _ = K * (lambdaComb c * √c) * √c := by
          linear_combination (K * lambdaComb c) * hc2
      _ ≤ K * δ₂ * FK := by
          gcongr
      _ ≤ ε / 2 * (P * FK) := by
          have : K * δ₂ = ε * P / 2 * (K / (K + 1)) := by
            rw [hδ₂, hPdef]; field_simp
          rw [this]
          have hk1 : K / (K + 1) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          have hεP : 0 ≤ ε * P / 2 := by positivity
          calc ε * P / 2 * (K / (K + 1)) * FK ≤ ε * P / 2 * 1 * FK := by gcongr
            _ = ε / 2 * (P * FK) := by ring
  have hdecomp : 1 / (P * FK) * ((h - ĥ) * V * Dt) - Wu =
      (1 / P) * (h * V * Dt / FK - P * Wu) - (ĥ * V * Dt) / (P * FK) := by
    field_simp
    ring
  rw [hdecomp]
  have hA : |(1 / P) * (h * V * Dt / FK - P * Wu)| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hP)]
    calc 1 / P * |h * V * Dt / FK - P * Wu| ≤ 1 / P * ε' := by gcongr
      _ = ε / 2 := by rw [hε']; field_simp
  have hBB : |(ĥ * V * Dt) / (P * FK)| ≤ ε / 2 := by
    rw [abs_div, abs_of_pos (mul_pos hP hFKpos), div_le_iff₀ (mul_pos hP hFKpos)]
    exact hB
  calc |(1 / P) * (h * V * Dt / FK - P * Wu) - (ĥ * V * Dt) / (P * FK)|
      ≤ |(1 / P) * (h * V * Dt / FK - P * Wu)| + |(ĥ * V * Dt) / (P * FK)| := abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hA hBB
    _ = ε := by ring

/-- **(P3): the window limit of `Ψ_g` for the designs.** -/
theorem design_psi_uniform (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ u ∈ Icc (-R) R,
      |psiScale c * psiAiry virasoroProblem c (designG N η d c) u - designWinW N η d u| ≤ ε :=
  by
  simpa only [designWinW_eq_sig, designG] using sig_psi_uniform N hN hη0 hη1 (designSigma1 d) hR hε

/-- **(P4): the vacuum bound** `∫ Ψ_c du ≤ V + ε` for arbitrary offsets `σs` (`V = windowIntegralSig`): see
`design_psi_limsup`. -/
theorem sig_psi_limsup (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop,
      ∫ u, psiScale c * psiAiry virasoroProblem c (sigG N η σs c) u ≤ windowIntegralSig N η σs + ε := by
  have hCs := CStar_pos
  filter_upwards [proposition_V_i_sig N hN hη0 hη1 σs (ε := ε * CStar) (by positivity),
    eventually_gt_atTop (0 : ℝ)] with c hV hc0
  have hFK := FKc_pos (q := 1) one_pos 1 hc0
  rw [integral_const_mul, integral_psiAiry_eq_neg_gVac virasoroProblem hc0]
  have e : psiScale c * (-virasoroProblem.gVac (c / 12) (sigG N η σs c) / (2 * π)) =
      (2 * sigPsiIntegral N η σs c / FKc 1 1 c) / CStar := by
    unfold psiScale sigPsiIntegral
    rw [sigGVac_eq]
    field_simp
  rw [e, div_le_iff₀ hCs]
  have : windowIntegralSig N η σs * CStar + ε * CStar = CStar * windowIntegralSig N η σs + ε * CStar := by ring
  linarith

/-- **(P4): the vacuum bound** `∫ Ψ_c du ≤ V_D + ε` (Proposition V (i), `∫ Ψ_g = -g_vac/(2π)`). -/
theorem design_psi_limsup (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop,
      ∫ u, psiScale c * psiAiry virasoroProblem c (designG N η d c) u ≤ windowIntegralVD N η d + ε :=
  by
  simpa only [windowIntegralVD_eq_sig, designG] using sig_psi_limsup N hN hη0 hη1 (designSigma1 d) hε

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sig_psi_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sig_psi_uniform

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sig_psi_limsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sig_psi_limsup

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.design_psi_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_psi_uniform

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.design_psi_limsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms design_psi_limsup

end FormalResearch.ModularBootstrap.Upper.Assembly
