import FormalResearch.FourQubitEntropy.RenyiFullCases
import FormalResearch.FourQubitEntropy.ThirdMoment

/-!
# The cluster sliver of `thm:fqe-renyi-classical`

Paper E, proof of `thm:fqe-renyi-classical`, paragraph *The sliver* (`sup_renyi.tex`).  One cut
(`λ`, purity `≥ 47/100`) is distinguished and the other two (`μ`, `ν`) have `p ≤ 29/100`.

* `window_bound`: from the sharp third-moment lemma applied to `μ, ν`,
  `|12 Y| ≤ κ X` with `X = (p_μ - 1/4) + (p_ν - 1/4) ≤ 1/25` and `κ = 4√3/5`, i.e.
  `F = F_c + (error of size at most κX)`.
* `sliver_core`: from `DetReduction`, `NearUniformDual` and `ClusterSliver`,
  `E_{q_s} < 5/3`.  (Equality is excluded because the equality case of `ClusterSliver` forces `λ = c₁`,
  `ε = 0` and then `20ε + 2F = 1`.)
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

theorem rpow_three_halves_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
      ← Real.sqrt_eq_rpow]

theorem cub_uniformFour {l : Fin 4 → ℝ} (h : UniformFour l) : cub l = 1 / 16 := by
  unfold cub; simp only [Fin.sum_univ_four, h _]; norm_num

/-- `κ X` bound on the third-moment error of the two small cuts. -/
theorem window_bound {m n : Fin 4 → ℝ} (hm : IsProb4 m) (hn : IsProb4 n)
    (hX : (pur m - 1 / 4) + (pur n - 1 / 4) ≤ 1 / 25) :
    |12 * (cub m + cub n - 1 / 8 - 3 / 4 * ((pur m - 1 / 4) + (pur n - 1 / 4)))| ≤
      kappaSL * ((pur m - 1 / 4) + (pur n - 1 / 4)) := by
  have pm := pur_ge_quarter hm
  have pn := pur_ge_quarter hn
  obtain ⟨-, tm, -, -⟩ := third_moment m hm.1 hm.2 (x := pur m - 1 / 4) (by unfold pur; ring)
  obtain ⟨-, tn, -, -⟩ := third_moment n hn.1 hn.2 (x := pur n - 1 / 4) (by unfold pur; ring)
  set a := pur m - 1 / 4 with ha
  set b := pur n - 1 / 4 with hb
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [rpow_three_halves_eq ha0] at tm
  rw [rpow_three_halves_eq hb0] at tn
  have hcm : cub m = ∑ i, m i ^ 3 := rfl
  have hcn : cub n = ∑ i, n i ^ 3 := rfl
  have hsX : Real.sqrt (a + b) ≤ 1 / 5 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have sa : Real.sqrt a ≤ Real.sqrt (a + b) := Real.sqrt_le_sqrt (by linarith)
  have sb : Real.sqrt b ≤ Real.sqrt (a + b) := Real.sqrt_le_sqrt (by linarith)
  have sa0 := Real.sqrt_nonneg a
  have sb0 := Real.sqrt_nonneg b
  -- Y = (tm - 1/16 - 3a/4) + (tn - 1/16 - 3b/4)
  have hY : cub m + cub n - 1 / 8 - 3 / 4 * (a + b) =
      (cub m - 1 / 16 - 3 * a / 4) + (cub n - 1 / 16 - 3 * b / 4) := by ring
  rw [hY]
  have e1 : |cub m - 1 / 16 - 3 * a / 4| ≤ a * Real.sqrt a / Real.sqrt 3 := by
    rw [hcm]; exact tm
  have e2 : |cub n - 1 / 16 - 3 * b / 4| ≤ b * Real.sqrt b / Real.sqrt 3 := by
    rw [hcn]; exact tn
  have e3 : |(cub m - 1 / 16 - 3 * a / 4) + (cub n - 1 / 16 - 3 * b / 4)| ≤
      a * Real.sqrt a / Real.sqrt 3 + b * Real.sqrt b / Real.sqrt 3 :=
    (abs_add_le _ _).trans (add_le_add e1 e2)
  have e4 : a * Real.sqrt a + b * Real.sqrt b ≤ (a + b) * (1 / 5) := by
    nlinarith [mul_le_mul_of_nonneg_left sa ha0, mul_le_mul_of_nonneg_left sb hb0,
      mul_le_mul_of_nonneg_left hsX (by linarith : 0 ≤ a + b)]
  have e5 : a * Real.sqrt a / Real.sqrt 3 + b * Real.sqrt b / Real.sqrt 3 ≤
      (a + b) * (1 / 5) / Real.sqrt 3 := by
    rw [← add_div]; exact div_le_div_of_nonneg_right e4 hs3.le
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  have e6 : 12 * ((a + b) * (1 / 5) / Real.sqrt 3) = kappaSL * (a + b) := by
    unfold kappaSL
    field_simp
    nlinarith [hs33]
  calc 12 * |(cub m - 1 / 16 - 3 * a / 4) + (cub n - 1 / 16 - 3 * b / 4)|
      ≤ 12 * ((a + b) * (1 / 5) / Real.sqrt 3) := by
        apply mul_le_mul_of_nonneg_left (e3.trans e5) (by norm_num)
    _ = kappaSL * (a + b) := e6

/-- `ℓ` is concave in `F`. -/
theorem ell_ge_min_F {α β γ ε F₀ F₁ F : ℝ} (hγ : 0 ≤ γ) (h0 : F₀ ≤ F) (h1 : F ≤ F₁) :
    min (ell α β γ ε F₀) (ell α β γ ε F₁) ≤ ell α β γ ε F := by
  have hc : 0 ≤ γ / 6 := by positivity
  have := quad_concave_min (a := β) (b := α * ε - γ / 6 * (17 / 2 * ε + 2 * ε ^ 2)) hc h0 h1
  unfold ell
  convert this using 1 <;> ring_nf

theorem RelaxTriple.rot {l₂ l₃ l₄ : Fin 4 → ℝ} (R : RelaxTriple l₂ l₃ l₄) :
    RelaxTriple l₃ l₄ l₂ := by
  have eP : Pm l₃ l₄ l₂ = Pm l₂ l₃ l₄ := by unfold Pm; ring
  have eT : Tm l₃ l₄ l₂ = Tm l₂ l₃ l₄ := by unfold Tm; ring
  have eF : Fm l₃ l₄ l₂ = Fm l₂ l₃ l₄ := by unfold Fm; rw [eP, eT]
  have eV : Vm l₃ l₄ l₂ = Vm l₂ l₃ l₄ := by unfold Vm; rw [eP]; ring
  refine ⟨R.prob₃, R.prob₄, R.prob₂, by rw [eP]; exact R.P_ge, by rw [eF]; exact R.F_ge, ?_⟩
  have := R.QK
  unfold QKTriple at this ⊢
  rw [eV, eF, eP]; exact this

theorem Pm_rot (l₂ l₃ l₄ : Fin 4 → ℝ) : Pm l₃ l₄ l₂ = Pm l₂ l₃ l₄ := by unfold Pm; ring
theorem Fm_rot (l₂ l₃ l₄ : Fin 4 → ℝ) : Fm l₃ l₄ l₂ = Fm l₂ l₃ l₄ := by
  unfold Fm Tm; rw [Pm_rot]; ring
theorem Em_rot (q : ℝ) (l₂ l₃ l₄ : Fin 4 → ℝ) : Em q l₃ l₄ l₂ = Em q l₂ l₃ l₄ := by
  unfold Em renyiE; ring

/-- **The sliver.** `λ` has `p ≥ 47/100`; from `DetReduction`, `NearUniformDual`, `ClusterSliver`:
`E_{q_s}(λ, μ, ν) < 5/3`, for `F ≥ 11/25`, `20ε + 2F < 1` (so `ε < 3/500`). -/
theorem sliver_core (hDM : DetReduction) (hNU : NearUniformDual) (hSL : ClusterSliver)
    {l m n : Fin 4 → ℝ} (R : RelaxTriple l m n)
    (hF : 11 / 25 ≤ Fm l m n) (hE : 20 * (Pm l m n - 1) + 2 * Fm l m n < 1)
    (hbig : 47 / 100 ≤ pur l) : Em qS l m n < 5 / 3 := by
  have hP0 := R.P_ge
  have hε : Pm l m n - 1 ≤ 3 / 500 := by linarith
  have pm := pur_ge_quarter R.prob₂
  have pl := pur_ge_quarter R.prob₃
  have pn := pur_ge_quarter R.prob₄
  unfold Pm at hε hP0
  -- the two small cuts
  have hmS : pur m ≤ 29 / 100 := by linarith
  have hnS : pur n ≤ 29 / 100 := by linarith
  have nu_m := hNU m R.prob₃ hmS
  have nu_n := hNU n R.prob₄ hnS
  -- chart replacement of the distinguished cut
  obtain ⟨μ, hμ, hpμ, hcμ, hHμ⟩ := hDM qS qS_gt_one (by unfold qS; norm_num) l R.prob₂
  have hΛ : Lam qS aH bH gH l ≤ Lam qS aH bH gH μ := by
    unfold Lam; rw [hpμ, hcμ]; linarith
  -- the window
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (pur m - 1 / 4) + (pur n - 1 / 4) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by linarith
  have hX1 : X ≤ 1 / 25 := by linarith
  have hXs : Xs (Pm l m n - 1) (pur μ) = X := by
    unfold Xs Pm; rw [hpμ]; linarith
  have hw := window_bound R.prob₃ R.prob₄ (by rw [← hXdef]; exact hX1)
  rw [← hXdef] at hw
  have hFc : Fm l m n = Fc (Pm l m n - 1) (pur μ) (cub μ) -
      12 * (cub m + cub n - 1 / 8 - 3 / 4 * X) := by
    unfold Fm Tm Fc Pm; rw [hpμ, hcμ, hXdef]; ring
  have hwin := abs_le.1 hw
  have hFlo : Fc (Pm l m n - 1) (pur μ) (cub μ) - kappaSL * Xs (Pm l m n - 1) (pur μ) ≤
      Fm l m n := by rw [hXs]; linarith [hwin.1, hwin.2]
  have hFhi : Fm l m n ≤ Fc (Pm l m n - 1) (pur μ) (cub μ) + kappaSL * Xs (Pm l m n - 1) (pur μ) := by
    rw [hXs]; linarith [hwin.1, hwin.2]
  have hF2 : Fm l m n ≤ 1 / 2 := by unfold Pm at hE; linarith
  have hεp : 0 ≤ Pm l m n - 1 := by unfold Pm; linarith
  have hεq : Pm l m n - 1 ≤ 1 / 100 := by unfold Pm; linarith
  have hXs0 : 0 ≤ Xs (Pm l m n - 1) (pur μ) := by rw [hXs]; exact hX0
  have hbigμ : 47 / 100 ≤ pur μ := by rw [hpμ]; exact hbig
  have hwindow : ∃ F : ℝ, Fc (Pm l m n - 1) (pur μ) (cub μ) - kappaSL * Xs (Pm l m n - 1) (pur μ)
      ≤ F ∧ F ≤ Fc (Pm l m n - 1) (pur μ) (cub μ) + kappaSL * Xs (Pm l m n - 1) (pur μ) ∧
      11 / 25 ≤ F ∧ F ≤ 1 / 2 := ⟨Fm l m n, hFlo, hFhi, hF, hF2⟩
  have sl := hSL μ hμ (Pm l m n - 1) hεp hεq hbigμ hXs0 hwindow
  -- concavity in F selects a sign
  have hγ : (0 : ℝ) ≤ gH := by unfold gH; norm_num
  have hcc := ell_ge_min_F (α := aH) (β := bH) (γ := gH) (ε := Pm l m n - 1) hγ hFlo hFhi
  have kpos : 0 ≤ kappaSL := by unfold kappaSL; positivity
  have hdual := dual_bound R.QK qS aH bH gH hγ
  have hcontact := contact_identity (q := qS) (by linarith [qS_gt_one]) qS_gt_one.ne' aH bH gH
  have hc2 : Lam qS aH bH gH c2 = Lam qS aH bH gH c2 := rfl
  have hEm : Em qS l m n = (renyiSpec qS l + renyiSpec qS m + renyiSpec qS n) / 3 := rfl
  -- the two signs, as ell at Fc ± κX
  have sp := sl 1 (Or.inl rfl)
  have sm := sl (-1) (Or.inr rfl)
  have hGp : Gsl 1 (Pm l m n - 1) μ = Lam qS aH bH gH c1 - Lam qS aH bH gH μ
      + ell aH bH gH (Pm l m n - 1) (Fc (Pm l m n - 1) (pur μ) (cub μ) +
        kappaSL * Xs (Pm l m n - 1) (pur μ)) - ell aH bH gH 0 (1 / 2) := by
    unfold Gsl; ring_nf
  have hGm : Gsl (-1) (Pm l m n - 1) μ = Lam qS aH bH gH c1 - Lam qS aH bH gH μ
      + ell aH bH gH (Pm l m n - 1) (Fc (Pm l m n - 1) (pur μ) (cub μ) -
        kappaSL * Xs (Pm l m n - 1) (pur μ)) - ell aH bH gH 0 (1 / 2) := by
    unfold Gsl; ring_nf
  -- main chain: 3E ≤ 5 - X/125 - (G for the selected sign)
  have key : (renyiSpec qS l + renyiSpec qS m + renyiSpec qS n) ≤ 5 - X / 125 ∧
      ((renyiSpec qS l + renyiSpec qS m + renyiSpec qS n) = 5 →
        X = 0 ∧ (Gsl 1 (Pm l m n - 1) μ = 0 ∨ Gsl (-1) (Pm l m n - 1) μ = 0)) := by
    rcases le_total (ell aH bH gH (Pm l m n - 1) (Fc (Pm l m n - 1) (pur μ) (cub μ) -
        kappaSL * Xs (Pm l m n - 1) (pur μ)))
      (ell aH bH gH (Pm l m n - 1) (Fc (Pm l m n - 1) (pur μ) (cub μ) +
        kappaSL * Xs (Pm l m n - 1) (pur μ))) with hle | hle
    · rw [min_eq_left hle] at hcc
      refine ⟨?_, fun h5 => ⟨?_, Or.inr ?_⟩⟩ <;>
        linarith [sm.1, hGm, nu_m, nu_n, hcontact, hdual, hΛ, hcc, hXdef, hX0]
    · rw [min_eq_right hle] at hcc
      refine ⟨?_, fun h5 => ⟨?_, Or.inl ?_⟩⟩ <;>
        linarith [sp.1, hGp, nu_m, nu_n, hcontact, hdual, hΛ, hcc, hXdef, hX0]
  have hlt : renyiSpec qS l + renyiSpec qS m + renyiSpec qS n < 5 := by
    by_contra hge
    push Not at hge
    have h5 : renyiSpec qS l + renyiSpec qS m + renyiSpec qS n = 5 := le_antisymm (by linarith [key.1, hX0]) hge
    obtain ⟨hX00, hG⟩ := key.2 h5
    have hGeq : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ Gsl s (Pm l m n - 1) μ = 0 := by
      rcases hG with h | h
      · exact ⟨1, Or.inl rfl, h⟩
      · exact ⟨-1, Or.inr rfl, h⟩
    obtain ⟨s, hs, hG0⟩ := hGeq
    obtain ⟨hμc, hε0⟩ := (sl s hs).2 hG0
    -- X = 0 and both small cuts are uniform-four
    have pm4 : pur m = 1 / 4 := by linarith
    have pn4 : pur n = 1 / 4 := by linarith
    have um := pur_eq_quarter R.prob₃ pm4
    have un := pur_eq_quarter R.prob₄ pn4
    have hF' : Fm l m n = 1 / 2 := by
      have hpl : pur l = 1 / 2 := by rw [← hpμ, hμc]; exact pur_c1
      have htl : cub l = 1 / 4 := by rw [← hcμ, hμc]; exact cub_c1
      unfold Fm Tm Pm
      rw [cub_uniformFour um, cub_uniformFour un, hpl, htl, pm4, pn4]; norm_num
    linarith
  rw [hEm]
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
