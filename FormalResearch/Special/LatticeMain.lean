module

public import FormalResearch.Special.LatticeSumGamma

/-!
# `lem:latticesum` (o) and (ii) for the Gamma phase

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `lem:latticesum`.  Setting: `ϰ = nc ≥ 1`,
`b > 0`, `c_* < ½`, `L^{c_*/2} ≤ X ≤ L^{c_*}`, `F_- ≤ F_i ≤ F_+`, `ℓ_Σ = ∑ log(L F_i)`,
`G(s) = θ₀ + sℓ_Σ - ϰ arg Γ(½+is)` (`gammaG`), `Θ` continuous strictly increasing on `[-X, X]` with
`|Θ - G| ≤ L^{-b}`, `S = {x ∈ [-X,X] : Θ(x) ∈ πℤ}`, `φ` analytic in `|Im s| ≤ δ` with
`|φ| ≤ C_φ e^{-κ|Re s|}`, `0 < b₁ < min(b, ϰ min(δ, ¼))`.

* (o): each `[a,a']` contains `≤ 2ϰ log L/π (a'-a) + 2` levels; consecutive levels are at distance in
  `[π/(4ϰ log L), 4π/(ϰ log L)]`;
* (ii): `‖∑_{x∈S} φ(x) - (1/π)∫_ℝ φ(s)(ℓ_Σ - ϰ Re ψ(½+is)) ds‖ ≤ C C_φ L^{-b₁}`, `C, L₀` depending only on
  `nc, b, c_*, F_±, δ, κ, b₁` (not on `φ`'s constant, `θ₀`, `X`, `Θ`, `F`).

Not formalised: the Gamma-function identification of the phase (the continuous branch
`argGammaHalf` is used; its relation to the polar argument of `Γ(½+is)` is not proved); (i) and (iii)
for the Gamma phase (the abstract (i) is `latticeI_bound`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory intervalIntegral

/-- Elementary bound `‖φ‖ |g| ≤ C (A + B|s|) e^{-κ|s|} ≤ C (A + 2B/κ) e^{-κ|s|/2}`. -/
lemma phi_gdens_le {κ Cφ A B u g s : ℝ} (hκ : 0 < κ) (hCφ : 0 ≤ Cφ)
    (hφs : u ≤ Cφ * Real.exp (-κ * |s|)) (hg : g ≤ A + B * |s|) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hg0 : 0 ≤ g) :
    u * g ≤ Cφ * (A + 2 * B / κ) * Real.exp (-(κ / 2) * |s|) := by
  have hs0 := abs_nonneg s
  have e1 : Real.exp (-κ * |s|) = Real.exp (-(κ / 2) * |s|) * Real.exp (-(κ / 2) * |s|) := by
    rw [← Real.exp_add]; ring_nf
  have hE0 := (Real.exp_pos (-(κ / 2) * |s|)).le
  have e3 : |s| * Real.exp (-(κ / 2) * |s|) ≤ 2 / κ := by
    have h5 : κ / 2 * |s| ≤ Real.exp (κ / 2 * |s|) := by
      have := Real.add_one_le_exp (κ / 2 * |s|); linarith
    have h6 : Real.exp (-(κ / 2) * |s|) * Real.exp (κ / 2 * |s|) = 1 := by
      rw [← Real.exp_add]; simp
    rw [le_div_iff₀ hκ]
    have := mul_le_mul_of_nonneg_left h5 hE0
    nlinarith
  have step : (A + B * |s|) * Real.exp (-(κ / 2) * |s|) ≤ A + 2 * B / κ := by
    have h1 : B * (|s| * Real.exp (-(κ / 2) * |s|)) ≤ B * (2 / κ) :=
      mul_le_mul_of_nonneg_left e3 hB0
    have e2 : Real.exp (-(κ / 2) * |s|) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h2 : A * Real.exp (-(κ / 2) * |s|) ≤ A := by nlinarith
    calc (A + B * |s|) * Real.exp (-(κ / 2) * |s|)
        = A * Real.exp (-(κ / 2) * |s|) + B * (|s| * Real.exp (-(κ / 2) * |s|)) := by ring
      _ ≤ A + B * (2 / κ) := add_le_add h2 h1
      _ = A + 2 * B / κ := by ring
  have h8 : Cφ * ((A + B * |s|) * Real.exp (-(κ / 2) * |s|)) ≤ Cφ * (A + 2 * B / κ) :=
    mul_le_mul_of_nonneg_left step hCφ
  calc u * g ≤ (Cφ * Real.exp (-κ * |s|)) * (A + B * |s|) :=
        mul_le_mul hφs hg hg0 (by positivity)
    _ = Cφ * ((A + B * |s|) * Real.exp (-(κ / 2) * |s|)) * Real.exp (-(κ / 2) * |s|) := by
        rw [e1]; ring
    _ ≤ Cφ * (A + 2 * B / κ) * Real.exp (-(κ / 2) * |s|) :=
        mul_le_mul_of_nonneg_right h8 hE0

/-- The fixed-`L` form of `latticesum_gamma`: all error terms explicit. -/
theorem latticesum_gamma_fixed (nc : ℕ) (hnc : 1 ≤ nc) {L Fm Fp cs δ κ b X θ0 y1 r r0 A1 A2 A3 : ℝ}
    (hL : 1 < L) (hFm : 0 < Fm) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hδ : 0 < δ)
    (hκ : 0 < κ) (hy1 : 0 < y1) (hr : 0 < r) (hr0 : 0 < r0) (hyr : y1 + r + r0 ≤ min δ (1 / 4))
    (hA : ∀ (Cφ ε X m : ℝ), 0 ≤ Cφ → 0 ≤ ε → ε ≤ 1 → 1 ≤ m →
      (1 / 2 + ε) * (2 * (Cφ * Real.exp (-κ * X))) +
      ε * (Cφ * Real.exp (κ * r0) / r0 * (2 / κ)) +
      (Cφ * Real.exp (κ * r0) / r0 * wconst κ * ε * (1 + 4 * (4 * m + 2 * ε + 1) / m) +
        (Cφ * Real.exp (κ * r0) / r0 * Real.exp (-κ * X) / m +
          1 / 12 * (2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m (nc * (16 * invSqSum) / Real.pi) * y1 *
              Real.exp (-κ * X) +
            2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m (nc * (16 * invSqSum) / Real.pi) / κ *
              Real.exp (-(2 * Real.pi * m * y1))))) ≤
      Cφ * (A1 * Real.exp (-κ * X) + A2 * ε + A3 * Real.exp (-(2 * Real.pi * m * y1))))
    (F : Fin nc → ℝ) (hF : ∀ i, Fm ≤ F i ∧ F i ≤ Fp)
    (hX : L ^ (cs / 2) ≤ X) (hXu : X ≤ L ^ cs)
    (h1 : Real.log 3 + 5 - Real.log Fm ≤ (1 / 2 - cs) * Real.log L)
    (h2 : Real.log Fp + 3 ≤ Real.log L) (hm1 : 2 * Real.pi ≤ nc * Real.log L)
    (hℓ0 : 0 ≤ lsum nc L F) (hε4 : L ^ (-b) ≤ 1 / 4)
    (Θ : ℝ → ℝ) (hΘc : ContinuousOn Θ (Icc (-X) X)) (hΘm : StrictMonoOn Θ (Icc (-X) X))
    (hΘG : ∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) (S : Finset ℝ)
    (hS : ∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) :
    ((∀ a a' : ℝ, -X ≤ a → a ≤ a' → a' ≤ X →
        ((S.filter fun x => x ∈ Icc a a').card : ℝ) ≤ 2 * nc * Real.log L / Real.pi * (a' - a) + 2) ∧
     (∀ x ∈ S, ∀ y ∈ S, x < y → (∀ z ∈ S, ¬(x < z ∧ z < y)) →
        Real.pi / (4 * nc * Real.log L) ≤ y - x ∧ y - x ≤ 4 * Real.pi / (nc * Real.log L))) ∧
    ∀ (φ : ℂ → ℂ) (Cφ : ℝ), 0 ≤ Cφ → DifferentiableOn ℂ φ {s | |s.im| ≤ δ} →
      (∀ s : ℂ, |s.im| ≤ δ → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|)) →
      ‖∑ x ∈ S, φ (x : ℂ) - ∫ s : ℝ, φ (s : ℂ) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)‖ ≤
        Cφ * (A1 * Real.exp (-κ * X) + A2 * (L ^ (-b) / Real.pi) +
          A3 * Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1))) +
        2 * (Cφ * ((lsum nc L F + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ)) *
          Real.exp (-(κ / 2) * X) / (κ / 2) := by
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hpi := Real.pi_pos
  have hncr : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
  set ℓ := lsum nc L F with hℓ
  set m : ℝ := nc * Real.log L / (2 * Real.pi) with hm
  have hm1' : 1 ≤ m := by rw [hm, le_div_iff₀ (by positivity)]; linarith
  set ε : ℝ := L ^ (-b) / Real.pi with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 / 4 := by
    rw [hε, div_le_iff₀ hpi]
    nlinarith [Real.pi_gt_three]
  have hCal := gamma_calPhase nc hnc hL hFm F hF hcs0 hcs hX hXu h1 h2 (θ0 := θ0)
  have hy0c : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hCal' := hCal.mono hy0c (min_le_right _ _)
  have hX0 : 0 < X := hCal.hX
  -- level data
  obtain ⟨t', hd, ht'⟩ := exists_levelData hCal' (continuous_realPhase_gamma nc ℓ θ0)
    (t := fun s => Θ s / Real.pi) (ε := ε)
    (hΘc.div_const _) (fun x hx y hy hxy => div_lt_div_of_pos_right (hΘm hx hy hxy) hpi) hε0
    (fun s hs => by
      rw [realPhase_gamma, ← sub_div, abs_div, abs_of_pos hpi]
      exact div_le_div_of_nonneg_right (hΘG s hs) hpi.le) (S := S)
    (fun x => by
      rw [hS x]
      refine and_congr_right (fun _ => exists_congr (fun n => ?_))
      rw [div_eq_iff hpi.ne'])
  have hmMeq : 4 * m = 2 * nc * Real.log L / Real.pi := by rw [hm]; field_simp; ring
  refine ⟨⟨fun a a' ha haa' ha' => ?_, fun x hx y hy hxy hcons => ?_⟩, fun φ Cφ hCφ hφd hφb => ?_⟩
  · have := hd.card_levels_le haa' ha ha'
    rw [hmMeq] at this
    linarith
  · have h3 := hd.spacing_ge hx hy hxy hcons
    have h4 := hd.spacing_le hx hy hxy hcons
    have hM : 4 * m = 2 * nc * Real.log L / Real.pi := hmMeq
    have hnl : 0 < (nc : ℝ) * Real.log L := mul_pos (by positivity) hlogL
    constructor
    · refine le_trans ?_ h3
      have e : (1 - 2 * ε) / (4 * m) = (1 - 2 * ε) * Real.pi / (2 * (nc * Real.log L)) := by
        rw [hm]; field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hpi hnl]
    · refine h4.trans ?_
      have e : (1 + 2 * ε) / m = (1 + 2 * ε) * (2 * Real.pi) / (nc * Real.log L) := by
        rw [hm]; field_simp
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hpi hnl]
  · have hφd' : DifferentiableOn ℂ φ {s | |s.im| ≤ min δ (1 / 4)} :=
      hφd.mono (fun s (hs : |s.im| ≤ min δ (1 / 4)) => show |s.im| ≤ δ from le_trans hs (min_le_left _ _))
    have hφb' : ∀ s : ℂ, |s.im| ≤ min δ (1 / 4) → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|) :=
      fun s hs => hφb s (hs.trans (min_le_left _ _))
    have hII := latticeII_bound hd (φ := φ) (Cφ := Cφ) (κ := κ) (y1 := y1) (r := r) (r0 := r0)
      hκ hCφ hy1 hr hr0 hyr hφd' hφb'
    have hE := hA Cφ ε X m hCφ hε0 (by linarith) hm1'
    have hφc : Continuous (fun s : ℝ => φ (s : ℂ)) := continuous_real_of_strip hy0c hφd'
    set f : ℝ → ℂ := fun s => φ (s : ℂ) * ((gdens nc ℓ s : ℝ) : ℂ) with hf
    have hfc : Continuous f := by
      have := continuous_gdens nc ℓ
      exact hφc.mul (Complex.continuous_ofReal.comp this)
    have hint_eq : ∫ s in (-X)..X, φ (s : ℂ) * ((CalPhase.realDeriv (gammaPhase nc ℓ θ0) s : ℝ) : ℂ) =
        ∫ s in (-X)..X, f s := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [hf, realDeriv_gamma]
    rw [hint_eq] at hII
    -- the tail
    have hfb : ∀ s, ‖f s‖ ≤ Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ) *
        Real.exp (-(κ / 2) * |s|) := by
      intro s
      have hφs : ‖φ (s : ℂ)‖ ≤ Cφ * Real.exp (-κ * |s|) := by
        have := hφb (s : ℂ) (by simpa using hδ.le)
        simpa using this
      simp only [hf]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact phi_gdens_le hκ hCφ hφs (abs_gdens_le nc hℓ0 s) (by positivity) (by positivity)
        (abs_nonneg _)
    have hD : 0 ≤ Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ) := by positivity
    obtain ⟨_, htail⟩ := tail_integral_le hfc (a := κ / 2) (X := X) (by positivity) hD hX0.le hfb
    have hfin : ‖∑ x ∈ S, φ (x : ℂ) - ∫ s : ℝ, f s‖ ≤
        ‖∑ x ∈ S, φ (x : ℂ) - ∫ s in (-X)..X, f s‖ + ‖(∫ s : ℝ, f s) - ∫ s in (-X)..X, f s‖ := by
      have : ∑ x ∈ S, φ (x : ℂ) - ∫ s : ℝ, f s =
          (∑ x ∈ S, φ (x : ℂ) - ∫ s in (-X)..X, f s) - ((∫ s : ℝ, f s) - ∫ s in (-X)..X, f s) := by ring
      rw [this]; exact norm_sub_le _ _
    simp only [hf] at hfin hII htail ⊢
    refine hfin.trans (add_le_add (hII.trans ?_) htail)
    convert hE using 3

end FormalResearch.Special.Lattice
