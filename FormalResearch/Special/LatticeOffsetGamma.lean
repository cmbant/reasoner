module

public import FormalResearch.Special.LatticeOffset
public import FormalResearch.Special.LatticeIIIGamma

/-!
# `prop:offsetcore` (i) and (ii) for the Gamma phase, unconditionally

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `prop:offsetcore`.  Setting of `latticesum_gamma_iii`
(`ϰ = nc`, `Θ`, `S`, `t₀ = Θ(0)/π`, `ℓ = ℓ_Σ = lsum nc L F`), together with the finite data
`𝔱 = ∑_{x∈S} λ(x) + k₀ + ∑_{s∈M} μ_s`, `|λ(x) - ν(2πx)| ≤ ε_λ`, `k₀ ∈ ℤ`, `μ_s ∈ [0,1]`,
`∑ μ_s(1-μ_s) ≤ ε_μ`, and `ε_𝔱 = L^{-b₁} + nc X (log L) ε_λ + ε_μ`.  Then for `L ≥ L₀`:

* (i) if `{t₀} ≠ 0`: `|𝔱 - (k₀ + K₊ + r₀ + {t₀} - ½)| ≤ C ε_𝔱`, with `K₊ = #{s : μ_s > ½}`,
  `r₀ = #{x ∈ S : x < 0}`; and in all cases `∃ m ∈ ℤ, |t₀ - 𝔱 - ½ - m| ≤ C ε_𝔱`;
* (ii) if some `x ∈ S` has `|e - 2πx| ≤ ε_e` then `∃ m ∈ ℤ`,
  `|𝒩(e) + 𝔱 + ½ - m| ≤ C(ε_𝔱 + L^{-b} + nc ε_e log L)`, where `𝒩(e) = Θ_mod(e/2π)/π`,
  `Θ_mod(s) = sℓ_Σ - ϰ arg Γ(½+is)` (`gammaG nc ℓ 0`).

(i) is the deduction `offsetcore_i_of_iii` (`LatticeOffset`) fed by the proved `latticesum_gamma_iii`, with
`n = #S ≤ 4 nc X log L` from `latticesum_gamma` (o).  (ii) follows the paper: `Θ(x_r) ∈ πℤ`, `θ₀ = G(0)`,
`|Θ - G| ≤ L^{-b}`, and the slope bound `|d𝒩/de| ≤ C nc log L` (from `CalPhase.real_slope_le`).  Where
`ε_e ≥ 1` the claim is trivial (a distance to `ℤ` is `≤ ½`) and is handled as such.

Not formalised: the identification of `argGammaHalf` with the polar argument of `Γ(½+is)`.
-/

@[expose] public section

universe u

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory intervalIntegral

lemma gammaG_add (nc : ℕ) (ℓ θ0 s : ℝ) : gammaG nc ℓ θ0 s = θ0 + gammaG nc ℓ 0 s := by
  unfold gammaG; ring

lemma gammaG_zero (nc : ℕ) (ℓ θ0 : ℝ) : gammaG nc ℓ θ0 0 = θ0 := by
  have h0 : argGammaHalf ((0 : ℝ) : ℂ) = 0 := by
    have := argGammaHalf_neg (0 : ℂ)
    simp only [neg_zero] at this
    have h2 : argGammaHalf 0 = 0 := by linear_combination (1 / 2 : ℂ) * this
    simpa using h2
  unfold gammaG
  rw [h0]; simp

/-- Distance to `ℤ` is at most `1/2`. -/
lemma exists_int_half (v : ℝ) : ∃ m : ℤ, |v - m| ≤ 1 / 2 := ⟨round v, abs_sub_round v⟩

lemma CalPhase.abs_realPhase_sub_le {τ0 : ℂ → ℂ} {X y0 m M K : ℝ} (h : CalPhase τ0 X y0 m M K) {x y : ℝ}
    (hx : |x| ≤ X + 1) (hy : |y| ≤ X + 1) : |realPhase τ0 y - realPhase τ0 x| ≤ M * |y - x| := by
  rcases le_total x y with hxy | hxy
  · have h1 := h.real_slope_ge hx hy hxy
    have h2 := h.real_slope_le hx hy hxy
    have hm := h.hm
    rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by linarith)]
    exact h2
  · have h1 := h.real_slope_ge hy hx hxy
    have h2 := h.real_slope_le hy hx hxy
    have hm := h.hm
    rw [abs_of_nonpos (by nlinarith), abs_of_nonpos (by linarith)]
    linarith

/-- Algebra: the number of levels `n ≤ 4 nc X log L`. -/
lemma card_le_four {nc n X lg : ℝ} (hnc : 1 ≤ nc) (hX : 1 ≤ X) (hlg : 1 ≤ lg)
    (h0 : n ≤ 2 * nc * lg / Real.pi * (X - -X) + 2) : n ≤ 4 * nc * X * lg := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hP : 1 ≤ nc * X * lg := by
    have h1 : 1 ≤ nc * X := by nlinarith
    nlinarith
  have e : 2 * nc * lg / Real.pi * (X - -X) = 4 * (nc * X * lg) / Real.pi := by
    field_simp; ring
  rw [e] at h0
  have h3 : 4 * (nc * X * lg) / Real.pi ≤ (4 / 3) * (nc * X * lg) := by
    rw [div_le_iff₀ hpi]; nlinarith
  nlinarith

/-- The core of (ii): at fixed `L`, given the calibration `hCal` and the offset information (i). -/
lemma offsetcore_ii_core (nc : ℕ) {L b X θ0 ℓ m e εe tt B : ℝ} {Θ : ℝ → ℝ} {S : Finset ℝ} {K : ℝ}
    (hnc : 1 ≤ nc) (hL1 : 1 < L) (hm : m = nc * Real.log L / (2 * Real.pi))
    (hCal : CalPhase (gammaPhase nc ℓ θ0) X (1 / 4) m (4 * m) K) (hεe0 : 0 ≤ εe) (hεe1 : εe < 1)
    (hΘG : ∀ s ∈ Icc (-X) X, |Θ s - gammaG nc ℓ θ0 s| ≤ L ^ (-b))
    (hS : ∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) {x : ℝ} (hxS : x ∈ S)
    (hxe : |e - 2 * Real.pi * x| ≤ εe) (hB : ∃ m1 : ℤ, |Θ 0 / Real.pi - tt - 1 / 2 - m1| ≤ B) :
    ∃ k : ℤ, |gammaG nc ℓ 0 (e / (2 * Real.pi)) / Real.pi + tt + 1 / 2 - k| ≤
      B + L ^ (-b) + nc * εe * Real.log L := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hncr : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log L := Real.log_pos hL1
  obtain ⟨m1, hm1⟩ := hB
  have hxI := (hS x).mp hxS
  obtain ⟨hxIcc, n, hn⟩ := hxI
  have hX0 : 0 < X := hCal.hX
  have hxw : |x| ≤ X + 1 := by rw [abs_le]; constructor <;> linarith [hxIcc.1, hxIcc.2]
  have hxa : |x| ≤ X := abs_le.mpr ⟨hxIcc.1, hxIcc.2⟩
  have hxu : |e / (2 * Real.pi) - x| ≤ εe / (2 * Real.pi) := by
    have : e / (2 * Real.pi) - x = (e - 2 * Real.pi * x) / (2 * Real.pi) := by field_simp
    rw [this, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact div_le_div_of_nonneg_right hxe (by positivity)
  have hu : |e / (2 * Real.pi)| ≤ X + 1 := by
    have h2 : |e / (2 * Real.pi) - x| ≤ 1 := by
      refine hxu.trans ?_
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have := abs_sub_abs_le_abs_sub (e / (2 * Real.pi)) x
    linarith
  have hlip := hCal.abs_realPhase_sub_le hxw hu
  rw [realPhase_gamma, realPhase_gamma, ← sub_div, abs_div, abs_of_pos hpi, gammaG_add nc ℓ θ0,
    gammaG_add nc ℓ θ0] at hlip
  have e1 : θ0 + gammaG nc ℓ 0 (e / (2 * Real.pi)) - (θ0 + gammaG nc ℓ 0 x) =
      gammaG nc ℓ 0 (e / (2 * Real.pi)) - gammaG nc ℓ 0 x := by ring
  rw [e1] at hlip
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hlip2 : |gammaG nc ℓ 0 (e / (2 * Real.pi)) - gammaG nc ℓ 0 x| / Real.pi ≤
      nc * Real.log L * εe := by
    refine hlip.trans ?_
    calc 4 * m * |e / (2 * Real.pi) - x| ≤ 4 * m * (εe / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hxu (by positivity)
      _ = nc * Real.log L * εe / Real.pi ^ 2 := by rw [hm]; field_simp; ring
      _ ≤ nc * Real.log L * εe := by
          rw [div_le_iff₀ (by positivity)]
          have : 0 ≤ nc * Real.log L * εe := by positivity
          have h9 : 1 ≤ Real.pi ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h9 this]
  -- calibration at `x`
  have hΘ0 := hΘG 0 ⟨by linarith, hX0.le⟩
  rw [gammaG_zero] at hΘ0
  have hΘx := hΘG x hxIcc
  rw [hn, gammaG_add nc ℓ θ0] at hΘx
  set g := gammaG nc ℓ 0 x with hg
  set Ne := gammaG nc ℓ 0 (e / (2 * Real.pi)) / Real.pi with hNe
  have hlip3 : |Ne - g / Real.pi| ≤ nc * Real.log L * εe := by
    have : Ne - g / Real.pi = (gammaG nc ℓ 0 (e / (2 * Real.pi)) - g) / Real.pi := by
      rw [hNe]; ring
    rw [this, abs_div, abs_of_pos hpi]; exact hlip2
  refine ⟨n - m1, ?_⟩
  have hq : Ne + tt + 1 / 2 - (((n - m1 : ℤ)) : ℝ) = (Ne - g / Real.pi) +
      ((Θ 0 - θ0) - (n * Real.pi - (θ0 + g))) / Real.pi - (Θ 0 / Real.pi - tt - 1 / 2 - m1) := by
    push_cast; field_simp; ring
  rw [hq]
  have hd : |((Θ 0 - θ0) - (n * Real.pi - (θ0 + g))) / Real.pi| ≤ L ^ (-b) := by
    rw [abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    have h1 : |(Θ 0 - θ0) - (n * Real.pi - (θ0 + g))| ≤ |Θ 0 - θ0| + |n * Real.pi - (θ0 + g)| := abs_sub _ _
    have h2 : |n * Real.pi - (θ0 + g)| = |(n * Real.pi - (θ0 + g))| := rfl
    have hLp : 0 ≤ L ^ (-b) := (Real.rpow_pos_of_pos hL0 _).le
    nlinarith [hΘ0, hΘx]
  have hs1 := abs_sub ((Ne - g / Real.pi) + ((Θ 0 - θ0) - (n * Real.pi - (θ0 + g))) / Real.pi)
    (Θ 0 / Real.pi - tt - 1 / 2 - m1)
  have hs2 := abs_add_le (Ne - g / Real.pi) (((Θ 0 - θ0) - (n * Real.pi - (θ0 + g))) / Real.pi)
  have hne : nc * εe * Real.log L = nc * Real.log L * εe := by ring
  linarith


/-- **`prop:offsetcore` (i), (ii) for the Gamma phase** (paper form), with `ε_𝔱 = L^{-b₁} + nc X (log L) ε_λ + ε_μ`.
`C, L₀` depend only on `nc, b, c_*, b₁, F_±`. -/
theorem offsetcore_gamma (nc : ℕ) (hnc : 1 ≤ nc) {b cs b1 Fm Fp : ℝ}
    (hb : 0 < b) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hb1 : 0 < b1) (hb1b : b1 < b)
    (hb1δ : b1 < nc * (1 / 4)) (hFm : 0 < Fm) (hFmp : Fm ≤ Fp) :
    ∃ C L0 : ℝ, 0 < C ∧ 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ F : Fin nc → ℝ, (∀ i, Fm ≤ F i ∧ F i ≤ Fp) →
      ∀ (X θ0 : ℝ), L ^ (cs / 2) ≤ X → X ≤ L ^ cs →
      ∀ Θ : ℝ → ℝ, ContinuousOn Θ (Icc (-X) X) → StrictMonoOn Θ (Icc (-X) X) →
      (∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) →
      ∀ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) →
      ∀ (ι : Type u) (M : Finset ι) (lam : ℝ → ℝ) (mu : ι → ℝ) (k0 : ℤ) (tt epl epm : ℝ),
        0 ≤ epl → 0 ≤ epm → (∀ x ∈ S, |lam x - nuR (2 * Real.pi * x)| ≤ epl) →
        (∀ s ∈ M, 0 ≤ mu s ∧ mu s ≤ 1) → ∑ s ∈ M, mu s * (1 - mu s) ≤ epm →
        tt = ∑ x ∈ S, lam x + k0 + ∑ s ∈ M, mu s →
        ((Int.fract (Θ 0 / Real.pi) ≠ 0 →
            |tt - (k0 + ((M.filter fun s => 1 / 2 < mu s).card : ℝ) +
              ((S.filter fun x => x < 0).card : ℝ) + (Int.fract (Θ 0 / Real.pi) - 1 / 2))| ≤
              C * (L ^ (-b1) + nc * X * Real.log L * epl + epm)) ∧
         ∃ m : ℤ, |Θ 0 / Real.pi - tt - 1 / 2 - m| ≤ C * (L ^ (-b1) + nc * X * Real.log L * epl + epm)) ∧
        ∀ e εe : ℝ, 0 ≤ εe → (∃ x ∈ S, |e - 2 * Real.pi * x| ≤ εe) →
          ∃ m : ℤ, |gammaG nc (lsum nc L F) 0 (e / (2 * Real.pi)) / Real.pi + tt + 1 / 2 - m| ≤
            C * ((L ^ (-b1) + nc * X * Real.log L * epl + epm) + L ^ (-b) + nc * εe * Real.log L) := by
  have hncpos : (0 : ℝ) < nc := by exact_mod_cast hnc
  have hncr : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
  obtain ⟨C3, L3, hC3, hL3, H3⟩ := latticesum_gamma_iii nc hnc hb hcs0 hcs hb1 hb1b hb1δ hFm (Fp := Fp)
  obtain ⟨C0, L0', hC0, hL0', H0⟩ := latticesum_gamma nc hnc (b := b) (cs := cs) (δ := 1 / 4) (κ := 1)
    (b1 := b1) (Fm := Fm) (Fp := Fp) hb hcs0 hcs (by norm_num) one_pos hb1 hb1b
    (by rw [min_self]; exact hb1δ) hFm hFmp
  set Λ : ℝ := max (max ((Real.log 3 + 5 - Real.log Fm) / (1 / 2 - cs)) (Real.log Fp + 3)) 1 with hΛ
  refine ⟨4 + C3 + 1, max (max L3 L0') (Real.exp Λ + 1), by positivity,
    lt_of_lt_of_le hL3 ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro L hLL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS ι M lam mu k0 tt epl epm hepl hepm hlam hmu hμsum htt
  have hLL3 : L3 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hLL
  have hLL0 : L0' ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hLL
  have hLΛ : Real.exp Λ + 1 ≤ L := (le_max_right _ _).trans hLL
  have hL1 : 1 < L := by linarith [Real.exp_pos Λ]
  have hL0 : 0 < L := by linarith
  have hlogL : Λ ≤ Real.log L := (Real.le_log_iff_exp_le hL0).2 (by linarith)
  have hlog1 : 1 ≤ Real.log L := le_trans (le_max_right _ _) hlogL
  have hΛ2 : (Real.log 3 + 5 - Real.log Fm) / (1 / 2 - cs) ≤ Real.log L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlogL
  have hΛ3 : Real.log Fp + 3 ≤ Real.log L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlogL
  have h1 : Real.log 3 + 5 - Real.log Fm ≤ (1 / 2 - cs) * Real.log L := by
    have := (div_le_iff₀ (by linarith : 0 < 1 / 2 - cs)).1 hΛ2
    linarith
  obtain ⟨hIIIa, hIIIb⟩ := H3 L hLL3 F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow hL1.le (by positivity)) hX
  have hXpos : 0 < X := by linarith
  have hle : -X ≤ X := by linarith
  -- the number of levels
  have hcard : (S.card : ℝ) ≤ 4 * nc * X * Real.log L := by
    have h0 := (H0 L hLL0 F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS).1.1 (-X) X le_rfl hle le_rfl
    have hf : S.filter (fun x => x ∈ Icc (-X) X) = S :=
      Finset.filter_true_of_mem (fun x hx => ((hS x).mp hx).1)
    rw [hf] at h0
    exact card_le_four hncr hX1 hlog1 h0
  -- part (i)
  have hi := offsetcore_i_of_iii S M lam mu k0 (Θ 0 / Real.pi) tt epl epm (C3 * L ^ (-b1)) hlam hmu hμsum htt
    (by obtain ⟨m, hm⟩ := hIIIb; exact ⟨m, by linarith [hm]⟩)
    (fun hf => by have := hIIIa hf; linarith)
  have hLb1 : 0 < L ^ (-b1) := Real.rpow_pos_of_pos hL0 _
  have hcardE : (S.card : ℝ) * epl ≤ 4 * (nc * X * Real.log L * epl) := by
    have := mul_le_mul_of_nonneg_right hcard hepl
    linarith
  have hept : S.card * epl + 2 * epm + C3 * L ^ (-b1) ≤
      (4 + C3 + 1) * (L ^ (-b1) + nc * X * Real.log L * epl + epm) := by
    have h5 : 0 ≤ nc * X * Real.log L * epl := by positivity
    have h6 := mul_nonneg hC3.le h5
    have h7 := mul_nonneg hC3.le hepm
    linarith
  have hi' : (Int.fract (Θ 0 / Real.pi) ≠ 0 →
            |tt - (k0 + ((M.filter fun s => 1 / 2 < mu s).card : ℝ) +
              ((S.filter fun x => x < 0).card : ℝ) + (Int.fract (Θ 0 / Real.pi) - 1 / 2))| ≤
              (4 + C3 + 1) * (L ^ (-b1) + nc * X * Real.log L * epl + epm)) ∧
         ∃ m : ℤ, |Θ 0 / Real.pi - tt - 1 / 2 - m| ≤
          (4 + C3 + 1) * (L ^ (-b1) + nc * X * Real.log L * epl + epm) := by
    refine ⟨fun hf => ?_, ?_⟩
    · exact (hi.1 hf).trans (by linarith [hept])
    · obtain ⟨m, hm⟩ := hi.2
      exact ⟨m, hm.trans (by linarith [hept])⟩
  refine ⟨hi', ?_⟩
  -- part (ii)
  intro e εe hεe ⟨x, hxS, hxe⟩
  by_cases hbig : 1 ≤ εe
  · obtain ⟨m, hm⟩ := exists_int_half (gammaG nc (lsum nc L F) 0 (e / (2 * Real.pi)) / Real.pi + tt + 1 / 2)
    refine ⟨m, hm.trans ?_⟩
    have h1' : 1 ≤ nc * εe * Real.log L := by nlinarith [mul_nonneg hncpos.le hεe]
    have h2' : 0 ≤ (L ^ (-b1) + nc * X * Real.log L * epl + epm) + L ^ (-b) := by
      have : 0 ≤ nc * X * Real.log L * epl := by positivity
      have := Real.rpow_pos_of_pos hL0 (-b)
      linarith
    have hC : (1 : ℝ) ≤ 4 + C3 + 1 := by linarith
    calc (1 / 2 : ℝ) ≤ nc * εe * Real.log L := by linarith
      _ ≤ ((L ^ (-b1) + nc * X * Real.log L * epl + epm) + L ^ (-b)) + nc * εe * Real.log L := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by linarith) hC
  · have hbig := not_le.mp hbig
    have hCal := gamma_calPhase nc hnc hL1 hFm F hF hcs0 hcs hX hXu h1 hΛ3 (θ0 := θ0)
    obtain ⟨k, hk⟩ := offsetcore_ii_core nc hnc hL1 (hm := rfl) hCal hεe hbig hΘG hS hxS hxe hi'.2
    refine ⟨k, hk.trans ?_⟩
    have hb' : 0 ≤ L ^ (-b) := (Real.rpow_pos_of_pos hL0 _).le
    have hz : 0 ≤ nc * εe * Real.log L := by positivity
    have hC : (1 : ℝ) ≤ 4 + C3 + 1 := by linarith
    have a1 := mul_le_mul_of_nonneg_right hC hb'
    have a2 := mul_le_mul_of_nonneg_right hC hz
    linarith

/-- info: 'FormalResearch.Special.Lattice.offsetcore_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms offsetcore_gamma

end FormalResearch.Special.Lattice
