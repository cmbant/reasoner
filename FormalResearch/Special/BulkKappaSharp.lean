module

public import FormalResearch.Special.BulkKappaAbs

/-!
# The sharp amplitude and the bulk form for the same Airy window (abstract, both lattices)

`bk_sharp_abs` (integer lattice `q_k = (k+½)h`, rows `hrAk, hrCk`) and `bk_sharp_absH` (half-integer lattice `q_k = (k+1)h`, rows `hrAkH, hrCkH`) have the hypotheses of `rk_kappa_sharp_abs`, `rk_kappa_sharp_absH`
(`RacahKappaSharp`, `RacahKappaHSharp`): a family `Fam` of solutions `Y` of the closed-form rows with Gauss weight `M h √s = 1`, `Y² ≤ M`, bounded support, total mass `M`, monotone tail beyond `q_* + h`, vanishing
left mass.  They conclude, with **one** set of constants `r, C_μ, ξ₀, g, c₁, c₂, C_A, δ_A` (`cs = 1/√s + 1`):

* (window) every member with `h ≤ δ_A³` has an Airy window `RkWinAt(H)` (`Y_max = cs/δ³`), with coefficients `κ, μ`;
* (sharp) for every `τ' > 0` there is `ε₁` such that for every member with `h ≤ ε₁`, **every** such window has `|κ² δ - 2| ≤ τ'`;
* (bulk) for every bulk window `[c, q_* - η]` there are `δ₀, C` such that for every member with `h ≤ δ₀³`, **every** such window satisfies the Liouville-Green bulk form `BkBulkAt`
  `Y_k = h^{1/6} π^{-1/2} w(q_k) (κ cos χ_k + μ sin χ_k) + O(C h^{7/6}(|κ| + |μ|) w(q_k))`, `χ_k = Θ(q_k)/h - Θ_*/h + π/4`, with the same `κ, μ`.

Together: **the amplitude of the bulk oscillation is `h^{1/6}|κ|/√π = √(2/π)(1 + o(1))` times the profile `w`** (the explicit compositions are in `BulkKappaExplicit`).

**Claim class: proved** (hypotheses on `Fam` as in `rk_kappa_sharp_abs`).  **Not formalised:** the sign of `κ` (the window and bulk form are for the window's `κ`; only `κ²` is pinned), the dependence of `ε₁, δ₀, C` on the data.
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma bk_cbrt {h : ℝ} (hh : 0 < h) : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
  refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
  norm_num

lemma bk_le_of_cube {δ δA : ℝ} (hδ : 0 < δ) (hA : 0 < δA) (h : δ ^ 3 ≤ δA ^ 3) : δ ≤ δA := by
  by_contra hcon
  push Not at hcon
  have : δA ^ 3 < δ ^ 3 := by gcongr
  linarith

/-- **The sharp amplitude and the bulk form for the same window, integer lattice** (see the module docstring). -/
theorem bk_sharp_abs {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hosc0 : ∀ q : ℝ, 0 < q → q < qs → |hrU P Q τ x q| < 1) (Rmax : ℝ) (hRmax : 0 ≤ Rmax)
    (Fam : ℝ → (ℤ → ℝ) → ℝ → Prop)
    (hrows : ∀ h Y M, Fam h Y M → ∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0)
    (hmass : ∀ h Y M, Fam h Y M → 0 < h → M * h * Real.sqrt (rkS P Q x) = 1)
    (hYle : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Y k ^ 2 ≤ M)
    (hsupp : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Rmax < ((k : ℝ) + 1 / 2) * h → Y k = 0)
    (hMeq : ∀ h Y M, Fam h Y M → ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = M)
    (hmono : ∀ h Y M, Fam h Y M → ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + 1 / 2) * h → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ cL hL : ℝ, 0 < cL ∧ 0 < hL ∧ ∀ h Y M, Fam h Y M → 0 < h → h ≤ hL →
      ∀ kc : ℤ, ((kc : ℝ) - 1 / 2) * h ≤ cL → ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ ε * M) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA δA : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧
      gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 < δA ∧
      (∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ δA ^ 3 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m N : ℤ) (κ μ : ℝ),
          RkWinAt P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ) ∧
      (∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε1 →
        ∀ (δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < δ → δ ^ 3 = h →
          RkWinAt P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
            |κ ^ 2 * δ - 2| ≤ τ') ∧
      (∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
        ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ δ0 ^ 3 →
          ∀ (δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < δ → δ ^ 3 = h →
            RkWinAt P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
              BkBulkAt (δ ^ 3 / 2) P Q τ x qs c0 c η δ C Y κ μ) := by
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  have hspos : 0 < rkS P Q x := by
    have h1 : 0 < 1 - x ^ 2 := by linarith
    rw [hs] at h1
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg qs]
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, hδA, Hex, Hbulk, Hband⟩ :=
    bk_win hP hQ a b τ x qs hqs hτ hκ hα hβ hturn hosc0
  have Hs := bk_sharp_absG hP hQ τ x qs hqs hτ hκ hα hβ hturn (1 / 2) (by norm_num) (by norm_num) (fun δ => δ ^ 3 / 2)
    (fun h Y => ∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0) Rmax hRmax r Cmu ξ0 gmax gmin c1 c2 CA hr hrq4 hCA hCmu
    hξ0 hgmax hc1 hc12 Hband Fam hrows hmass hYle hsupp hMeq hmono
    (fun ε hε => by
      obtain ⟨cL, hL, hcL, hhL, HL⟩ := hLeft ε hε
      exact ⟨cL, hL, hcL, hhL, fun h Y M hF hh hhL' kc hkc => HL h Y M hF hh hhL' kc (by linarith)⟩)
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, min δA 1, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, lt_min hδA one_pos, ?_, Hs, ?_⟩
  · intro h Y M hF hh hhA
    obtain ⟨δ, hδ, hδ3⟩ := bk_cbrt hh
    have hδA' : δ ≤ min δA 1 := bk_le_of_cube hδ (lt_min hδA one_pos) (by rw [hδ3]; exact hhA)
    subst hδ3
    have hM := hmass _ Y M hF hh
    obtain ⟨J, m, N, κ, μ, hW⟩ := Hex δ Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) hδ (hδA'.trans (min_le_left _ _)) (hrows _ Y M hF)
      (fun k _ => rk_tail_bd hδ (hδA'.trans (min_le_right _ _)) hsq hM (hYle _ Y M hF k))
    exact ⟨δ, hδ, rfl, J, m, N, κ, μ, hW⟩
  · intro c0 hc0 hc0q η hη hηr c hc0c hcr
    obtain ⟨δ0, C, hδ0, hC, HH⟩ := Hbulk c0 hc0 hc0q η hη hηr c hc0c hcr
    refine ⟨min δ0 1, C, lt_min hδ0 one_pos, hC, ?_⟩
    intro h Y M hF hh hhδ δ J m N κ μ hδ hδ3 hW
    subst hδ3
    have hδle : δ ≤ min δ0 1 := bk_le_of_cube hδ (lt_min hδ0 one_pos) hhδ
    have hM := hmass _ Y M hF hh
    exact HH δ Y _ hδ (hδle.trans (min_le_left _ _)) (hrows _ Y M hF)
      (fun k _ => rk_tail_bd hδ (hδle.trans (min_le_right _ _)) hsq hM (hYle _ Y M hF k)) J m N κ μ hW

/-- info: 'FormalResearch.Special.bk_sharp_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_sharp_abs

/-- **The sharp amplitude and the bulk form for the same window, half-integer lattice** (see the module docstring). -/
theorem bk_sharp_absH {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hosc0 : ∀ q : ℝ, 0 < q → q < qs → |hrU P Q τ x q| < 1) (Rmax : ℝ) (hRmax : 0 ≤ Rmax)
    (Fam : ℝ → (ℤ → ℝ) → ℝ → Prop)
    (hrows : ∀ h Y M, Fam h Y M → ∀ k : ℤ, 1 ≤ k → jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0)
    (hmass : ∀ h Y M, Fam h Y M → 0 < h → M * h * Real.sqrt (rkS P Q x) = 1)
    (hYle : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Y k ^ 2 ≤ M)
    (hsupp : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Rmax < ((k : ℝ) + 1) * h → Y k = 0)
    (hMeq : ∀ h Y M, Fam h Y M → ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = M)
    (hmono : ∀ h Y M, Fam h Y M → ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + 1) * h → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2)
    (hLeft : ∀ ε : ℝ, 0 < ε → ∃ cL hL : ℝ, 0 < cL ∧ 0 < hL ∧ ∀ h Y M, Fam h Y M → 0 < h → h ≤ hL →
      ∀ kc : ℤ, (kc : ℝ) * h ≤ cL → ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ ε * M) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA δA : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧
      gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 < δA ∧
      (∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ δA ^ 3 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m N : ℤ) (κ μ : ℝ),
          RkWinAtH P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ) ∧
      (∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε1 →
        ∀ (δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < δ → δ ^ 3 = h →
          RkWinAtH P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
            |κ ^ 2 * δ - 2| ≤ τ') ∧
      (∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
        ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ δ0 ^ 3 →
          ∀ (δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < δ → δ ^ 3 = h →
            RkWinAtH P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
              BkBulkAt (δ ^ 3) P Q τ x qs c0 c η δ C Y κ μ) := by
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  have hspos : 0 < rkS P Q x := by
    have h1 : 0 < 1 - x ^ 2 := by linarith
    rw [hs] at h1
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg qs]
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, hδA, Hex, Hbulk, Hband⟩ :=
    bk_winH hP hQ a b τ x qs hqs hτ hκ hα hβ hturn hosc0
  have Hs := bk_sharp_absG hP hQ τ x qs hqs hτ hκ hα hβ hturn 1 (by norm_num) (by norm_num) (fun δ => δ ^ 3)
    (fun h Y => ∀ k : ℤ, 1 ≤ k → jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0) Rmax hRmax r Cmu ξ0 gmax gmin c1 c2 CA hr hrq4 hCA hCmu
    hξ0 hgmax hc1 hc12 Hband Fam hrows hmass hYle hsupp hMeq hmono
    (fun ε hε => by
      obtain ⟨cL, hL, hcL, hhL, HL⟩ := hLeft ε hε
      exact ⟨cL, hL, hcL, hhL, fun h Y M hF hh hhL' kc hkc => HL h Y M hF hh hhL' kc (by linarith)⟩)
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, min δA 1, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, lt_min hδA one_pos, ?_, Hs, ?_⟩
  · intro h Y M hF hh hhA
    obtain ⟨δ, hδ, hδ3⟩ := bk_cbrt hh
    have hδA' : δ ≤ min δA 1 := bk_le_of_cube hδ (lt_min hδA one_pos) (by rw [hδ3]; exact hhA)
    subst hδ3
    have hM := hmass _ Y M hF hh
    obtain ⟨J, m, N, κ, μ, hW⟩ := Hex δ Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) hδ (hδA'.trans (min_le_left _ _)) (hrows _ Y M hF)
      (fun k _ => rk_tail_bd hδ (hδA'.trans (min_le_right _ _)) hsq hM (hYle _ Y M hF k))
    exact ⟨δ, hδ, rfl, J, m, N, κ, μ, hW⟩
  · intro c0 hc0 hc0q η hη hηr c hc0c hcr
    obtain ⟨δ0, C, hδ0, hC, HH⟩ := Hbulk c0 hc0 hc0q η hη hηr c hc0c hcr
    refine ⟨min δ0 1, C, lt_min hδ0 one_pos, hC, ?_⟩
    intro h Y M hF hh hhδ δ J m N κ μ hδ hδ3 hW
    subst hδ3
    have hδle : δ ≤ min δ0 1 := bk_le_of_cube hδ (lt_min hδ0 one_pos) hhδ
    have hM := hmass _ Y M hF hh
    exact HH δ Y _ hδ (hδle.trans (min_le_left _ _)) (hrows _ Y M hF)
      (fun k _ => rk_tail_bd hδ (hδle.trans (min_le_right _ _)) hsq hM (hYle _ Y M hF k)) J m N κ μ hW

/-- info: 'FormalResearch.Special.bk_sharp_absH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_sharp_absH

end FormalResearch.Special
