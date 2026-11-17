module

public import FormalResearch.Special.RacahKappaChain

/-!
# The sharp amplitude `κ²δ → 2` for the centred Racah / Hahn closed-form chains (abstract form)

`rk_kappa_sharp_abs`: let `Fam` be a family of chains `Y` at scales `h` (with Gauss weight `M`) of the closed-form rows `jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0` (`k ≥ 1`) with

* `M h √s = 1`, `s = P + Q - 2x√(PQ)`, and `Σ_{k ≥ 0} Y_k² = M` (support in `0 ≤ k`, `q_k ≤ R_max`), `Y_k² ≤ M`;
* monotone decay `Y_k² ≤ Y_{k'}²` for `k ≥ k'`, `q_{k'} ≥ q_* + h`;
* a vanishing left mass: for every `ε > 0` there are `c_L, h_L > 0` with `Σ_{k < k_c} Y_k² ≤ εM` for `h ≤ h_L`, `q_{k_c - 1} ≤ c_L`.

Then there are constants `r, C_μ, ξ₀, g, c₁, c₂, C_A, c_s` (depending on `P, Q, τ, x, a, b`) such that for every `τ' > 0` there is `ε₁` (depending on `τ'`, on `P, Q, τ, x, a, b`, and on the family only through the left-mass hypothesis) such that for every member with `h ≤ ε₁` there is an Airy window `RkWinAt` (with `Y_max = c_s/δ³`, `δ³ = h`)
with `|κ²δ - 2| ≤ τ'`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `|Y k| ≤ c_s/δ³` from `Y_k² ≤ M = 1/(δ³ √s)`. -/
lemma rk_tail_bd {δ sq M y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsq : 0 < sq) (hM : M * δ ^ 3 * sq = 1) (hy : y ^ 2 ≤ M) :
    |y| ≤ (1 / sq + 1) / δ ^ 3 := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hMe : M = (1 / sq) / δ ^ 3 := by
    have : δ ^ 3 * sq ≠ 0 := by positivity
    field_simp; linarith
  apply abs_le_of_sq_le_sq _ (by positivity)
  refine hy.trans ?_
  rw [hMe, div_pow, div_le_div_iff₀ hδ3 (pow_pos hδ3 2)]
  have h1 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hu : 0 < 1 / sq := by positivity
  have h2 : 1 / sq ≤ (1 / sq + 1) ^ 2 := by nlinarith
  have h3 : (1 / sq) * (δ ^ 3) ^ 2 ≤ (1 / sq) * δ ^ 3 := by
    have : (δ ^ 3) ^ 2 ≤ δ ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hu.le
  have h4 : (1 / sq) * δ ^ 3 ≤ (1 / sq + 1) ^ 2 * δ ^ 3 := mul_le_mul_of_nonneg_right h2 hδ3.le
  linarith

/-- A common smallness threshold for fourteen positive bounds. -/
lemma rk_delta_exists {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : ℝ} (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hb4 : 0 < b4)
    (hb5 : 0 < b5) (hb6 : 0 < b6) (hb7 : 0 < b7) (hb8 : 0 < b8) (hb9 : 0 < b9) (hb10 : 0 < b10) (hb11 : 0 < b11) (hb12 : 0 < b12)
    (hb13 : 0 < b13) (hb14 : 0 < b14) :
    ∃ δm : ℝ, 0 < δm ∧ ∀ δ : ℝ, δ ≤ δm → δ ≤ b1 ∧ δ ≤ b2 ∧ δ ≤ b3 ∧ δ ≤ b4 ∧ δ ≤ b5 ∧ δ ≤ b6 ∧ δ ≤ b7 ∧ δ ≤ b8 ∧ δ ≤ b9 ∧
      δ ≤ b10 ∧ δ ≤ b11 ∧ δ ≤ b12 ∧ δ ≤ b13 ∧ δ ≤ b14 := by
  refine ⟨min b1 (min b2 (min b3 (min b4 (min b5 (min b6 (min b7 (min b8 (min b9 (min b10 (min b11 (min b12 (min b13 (b14))))))))))))), (lt_min hb1 (lt_min hb2 (lt_min hb3 (lt_min hb4 (lt_min hb5 (lt_min hb6 (lt_min hb7 (lt_min hb8 (lt_min hb9 (lt_min hb10 (lt_min hb11 (lt_min hb12 (lt_min hb13 hb14))))))))))))), fun δ hδ => ?_⟩
  simp only [le_min_iff] at hδ
  exact hδ

/-- **The sharp constant, abstract form** (see the module docstring). -/
theorem rk_kappa_sharp_abs {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
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
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA cs : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧
      gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ cs ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m N : ℤ) (κ μ : ℝ),
          RkWinAt P Q τ x qs Y (cs / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  have hspos : 0 < rkS P Q x := by
    have h1 : 0 < 1 - x ^ 2 := by linarith
    rw [hs] at h1
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg qs]
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, Hb⟩ :=
    rk_bulk_band hP hQ a b τ x qs hqs hτ hκ hα hβ hturn hosc0
  have hc2 : 0 < c2 := hc1.trans_le hc12
  set sq : ℝ := Real.sqrt (rkS P Q x) with hsqdef
  set cs : ℝ := 1 / sq + 1 with hcsdef
  have hcs0 : 0 ≤ cs := by positivity
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, cs, hr, hrq4, hCA, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, hcs0, ?_⟩
  intro τ' hτ'
  set u : ℝ := min (τ' / 40) (1 / 6) with hudef
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  have hu40 : 40 * u ≤ τ' := by have := min_le_left (τ' / 40) (1 / 6); linarith
  have hu6 : u ≤ 1 / 6 := min_le_right _ _
  obtain ⟨cL, hL, hcL, hhL, HL⟩ := hLeft u hu
  set c : ℝ := min cL (min (u * qs) (qs / 2)) with hcdef
  have hcpos : 0 < c := lt_min hcL (lt_min (by positivity) (by positivity))
  have hc_cL : c ≤ cL := min_le_left _ _
  have hcu : c / qs ≤ u := by
    rw [div_le_iff₀ hqs]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcq2 : c ≤ qs / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨η, hη, hηr, hη1, hηu, hA0⟩ := rk_choose_eta hc1 hc2 hgmax.le hsq hu hqs hr
  have hc0 : 0 < c / 2 := by positivity
  obtain ⟨δ0, θ0, hδ0, hθ0, HB⟩ := Hb (c / 2) hc0 (by linarith) η hη hηr c (by linarith) (by linarith)
  set K3 : ℝ := rkzK3 c1 gmax CA 4 (Rmax + 2) with hK3def
  set A0v : ℝ := 2 * gmax ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1 with hA0vdef
  have hK30 : 0 ≤ K3 := rkzK3_nonneg hc1 (by norm_num) (by linarith)
  have hA0v0 : 0 ≤ A0v := by rw [hA0vdef]; positivity
  obtain ⟨δm, hδm, Hδ⟩ := rk_delta_exists (b1 := δ0) (b2 := 1) (b3 := hL) (b4 := (ξ0 / 14)) (b5 := (1 * ξ0 ^ 3 / (48 * ((450 * gmax + CA) * Cmu * cs + 1)))) (b6 := (η / 2)) (b7 := (c1 * η / (2 * (1 + c2)))) (b8 := (c1 * r / 8)) (b9 := (1 / c2)) (b10 := (1 * ξ0 ^ 3 / (48 * (Cmu * cs + 1)))) (b11 := (u / (θ0 + 1))) (b12 := (u / (8 * sq * K3 + 1))) (b13 := (u / (2 * sq * (A0v + K3) + 1))) (b14 := (8 * u)) hδ0 one_pos hhL (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  refine ⟨δm ^ 3, by positivity, ?_⟩
  intro h Y M hF hh hhδ
  obtain ⟨δ, hδ, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  subst hδ3
  have hδle : δ ≤ δm := by
    by_contra hcon
    push Not at hcon
    have : δm ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨d0, d1, dL, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := Hδ δ hδle
  have hM := hmass _ Y M hF hh
  have hδ3le : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le d1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hbd : ∀ k : ℤ, qs + δ ^ 3 ≤ ((k : ℝ) + 1 / 2) * δ ^ 3 → |Y k| ≤ cs / δ ^ 3 := fun k _ =>
    rk_tail_bd hδ d1 hsq hM (hYle _ Y M hF k)
  obtain ⟨J, m, N, κ, μ, hWin, hbands⟩ := HB δ Y (cs / δ ^ 3) hδ d0 (hrows _ Y M hF) hbd
  obtain ⟨kc, jz, hkc1, hkc2, hjz1, hjz2⟩ := rk_idx (θ := 1 / 2) (c := c) (d := qs - η) hδ
  obtain ⟨hBlo, hBhi⟩ := hbands kc jz M hkc1 (by linarith) hjz1 (by linarith) hM
  have hLeftB : ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ u * M :=
    HL _ Y M hF hh (hδ3le.trans dL) kc (by linarith)
  refine ⟨δ, hδ, rfl, J, m, N, κ, μ, hWin, ?_⟩
  have hcη : c + δ ^ 3 < qs - η := by
    have : η ≤ qs / 8 := by linarith
    have : δ ^ 3 ≤ η / 2 := hδ3le.trans d6
    linarith
  have hδ2 : δ ^ 2 ≤ δ := by
    calc δ ^ 2 = δ * δ := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left d1 hδ.le
      _ = δ := mul_one _
  have hc2δ : c2 * δ ≤ 1 := by
    calc c2 * δ ≤ c2 * (1 / c2) := mul_le_mul_of_nonneg_left d9 hc2.le
      _ = 1 := by field_simp
  have hθδ : θ0 * δ ^ 3 ≤ u := by
    have h1 : θ0 * δ ^ 3 ≤ θ0 * δ := mul_le_mul_of_nonneg_left hδ3le hθ0
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < θ0 + 1)).1 d11
    linarith only [h1, h2, hδ]
  have hK3δ : 4 * sq * (K3 * δ) ≤ u / 2 := by
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * sq * K3 + 1)).1 d12
    linarith only [h2, hδ]
  have hξδ : 2 * sq * δ * (A0v + K3 * δ) ≤ u := by
    have h1 : δ * (A0v + K3 * δ) ≤ δ * (A0v + K3) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      have : K3 * δ ≤ K3 * 1 := mul_le_mul_of_nonneg_left d1 hK30
      linarith only [this]
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * sq * (A0v + K3) + 1)).1 d13
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * sq)
    linarith only [h2, h3, hδ]
  have hfin := rk_chain_step (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) (Y := Y) (r := r) (C := CA) (Cmu := Cmu) (ξ0 := ξ0)
    (gmin := gmin) (gmax := gmax) (c1 := c1) (c2 := c2) (δ := δ) (cs := cs) (Rmax := Rmax) (η := η) (c := c) (M := M) (sq := sq) (u := u)
    (θ0 := θ0) hWin (by norm_num) (by norm_num) hδ d1 hc1 hc12 hgmax.le hCA.le hCmu.le hcs0 hξ0 hRmax hr hη hηr hη1 hsq hqs d4 d5 (hδ3le.trans d6)
    (hδ2.trans d7) d8 hc2δ d10 hkc1 hkc2 hcpos hcη hjz1 hjz2 hM (hmono _ Y M hF) (hsupp _ Y M hF) (hMeq _ Y M hF) hLeftB hBlo hBhi
    hu hu6 hθ0 hcu hηu hθδ hA0 hK3δ hξδ d14
  linarith

/-- info: 'FormalResearch.Special.rk_kappa_sharp_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_kappa_sharp_abs

end FormalResearch.Special
