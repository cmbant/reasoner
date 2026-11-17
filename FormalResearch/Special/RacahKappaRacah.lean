module

public import FormalResearch.Special.RacahKappaFam

/-!
# The sharp amplitude theorem for the actual `6j` chain (integer data)

`rk_racah_sharp_gen`: for the (twisted) physical Wigner `6j` chain `Y_k = u_k Ŷ_k`, `u_k² = 1`, with geometric data `(α, β, x)` having a simple turn `Φ(q_*²) = 0` (`τ = ±1`),
the Airy-window amplitude `κ` of the Langer matching satisfies `κ² δ → 2` as `h = δ³ → 0` (`|κ²δ - 2| ≤ τ'` for `h ≤ ε₁`, where `ε₁` depends on `τ'` and on the fixed data `(α, β, x, m, n)` but not on the system; the quantifier order and the not-formalised list are in `RacahKappaSharpInst`).  The instances `racah_chain_kappa_sharp` (`τ = +1`) and `racah_chain_kappa_sharp_neg`
(`τ = -1`, twisted chain) are in `RacahKappaSharpInst`.

**Claim class: proved** (integer data; `κ` itself is the window amplitude `RkWinAt`, its sign is not asserted).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The family of physical (twisted) `6j` chains of shape `(α, β, x)` with `h ≤ hm`. -/
def rkFam (α β x : ℝ) (m n : ℤ) (u : ℤ → ℝ) (hm : ℝ) : ℝ → (ℤ → ℝ) → ℝ → Prop := fun h Y M =>
  0 < h ∧ h ≤ hm ∧ ∃ (a b c : ℤ) (D : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D ∧
    ∃ i : Fin (D + 1), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i ∧ wA (a : ℚ) (n : ℚ) * h = α ∧
      wB (b : ℚ) (m : ℚ) * h = β ∧ cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x ∧
      Y = (fun j => u j * racah6jY a b c m n j) ∧ M = 4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ))

/-- **The sharp amplitude theorem for the actual `6j` chain** (see the module docstring). -/
theorem rk_racah_sharp_gen (α β x τ qs : ℝ) (m n : ℤ) (hα : 0 < α) (hβ : 0 < β) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hαq : 0 < 1 - 1 / (4 * α ^ 2) * qs ^ 2) (hβq : 0 < 1 - 1 / (4 * β ^ 2) * qs ^ 2)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) (n : ℚ) * h = α →
      wB (b : ℚ) (m : ℚ) * h = β → cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (m : ℝ) (n : ℝ) h) (fun j => u j * racah6jY a b c m n j) k = 0) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA cs : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧ 0 < gmin ∧
      gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ cs ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (a b c : ℤ) (D' : ℕ),
        RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε1 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m' N : ℤ) (κ μ : ℝ),
          RkWinAt (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (fun j => u j * racah6jY a b c m n j) (cs / δ ^ 3) r CA Cmu ξ0
            gmin gmax c1 c2 δ J m' N κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  have hs := rk_turn_id hP hQ hτ hαq hβq hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hαq hβq hκ hturn
  have hspos : 0 < rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x := by
    have : 0 < rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x * qs ^ 2 := by rw [← hs]; linarith
    by_contra hc; push Not at hc
    nlinarith only [this, mul_nonneg (neg_nonneg.2 hc) (sq_nonneg qs)]
  set ρ : ℝ := hrRho (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) qs with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; unfold hrRho; positivity
  have hM1 : 1 ≤ hrM (m : ℝ) (n : ℝ) := le_max_left _ _
  have hκq : 0 ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs := by positivity
  set hm : ℝ := min (qs / (2 * hrM (m : ℝ) (n : ℝ))) ((2 * ((1 - τ * x) / qs ^ 2) * qs) / (ρ + 1)) with hhm
  have hmpos : 0 < hm := lt_min (by positivity) (by
    apply div_pos _ (by positivity)
    have : 0 < (1 - τ * x) / qs ^ 2 := by positivity
    positivity)
  set kmin : ℤ := max |m| |n| with hkmin
  have hkmin0 : 0 ≤ kmin := le_trans (abs_nonneg m) (le_max_left _ _)
  have hka : |(m : ℝ)| ≤ (kmin : ℝ) := by
    have : |m| ≤ kmin := le_max_left _ _
    have h' : ((|m| : ℤ) : ℝ) ≤ (kmin : ℝ) := by exact_mod_cast this
    simpa using h'
  have hkb : |(n : ℝ)| ≤ (kmin : ℝ) := by
    have : |n| ≤ kmin := le_max_right _ _
    have h' : ((|n| : ℤ) : ℝ) ≤ (kmin : ℝ) := by exact_mod_cast this
    simpa using h'
  have hsqY : ∀ (a b c : ℤ) (j : ℤ), (u j * racah6jY a b c m n j) ^ 2 = racah6jY a b c m n j ^ 2 := by
    intro a b c j; rw [mul_pow, hu j, one_mul]
  have hzero : ∀ (a b c : ℤ) (j : ℤ), u j * racah6jY a b c m n j = 0 → racah6jY a b c m n j = 0 := by
    intro a b c j h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · have := hu j; rw [h1] at this; norm_num at this
    · exact h1
  set Fam := rkFam α β x m n u hm with hFam
  have hrowsF : ∀ h Y M, Fam h Y M → ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
      (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (m : ℝ) (n : ℝ) h) Y k = 0 := by
    rintro h Y M ⟨hh, hhm, a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ k hk
    exact hrowsAll a b c D' hsys i hc h hh hAh hBh hx k hk
  have hmassF : ∀ h Y M, Fam h Y M → 0 < h → M * h * Real.sqrt (rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x) = 1 := by
    rintro h Y M ⟨hh, hhm, a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ -
    exact rd_mass hα hβ a b c m n i hc hh hAh hBh hx
  have hYleF : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Y k ^ 2 ≤ M := by
    rintro h Y M ⟨hh, hhm, a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ k
    rw [hsqY]
    exact rd_sq_le hα hβ a b c m n hsys i hc hh hAh hBh k
  have hsuppF : ∀ h Y M, Fam h Y M → ∀ k : ℤ, 2 * α < ((k : ℝ) + 1 / 2) * h → Y k = 0 := by
    rintro h Y M ⟨hh, hhm, a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ k hk
    show u k * racah6jY a b c m n k = 0
    rw [rd_supp_up a b c m n hh hAh k hk, mul_zero]
  have hMeqF : ∀ h Y M, Fam h Y M → ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = M := by
    rintro h Y M ⟨hh, hhm, a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ END hEND
    simp only [hsqY]
    exact rd_meq a b c m n hsys i hc END (fun k hk => hzero a b c k (hEND k hk))
  have hmonoF : ∀ h Y M, Fam h Y M → ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + 1 / 2) * h → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2 := by
    rintro h Y M ⟨hh, hhm, a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ k' k hk' hkk
    have h1 : h ≤ qs / (2 * hrM (m : ℝ) (n : ℝ)) := hhm.trans (min_le_left _ _)
    have h2 : h ≤ (2 * ((1 - τ * x) / qs ^ 2) * qs) / (ρ + 1) := hhm.trans (min_le_right _ _)
    have hhM : h * (2 * hrM (m : ℝ) (n : ℝ)) ≤ qs := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith only [h1]
    have hhC : h * ρ ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs := by
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith only [h2, hρ0, hκq, hh]
    exact rd_mono hα hβ hqs hτ hκ hturn a b c m n hh hAh hBh u hu hhM hhC
      (fun k hk => hrowsAll a b c D' hsys i hc h hh hAh hBh hx k hk) k' k hk' hkk
  have hlowF : ∀ h Y M, Fam h Y M → ∀ k : ℤ, k < kmin → Y k = 0 := by
    rintro h Y M ⟨hh, hhm, a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ k hk
    show u k * racah6jY a b c m n k = 0
    rw [rd_supp0 a b c m n k (Or.inl hk), mul_zero]
  have hLeftF := rl_left (a := (m : ℝ)) (b := (n : ℝ)) hP hQ hτ hs hspos hqs hαq hβq hka hkb hkmin0 Fam hrowsF hlowF
    (rk_mle hsuppF hMeqF)
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, cs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, H⟩ :=
    rk_kappa_sharp_abs hP hQ (m : ℝ) (n : ℝ) τ x qs hqs hτ hκ hαq hβq hturn (rk_hosc0 hP hQ hτ hqs hκ hαq hβq hturn)
      (2 * α) (by positivity) Fam hrowsF hmassF hYleF hsuppF hMeqF hmonoF hLeftF
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, cs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
  intro τ' hτ'
  obtain ⟨ε1, hε1, H'⟩ := H τ' hτ'
  refine ⟨min ε1 hm, lt_min hε1 hmpos, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx
  exact H' h _ _ ⟨hh, hhε.trans (min_le_right _ _), a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ hh
    (hhε.trans (min_le_left _ _))

/-- info: 'FormalResearch.Special.rk_racah_sharp_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_racah_sharp_gen

end FormalResearch.Special
