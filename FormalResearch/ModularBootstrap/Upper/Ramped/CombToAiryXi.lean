module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryPair

/-!
# The pair sum `∑ |Ξ_k| ≤ C λ`: Step 3 of Proposition 1.2(2) (`rem:P1.2`)

`Ξ_k = log q'_k - log((τ(x) - τ(χ'_k))² + ε̃_k²) - 2 𝒦(x, χ'_k)`, `ε̃_k = η_k (τ(χ_{k+1}) - τ(χ_k))`
(`xiPair`).  Exactly `Ξ_k = δ_k - log(1 + A_k)` (`xiPair_eq`).  Per pair (`xi_pair_bound`):
`|Ξ_k| ≤ C₁ ℓ_k² e^{-π|x - χ'_k|} + C₂ λ T_k (|σ - σ_k| + 1)`, `T_k = ε̂_k²/((σ - σ_k)² + ε̂_k²)`; the first
term sums to `O(λ)` by `sum_gap_exp_le` (the integral comparison of `rem:P1.2`, Step 3 (i)), the second by
`nearSum_le` (Step 3 (iii)).
-/

@[expose] public section

open Filter Topology Set Finset
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb

lemma sum_Icc_two_telescope (g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 2 n, (g (k + 1) - g k) = g (n + 1) - g 2 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

/-- Integral comparison: `∑_{k ≥ 2} ℓ_k e^{-π|χ_k - x|} ≤ e^{π/2}` when every `ℓ_k ≤ 1/2`. -/
theorem sum_gap_exp_le {c' : ℝ} (hc' : 0 < c') (hg : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ 1 / 2) (x : ℝ)
    (n : ℕ) :
    ∑ k ∈ Icc 2 n, siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|) ≤ Real.exp (π / 2) := by
  have hpi := Real.pi_pos
  set H : ℝ → ℝ := fun t => Real.arctan (Real.sinh (π * (t - x))) with hH
  have hHd : ∀ t : ℝ, HasDerivAt H (π / Real.cosh (π * (t - x))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => π * (t - x)) π t := by
      simpa using ((hasDerivAt_id t).sub_const x).const_mul π
    have h2 := (Real.hasDerivAt_sinh (π * (t - x))).comp t h1
    have h3 := h2.arctan
    refine h3.congr_deriv ?_
    have hc := Real.cosh_pos (π * (t - x))
    have hs : 1 + Real.sinh (π * (t - x)) ^ 2 = Real.cosh (π * (t - x)) ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq (π * (t - x))]
    simp only [Function.comp_apply]
    rw [hs]; field_simp
  have hHb : ∀ t : ℝ, |H t| ≤ π / 2 := fun t =>
    abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hstep : ∀ k : ℕ, 1 ≤ k →
      siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|) ≤
        Real.exp (π / 2) / π * (H (chiQuantile c' ((k : ℝ) + 1)) - H (chiQuantile c' (k : ℝ))) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlt : chiQuantile c' (k : ℝ) < chiQuantile c' ((k : ℝ) + 1) :=
      chiQuantile_strictMonoOn hc' (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith))
        (by linarith)
    have hcont : ContinuousOn H (Icc (chiQuantile c' (k : ℝ)) (chiQuantile c' ((k : ℝ) + 1))) :=
      fun t _ => (hHd t).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope H (fun t => π / Real.cosh (π * (t - x))) hlt
      hcont (fun t _ => hHd t)
    have hgap : siteGap c' k = chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ) := rfl
    have hsl : H (chiQuantile c' ((k : ℝ) + 1)) - H (chiQuantile c' (k : ℝ)) =
        π / Real.cosh (π * (ξ - x)) * siteGap c' k := by
      rw [hgap, hξe]; field_simp
    have hcosh : Real.cosh (π * (ξ - x)) ≤ Real.exp (π * |ξ - x|) := by
      have := Real.cosh_le_exp_half_sq
      rw [Real.cosh_eq]
      have h1 : Real.exp (π * (ξ - x)) ≤ Real.exp (π * |ξ - x|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) hpi.le)
      have h2 : Real.exp (-(π * (ξ - x))) ≤ Real.exp (π * |ξ - x|) :=
        Real.exp_le_exp.mpr (by
          have := neg_le_abs (ξ - x); nlinarith)
      linarith
    have hdist : |ξ - x| ≤ |chiQuantile c' (k : ℝ) - x| + siteGap c' k := by
      calc |ξ - x| = |(ξ - chiQuantile c' (k : ℝ)) + (chiQuantile c' (k : ℝ) - x)| := by ring_nf
        _ ≤ |ξ - chiQuantile c' (k : ℝ)| + |chiQuantile c' (k : ℝ) - x| := abs_add_le _ _
        _ ≤ siteGap c' k + |chiQuantile c' (k : ℝ) - x| := by
            rw [abs_of_nonneg (by linarith [hξ.1])]
            linarith [hξ.2]
        _ = _ := add_comm _ _
    have hgk := hg k hk
    have hcp := Real.cosh_pos (π * (ξ - x))
    have hl0 : 0 ≤ siteGap c' k := by rw [hgap]; linarith
    rw [hsl]
    have e1 : Real.exp (-π * |chiQuantile c' (k : ℝ) - x|) ≤
        Real.exp (π / 2) * Real.exp (-π * |ξ - x|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have e2 : Real.exp (-π * |ξ - x|) ≤ 1 / Real.cosh (π * (ξ - x)) := by
      rw [le_div_iff₀ hcp]
      calc Real.exp (-π * |ξ - x|) * Real.cosh (π * (ξ - x))
          ≤ Real.exp (-π * |ξ - x|) * Real.exp (π * |ξ - x|) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
    calc siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|)
        ≤ siteGap c' k * (Real.exp (π / 2) * (1 / Real.cosh (π * (ξ - x)))) := by
          gcongr
          exact e1.trans (by gcongr)
      _ = Real.exp (π / 2) / π * (π / Real.cosh (π * (ξ - x)) * siteGap c' k) := by
          field_simp
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0; simp; positivity
  calc ∑ k ∈ Icc 2 n, siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|)
      ≤ ∑ k ∈ Icc 2 n, Real.exp (π / 2) / π *
          (H (chiQuantile c' ((k : ℝ) + 1)) - H (chiQuantile c' (k : ℝ))) :=
        Finset.sum_le_sum fun k hk => hstep k (by have := (Finset.mem_Icc.1 hk).1; omega)
    _ = Real.exp (π / 2) / π * ∑ k ∈ Icc 2 n,
          (H (chiQuantile c' ((k : ℝ) + 1)) - H (chiQuantile c' (k : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (π / 2) / π * π := by
        gcongr
        have := sum_Icc_two_telescope (fun k : ℕ => H (chiQuantile c' (k : ℝ))) n hn0
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at this ⊢
        rw [this]
        have h1 := abs_le.mp (hHb (chiQuantile c' ((n : ℝ) + 1)))
        have h2 := abs_le.mp (hHb (chiQuantile c' 2))
        linarith
    _ = Real.exp (π / 2) := by field_simp

/-! ### The pair remainder `Ξ_k` -/

/-- `ε̃_k = η_k (τ(χ_{k+1}) - τ(χ_k))`, the width of the Airy model in the `τ` variable. -/
noncomputable def widthT (c' : ℝ) (η : ℕ → ℝ) (k : ℕ) : ℝ :=
  η k * (langerTau (chiQuantile c' ((k : ℝ) + 1)) - langerTau (chiQuantile c' (k : ℝ)))

/-- `Ξ_k = log q'_k - log((τ(x) - τ(χ'_k))² + ε̃_k²) - 2 𝒦(x, χ'_k)`. -/
noncomputable def xiPair (c' : ℝ) (σ η : ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  Real.log (qPair c' σ η k x) -
    Real.log ((langerTau x - langerTau (siteX c' σ k)) ^ 2 + widthT c' η k ^ 2) -
    2 * langerK x (siteX c' σ k)

/-- Exactly `Ξ_k = δ_k - log(1 + A_k)`, `A_k = ε̃_k²/(τ(x) - τ(χ'_k))²`. -/
lemma xiPair_eq {c' : ℝ} {σ η : ℕ → ℝ} {x : ℝ} {k : ℕ} (hx : 0 < x) (hy : 0 < siteX c' σ k)
    (hxy : x ≠ siteX c' σ k) (hε0 : 0 ≤ widthE c' η k) (hε : widthE c' η k ≤ 1 / 2) :
    xiPair c' σ η x k = deltaDetune (siteX c' σ k) (widthE c' η k) x -
      Real.log (1 + widthT c' η k ^ 2 / (langerTau x - langerTau (siteX c' σ k)) ^ 2) := by
  have hq : Real.log (qPair c' σ η k x) =
      2 * realLogT x (siteX c' σ k) + deltaDetune (siteX c' σ k) (widthE c' η k) x :=
    Design.log_blaschkePairQ hy.le hx.le hxy hε0 hε
  have hR := realLogT_eq_log_add_langerK hx hy hxy.symm
  have hD : langerTau x - langerTau (siteX c' σ k) ≠ 0 := by
    intro h
    exact hxy (langerTau_strictMonoOn.injOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) (by linarith))
  have hD2 : 0 < (langerTau x - langerTau (siteX c' σ k)) ^ 2 := by positivity
  have hlog : Real.log ((langerTau x - langerTau (siteX c' σ k)) ^ 2 + widthT c' η k ^ 2) =
      2 * Real.log |langerTau x - langerTau (siteX c' σ k)| +
        Real.log (1 + widthT c' η k ^ 2 / (langerTau x - langerTau (siteX c' σ k)) ^ 2) := by
    have e : (langerTau x - langerTau (siteX c' σ k)) ^ 2 + widthT c' η k ^ 2 =
        (langerTau x - langerTau (siteX c' σ k)) ^ 2 *
          (1 + widthT c' η k ^ 2 / (langerTau x - langerTau (siteX c' σ k)) ^ 2) := by
      field_simp
    rw [e, Real.log_mul hD2.ne' (by positivity), Real.log_pow, Real.log_abs]
    push_cast; ring
  unfold xiPair
  rw [hq, hlog, hR]
  ring

lemma phi_diff_bounds {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ) ∧
      phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ) ≤ cr k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set p : ℝ := (k : ℝ) - 1 / 4 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have e1 : phiQuantile ((k : ℝ) + 1) = (p + 1) ^ (2 / 3 : ℝ) := by
    unfold phiQuantile; rw [hp]; ring_nf
  have e2 : phiQuantile (k : ℝ) = p ^ (2 / 3 : ℝ) := rfl
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · have := Real.rpow_le_rpow hp0.le (by linarith : p ≤ p + 1) (by norm_num : (0 : ℝ) ≤ 2 / 3)
    linarith
  · have hb : (1 + 1 / p) ^ (2 / 3 : ℝ) ≤ 1 + 2 / 3 * (1 / p) :=
      rpow_one_add_le_one_add_mul_self (by linarith [show 0 < 1 / p by positivity])
        (by norm_num) (by norm_num)
    have hp1 : (p + 1) ^ (2 / 3 : ℝ) = p ^ (2 / 3 : ℝ) * (1 + 1 / p) ^ (2 / 3 : ℝ) := by
      rw [← Real.mul_rpow hp0.le (by positivity)]; congr 1; field_simp
    have hp2 : p ^ (2 / 3 : ℝ) * (1 / p) = p ^ (-(1 / 3 : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
    have hpk : p ^ (-(1 / 3 : ℝ)) ≤ 4 / 3 * cr k := by
      have h1 : p ^ (-(1 / 3 : ℝ)) ≤ (3 / 4 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [hp]; linarith) (by norm_num)
      rw [Real.mul_rpow (by norm_num) (by positivity)] at h1
      have h2 : (3 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 4 / 3 := by
        have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
          (by norm_num : (-1 : ℝ) ≤ -(1 / 3))
        rw [Real.rpow_neg_one] at this
        simpa using this
      have h3 : 0 ≤ cr k := (cr_pos hk).le
      calc p ^ (-(1 / 3 : ℝ)) ≤ (3 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := h1
        _ ≤ 4 / 3 * cr k := by unfold cr; gcongr
    have : p ^ (2 / 3 : ℝ) * (1 + 2 / 3 * (1 / p)) = p ^ (2 / 3 : ℝ) + 2 / 3 * p ^ (-(1 / 3 : ℝ)) := by
      rw [← hp2]; ring
    have hpow0 : 0 ≤ p ^ (2 / 3 : ℝ) := Real.rpow_nonneg hp0.le _
    have h4 : p ^ (2 / 3 : ℝ) * (1 + 1 / p) ^ (2 / 3 : ℝ) ≤ p ^ (2 / 3 : ℝ) * (1 + 2 / 3 * (1 / p)) :=
      mul_le_mul_of_nonneg_left hb hpow0
    have hc := (cr_pos hk).le
    rw [hp1]
    nlinarith

/-- The point `σ = τ(x)/λ` of the `σ` variable. -/
noncomputable def sigmaOf (c' x : ℝ) : ℝ := langerTau x / lambdaComb c'

lemma nearT_scale {l a b : ℝ} (hl : l ≠ 0) : nearT (l * a) (l * b) = nearT a b := by
  unfold nearT
  rw [show (l * b) ^ 2 + (l * a) ^ 2 = l ^ 2 * (b ^ 2 + a ^ 2) by ring,
    show (l * a) ^ 2 = l ^ 2 * a ^ 2 by ring, mul_div_mul_left _ _ (pow_ne_zero 2 hl)]

lemma nearT_eq_div {e d : ℝ} (hd : d ≠ 0) : nearT e d = (e ^ 2 / d ^ 2) / (1 + e ^ 2 / d ^ 2) := by
  have hd2 : 0 < d ^ 2 := by positivity
  unfold nearT
  field_simp

lemma tau_abs_sub_ge {cτ x y : ℝ} (hcp : 0 < cτ) (hc : ∀ z : ℝ, xiStar / 2 ≤ z → cτ ≤ deriv langerTau z)
    (hx : xiStar / 2 ≤ x) (hy : xiStar / 2 ≤ y) :
    cτ * |x - y| ≤ |langerTau x - langerTau y| := by
  have ha : 0 < xiStar / 2 := by have := xiStar_pos; positivity
  rcases le_total x y with hxy | hxy
  · have := langerTau_sub_ge ha hc hx hxy
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 hxy), abs_sub_comm,
      abs_of_nonneg (by nlinarith [mul_nonneg hcp.le (sub_nonneg.2 hxy)] : (0 : ℝ) ≤ langerTau y - langerTau x)]
    · exact this
  · have := langerTau_sub_ge ha hc hy hxy
    rw [abs_of_nonneg (sub_nonneg.2 hxy),
      abs_of_nonneg (by nlinarith [mul_nonneg hcp.le (sub_nonneg.2 hxy)] : (0 : ℝ) ≤ langerTau x - langerTau y)]
    exact this

lemma xi_far_abstract {δ eh Δ lam ℓ ε E cτ δ0 Cd CR : ℝ} (hCd : 0 < Cd) (hCR : 0 < CR)
    (hcτ : 0 < cτ) (hδ0 : 0 < δ0) (hlam : 0 < lam) (hδn : 0 ≤ δ) (hδ1 : δ ≤ Cd * ε ^ 2 * E)
    (hE : 0 ≤ E) (hε2 : ε ^ 2 ≤ ℓ ^ 2 / 16) (heh0 : 0 ≤ eh) (heh1 : eh ≤ 1 / 4) (hΔ2 : 2 ≤ |Δ|)
    (hlamΔ : cτ * δ0 ≤ lam * |Δ|) :
    |δ - Real.log (1 + eh ^ 2 / Δ ^ 2)| ≤
      (CR + Cd) / 16 * ℓ ^ 2 * E + 5 / (4 * cτ * δ0) * lam * (nearT eh Δ * (|Δ| + 1)) := by
  have hΔne : Δ ≠ 0 := abs_pos.1 (by linarith)
  have hΔ0 : 0 < Δ ^ 2 := by positivity
  have hA0 : 0 ≤ eh ^ 2 / Δ ^ 2 := by positivity
  have hA1 : eh ^ 2 / Δ ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hΔ0]
    have : 4 ≤ Δ ^ 2 := by nlinarith [abs_nonneg Δ, sq_abs Δ]
    nlinarith [sq_nonneg eh]
  have hlogA0 : 0 ≤ Real.log (1 + eh ^ 2 / Δ ^ 2) := Real.log_nonneg (by linarith)
  have hlogA1 : Real.log (1 + eh ^ 2 / Δ ^ 2) ≤ eh ^ 2 / Δ ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + eh ^ 2 / Δ ^ 2 by linarith)
    linarith
  have hTd : nearT eh Δ = (eh ^ 2 / Δ ^ 2) / (1 + eh ^ 2 / Δ ^ 2) := nearT_eq_div hΔne
  have hAT : eh ^ 2 / Δ ^ 2 ≤ 5 / 4 * nearT eh Δ := by
    rw [hTd, ← mul_div_assoc, le_div_iff₀ (by linarith)]
    nlinarith
  have hT0 := nearT_nonneg eh Δ
  have hcd : 0 < cτ * δ0 := by positivity
  have h1 : nearT eh Δ ≤ nearT eh Δ * (lam * (|Δ| + 1)) / (cτ * δ0) := by
    rw [le_div_iff₀ hcd]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hT0
  have hX1 : Cd * ε ^ 2 * E ≤ (CR + Cd) / 16 * ℓ ^ 2 * E := by
    have : Cd * ε ^ 2 ≤ (CR + Cd) / 16 * ℓ ^ 2 := by
      nlinarith [mul_nonneg hCR.le (sq_nonneg ℓ), mul_le_mul_of_nonneg_left hε2 hCd.le]
    exact mul_le_mul_of_nonneg_right this hE
  have hX2 : eh ^ 2 / Δ ^ 2 ≤ 5 / (4 * cτ * δ0) * lam * (nearT eh Δ * (|Δ| + 1)) := by
    calc eh ^ 2 / Δ ^ 2 ≤ 5 / 4 * nearT eh Δ := hAT
      _ ≤ 5 / 4 * (nearT eh Δ * (lam * (|Δ| + 1)) / (cτ * δ0)) := by gcongr
      _ = 5 / (4 * cτ * δ0) * lam * (nearT eh Δ * (|Δ| + 1)) := by field_simp
  rw [abs_le]
  constructor <;> linarith

lemma xi_near_abstract {δ LB LA R T μ lam Δ ℓ E K3 CR Cd : ℝ} (hsplit : δ = LB + R) (hR0 : 0 ≤ R)
    (hR1 : R ≤ (CR + Cd) / 16 * ℓ ^ 2 * E) (hT : 0 ≤ T) (hnl : |LB - LA| ≤ 2 * μ * T)
    (hμ : 2 * μ ≤ K3 * lam * (|Δ| + 1)) :
    |δ - LA| ≤ (CR + Cd) / 16 * ℓ ^ 2 * E + K3 * lam * (|Δ| + 1) * T := by
  have h1 : 2 * μ * T ≤ K3 * lam * (|Δ| + 1) * T := mul_le_mul_of_nonneg_right hμ hT
  have : δ - LA = (LB - LA) + R := by rw [hsplit]; ring
  rw [this]
  calc |(LB - LA) + R| ≤ |LB - LA| + |R| := abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg hR0]; linarith

lemma xi_coef_bound {ϑ ε2 d Δ lam M' cτ S0 Cg : ℝ} (hcτ : 0 < cτ) (hM' : 0 < M') (hS0 : 0 < S0)
    (hCg : 0 < Cg) (hlam : 0 < lam) (hϑ : |ϑ| ≤ M' * (d + lam * S0) / cτ) (hd : d ≤ lam * |Δ| / cτ)
    (hε : ε2 ≤ Cg * lam / 32) :
    2 * (3 * |ϑ| + 2 * ε2 + d) ≤
      (6 * M' / cτ ^ 2 + 2 / cτ + 6 * M' * S0 / cτ + Cg / 8) * lam * (|Δ| + 1) := by
  have e1 : M' * (d + lam * S0) / cτ ≤ M' * (lam * |Δ| / cτ + lam * S0) / cτ := by gcongr
  have e2 : 3 * (M' * (lam * |Δ| / cτ + lam * S0) / cτ) =
      lam * (3 * M' / cτ ^ 2 * |Δ| + 3 * M' * S0 / cτ) := by field_simp
  have e3 : 2 * (lam * |Δ| / cτ) = lam * (2 / cτ * |Δ|) := by field_simp
  have e4 : 2 * (3 * |ϑ| + 2 * ε2 + d) ≤
      lam * ((6 * M' / cτ ^ 2 + 2 / cτ) * |Δ| + (6 * M' * S0 / cτ + Cg / 8)) := by
    have h3 : 3 * |ϑ| ≤ 3 * (M' * (lam * |Δ| / cτ + lam * S0) / cτ) := by linarith
    have key : lam * ((6 * M' / cτ ^ 2 + 2 / cτ) * |Δ| + (6 * M' * S0 / cτ + Cg / 8)) -
        2 * (3 * |ϑ| + 2 * ε2 + d) =
        2 * (3 * (M' * (lam * |Δ| / cτ + lam * S0) / cτ) - 3 * |ϑ|) +
          2 * (lam * |Δ| / cτ - d) + 4 * (Cg * lam / 32 - ε2) := by
      field_simp; ring
    nlinarith [key, h3, hd, hε]
  refine e4.trans ?_
  have hq0 : 0 ≤ 6 * M' / cτ ^ 2 + 2 / cτ := by positivity
  have hq1 : 0 ≤ 6 * M' * S0 / cτ + Cg / 8 := by positivity
  have : (6 * M' / cτ ^ 2 + 2 / cτ) * |Δ| + (6 * M' * S0 / cτ + Cg / 8) ≤
      (6 * M' / cτ ^ 2 + 2 / cτ + 6 * M' * S0 / cτ + Cg / 8) * (|Δ| + 1) := by
    nlinarith [mul_nonneg hq1 (abs_nonneg Δ), abs_nonneg Δ]
  calc _ ≤ lam * ((6 * M' / cτ ^ 2 + 2 / cτ + 6 * M' * S0 / cτ + Cg / 8) * (|Δ| + 1)) :=
        mul_le_mul_of_nonneg_left this hlam.le
    _ = _ := by ring

/-- Geometry of a near pair: the mean value `m = τ'(ζ)` over the cell, and `τ(x) - τ(y) = (x - y) m (1 + ϑ)`. -/
lemma near_geometry {x y χ χ1 η lam S0 δ0 M' cτ : ℝ} (hcτ : 0 < cτ)
    (hcτd : ∀ z : ℝ, xiStar / 2 ≤ z → cτ ≤ deriv langerTau z)
    (hM2 : ∀ z ∈ Icc (xiStar / 2) (xiStar + 1), |deriv (deriv langerTau) z| ≤ M')
    (hxmem : x ∈ Icc (xiStar / 2) (xiStar + 1)) (hymem : y ∈ Icc (xiStar / 2) (xiStar + 1))
    (hmem : χ ∈ Icc (xiStar / 2) (xiStar + 1)) (hmem1 : χ1 ∈ Icc (xiStar / 2) (xiStar + 1))
    (hne : χ1 ≠ χ) (hxy : x ≠ y) (hdy : |x - y| ≤ δ0) (hs : |y - χ| + |χ1 - χ| ≤ lam * S0)
    (hlamS : lam * S0 ≤ δ0) (hδ0M : δ0 * (20 * M') ≤ cτ) (hM' : 0 < M') :
    ∃ ϑ m : ℝ, cτ ≤ m ∧ |ϑ| ≤ 1 / 10 ∧ |ϑ| ≤ M' * (|x - y| + lam * S0) / cτ ∧
      langerTau x - langerTau y = (x - y) * m * (1 + ϑ) ∧
        η * (langerTau χ1 - langerTau χ) = η * (χ1 - χ) * m := by
  have ha0 : 0 < xiStar / 2 := by have := xiStar_pos; positivity
  obtain ⟨ζ, hζmem, hζdist, hζτ⟩ := tau_mid ha0 hmem1 hmem hne
  have hζy : |y - ζ| ≤ lam * S0 := by
    have h1 := abs_sub_le y χ ζ
    rw [abs_sub_comm χ ζ] at h1
    linarith
  obtain ⟨ϑ, hϑb, hϑe⟩ := tau_sub_formula ha0 hcτ hcτd hM2 hxmem hymem hζmem hxy
  have hm : cτ ≤ deriv langerTau ζ := hcτd ζ (by linarith [hζmem.1])
  refine ⟨ϑ, deriv langerTau ζ, hm, ?_, ?_, hϑe, ?_⟩
  · refine hϑb.trans ?_
    rw [div_le_iff₀ hcτ]
    have h1 : |x - y| + |y - ζ| ≤ 2 * δ0 := by linarith
    calc M' * (|x - y| + |y - ζ|) ≤ M' * (2 * δ0) := by gcongr
      _ ≤ 1 / 10 * cτ := by nlinarith
  · refine hϑb.trans ?_
    gcongr
  · rw [hζτ]; ring

/-- **Per-pair bound.**  `|Ξ_k| ≤ C₁ ℓ_k² e^{-π|x - χ'_k|} + C₂ λ T_k (|σ - σ_k| + 1)` for `c'` large, uniformly
in the design (through `C_sh`), in `x ∈ X`, in `k ≥ 2` and in the heights. -/
theorem xi_pair_bound (Csh : ℝ) :
    ∃ C1 C2 c0 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {csep : ℝ} {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2), ∀ k : ℕ, 2 ≤ k → x ≠ siteX c' σ k →
      |xiPair c' σ η x k| ≤ C1 * siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|) +
        C2 * lambdaComb c' * (nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))
            (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1)) := by
  have hpi := Real.pi_pos
  have hxs := xiStar_pos
  obtain ⟨cτ, hcτ, hcτd, hX⟩ := siteX_sub_chi
  obtain ⟨M, hM⟩ := langerTau_deriv_bound_compact (a := xiStar / 2) (b := xiStar + 1) (by positivity)
  obtain ⟨Cg, hCg, hgev⟩ := siteGap_le_unif
  obtain ⟨CR, hCR, hR⟩ := detuneRem_bounds
  set M' : ℝ := |M| + 1 with hM'
  have hM'0 : 0 < M' := by positivity
  set δ0 : ℝ := min (1 / 10) (cτ / (20 * M')) with hδ0
  have hδ0p : 0 < δ0 := lt_min (by norm_num) (by positivity)
  have hδ01 : δ0 ≤ 1 / 10 := min_le_left _ _
  have hδ02 : δ0 ≤ cτ / (20 * M') := min_le_right _ _
  obtain ⟨Cd, hCd, hdet⟩ := deltaDetune_le_of_dist_ge hδ0p
  set S0 : ℝ := |Csh| / cτ + Cg with hS0
  have hS0p : 0 < S0 := by positivity
  set l0 : ℝ := min (δ0 / (S0 + 1)) (cτ * δ0 / 2) with hl0
  have hl0p : 0 < l0 := lt_min (by positivity) (by positivity)
  have hev : ∀ᶠ c' in atTop, (∀ k : ℕ, 1 ≤ k →
      siteGap c' k ≤ Cg * lambdaComb c' ∧ siteGap c' k ≤ 1 / 2) ∧ lambdaComb c' < l0 :=
    hgev.and (tendsto_lambdaComb_atTop.eventually (gt_mem_nhds hl0p))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set K3 : ℝ := 6 * M' / cτ ^ 2 + 2 / cτ + 6 * M' * S0 / cτ + Cg / 8 with hK3
  have hK3p : 0 < K3 := by positivity
  refine ⟨(CR + Cd) / 16, K3 + 5 / (4 * cτ * δ0), max N 1, by positivity, by positivity,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro c' hc' csep σ η h x hx k hk hxk
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hc')
  obtain ⟨hgap, hlam⟩ := hN c' ((le_max_left _ _).trans hc')
  have hlp := lamPos hc'0
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  obtain ⟨hx1, hx2⟩ : xiStar / 2 ≤ x ∧ x ≤ xiStar + 1 / 2 := hx
  have hxpos : 0 < x := by linarith
  have hy : xiStar ≤ siteX c' σ k := xiStar_le_siteX hc'0 (h.nonneg k hk1)
  have hypos : 0 < siteX c' σ k := by linarith
  have hxy : x ≠ siteX c' σ k := hxk
  obtain ⟨hgk1, hgk2⟩ := hgap k hk1
  have hk14 : (1 / 4 : ℝ) ≤ k := by linarith
  have hk14' : (1 / 4 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hℓ0 : 0 < siteGap c' k := by
    unfold siteGap
    have := chiQuantile_strictMonoOn hc'0 (Set.mem_Ici.2 hk14) (Set.mem_Ici.2 hk14') (by linarith)
    linarith
  obtain ⟨hη0, hη1⟩ := h.height k hk
  have hε0 : 0 ≤ widthE c' η k := mul_nonneg hη0 hℓ0.le
  have hε1 : widthE c' η k ≤ siteGap c' k / 4 := by
    unfold widthE
    have := mul_le_mul_of_nonneg_right hη1 hℓ0.le
    linarith
  have hε8 : widthE c' η k ≤ 1 / 8 := by linarith
  have hε2 : widthE c' η k ^ 2 ≤ siteGap c' k ^ 2 / 16 :=
    calc widthE c' η k ^ 2 ≤ (siteGap c' k / 4) ^ 2 := pow_le_pow_left₀ hε0 hε1 2
      _ = siteGap c' k ^ 2 / 16 := by ring
  have hwT : widthT c' η k =
      lambdaComb c' * (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) := by
    unfold widthT; rw [langerTau_chiQuantile hc'0 hk14', langerTau_chiQuantile hc'0 hk14]; ring
  have hτy : langerTau (siteX c' σ k) = lambdaComb c' * σ k :=
    langerTau_siteX hc'0 (h.nonneg k hk1)
  have hτx : langerTau x = lambdaComb c' * sigmaOf c' x := by unfold sigmaOf; field_simp
  have hD : langerTau x - langerTau (siteX c' σ k) = lambdaComb c' * (sigmaOf c' x - σ k) := by
    rw [hτy, hτx]; ring
  have hDne : langerTau x - langerTau (siteX c' σ k) ≠ 0 := by
    intro h0
    exact hxy (langerTau_strictMonoOn.injOn (Set.mem_Ioi.2 hxpos) (Set.mem_Ioi.2 hypos)
      (by linarith))
  have hT : nearT (widthT c' η k) (langerTau x - langerTau (siteX c' σ k)) =
      nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) := by
    rw [hwT, hD]; exact nearT_scale hlp.ne'
  have hdist := tau_abs_sub_ge hcτ hcτd (by linarith : xiStar / 2 ≤ x)
    (by linarith : xiStar / 2 ≤ siteX c' σ k)
  have hDabs : |langerTau x - langerTau (siteX c' σ k)| = lambdaComb c' * |sigmaOf c' x - σ k| := by
    rw [hD, abs_mul, abs_of_pos hlp]
  have hdistD : cτ * |x - siteX c' σ k| ≤ lambdaComb c' * |sigmaOf c' x - σ k| := hDabs ▸ hdist
  have hΔne : sigmaOf c' x - σ k ≠ 0 := by
    intro h0; apply hDne; rw [hD, h0]; ring
  have hΞ := xiPair_eq hxpos hypos hxy hε0 (by linarith)
  have hAeq : widthT c' η k ^ 2 / (langerTau x - langerTau (siteX c' σ k)) ^ 2 =
      (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) ^ 2 / (sigmaOf c' x - σ k) ^ 2 := by
    rw [hwT, hD]; field_simp
  rw [hΞ, hAeq]
  have hE := (Real.exp_pos (-π * |x - siteX c' σ k|)).le
  have hRHS0 : 0 ≤ K3 * lambdaComb c' * (nearT (η k * (phiQuantile ((k : ℝ) + 1) -
      phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1)) := by
    have := nearT_nonneg (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))
      (sigmaOf c' x - σ k)
    positivity
  obtain ⟨hp0, hp1⟩ := phi_diff_bounds hk1
  have hcr1 : cr k ≤ 1 := cr_le_one hk1
  have heh0 : 0 ≤ η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)) := mul_nonneg hη0 hp0
  have heh1 : η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)) ≤ 1 / 4 := by
    have := mul_le_mul hη1 (hp1.trans hcr1) hp0 (by norm_num)
    linarith
  have hlam2 : lambdaComb c' < cτ * δ0 / 2 := lt_of_lt_of_le hlam (min_le_right _ _)
  have hlamS : lambdaComb c' * S0 ≤ δ0 := by
    have h1 : lambdaComb c' < δ0 / (S0 + 1) := lt_of_lt_of_le hlam (min_le_left _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    have : lambdaComb c' * (S0 + 1) = lambdaComb c' * S0 + lambdaComb c' := by ring
    linarith
  obtain ⟨hδn, hδu⟩ := deltaDetune_bounds_universal hypos.le hxpos.le hxy hε0 hε8
  by_cases hε : widthE c' η k = 0
  · -- zero width: `Ξ_k = 0`
    have hδ0' : deltaDetune (siteX c' σ k) (widthE c' η k) x = 0 := by
      have h5 : 5 * widthE c' η k ^ 2 / (x - siteX c' σ k) ^ 2 = 0 := by rw [hε]; simp
      linarith
    have hη : η k = 0 := by
      unfold widthE at hε
      rcases mul_eq_zero.1 hε with h1 | h1
      · exact h1
      · exact absurd h1 hℓ0.ne'
    rw [hδ0', hη]
    simp only [zero_mul, zero_pow two_ne_zero, zero_div, add_zero, Real.log_one, sub_zero, abs_zero]
    have h1 : 0 ≤ (CR + Cd) / 16 * siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|) := by
      positivity
    have h2 : 0 ≤ (K3 + 5 / (4 * cτ * δ0)) * lambdaComb c' *
        (nearT 0 (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1)) := by
      have := nearT_nonneg 0 (sigmaOf c' x - σ k)
      positivity
    linarith
  have hε_pos : 0 < widthE c' η k := lt_of_le_of_ne hε0 (Ne.symm hε)
  obtain ⟨hR0, hR1⟩ := hR hx1 hy hε0 hε8
  have hδsplit := deltaDetune_eq_add hypos.le hxpos.le hxy hε0 hε8
  have hR2 : detuneRem (siteX c' σ k) (widthE c' η k) x ≤
      (CR + Cd) / 16 * siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|) := by
    refine hR1.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hε2 hCR.le
    have h2 := mul_nonneg hCd.le (sq_nonneg (siteGap c' k))
    have : CR * widthE c' η k ^ 2 ≤ (CR + Cd) / 16 * siteGap c' k ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hE
  by_cases hdlt : |x - siteX c' σ k| < δ0
  · -- near pair
    have hdisp : |siteX c' σ k - chiQuantile c' (k : ℝ)| ≤ lambdaComb c' * (|Csh| / cτ) := by
      have h1 := hX hc'0 σ k hk1 (h.nonneg k hk1)
      have h2 := h.near k hk1
      have h3 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hkR (by norm_num)
      have h4 : |σ k - phiQuantile (k : ℝ)| ≤ |Csh| := by
        refine h2.trans ?_
        calc Csh * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ |Csh| * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
              gcongr; exact le_abs_self _
          _ ≤ |Csh| * 1 := by gcongr
          _ = |Csh| := mul_one _
      refine h1.trans ?_
      rw [mul_div_assoc]
      gcongr
    have hχk := (chiQuantile_spec hc'0 hk14).1
    have hχk1 := (chiQuantile_spec hc'0 hk14').1
    have hgapdef : siteGap c' k = chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ) := rfl
    have hdisp' := abs_le.1 hdisp
    have hdlt' := abs_lt.1 hdlt
    have hS0eq : lambdaComb c' * S0 = lambdaComb c' * (|Csh| / cτ) + Cg * lambdaComb c' := by
      rw [hS0]; ring
    have ha0 : 0 < xiStar / 2 := by positivity
    have hmemk : chiQuantile c' (k : ℝ) ∈ Icc (xiStar / 2) (xiStar + 1) :=
      ⟨by linarith, by linarith⟩
    have hmemk1 : chiQuantile c' ((k : ℝ) + 1) ∈ Icc (xiStar / 2) (xiStar + 1) :=
      ⟨by linarith, by linarith⟩
    have hxmem : x ∈ Icc (xiStar / 2) (xiStar + 1) := ⟨hx1, by linarith⟩
    have hymem : siteX c' σ k ∈ Icc (xiStar / 2) (xiStar + 1) := ⟨by linarith, by linarith⟩
    have hne : chiQuantile c' ((k : ℝ) + 1) ≠ chiQuantile c' (k : ℝ) := by
      intro h0; linarith
    have hM2 : ∀ z ∈ Icc (xiStar / 2) (xiStar + 1), |deriv (deriv langerTau) z| ≤ M' := by
      intro z hz
      exact ((hM z hz).2).trans ((le_abs_self M).trans (by rw [hM']; linarith))
    have hδ0M : δ0 * (20 * M') ≤ cτ := (le_div_iff₀ (by positivity)).1 hδ02
    have hs : |siteX c' σ k - chiQuantile c' (k : ℝ)| + |chiQuantile c' ((k : ℝ) + 1) -
        chiQuantile c' (k : ℝ)| ≤ lambdaComb c' * S0 := by
      rw [abs_of_pos (by linarith : 0 < chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ))]
      linarith [abs_le.2 hdisp']
    obtain ⟨ϑ, m, hm, hϑ, hϑ', hϑe, hεt'⟩ := near_geometry (η := η k) (lam := lambdaComb c')
      (S0 := S0) hcτ hcτd hM2 hxmem hymem hmemk hmemk1 hne hxy hdlt.le hs hlamS hδ0M hM'0
    have hεt : widthT c' η k = widthE c' η k * m := by
      unfold widthT widthE siteGap; exact hεt'
    have hnl := near_log_bound (x := x) (y := siteX c' σ k) (m := m) (ϑ := ϑ)
      (ε := widthE c' η k) (lt_of_lt_of_le hcτ hm) hxy (hdlt.le.trans hδ01) hε_pos hε8 hϑ
    rw [← hεt, ← hϑe] at hnl
    rw [hAeq, hT] at hnl
    have hT0 := nearT_nonneg (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))
      (sigmaOf c' x - σ k)
    have hd_le : |x - siteX c' σ k| ≤ lambdaComb c' * |sigmaOf c' x - σ k| / cτ := by
      rw [le_div_iff₀ hcτ]; linarith
    have hε2' : widthE c' η k ^ 2 ≤ Cg * lambdaComb c' / 32 := by
      have h1 : widthE c' η k * widthE c' η k ≤ widthE c' η k * (1 / 8) :=
        mul_le_mul_of_nonneg_left hε8 hε0
      have h2 : widthE c' η k ^ 2 = widthE c' η k * widthE c' η k := sq _
      linarith
    have hcoef := xi_coef_bound (ϑ := ϑ) (ε2 := widthE c' η k ^ 2) (d := |x - siteX c' σ k|)
      (Δ := sigmaOf c' x - σ k) (lam := lambdaComb c') (M' := M') (cτ := cτ) (S0 := S0) (Cg := Cg)
      hcτ hM'0 hS0p hCg hlp hϑ' hd_le hε2'
    have hnear := xi_near_abstract (δ := deltaDetune (siteX c' σ k) (widthE c' η k) x)
      (LB := Real.log (1 + pairB (siteX c' σ k) (widthE c' η k) x))
      (LA := Real.log (1 + (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) ^ 2 /
        (sigmaOf c' x - σ k) ^ 2))
      (R := detuneRem (siteX c' σ k) (widthE c' η k) x)
      (T := nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) (sigmaOf c' x - σ k))
      (μ := 3 * |ϑ| + 2 * widthE c' η k ^ 2 + |x - siteX c' σ k|) (lam := lambdaComb c')
      (Δ := sigmaOf c' x - σ k) (ℓ := siteGap c' k)
      (E := Real.exp (-π * |x - siteX c' σ k|)) (K3 := K3) (CR := CR) (Cd := Cd)
      hδsplit hR0 hR2 hT0 hnl hcoef
    refine hnear.trans ?_
    have h5 : 0 ≤ 5 / (4 * cτ * δ0) * lambdaComb c' *
        (nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) *
          (|sigmaOf c' x - σ k| + 1)) := by positivity
    have e1 : (K3 + 5 / (4 * cτ * δ0)) * lambdaComb c' *
        (nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) *
          (|sigmaOf c' x - σ k| + 1)) =
        K3 * lambdaComb c' * (|sigmaOf c' x - σ k| + 1) *
          nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) +
        5 / (4 * cτ * δ0) * lambdaComb c' *
        (nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) *
          (|sigmaOf c' x - σ k| + 1)) := by ring
    rw [e1]; linarith
  · -- far pair
    have hdge : δ0 ≤ |x - siteX c' σ k| := not_lt.1 hdlt
    have hlamΔ : cτ * δ0 ≤ lambdaComb c' * |sigmaOf c' x - σ k| := by
      have : cτ * δ0 ≤ cτ * |x - siteX c' σ k| := mul_le_mul_of_nonneg_left hdge hcτ.le
      linarith
    have hΔ2 : 2 ≤ |sigmaOf c' x - σ k| := by
      by_contra hcon
      have hcon' := not_le.1 hcon
      have : lambdaComb c' * |sigmaOf c' x - σ k| < lambdaComb c' * 2 :=
        mul_lt_mul_of_pos_left hcon' hlp
      linarith
    have hδ1 := hdet hypos.le hxpos.le hdge hε0 hε8
    have hfar := xi_far_abstract (ε := widthE c' η k) (E := Real.exp (-π * |x - siteX c' σ k|))
      (ℓ := siteGap c' k) (lam := lambdaComb c') (CR := CR) hCd hCR hcτ hδ0p hlp hδn hδ1 hE hε2
      heh0 heh1 hΔ2 hlamΔ
    refine hfar.trans ?_
    have e1 : (K3 + 5 / (4 * cτ * δ0)) * lambdaComb c' * (nearT (η k * (phiQuantile ((k : ℝ) + 1) -
        phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1)) =
        K3 * lambdaComb c' * (nearT (η k * (phiQuantile ((k : ℝ) + 1) -
        phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1)) +
        5 / (4 * cτ * δ0) * lambdaComb c' * (nearT (η k * (phiQuantile ((k : ℝ) + 1) -
        phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1)) := by ring
    rw [e1]; linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.xi_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xi_pair_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.sum_gap_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_gap_exp_le

end FormalResearch.ModularBootstrap.Upper.Ramped
