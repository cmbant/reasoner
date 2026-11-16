module

public import FormalResearch.Special.DiscreteAiryLimitHahn

/-!
# Discrete-to-Airy limit: the bounded-window form `Y = κ g (Ai + O(h))`

Part of the wiring module `DiscreteAiryLimit*`.  `dal_conclusion_window` post-processes `DalConclusion` (the output of
`discrete_airy_limit` and of `discrete_airy_hahn_racah`): the recessive contamination `μ f₂` is exponentially small,
`|μ| ≤ C_μ Y_max e^{-ξ₀/δ³}`, so on every bounded window `X_k ≤ Z` it is absorbed in `δⁿ` for any fixed `n`:

for `|Y_N|, |Y_{N+1}| ≤ δ^{-p}` (the polynomial bound `(R)`) and `δ ≤ δ₁(n, p, Z, …)`:
`∃ κ, ∀ k ∈ [J, N+1], X_k ≤ Z → |Y_k - κ ψ_k| ≤ C δ³ |κ| W + δⁿ`, `ψ_k = g(q_k) Ai(X_k)`.

This is the column form of P3 `thm:general-rank-airy`(i) (`Y_k = κ g [Ai + O(h)]` on `X ≥ -A₀`): when `|κ| ≥ δ^s`
the additive `δⁿ` (`n > 3 + s`) is a relative `O(h)` error.  `κ` is not identified (Darboux matching) and
`κ ≠ 0` is not proved.  `discrete_airy_hahn_racah_window` is the Hahn/centred-Racah instance.

Proved.  Constants in `δ₁` are existential.  `dal_conclusion_window` is for arbitrary `J ≤ m ≤ N` (the window position
is a property of the data it is applied to); `discrete_airy_hahn_racah_window` exports the position (`q_* - Dδ² ≤ q_J ≤ q_*`,
`q_* ≤ q_m < q_* + h`, `X_J ≤ -A₀`) next to the bound.  Scope as in `DiscreteAiryLimitHahn`: this is the recessive-plus-bounded-window
form, not a replacement of Geronimo/GBVA in full (no non-recessive `Ai`/`Bi` pair, no full oscillatory side, no uniformity over
families; `κ` unidentified, `κ ≠ 0` unproved; `(R)` and the identification of the closed forms with the 3j/6j chains are
hypotheses/obligations).
-/

@[expose] public section

open FormalResearch.DiscreteAiry FormalResearch.Racah.P3

namespace FormalResearch.Special

/-- `e^{-ξ₀/δ³} ≤ K δ^{3n}`. -/
lemma dal_exp_small {ξ0 : ℝ} (hξ : 0 < ξ0) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → Real.exp (-(ξ0 / δ ^ 3)) ≤ K * δ ^ (3 * n) := by
  refine ⟨(n.factorial : ℝ) / ξ0 ^ n, by positivity, fun δ hδ => ?_⟩
  have ht : 0 ≤ ξ0 / δ ^ 3 := by positivity
  have h := Real.pow_div_factorial_le_exp (ξ0 / δ ^ 3) ht n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hpos : 0 < (ξ0 / δ ^ 3) ^ n / n.factorial := by positivity
  rw [Real.exp_neg]
  calc (Real.exp (ξ0 / δ ^ 3))⁻¹ ≤ ((ξ0 / δ ^ 3) ^ n / n.factorial)⁻¹ := inv_anti₀ hpos h
    _ = (n.factorial : ℝ) / ξ0 ^ n * δ ^ (3 * n) := by
      rw [div_pow, pow_mul]
      field_simp

/-- A lower bound for the weight on `[0, Z]`. -/
lemma dal_airyWt_ge_Z {X Z : ℝ} (h0 : 0 ≤ X) (hZ : X ≤ Z) :
    (2 + Z) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi Z) ≤ airyWt X := by
  unfold airyWt
  have h1 : (2 + Z) ^ (-(1 / 4) : ℝ) ≤ (2 + |X|) ^ (-(1 / 4) : ℝ) := by
    rw [abs_of_nonneg h0]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have h2 : Real.exp (-airyXi Z) ≤ Real.exp (-airyXi X) :=
    Real.exp_le_exp.2 (by linarith [airyXi_mono hZ])
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- **Bounded-window form** (see the module docstring). -/
theorem dal_conclusion_window (C Cosc Ctop W Cmu ξ0 Z : ℝ) (hC : 0 ≤ C) (hCosc : 0 < Cosc) (hCtop : 0 < Ctop)
    (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0) (hZ : 0 ≤ Z) (n p : ℕ) :
    ∃ δ1 : ℝ, 0 < δ1 ∧ δ1 ≤ 1 ∧ ∀ (a c ψ X : ℤ → ℝ) (J m N : ℤ) (δ : ℝ), 0 < δ → δ ≤ δ1 → J ≤ m → m ≤ N →
      DalConclusion a c ψ X J m N δ C Cosc Ctop W Cmu ξ0 → ∀ Y : ℤ → ℝ,
      (∀ k ∈ Finset.Icc (J + 1) N, jac a c Y k = 0) → |Y N| ≤ (δ ^ p)⁻¹ → |Y (N + 1)| ≤ (δ ^ p)⁻¹ →
      ∃ κ : ℝ, ∀ k ∈ Finset.Icc J (N + 1), X k ≤ Z → |Y k - κ * ψ k| ≤ C * δ ^ 3 * |κ| * W + δ ^ n := by
  obtain ⟨K, hK, hKb⟩ := dal_exp_small hξ0 (n + p + 3)
  set wZ : ℝ := (2 + Z) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi Z) with hwZ
  have hwZp : 0 < wZ := by rw [hwZ]; positivity
  set L : ℝ := (Cosc + Ctop / wZ) * Cmu * K with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  refine ⟨min 1 (1 / (L + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro a c ψ X J m N δ hδ hδ1 hJm hmN H Y hY hYN hYN1
  have hδ1' : δ ≤ 1 := hδ1.trans (min_le_left _ _)
  have hδL : δ * (L + 1) ≤ 1 := by
    have := hδ1.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  obtain ⟨hxi, hpsi, hX0, -, hphys⟩ := H
  obtain ⟨κ, μ, hμ, hosc, htop⟩ := hphys Y (δ ^ p)⁻¹ hY hYN hYN1
  refine ⟨κ, fun k hk hXk => ?_⟩
  -- smallness of `μ`
  have hδp : 0 < δ ^ p := by positivity
  have hexp : Real.exp (-airyXi (X N)) ≤ K * δ ^ (3 * (n + p + 3)) :=
    (Real.exp_le_exp.2 (by linarith [hxi])).trans (hKb δ hδ)
  have hY0 : 0 ≤ (δ ^ p)⁻¹ := by positivity
  have hμ' : |μ| ≤ Cmu * (δ ^ p)⁻¹ * (K * δ ^ (3 * (n + p + 3))) :=
    hμ.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have e1 : Cmu * (δ ^ p)⁻¹ * (K * δ ^ (3 * (n + p + 3))) / δ =
      Cmu * K * δ ^ (3 * n + 2 * p + 8) := by
    have : δ ^ (3 * (n + p + 3)) = δ ^ p * δ * δ ^ (3 * n + 2 * p + 8) := by
      rw [← pow_succ, ← pow_add]; congr 1; ring
    rw [this]; field_simp
  have hmu1 : |μ| / δ ≤ Cmu * K * δ ^ (3 * n + 2 * p + 8) := by
    rw [← e1]; exact div_le_div_of_nonneg_right hμ' hδ.le
  have hδe : δ ^ (3 * n + 2 * p + 8) ≤ δ ^ n * δ := by
    have h1 : δ ^ (3 * n + 2 * p + 8) = δ ^ n * δ ^ (2 * n + 2 * p + 8) := by
      rw [← pow_add]; congr 1; ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc δ ^ (2 * n + 2 * p + 8) ≤ δ ^ 1 := pow_le_pow_of_le_one hδ.le hδ1' (by omega)
      _ = δ := pow_one δ
  -- the absorbed error
  have habs : ∀ B : ℝ, 0 ≤ B → B ≤ Cosc + Ctop / wZ → B * (|μ| / δ) ≤ δ ^ n := by
    intro B hB hBL
    have h1 : B * (|μ| / δ) ≤ (Cosc + Ctop / wZ) * (Cmu * K * δ ^ (3 * n + 2 * p + 8)) :=
      mul_le_mul hBL hmu1 (by positivity) (by positivity)
    have h2 : (Cosc + Ctop / wZ) * (Cmu * K * δ ^ (3 * n + 2 * p + 8)) ≤ L * (δ ^ n * δ) := by
      rw [hL]
      have : (Cosc + Ctop / wZ) * (Cmu * K * δ ^ (3 * n + 2 * p + 8)) =
          (Cosc + Ctop / wZ) * Cmu * K * δ ^ (3 * n + 2 * p + 8) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hδe (by positivity)
    have h3 : L * (δ ^ n * δ) ≤ δ ^ n := by
      have : 0 ≤ δ ^ n := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.2 hδL), mul_nonneg this hδ.le]
    linarith
  have hk' := Finset.mem_Icc.1 hk
  rcases le_or_gt k m with hkm | hkm
  · have hk2 : k ∈ Finset.Icc J m := by rw [Finset.mem_Icc]; omega
    refine (hosc k hk2).trans ?_
    have := habs Cosc hCosc.le (by
      have : 0 ≤ Ctop / wZ := by positivity
      linarith)
    linarith
  · have hk2 : k ∈ Finset.Icc m (N + 1) := by rw [Finset.mem_Icc]; omega
    refine (htop k hk2).trans ?_
    have hX := hX0 k hk2
    have hw := dal_airyWt_ge_Z hX hXk
    have hwp := airyWt_pos (X k)
    have hψk : ψ k ≤ W := (le_abs_self _).trans (hpsi k hk)
    have hμ0 : 0 ≤ |μ| / δ := by positivity
    have h5 : Ctop * |μ| / δ / airyWt (X k) ≤ (Ctop / wZ) * (|μ| / δ) := by
      have e : Ctop * |μ| / δ / airyWt (X k) = Ctop * (|μ| / δ) / airyWt (X k) := by ring
      rw [e, div_le_iff₀ hwp]
      have : Ctop / wZ * (|μ| / δ) * airyWt (X k) ≥ Ctop / wZ * (|μ| / δ) * wZ :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      have e2 : Ctop / wZ * (|μ| / δ) * wZ = Ctop * (|μ| / δ) := by field_simp
      linarith
    have h6 := habs (Ctop / wZ) (by positivity) (by linarith)
    have h7 : C * δ ^ 3 * |κ| * ψ k ≤ C * δ ^ 3 * |κ| * W := by
      have hC' : 0 ≤ C * δ ^ 3 * |κ| := by positivity
      exact mul_le_mul_of_nonneg_left hψk hC'
    linarith

/-- info: 'FormalResearch.Special.dal_conclusion_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dal_conclusion_window

/-- **Hahn / centred Racah, bounded-window form** (`Y = κ g [Ai + O(h)]` on `X ∈ [-A₀, Z]`, P3
`thm:hahnAiryConnection`, `thm:racahAiryConnection` up to the normalisation `κ`): see the module docstring of
`DiscreteAiryLimitHahn` for the hypotheses and the obligations left (closed forms = actual chains, `(R)`, `κ`). -/
theorem discrete_airy_hahn_racah_window {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) (A0 Z : ℝ) (hA0 : 0 < A0) (hZ : 0 ≤ Z) (n p : ℕ) :
    ∃ (r δ0 C W D : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < W ∧ 0 < D ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
        qs - D * δ ^ 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 ≤ qs ∧
        qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
        turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ J ≤ -A0 ∧
        ∀ Y : ℤ → ℝ, (∀ k ∈ Finset.Icc (J + 1) N, jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
          |Y N| ≤ (δ ^ p)⁻¹ → |Y (N + 1)| ≤ (δ ^ p)⁻¹ →
          ∃ κ : ℝ, ∀ k ∈ Finset.Icc J (N + 1), turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k ≤ Z →
            |Y k - κ * turnPsi (hrU P Q τ x) (hrA1 P Q) qs (δ ^ 3 / 2) δ k| ≤ C * δ ^ 3 * |κ| * W + δ ^ n := by
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hrq, hδ0, hδ01, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    discrete_airy_hahn_racah hP hQ a b τ x qs hqs hτ hκ hα hβ hturn A0 hA0
  obtain ⟨δ1, hδ1, hδ11, Hw⟩ := dal_conclusion_window C Cosc Ctop W Cmu ξ0 Z hC.le hCosc hCtop hCmu hξ0 hZ n p
  refine ⟨r, min δ0 δ1, C, W, D, hr, hrq, lt_min hδ0 hδ1, (min_le_left _ _).trans hδ01, hC, hW, hD, ?_⟩
  intro δ hδ hδδ
  obtain ⟨J, m, N, hJ1, hJm, hmN, hloc, hp1, hp2, hp3, hp4, hXJ, Hc⟩ := H δ hδ (hδδ.trans (min_le_left _ _))
  exact ⟨J, m, N, hJ1, hJm, hmN, hloc, hp1, hp2, hp3, hp4, hXJ, fun Y hY hYN hYN1 =>
    Hw _ _ _ _ J m N δ hδ (hδδ.trans (min_le_right _ _)) hJm hmN Hc Y hY hYN hYN1⟩

/-- info: 'FormalResearch.Special.discrete_airy_hahn_racah_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_hahn_racah_window

end FormalResearch.Special
