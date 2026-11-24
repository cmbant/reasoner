module

public import FormalResearch.SignUncertainty.O4CertAll
public import FormalResearch.SignUncertainty.O4CertSem
public import FormalResearch.SignUncertainty.O4SigmaBounds
public import FormalResearch.CohnElkies.O4CircleReduction

/-!
# `O4QuotientBound` from the kernel box certificate and a truncation hypothesis (`u1co:O4`)

`o4QuotientBound_of_trunc`: if the truncation `Φ_L(τ) ≈ L τ - π² τ³ / 36 + ρ₁₃(τ)` has error at most `tailR / SC` on the disc `‖τ‖ ≤ T`,
`T = (1 + 0.606 · 0.002)/4`, then `‖𝓕‖ ≤ 0.13` on the quarter arc, hence `O4QuotientBound L`.  The proof picks the box `(i, j)` of the
kernel certificate `checkBox_all` that contains `(L, σ₀, α̃, t)` (boxes from `o4Sigma0_sharp`, `edgeKappa0_bounds`), and identifies
`𝓕(θ)` with `numV / denV` (`numV_toC`, `denV_toC`) with `er + i ei` the truncation error.  The truncation hypothesis itself is
discharged in `O4QuotientBound`.

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty.O4Cert

open FormalResearch.CohnElkies FormalResearch.SignUncertainty Complex

lemma NL_real : (NL : ℝ) = 40 := by norm_num [NL]
lemma NT_real : (NT : ℝ) = 320 := by norm_num [NT]

lemma exists_index (n : ℕ) (hn : 0 < n) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ n) :
    ∃ i : ℕ, i < n ∧ (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 := by
  by_cases h : ⌊x⌋₊ < n
  · exact ⟨⌊x⌋₊, h, Nat.floor_le h0, (Nat.lt_floor_add_one x).le⟩
  · refine ⟨n - 1, by omega, ?_, ?_⟩
    · have : n ≤ ⌊x⌋₊ := not_lt.mp h
      have h2 : (n : ℝ) ≤ x := by
        calc (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast this
          _ ≤ x := Nat.floor_le h0
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      linarith
    · have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      linarith

lemma thC_norm (t : ℝ) : ‖thC t‖ = 1 / 4 := by
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold thC
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_add_mul_I]
  have : Real.sqrt ((1 - t ^ 2) ^ 2 + (2 * t) ^ 2) = 1 + t ^ 2 := by
    rw [show (1 - t ^ 2) ^ 2 + (2 * t) ^ 2 = (1 + t ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq h1.le
  rw [this, Real.norm_of_nonneg (by norm_num), Real.norm_of_nonneg h1.le]
  field_simp

/-- **The quarter-arc bound from the box certificate.** -/
lemma o4QuotientBound_of_trunc {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002)
    (hE : ∀ τ : ℂ, ‖τ‖ ≤ (1 + 0.606 * 0.002) / 4 →
      ‖edgePhiC L τ - ((L : ℂ) * τ - (Real.pi : ℂ) ^ 2 / 36 * τ ^ 3 + rho13 τ)‖ ≤ (tailR : ℝ) / SC) :
    O4QuotientBound L := by
  apply o4QuotientBound_of_quarter hL0 hL2
  intro t ht0 ht1
  show ‖o4Quot L (thC t)‖ ≤ 0.13
  obtain ⟨hσ1, hσ2⟩ := o4Sigma0_sharp hL0 hL2
  obtain ⟨hk1, hk2⟩ := edgeKappa0_bounds hL0 hL2
  set σ := o4Sigma0 L with hσdef
  set a := edgeAlphaTilde L with hadef
  have ha : a = edgeKappa0 L * L := by
    unfold edgeKappa0; rw [div_mul_cancel₀ _ hL0.ne']
  have haL : L ≤ a := by rw [ha]; nlinarith
  have haU : a ≤ L * (1 + L / 4) := by rw [ha]; nlinarith
  have hσpos : 0 < σ := by linarith
  -- indices
  obtain ⟨i, hi, hi1, hi2⟩ := exists_index NL (by norm_num [NL]) (x := 20000 * L) (by positivity)
    (by rw [NL_real]; linarith)
  obtain ⟨j, hj, hj1, hj2⟩ := exists_index NT (by norm_num [NT]) (x := 320 * t) (by positivity)
    (by rw [NT_real]; linarith)
  have hL1 : 2 * (i : ℝ) / (1000 * NL) ≤ L := by
    rw [NL_real, div_le_iff₀ (by norm_num)]; linarith
  have hL2' : L ≤ 2 * ((i : ℝ) + 1) / (1000 * NL) := by
    rw [NL_real, le_div_iff₀ (by norm_num)]; linarith
  have hs1 : (4000 * (NL : ℝ) - ((i : ℝ) + 1)) / (4000 * NL) ≤ σ := by
    rw [NL_real, div_le_iff₀ (by norm_num)]; nlinarith
  have hs2 : σ ≤ (500000 * (NL : ℝ) + 606 * ((i : ℝ) + 1)) / (500000 * NL) := by
    rw [NL_real, le_div_iff₀ (by norm_num)]; nlinarith
  have ha1 : 2 * (i : ℝ) / (1000 * NL) ≤ a := le_trans hL1 haL
  have ha2 : a ≤ ((i : ℝ) + 1) * (2000 * (NL : ℝ) + ((i : ℝ) + 1)) / (1000000 * NL * NL) := by
    rw [NL_real, le_div_iff₀ (by norm_num)]; nlinarith
  have ht1' : (j : ℝ) / NT ≤ t := by
    rw [NT_real, div_le_iff₀ (by norm_num)]; linarith
  have ht2' : t ≤ ((j : ℝ) + 1) / NT := by
    rw [NT_real, le_div_iff₀ (by norm_num)]; linarith
  -- truncation error
  set τ : ℂ := (σ : ℂ) * thC t with hτ
  have hτn : ‖τ‖ ≤ (1 + 0.606 * 0.002) / 4 := by
    rw [hτ, norm_mul, Complex.norm_real, thC_norm, Real.norm_of_nonneg hσpos.le]
    nlinarith
  set E : ℂ := edgePhiC L τ - ((L : ℂ) * τ - (Real.pi : ℂ) ^ 2 / 36 * τ ^ 3 + rho13 τ) with hEdef
  have hEn := hE τ hτn
  have her : |E.re| ≤ (tailR : ℝ) / SC := le_trans (Complex.abs_re_le_norm E) hEn
  have hei : |E.im| ≤ (tailR : ℝ) / SC := le_trans (Complex.abs_im_le_norm E) hEn
  obtain ⟨hb, hD⟩ := box_quot_bound (checkBox_all hi hj) hL1 hL2' hs1 hs2 ha1 ha2 ht1' ht2' her hei
  rw [numV_toC, denV_toC] at hb
  rw [denV_toC] at hD
  have hfrac : o4Quot L (thC t) =
      (((L * σ + -a : ℝ) : ℂ) * thC t -
        (((Real.pi * Real.pi) * ((1 : ℤ) / (36 : ℕ) : ℝ) * ((σ * σ) * σ + -1) : ℝ) : ℂ) * (thC t * thC t * thC t) +
      rho13 ((σ : ℂ) * thC t) + ((E.re : ℂ) + (E.im : ℂ) * Complex.I)) /
      (thC t * ((thC t * thC t - (((12 : ℤ) * a * (Real.pi * Real.pi)⁻¹ : ℝ) : ℂ)) *
        (thC t * thC t - (((12 : ℤ) * a * (Real.pi * Real.pi)⁻¹ : ℝ) : ℂ)))) := by
    rw [Complex.re_add_im E]
    unfold o4Quot o4PhiHat o4PhiMod o4Theta0Sq
    rw [hEdef, hτ]
    congr 1
    · push_cast; ring
    · push_cast; ring
  rw [hfrac, norm_div, div_le_iff₀ (norm_pos_iff.mpr hD)]
  norm_num at hb ⊢
  exact hb

end FormalResearch.SignUncertainty.O4Cert
