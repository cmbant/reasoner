module

public import FormalResearch.ModularBootstrap.Upper.Window.WindowLimit
public import FormalResearch.ModularBootstrap.Upper.Design.PerturbP

/-!
# Lemma R: shifted zero and the design family in window form

`ModifiedCombData.shiftF`, `CompactCombFamily.shiftF`: move the simple zero `σ_f` of a finite modification to
`σ_f + δ` (the proof of Lemma R, `ut:R`, divides by `σ - σ_f` before the window limit: this is done by
comparing with the modification whose zero is at `σ_f - 1`).

* `sigMod`: the comb `designComb c' 1 N (1/4) σ (designWidth1 c' η_*)` with arbitrary offsets `σ` as
  `ModifiedCombData 1 N`, with widths `ε̂_k(c') = min(M_ε, η_* ℓ_k / λ)`; `sigModFamily` is the one-member
  compact family; `sigComb_eq_modifiedCombB` identifies the two forms for large `c'`.  `designMod`,
  `designModFamily`, `designComb_eq_modifiedCombB` are the case `σ = designSigma1 d` (the design
  `D(N, η_*, d)`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Window

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design

/-! ### Shifting the zero -/

/-- Move the simple zero `σ_f` of a finite modification to `σ_f - δ`. -/
def ModifiedCombData.shiftF {f N : ℕ} (d : ModifiedCombData f N) (δ : ℝ) : ModifiedCombData f N :=
  { d with sigmaF := fun c' => d.sigmaF c' - δ, sigmaFLim := d.sigmaFLim - δ }

lemma ModifiedCombData.shiftF_allSigmaLim {f N : ℕ} (d : ModifiedCombData f N) (δ : ℝ) :
    (d.shiftF δ).allSigmaLim = d.allSigmaLim := rfl

lemma ModifiedCombData.shiftF_allEpsLim {f N : ℕ} (d : ModifiedCombData f N) (δ : ℝ) :
    (d.shiftF δ).allEpsLim = d.allEpsLim := rfl

/-- The compact family with all zeros moved to `σ_f - δ`. -/
noncomputable def CompactCombFamily.shiftF {f N : ℕ} (𝒦 : CompactCombFamily f N) (δ : ℝ) :
    CompactCombFamily f N where
  members := (fun d => d.shiftF δ) '' 𝒦.members
  hf := 𝒦.hf
  hN := 𝒦.hN
  M := 𝒦.M + |δ|
  hM := by have := 𝒦.hM; positivity
  eta0_bounds := by
    rintro _ ⟨d, hd, rfl⟩
    exact 𝒦.eta0_bounds d hd
  finite_bounds := by
    rintro _ ⟨d, hd, rfl⟩ c' hc'
    obtain ⟨h1, h2⟩ := 𝒦.finite_bounds d hd hc'
    refine ⟨?_, fun k hk => ?_⟩
    · exact (abs_sub _ _).trans (add_le_add h1 le_rfl)
    · obtain ⟨a, b, c⟩ := h2 k hk
      exact ⟨a.trans (by linarith [abs_nonneg δ]), b, c.trans (by linarith [abs_nonneg δ])⟩
  lim_bounds := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨h1, h2⟩ := 𝒦.lim_bounds d hd
    refine ⟨?_, fun k hk => ?_⟩
    · exact (abs_sub _ _).trans (add_le_add h1 le_rfl)
    · obtain ⟨a, b, c⟩ := h2 k hk
      exact ⟨a.trans (by linarith [abs_nonneg δ]), b, c.trans (by linarith [abs_nonneg δ])⟩
  uniform_tendsto := by
    intro ε hε
    obtain ⟨C₀, hC₀, h⟩ := 𝒦.uniform_tendsto hε
    refine ⟨C₀, hC₀, fun hc' _ => ?_⟩
    rintro ⟨d, hd, rfl⟩
    obtain ⟨h1, h2⟩ := h hc' d hd
    refine ⟨?_, h2⟩
    simpa [ModifiedCombData.shiftF, sub_sub_sub_cancel_right] using h1

/-! ### The design `D(N, η_*, d)` in window form -/

lemma phiWKB_eq_phiQuantile (k : ℕ) : phiWKB k = phiQuantile (k : ℝ) := rfl

lemma phiWKB_succ_eq_phiQuantile (k : ℕ) : phiWKB (k + 1) = phiQuantile ((k : ℝ) + 1) := by
  unfold phiWKB phiQuantile; push_cast; ring_nf

/-- `ℓ_k / λ` converges to `Φ_{k+1} - Φ_k`, with a rate linear in `λ`. -/
lemma siteGap_div_lambda_close (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c' : ℝ, 0 < c' →
      |siteGap c' k / lambdaComb c' - (phiWKB (k + 1) - phiWKB k)| ≤ C * lambdaComb c' := by
  have hk4 : (1 / 4 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨(2 * c1K0 / 3) * (phiQuantile ((k : ℝ) + 1) ^ 2 + phiQuantile (k : ℝ) ^ 2),
    mul_nonneg (by have := c1K0_pos; positivity) (by positivity), fun c' hc' => ?_⟩
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  have h1 := siteRadius_asymptotic hc' (by linarith : (1 / 4 : ℝ) ≤ (k : ℝ) + 1)
  have h2 := siteRadius_asymptotic hc' hk4
  rw [phiWKB_succ_eq_phiQuantile, phiWKB_eq_phiQuantile]
  have hsg : siteGap c' k = siteRadius c' ((k : ℝ) + 1) - siteRadius c' (k : ℝ) := by
    unfold siteGap siteRadius; ring
  have heq : siteGap c' k / lambdaComb c' - (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)) =
      ((siteRadius c' ((k : ℝ) + 1) - lambdaComb c' * phiQuantile ((k : ℝ) + 1)) -
        (siteRadius c' (k : ℝ) - lambdaComb c' * phiQuantile (k : ℝ))) / lambdaComb c' := by
    rw [hsg]; field_simp; ring
  rw [heq, abs_div, abs_of_pos hlam, div_le_iff₀ hlam]
  have hc1 := c1K0_pos
  have := (abs_sub _ _).trans (add_le_add h1 h2)
  refine this.trans (le_of_eq ?_)
  ring

/-- The `f = 1` finite modification with offsets `σ` (first site `σ_1`, sites `σ_2, …, σ_N` arbitrary), widths
`η_* ℓ_k` and `η₀ = 1/4` as `ModifiedCombData 1 N`: widths `min(M_ε, η_* ℓ_k / λ)`. -/
noncomputable def sigMod (N : ℕ) (η : ℝ) (σ : ℕ → ℝ) : ModifiedCombData 1 N where
  sigmaF _ := σ 1
  sigmaK _ k := σ k
  epsHat c' k := min (phiWKB (N + 1) + 1) (η * siteGap c' k / lambdaComb c')
  eta0 := 1 / 4
  sigmaFLim := σ 1
  sigmaKLim k := σ k
  epsHatLim k := η * (phiWKB (k + 1) - phiWKB k)

/-- The design `D(N, η_*, d)` as `ModifiedCombData 1 N`: widths `min(M_ε, η_* ℓ_k / λ)`
(`sigMod` at `σ = designSigma1 d`). -/
noncomputable def designMod (N : ℕ) (η d : ℝ) : ModifiedCombData 1 N := sigMod N η (designSigma1 d)

lemma phiWKB_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ phiWKB k := by
  unfold phiWKB
  refine Real.rpow_nonneg ?_ _
  have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

lemma phiWKB_succ_sub_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ phiWKB (k + 1) - phiWKB k := by
  unfold phiWKB
  refine sub_nonneg.mpr (Real.rpow_le_rpow ?_ ?_ (by norm_num))
  · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  · push_cast; linarith

lemma phiWKB_succ_sub_le {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    phiWKB (k + 1) - phiWKB k ≤ phiWKB (N + 1) := by
  have h0 : 0 ≤ phiWKB k := phiWKB_nonneg hk
  have hm : phiWKB (k + 1) ≤ phiWKB (N + 1) := by
    unfold phiWKB
    refine Real.rpow_le_rpow ?_ ?_ (by norm_num)
    · have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      linarith
    · have : ((k + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ N + 1)
      linarith
  linarith

/-- For large `c'` the clipping in `designMod` is inactive, and the widths converge. -/
lemma designMod_eps_eventually (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ k ∈ Finset.Icc 2 N,
      η * siteGap c' k / lambdaComb c' ≤ phiWKB (N + 1) + 1 ∧
      |η * siteGap c' k / lambdaComb c' - η * (phiWKB (k + 1) - phiWKB k)| ≤ ε := by
  have hfin : ∀ k ∈ Finset.Icc 2 N, ∀ᶠ c' in atTop, 0 < c' →
      |siteGap c' k / lambdaComb c' - (phiWKB (k + 1) - phiWKB k)| ≤ min 1 ε / 2 := by
    intro k hk
    obtain ⟨C, hC, h⟩ := siteGap_div_lambda_close k (by have := (Finset.mem_Icc.mp hk).1; omega)
    have hlt : ∀ᶠ c' in atTop, C * lambdaComb c' ≤ min 1 ε / 2 := by
      have := (tendsto_lambdaComb_atTop.const_mul C)
      rw [mul_zero] at this
      exact this.eventually_le_const (by positivity)
    filter_upwards [hlt] with c' h1 hc'
    exact (h c' hc').trans h1
  have hall := (Finset.eventually_all (Finset.Icc 2 N)).mpr hfin
  filter_upwards [hall, eventually_gt_atTop (0 : ℝ)] with c' h hc'
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  have hh := h k hk hc'
  have hm : min 1 ε ≤ 1 := min_le_left _ _
  have hm' : min 1 ε ≤ ε := min_le_right _ _
  have hm0 : 0 < min 1 ε := lt_min one_pos hε
  have hgap_le := phiWKB_succ_sub_le (k := k) (N := N) (by omega) hk'.2
  have hgap_nn := phiWKB_succ_sub_nonneg (k := k) (by omega)
  have hmul : η * siteGap c' k / lambdaComb c' - η * (phiWKB (k + 1) - phiWKB k) =
      η * (siteGap c' k / lambdaComb c' - (phiWKB (k + 1) - phiWKB k)) := by ring
  have habs : |η * siteGap c' k / lambdaComb c' - η * (phiWKB (k + 1) - phiWKB k)| ≤ ε := by
    rw [hmul, abs_mul, abs_of_nonneg hη0]
    calc η * |siteGap c' k / lambdaComb c' - (phiWKB (k + 1) - phiWKB k)| ≤ 1 * (min 1 ε / 2) :=
          mul_le_mul (hη1.trans (by norm_num)) hh (abs_nonneg _) (by norm_num)
      _ ≤ ε := by linarith
  refine ⟨?_, habs⟩
  have hu := (abs_le.mp habs).2
  have h4 : η * (phiWKB (k + 1) - phiWKB k) ≤ phiWKB (N + 1) := by
    have h0 : 0 ≤ phiWKB (N + 1) := phiWKB_nonneg (by omega)
    calc η * (phiWKB (k + 1) - phiWKB k) ≤ 1 * (phiWKB (N + 1)) :=
          mul_le_mul (hη1.trans (by norm_num)) hgap_le hgap_nn (by norm_num)
      _ = _ := one_mul _
  have hε1 : ε ≤ 1 ∨ 1 < ε := le_or_gt ε 1
  rcases hε1 with h5 | h5
  · linarith
  · -- the bound with `ε > 1`: use `min 1 ε = 1`
    have := habs
    have h6 : |η * siteGap c' k / lambdaComb c' - η * (phiWKB (k + 1) - phiWKB k)| ≤ 1 / 2 * 1 := by
      rw [hmul, abs_mul, abs_of_nonneg hη0]
      calc η * |siteGap c' k / lambdaComb c' - (phiWKB (k + 1) - phiWKB k)| ≤ 1 * (min 1 ε / 2) :=
            mul_le_mul (hη1.trans (by norm_num)) hh (abs_nonneg _) (by norm_num)
        _ ≤ 1 / 2 * 1 := by nlinarith
    have := (abs_le.mp h6).2
    linarith

/-- The one-member compact family `{sigMod N η σ}` in window form. -/
noncomputable def sigModFamily (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σ : ℕ → ℝ) : CompactCombFamily 1 N where
  members := {sigMod N η σ}
  hf := le_rfl
  hN := hN
  M := (∑ k ∈ Finset.Icc 1 N, |σ k|) + phiWKB (N + 1) + 1
  hM := by
    have := phiWKB_nonneg (k := N + 1) (by omega)
    have : 0 ≤ ∑ k ∈ Finset.Icc 1 N, |σ k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  eta0_bounds := by
    rintro _ rfl
    norm_num [sigMod]
  finite_bounds := by
    rintro _ rfl c' hc'
    have hP := phiWKB_nonneg (k := N + 1) (by omega)
    have hS : ∀ k ∈ Finset.Icc 1 N, |σ k| ≤ ∑ j ∈ Finset.Icc 1 N, |σ j| :=
      fun k hk => Finset.single_le_sum (f := fun j => |σ j|) (fun _ _ => abs_nonneg _) hk
    refine ⟨?_, fun k hk => ?_⟩
    · have := hS 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
      show |σ 1| ≤ _
      linarith
    · have hk' := Finset.mem_Icc.mp hk
      have hk2 : 2 ≤ k := by omega
      have hkN : k ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩
      have := hS k hkN
      have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
      refine ⟨by simpa [sigMod] using this.trans (by linarith), ?_, ?_⟩
      · show 0 ≤ min (phiWKB (N + 1) + 1) (η * siteGap c' k / lambdaComb c')
        refine le_min (by linarith) ?_
        have := siteGap_nonneg hc' (by omega : 1 ≤ k)
        positivity
      · exact (min_le_left _ _).trans (by linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.Icc 1 N) =>
          abs_nonneg (σ j))])
  lim_bounds := by
    rintro _ rfl
    have hP := phiWKB_nonneg (k := N + 1) (by omega)
    have hS : ∀ k ∈ Finset.Icc 1 N, |σ k| ≤ ∑ j ∈ Finset.Icc 1 N, |σ j| :=
      fun k hk => Finset.single_le_sum (f := fun j => |σ j|) (fun _ _ => abs_nonneg _) hk
    refine ⟨?_, fun k hk => ?_⟩
    · have := hS 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
      show |σ 1| ≤ _
      linarith
    · have hk' := Finset.mem_Icc.mp hk
      have hkN : k ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩
      have := hS k hkN
      refine ⟨by simpa [sigMod] using this.trans (by linarith), ?_, ?_⟩
      · exact mul_nonneg hη0 (phiWKB_succ_sub_nonneg (by omega))
      · have h1 := phiWKB_succ_sub_le (k := k) (N := N) (by omega) hk'.2
        have h2 := phiWKB_succ_sub_nonneg (k := k) (by omega)
        show η * (phiWKB (k + 1) - phiWKB k) ≤ _
        have h3 : η * (phiWKB (k + 1) - phiWKB k) ≤ 1 * phiWKB (N + 1) :=
          mul_le_mul (hη1.trans (by norm_num)) h1 h2 (by norm_num)
        have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.Icc 1 N) => abs_nonneg (σ j))
        linarith
  uniform_tendsto := by
    intro ε hε
    obtain ⟨C₀, hC₀⟩ := eventually_atTop.mp (designMod_eps_eventually N hη0 hη1 hε)
    refine ⟨max C₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun {c'} hc' m hm => ?_⟩
    subst hm
    refine ⟨by simp [sigMod, hε.le], fun k hk => ⟨by simp [sigMod, hε.le], ?_⟩⟩
    have hk2 : k ∈ Finset.Icc 2 N := hk
    obtain ⟨hA, hB⟩ := hC₀ c' ((le_max_left _ _).trans hc') k hk2
    show |min (phiWKB (N + 1) + 1) (η * siteGap c' k / lambdaComb c') -
      η * (phiWKB (k + 1) - phiWKB k)| ≤ ε
    rwa [min_eq_right hA]

lemma sigModFamily_mem (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σ : ℕ → ℝ) :
    sigMod N η σ ∈ (sigModFamily N hN hη0 hη1 σ).members := rfl

/-- The comb equals `modifiedCombB` of `sigMod` for large `c'`. -/
lemma sigComb_eq_modifiedCombB (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σ : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ∀ z : ℂ,
      designComb c' 1 N (1 / 4) (σ) (designWidth1 c' η) z =
        modifiedCombB 1 N (sigMod N η σ) c' z := by
  filter_upwards [designMod_eps_eventually N hη0 hη1 one_pos, eventually_gt_atTop (0 : ℝ)]
    with c' h hc' z
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  unfold designComb modifiedCombB
  have hprod : (∏ i ∈ Finset.range (N - 1), pairT (designSite c' (σ) (1 + 1 + i))
        (designWidth1 c' η (1 + 1 + i)) z) =
      ∏ k ∈ Finset.Icc (1 + 1) N,
        blaschkeT (((xiStar + lambdaComb c' * (sigMod N η σ).sigmaK c' k : ℝ) : ℂ) +
          ((lambdaComb c' * (sigMod N η σ).epsHat c' k : ℝ) : ℂ) * Complex.I) z *
        blaschkeT (((xiStar + lambdaComb c' * (sigMod N η σ).sigmaK c' k : ℝ) : ℂ) -
          ((lambdaComb c' * (sigMod N η σ).epsHat c' k : ℝ) : ℂ) * Complex.I) z := by
    have hIcc : Finset.Icc (1 + 1) N = Finset.Ico (1 + 1) (N + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.prod_Ico_eq_prod_range]
    have hlen : N + 1 - (1 + 1) = N - 1 := by omega
    rw [hlen]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hmem : 1 + 1 + i ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hle := (h _ hmem).1
    have hε : lambdaComb c' * (sigMod N η σ).epsHat c' (1 + 1 + i) =
        designWidth1 c' η (1 + 1 + i) := by
      show lambdaComb c' * min (phiWKB (N + 1) + 1) (η * siteGap c' (1 + 1 + i) / lambdaComb c') = _
      rw [min_eq_right hle]
      unfold designWidth1
      field_simp
    unfold pairT designSite
    simp only [hε]
    rfl
  have hprod' : (∏ i ∈ Finset.range (N - 1), pairT (designSite c' (σ) (1 + 1 + i))
        (designWidth1 c' η (1 + 1 + i)) z) = _ := hprod
  rw [hprod']
  rfl

/-- The one-member compact family `{D(N, η_*, d)}` in window form. -/
noncomputable def designModFamily (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (d : ℝ) : CompactCombFamily 1 N :=
  sigModFamily N hN hη0 hη1 (designSigma1 d)

lemma designModFamily_mem (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    designMod N η d ∈ (designModFamily N hN hη0 hη1 d).members := rfl

/-- The design comb equals `modifiedCombB` of `designMod` for large `c'`. -/
lemma designComb_eq_modifiedCombB (N : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) :
    ∀ᶠ c' in atTop, ∀ z : ℂ,
      designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η) z =
        modifiedCombB 1 N (designMod N η d) c' z :=
  sigComb_eq_modifiedCombB N hη0 hη1 (designSigma1 d)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.sigComb_eq_modifiedCombB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigComb_eq_modifiedCombB

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.designComb_eq_modifiedCombB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_eq_modifiedCombB

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.designMod_eps_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designMod_eps_eventually

end FormalResearch.ModularBootstrap.Upper.Window
