module

public import FormalResearch.ModularBootstrap.Upper.Design.PerturbP
public import FormalResearch.ModularBootstrap.Upper.Comb.EdgePhase

/-!
# Comb phase decomposition of a finite modification: Lemma `Φ`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, §1, Lemma `Φ` (`ut:Phi`), items (a) and (b)
(the "Consequently" part is `Design.CombTransform`).

For a finite modification `designComb c' f N η₀ σ ε` of the index-`f` reference comb
(`Design.PerturbP`), `designDelta` is the explicit finite sum
`Δ_D = [φ_{χ'_f} - φ_{χ_f}] + Σ_{f<k≤N} [ψ(χ'_k, ε'_k) - ψ(χ_k, ε_k⁰)]`,
`ψ(χ, ε) = φ_{χ+iε} + φ_{χ-iε}`, on `𝒩`.  `lemma_Phi_b` states, for a compact family
(`|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ`), that for `c'` large and uniformly in the family:

* `exp(c' Φ₀ + Φ₁^{(f)} + Δ_D) = B_D^{(f)}` on `𝒩`, and `exp Δ_D = B_D^{(f)}/B_ref^{(f)}`, so that
  `log B_D^{(f)} = c' Φ₀ + Φ₁^{(f)} + Δ_D` with `Φ₁^{(f)} = phi1Comb` from Lemma `K3`
  (`logRefComb_eq_comb_decomp`);
* `Re(Φ₁^{(f)} + Δ_D) = 0` on `E₊ = {Im b = 1/2}`;
* `‖Δ_D^{(i)}‖ ≤ C λ` on `𝒩` for `i = 0, 1, 2`, `C = C(N, M, E)`.

The estimate is the paper's (PC) argument in its squared form, uniform in `N`: `iteratedDeriv_designDelta_le_sq`
bounds `‖∂_b^i Δ_D‖ ≤ K Σ(|ε'² - ε²| + 2|χ' - χ|)` with an absolute `K` (path `(χ, ε) → (χ, ε') → (χ', ε')`;
the `χ`-step is Lemma `K1`(d) for `∂_ζ φ`, the `ε`-step integrates `∂_{ε²}ψ`, bounded through `∂_ζ² φ`, over `ε²`).
`designPhiDecomp_of_pairChange` turns it into `DesignPhiDecomp` for any admissible finite modification, with a
threshold in `c'` independent of `N`; the compact-family `lemma_Phi_b` (the first-order bound with
`C = C(N, M, E)`) and the linear `iteratedDeriv_designDelta_le` are corollaries.
* `lemma_Phi_a_fixedN`: item `ut:Phi`(a) for the `f = 1` design `D(N, η_*, d)` at fixed `N`.

Item `ut:Phi`(a) with the explicit `N`-dependence is not formalised (it needs Lemma `Z`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. The difference of two phases and its derivatives -/

/-- The phase difference `φ_{ζ'}(b) - φ_ζ(b)`. -/
noncomputable def dphi (ζ' ζ b : ℂ) : ℂ := phiZeta ζ' b - phiZeta ζ b

/-- The pair phase `ψ(χ, ε) = φ_{χ+iε} + φ_{χ-iε}`. -/
noncomputable def psiPair (χ ε : ℝ) (b : ℂ) : ℂ :=
  phiZeta ((χ : ℂ) + (ε : ℂ) * Complex.I) b + phiZeta ((χ : ℂ) - (ε : ℂ) * Complex.I) b

/-- `Δ_D`, the logarithm of `B_D^{(f)} / B_ref^{(f)}` on `𝒩`. -/
noncomputable def designDelta (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (b : ℂ) : ℂ :=
  (phiZeta (designSite c' σ f : ℂ) b - phiZeta (chiQuantile c' (f : ℝ) : ℂ) b) +
    ∑ i ∈ Finset.range (N - f),
      (psiPair (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) b -
        psiPair (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) b)

lemma memCombZ_of_re_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : |y| ≤ 1 / 8) :
    (x : ℂ) + (y : ℂ) * Complex.I ∈ combZ := ⟨by simpa using hx, by simpa using hy⟩

lemma memCombZ_of_re_nonneg' {x y : ℝ} (hx : 0 ≤ x) (hy : |y| ≤ 1 / 8) :
    (x : ℂ) - (y : ℂ) * Complex.I ∈ combZ := ⟨by simpa using hx, by simpa [abs_neg] using hy⟩

lemma ofReal_memCombZ {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ∈ combZ := ⟨by simpa using hx, by simp⟩

lemma convex_combZ : Convex ℝ combZ := by
  intro z hz w hw a b ha hb hab
  refine ⟨?_, ?_⟩
  · have h1 : 0 ≤ z.re := hz.1
    have h2 : 0 ≤ w.re := hw.1
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    positivity
  · have h1 : |z.im| ≤ 1 / 8 := hz.2
    have h2 : |w.im| ≤ 1 / 8 := hw.2
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    calc |a * z.im + b * w.im| ≤ |a * z.im| + |b * w.im| := abs_add_le _ _
      _ = a * |z.im| + b * |w.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (1 / 8) + b * (1 / 8) := by gcongr
      _ = 1 / 8 := by rw [← add_mul, hab, one_mul]

/-- Lipschitz bound in `ζ` of the mixed derivatives `∂_b^i ∂_ζ^j φ_ζ(b)` on `𝒩 × combZ`, `i ≤ 2`,
`j ≤ 1` (the bound `combPhiDeriv_bound` for `i + (j + 1) ≤ 4`). -/
lemma combPhiDeriv_lipschitz_zeta_le :
    ∃ K > 0, ∀ (i j : ℕ), i ≤ 2 → j ≤ 1 → ∀ {b ζ ζ' : ℂ}, b ∈ combNMid → ζ ∈ combZ → ζ' ∈ combZ →
      ‖combPhiDeriv i j ζ' b - combPhiDeriv i j ζ b‖ ≤ K * ‖ζ' - ζ‖ := by
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  refine ⟨C, hC, fun i j hi hj b ζ ζ' hb hζ hζ' => ?_⟩
  have hb' := combNMid_subset_combNOpen hb
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => combPhiDeriv i j z b) (f' := fun z => combPhiDeriv i (j + 1) z b) (C := C)
    (s := combZ) (x := ζ) (y := ζ')
    (fun z hz => (hasDerivAt_combPhiDeriv_zeta (i := i) (j := j) hb'
      (combZ_subset_combZOpen hz)).hasDerivWithinAt)
    (fun z hz => by
      calc ‖combPhiDeriv i (j + 1) z b‖ ≤ C * min 1 (Real.exp (-π * (z.re - |b.re|))) :=
            hbd i (j + 1) (by omega) hb hz
        _ ≤ C * 1 := by gcongr; exact min_le_left _ _
        _ = C := mul_one C)
    convex_combZ hζ hζ'
  exact key

/-- Lipschitz bound in `ζ` of the `b`-derivatives `∂_b^i φ_ζ(b)` on `𝒩 × combZ`, `i ≤ 2`. -/
lemma combPhiDeriv_lipschitz_zeta :
    ∃ K > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {b ζ ζ' : ℂ}, b ∈ combNMid → ζ ∈ combZ → ζ' ∈ combZ →
      ‖combPhiDeriv i 0 ζ' b - combPhiDeriv i 0 ζ b‖ ≤ K * ‖ζ' - ζ‖ := by
  obtain ⟨K, hK, h⟩ := combPhiDeriv_lipschitz_zeta_le
  exact ⟨K, hK, fun i hi _ _ _ hb hζ hζ' => h i 0 hi (by norm_num) hb hζ hζ'⟩

lemma differentiableOn_phiZeta {ζ : ℂ} (hζ : ζ ∈ combZ) :
    DifferentiableOn ℂ (fun b => phiZeta ζ b) combNOpen := fun _ hb =>
  (hasDerivAt_phiZeta_b hb (combZ_subset_combZOpen hζ)).differentiableAt.differentiableWithinAt

lemma contDiffAt_phiZeta {ζ b : ℂ} (hζ : ζ ∈ combZ) (hb : b ∈ combNOpen) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (fun b => phiZeta ζ b) b :=
  ((differentiableOn_phiZeta hζ).analyticOnNhd isOpen_combNOpen b hb).contDiffAt

lemma iteratedDeriv_phiZeta_eq {ζ b : ℂ} (hζ : ζ ∈ combZ) (hb : b ∈ combNOpen) (i : ℕ) :
    iteratedDeriv i (fun b => phiZeta ζ b) b = combPhiDeriv i 0 ζ b := by
  have h := iteratedDeriv_combPhiDeriv_b i 0 hb (combZ_subset_combZOpen hζ)
  simpa [combPhiDeriv_zero] using h

/-- `‖∂_b^i (φ_{ζ'} - φ_ζ)‖ ≤ K ‖ζ' - ζ‖` on `𝒩` for `i ≤ 2` and `ζ, ζ' ∈ combZ`. -/
lemma iteratedDeriv_dphi_le :
    ∃ K > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {b ζ ζ' : ℂ}, b ∈ combNMid → ζ ∈ combZ → ζ' ∈ combZ →
      iteratedDeriv i (dphi ζ' ζ) b = combPhiDeriv i 0 ζ' b - combPhiDeriv i 0 ζ b ∧
      ‖iteratedDeriv i (dphi ζ' ζ) b‖ ≤ K * ‖ζ' - ζ‖ := by
  obtain ⟨K, hK, hlip⟩ := combPhiDeriv_lipschitz_zeta
  refine ⟨K, hK, fun i hi b ζ ζ' hb hζ hζ' => ?_⟩
  have hb' := combNMid_subset_combNOpen hb
  have heq : iteratedDeriv i (dphi ζ' ζ) b = combPhiDeriv i 0 ζ' b - combPhiDeriv i 0 ζ b := by
    unfold dphi
    rw [iteratedDeriv_fun_sub (contDiffAt_phiZeta hζ' hb' i) (contDiffAt_phiZeta hζ hb' i),
      iteratedDeriv_phiZeta_eq hζ' hb' i, iteratedDeriv_phiZeta_eq hζ hb' i]
  exact ⟨heq, by rw [heq]; exact hlip i hi hb hζ hζ'⟩

/-! ### 2. The exponential of `Δ_D` -/

lemma exp_dphi {ζ' ζ b : ℂ} (hb : b ∈ combN) (hζ' : ζ' ∈ combZ) (hζ : ζ ∈ combZ) :
    Complex.exp (dphi ζ' ζ b) = blaschkeT ζ' b / blaschkeT ζ b ∧ blaschkeT ζ b ≠ 0 := by
  have hT : blaschkeT ζ b ≠ 0 := by
    intro h
    have := cexp_phiZeta hb hζ
    rw [h, neg_zero] at this
    exact Complex.exp_ne_zero _ this
  refine ⟨?_, hT⟩
  unfold dphi
  rw [Complex.exp_sub, cexp_phiZeta hb hζ', cexp_phiZeta hb hζ, neg_div_neg_eq]

lemma exp_psiPair {χ ε : ℝ} {b : ℂ} (hb : b ∈ combN) (hχ : 0 ≤ χ) (hε : |ε| ≤ 1 / 8) :
    Complex.exp (psiPair χ ε b) = pairT χ ε b ∧ pairT χ ε b ≠ 0 := by
  have h1 := memCombZ_of_re_nonneg hχ hε
  have h2 := memCombZ_of_re_nonneg' hχ hε
  have e : Complex.exp (psiPair χ ε b) = pairT χ ε b := by
    unfold psiPair pairT
    rw [Complex.exp_add, cexp_phiZeta hb h1, cexp_phiZeta hb h2, neg_mul_neg]
  refine ⟨e, ?_⟩
  rw [← e]
  exact Complex.exp_ne_zero _

lemma re_psiPair_eq_zero {χ ε : ℝ} {b : ℂ} (hb_im : b.im = 1 / 2) (hχ : 0 ≤ χ) (hε : |ε| ≤ 1 / 8) :
    (psiPair χ ε b).re = 0 := by
  have hb : b ∈ combN := by change |b.im - 1 / 2| ≤ 1 / 4; rw [hb_im]; norm_num
  have h1 := exp_psiPair hb hχ hε
  have hn : ‖pairT χ ε b‖ = 1 :=
    norm_pair_blaschkeT_eq_one χ ε (hε.trans (by norm_num)) (by rw [hb_im]; norm_num)
  have : Real.exp (psiPair χ ε b).re = 1 := by
    rw [← Complex.norm_exp, h1.1, hn]
  rwa [Real.exp_eq_one_iff] at this

/-- Hypotheses on the data of a finite modification: all sites nonnegative, all widths `≤ 1/8`. -/
structure DesignAdmissible (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) : Prop where
  first : 0 ≤ designSite c' σ f
  ref_first : 0 ≤ chiQuantile c' (f : ℝ)
  site : ∀ i < N - f, 0 ≤ designSite c' σ (f + 1 + i)
  width : ∀ i < N - f, |ε (f + 1 + i)| ≤ 1 / 8
  ref_site : ∀ i < N - f, 0 ≤ chiQuantile c' ((f + 1 + i : ℕ) : ℝ)
  ref_width : ∀ i < N - f, |η₀ * siteGap c' (f + 1 + i)| ≤ 1 / 8

/-- `B_ref · exp Δ_D = B_D` on `𝒩`, given the splitting of the reference comb. -/
theorem refComb_mul_exp_designDelta {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ} {b : ℂ}
    (hb : b ∈ combN) (hA : DesignAdmissible c' f N η₀ σ ε)
    (hsp : refComb c' f η₀ b =
      blaschkeT (chiQuantile c' (f : ℝ) : ℂ) b *
        (∏ i ∈ Finset.range (N - f),
          pairT (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) b) *
        combTail c' N η₀ b) :
    refComb c' f η₀ b * Complex.exp (designDelta c' f N η₀ σ ε b) =
      designComb c' f N η₀ σ ε b := by
  have hf := exp_dphi (b := b) hb (ofReal_memCombZ hA.first) (ofReal_memCombZ hA.ref_first)
  have hpair : ∀ i ∈ Finset.range (N - f),
      Complex.exp (psiPair (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) b -
        psiPair (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) b) =
      pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) b /
        pairT (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) b := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Complex.exp_sub, (exp_psiPair hb (hA.site i hi') (hA.width i hi')).1,
      (exp_psiPair hb (hA.ref_site i hi') (hA.ref_width i hi')).1]
  have hne : ∀ i ∈ Finset.range (N - f),
      pairT (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) b ≠ 0 :=
    fun i hi => (exp_psiPair hb (hA.ref_site i (Finset.mem_range.mp hi))
      (hA.ref_width i (Finset.mem_range.mp hi))).2
  have hprod_ne : ∏ i ∈ Finset.range (N - f),
      pairT (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) b ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hne
  have hexp : Complex.exp (designDelta c' f N η₀ σ ε b) =
      (blaschkeT (designSite c' σ f : ℂ) b / blaschkeT (chiQuantile c' (f : ℝ) : ℂ) b) *
        ((∏ i ∈ Finset.range (N - f),
            pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) b) /
          ∏ i ∈ Finset.range (N - f),
            pairT (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) b) := by
    unfold designDelta
    rw [Complex.exp_add, ← Finset.prod_div_distrib, Complex.exp_sum]
    have : (phiZeta (designSite c' σ f : ℂ) b - phiZeta (chiQuantile c' (f : ℝ) : ℂ) b) =
        dphi (designSite c' σ f : ℂ) (chiQuantile c' (f : ℝ) : ℂ) b := rfl
    rw [this, hf.1]
    congr 1
    exact Finset.prod_congr rfl hpair
  rw [hexp, hsp]
  unfold designComb
  field_simp [hf.2, hprod_ne]

/-! ### 3. Derivative bounds for `Δ_D` -/

lemma designDelta_eq_dphi (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) :
    designDelta c' f N η₀ σ ε = fun b =>
      dphi (designSite c' σ f : ℂ) (chiQuantile c' (f : ℝ) : ℂ) b +
        ∑ i ∈ Finset.range (N - f),
          (dphi ((designSite c' σ (f + 1 + i) : ℂ) + (ε (f + 1 + i) : ℂ) * Complex.I)
              ((chiQuantile c' ((f + 1 + i : ℕ) : ℝ) : ℂ) +
                ((η₀ * siteGap c' (f + 1 + i) : ℝ) : ℂ) * Complex.I) b +
            dphi ((designSite c' σ (f + 1 + i) : ℂ) - (ε (f + 1 + i) : ℂ) * Complex.I)
              ((chiQuantile c' ((f + 1 + i : ℕ) : ℝ) : ℂ) -
                ((η₀ * siteGap c' (f + 1 + i) : ℝ) : ℂ) * Complex.I) b) := by
  funext b
  unfold designDelta psiPair dphi
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma norm_add_I_sub_le (a b a₀ b₀ : ℝ) :
    ‖((a : ℂ) + (b : ℂ) * Complex.I) - ((a₀ : ℂ) + (b₀ : ℂ) * Complex.I)‖ ≤ |a - a₀| + |b - b₀| := by
  have : ((a : ℂ) + (b : ℂ) * Complex.I) - ((a₀ : ℂ) + (b₀ : ℂ) * Complex.I) =
      ((a - a₀ : ℝ) : ℂ) + ((b - b₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  calc _ ≤ ‖((a - a₀ : ℝ) : ℂ)‖ + ‖((b - b₀ : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |a - a₀| + |b - b₀| := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs]

lemma norm_sub_I_sub_le (a b a₀ b₀ : ℝ) :
    ‖((a : ℂ) - (b : ℂ) * Complex.I) - ((a₀ : ℂ) - (b₀ : ℂ) * Complex.I)‖ ≤ |a - a₀| + |b - b₀| := by
  have : ((a : ℂ) - (b : ℂ) * Complex.I) - ((a₀ : ℂ) - (b₀ : ℂ) * Complex.I) =
      ((a - a₀ : ℝ) : ℂ) - ((b - b₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  calc _ ≤ ‖((a - a₀ : ℝ) : ℂ)‖ + ‖((b - b₀ : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = |a - a₀| + |b - b₀| := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs]

/-! #### The squared pair-change bound `(PC)` -/

/-- `∂_b^i ψ(χ, ε)`, the `b`-derivative of the pair phase `ψ(χ, ε) = φ_{χ+iε} + φ_{χ-iε}`. -/
noncomputable def pairDeriv (i : ℕ) (χ ε : ℝ) (b : ℂ) : ℂ :=
  combPhiDeriv i 0 ((χ : ℂ) + (ε : ℂ) * Complex.I) b +
    combPhiDeriv i 0 ((χ : ℂ) - (ε : ℂ) * Complex.I) b

lemma pairDeriv_neg (i : ℕ) (χ ε : ℝ) (b : ℂ) : pairDeriv i χ (-ε) b = pairDeriv i χ ε b := by
  unfold pairDeriv
  have h1 : (χ : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I = (χ : ℂ) - (ε : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : (χ : ℂ) - ((-ε : ℝ) : ℂ) * Complex.I = (χ : ℂ) + (ε : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, h2, add_comm]

lemma pairDeriv_abs (i : ℕ) (χ ε : ℝ) (b : ℂ) : pairDeriv i χ |ε| b = pairDeriv i χ ε b := by
  rcases abs_choice ε with h | h
  · rw [h]
  · rw [h, pairDeriv_neg]

lemma pairDeriv_eq_iteratedDeriv {χ ε : ℝ} {b : ℂ} (hb : b ∈ combNMid) (hχ : 0 ≤ χ)
    (hε : |ε| ≤ 1 / 8) (i : ℕ) :
    iteratedDeriv i (fun b => psiPair χ ε b) b = pairDeriv i χ ε b := by
  have hb' := combNMid_subset_combNOpen hb
  unfold psiPair pairDeriv
  rw [iteratedDeriv_fun_add (contDiffAt_phiZeta (memCombZ_of_re_nonneg hχ hε) hb' i)
    (contDiffAt_phiZeta (memCombZ_of_re_nonneg' hχ hε) hb' i),
    iteratedDeriv_phiZeta_eq (memCombZ_of_re_nonneg hχ hε) hb' i,
    iteratedDeriv_phiZeta_eq (memCombZ_of_re_nonneg' hχ hε) hb' i]

/-- The `ε`-step of `(PC)`: for `0 ≤ a ≤ c ≤ 1/8` and `χ ≥ 0`,
`‖∂_b^i [ψ(χ, c) - ψ(χ, a)]‖ ≤ K (c² - a²)`.  Since `ψ` is even in `ε`,
`∂_{ε²} ψ = -(1/(2ε)) ∫_{-ε}^{ε} ∂_ζ² φ_{χ+is} ds`, which the mean value argument below replaces by
`‖∂_ζ^2 φ‖ ≤ K` (`combPhiDeriv_bound`). -/
lemma pairDeriv_sub_le_of_le :
    ∃ K > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {χ a c : ℝ} {b : ℂ}, b ∈ combNMid → 0 ≤ χ → 0 ≤ a → a ≤ c →
      c ≤ 1 / 8 → ‖pairDeriv i χ c b - pairDeriv i χ a b‖ ≤ K * (c ^ 2 - a ^ 2) := by
  obtain ⟨K, hK, hlip⟩ := combPhiDeriv_lipschitz_zeta_le
  refine ⟨K, hK, fun i hi χ a c b hb hχ ha hac hc => ?_⟩
  have hb' := combNMid_subset_combNOpen hb
  have hz : ∀ t : ℝ, |t| ≤ 1 / 8 →
      (χ : ℂ) + (t : ℂ) * Complex.I ∈ combZ ∧ (χ : ℂ) - (t : ℂ) * Complex.I ∈ combZ :=
    fun t ht => ⟨memCombZ_of_re_nonneg hχ ht, memCombZ_of_re_nonneg' hχ ht⟩
  have hder : ∀ t : ℝ, |t| ≤ 1 / 8 → HasDerivAt (fun t : ℝ => pairDeriv i χ t b)
      (Complex.I * (combPhiDeriv i 1 ((χ : ℂ) + (t : ℂ) * Complex.I) b -
        combPhiDeriv i 1 ((χ : ℂ) - (t : ℂ) * Complex.I) b)) t := fun t ht => by
    have hu1 : HasDerivAt (fun z : ℂ => (χ : ℂ) + z * Complex.I) Complex.I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (χ : ℂ)
    have hu2 : HasDerivAt (fun z : ℂ => (χ : ℂ) - z * Complex.I) (-Complex.I) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_sub (χ : ℂ)
    have h1 := (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0) hb'
      (combZ_subset_combZOpen (hz t ht).1)).comp (t : ℂ) hu1
    have h2 := (hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0) hb'
      (combZ_subset_combZOpen (hz t ht).2)).comp (t : ℂ) hu2
    have h3 := (h1.add h2).comp_ofReal
    unfold pairDeriv
    refine h3.congr_deriv ?_
    simp only [zero_add]
    ring
  have hcont : ContinuousOn (fun t : ℝ => pairDeriv i χ t b - pairDeriv i χ a b) (Set.Icc a c) :=
    fun t ht => ((hder t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])).continuousAt.sub
      continuousAt_const).continuousWithinAt
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t : ℝ => pairDeriv i χ t b - pairDeriv i χ a b)
    (f' := fun t : ℝ => Complex.I * (combPhiDeriv i 1 ((χ : ℂ) + (t : ℂ) * Complex.I) b -
        combPhiDeriv i 1 ((χ : ℂ) - (t : ℂ) * Complex.I) b))
    (B := fun t : ℝ => K * (t ^ 2 - a ^ 2)) (B' := fun t : ℝ => K * (2 * t))
    (a := a) (b := c) hcont
    (fun t ht => ((hder t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])).sub_const _
      ).hasDerivWithinAt)
    (by simp)
    (fun t => by
      have := ((hasDerivAt_id t).pow 2).sub_const (a ^ 2) |>.const_mul K
      simpa using this)
    (fun t ht => by
      have ht0 : 0 ≤ t := ha.trans ht.1
      have ht1 : |t| ≤ 1 / 8 := by rw [abs_of_nonneg ht0]; linarith [ht.2]
      rw [norm_mul, Complex.norm_I, one_mul]
      refine (hlip i 1 hi le_rfl hb (hz t ht1).2 (hz t ht1).1).trans ?_
      have : ‖((χ : ℂ) + (t : ℂ) * Complex.I) - ((χ : ℂ) - (t : ℂ) * Complex.I)‖ = 2 * t := by
        have e : ((χ : ℂ) + (t : ℂ) * Complex.I) - ((χ : ℂ) - (t : ℂ) * Complex.I) =
            ((2 * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
      rw [this])
  have := key (Set.right_mem_Icc.mpr hac)
  simpa using this

/-- The pair step of `(PC)`: for `χ, χ' ≥ 0` and `|ε|, |ε'| ≤ 1/8`,
`‖∂_b^i [ψ(χ', ε') - ψ(χ, ε)]‖ ≤ K |ε'² - ε²| + 2 K |χ' - χ|`
(path `(χ, ε) → (χ, ε') → (χ', ε')`). -/
lemma pairDeriv_sub_le :
    ∃ K > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {χ' χ ε' ε : ℝ} {b : ℂ}, b ∈ combNMid → 0 ≤ χ' → 0 ≤ χ →
      |ε'| ≤ 1 / 8 → |ε| ≤ 1 / 8 →
      ‖pairDeriv i χ' ε' b - pairDeriv i χ ε b‖ ≤ K * |ε' ^ 2 - ε ^ 2| + 2 * K * |χ' - χ| := by
  obtain ⟨K₁, hK₁, hlip⟩ := combPhiDeriv_lipschitz_zeta
  obtain ⟨K₂, hK₂, hε⟩ := pairDeriv_sub_le_of_le
  refine ⟨K₁ + K₂, by positivity, fun i hi χ' χ ε' ε b hb hχ' hχ hε' hε0 => ?_⟩
  have hs1 : ‖pairDeriv i χ' ε' b - pairDeriv i χ ε' b‖ ≤ 2 * K₁ * |χ' - χ| := by
    unfold pairDeriv
    have a1 := hlip i hi hb (memCombZ_of_re_nonneg hχ hε') (memCombZ_of_re_nonneg hχ' hε')
    have a2 := hlip i hi hb (memCombZ_of_re_nonneg' hχ hε') (memCombZ_of_re_nonneg' hχ' hε')
    have n1 : ‖((χ' : ℂ) + (ε' : ℂ) * Complex.I) - ((χ : ℂ) + (ε' : ℂ) * Complex.I)‖ =
        |χ' - χ| := by
      rw [add_sub_add_right_eq_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have n2 : ‖((χ' : ℂ) - (ε' : ℂ) * Complex.I) - ((χ : ℂ) - (ε' : ℂ) * Complex.I)‖ =
        |χ' - χ| := by
      rw [sub_sub_sub_cancel_right, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [n1] at a1
    rw [n2] at a2
    calc _ = ‖(combPhiDeriv i 0 ((χ' : ℂ) + (ε' : ℂ) * Complex.I) b -
            combPhiDeriv i 0 ((χ : ℂ) + (ε' : ℂ) * Complex.I) b) +
          (combPhiDeriv i 0 ((χ' : ℂ) - (ε' : ℂ) * Complex.I) b -
            combPhiDeriv i 0 ((χ : ℂ) - (ε' : ℂ) * Complex.I) b)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  have hs2 : ‖pairDeriv i χ ε' b - pairDeriv i χ ε b‖ ≤ K₂ * |ε' ^ 2 - ε ^ 2| := by
    rw [← pairDeriv_abs i χ ε' b, ← pairDeriv_abs i χ ε b]
    have hsq : ∀ u v : ℝ, |u| ^ 2 - |v| ^ 2 = u ^ 2 - v ^ 2 := fun u v => by
      rw [sq_abs, sq_abs]
    rcases le_total |ε| |ε'| with h | h
    · have hnn : 0 ≤ ε' ^ 2 - ε ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg ε) h 2
        rw [sq_abs, sq_abs] at this
        linarith
      have := hε i hi hb hχ (abs_nonneg ε) h hε'
      rw [hsq] at this
      rw [abs_of_nonneg hnn]
      exact this
    · have hnn : 0 ≤ ε ^ 2 - ε' ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg ε') h 2
        rw [sq_abs, sq_abs] at this
        linarith
      have := hε i hi hb hχ (abs_nonneg ε') h hε0
      rw [hsq] at this
      rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg hnn]
      exact this
  calc ‖pairDeriv i χ' ε' b - pairDeriv i χ ε b‖
      = ‖(pairDeriv i χ' ε' b - pairDeriv i χ ε' b) + (pairDeriv i χ ε' b - pairDeriv i χ ε b)‖ := by
        congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by
        have := abs_nonneg (ε' ^ 2 - ε ^ 2)
        have := abs_nonneg (χ' - χ)
        nlinarith)

/-- The total pair change `|χ'_f - χ_f| + Σ_j (|ε'_j² - ε_j⁰²| + 2 |χ'_j - χ_j|)` of a finite
modification (`ut:Phi`, display `ut:PC`, summed over the modified factors). -/
noncomputable def designPairChange (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) : ℝ :=
  |designSite c' σ f - chiQuantile c' (f : ℝ)| +
    ∑ j ∈ Finset.range (N - f),
      (|ε (f + 1 + j) ^ 2 - (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)|)

lemma designPairChange_nonneg (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) :
    0 ≤ designPairChange c' f N η₀ σ ε := by
  unfold designPairChange
  positivity

/-- `|ε² - ε₀²| ≤ 2 |ε - ε₀|` for widths `≤ 1/8` (the squared bound is the sharper one). -/
lemma abs_sq_sub_sq_le {ε ε₀ : ℝ} (h : |ε| ≤ 1 / 8) (h₀ : |ε₀| ≤ 1 / 8) :
    |ε ^ 2 - ε₀ ^ 2| ≤ 2 * |ε - ε₀| := by
  have : ε ^ 2 - ε₀ ^ 2 = (ε - ε₀) * (ε + ε₀) := by ring
  rw [this, abs_mul]
  have h1 : |ε + ε₀| ≤ 1 / 4 := (abs_add_le _ _).trans (by linarith)
  nlinarith [abs_nonneg (ε - ε₀), abs_nonneg (ε + ε₀)]

/-- **Squared pair-change bound `(PC)`** (`ut:Phi`, eq. `ut:PC`): for an admissible finite modification,
`‖∂_b^i Δ_D‖ ≤ K · (|χ'_f - χ_f| + Σ_j (|ε'_j² - ε_j⁰²| + 2 |χ'_j - χ_j|))` on `𝒩` for `i ≤ 2`, with `K`
absolute: independent of `c'`, `f`, `N`, `η₀` and of the data.  The widths enter only through
`∂_{ε²} ψ = -(1/(2ε)) ∫_{-ε}^{ε} ∂_ζ² φ_{χ+is} ds`. -/
theorem iteratedDeriv_designDelta_le_sq :
    ∃ K > 0, ∀ {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ} {b : ℂ} (i : ℕ), i ≤ 2 → b ∈ combNMid →
      DesignAdmissible c' f N η₀ σ ε →
      ‖iteratedDeriv i (designDelta c' f N η₀ σ ε) b‖ ≤ K * designPairChange c' f N η₀ σ ε := by
  obtain ⟨K₁, hK₁, hd⟩ := iteratedDeriv_dphi_le
  obtain ⟨K₂, hK₂, hpair⟩ := pairDeriv_sub_le
  refine ⟨K₁ + K₂, by positivity, fun {c' f N η₀ σ ε b} i hi hb hA => ?_⟩
  have hb' := combNMid_subset_combNOpen hb
  rw [designDelta_eq_dphi]
  have hzf := ofReal_memCombZ hA.first
  have hzf0 := ofReal_memCombZ hA.ref_first
  have hpl : ∀ j ∈ Finset.range (N - f),
      ((designSite c' σ (f + 1 + j) : ℂ) + (ε (f + 1 + j) : ℂ) * Complex.I) ∈ combZ ∧
      ((designSite c' σ (f + 1 + j) : ℂ) - (ε (f + 1 + j) : ℂ) * Complex.I) ∈ combZ ∧
      ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) ∈ combZ ∧
      ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) ∈ combZ := fun j hj => by
    have hj' := Finset.mem_range.mp hj
    exact ⟨memCombZ_of_re_nonneg (hA.site j hj') (hA.width j hj'),
      memCombZ_of_re_nonneg' (hA.site j hj') (hA.width j hj'),
      memCombZ_of_re_nonneg (hA.ref_site j hj') (hA.ref_width j hj'),
      memCombZ_of_re_nonneg' (hA.ref_site j hj') (hA.ref_width j hj')⟩
  have hcd : ∀ ζ' ζ : ℂ, ζ' ∈ combZ → ζ ∈ combZ → ContDiffAt ℂ i (dphi ζ' ζ) b :=
    fun ζ' ζ h' h => by
      unfold dphi
      exact (contDiffAt_phiZeta h' hb' i).sub (contDiffAt_phiZeta h hb' i)
  rw [iteratedDeriv_fun_add (hcd _ _ hzf hzf0)
    (ContDiffAt.sum fun j hj => (hcd _ _ (hpl j hj).1 (hpl j hj).2.2.1).add
      (hcd _ _ (hpl j hj).2.1 (hpl j hj).2.2.2)),
    iteratedDeriv_fun_sum (fun j hj => (hcd _ _ (hpl j hj).1 (hpl j hj).2.2.1).add
      (hcd _ _ (hpl j hj).2.1 (hpl j hj).2.2.2))]
  refine (norm_add_le _ _).trans ?_
  have h1 := (hd i hi hb hzf0 hzf).2
  have hfirst : ‖((designSite c' σ f : ℂ)) - ((chiQuantile c' (f : ℝ) : ℝ) : ℂ)‖ =
      |designSite c' σ f - chiQuantile c' (f : ℝ)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hfirst] at h1
  have h2 : ‖∑ j ∈ Finset.range (N - f), iteratedDeriv i (fun b =>
      dphi ((designSite c' σ (f + 1 + j) : ℂ) + (ε (f + 1 + j) : ℂ) * Complex.I)
        ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) b +
      dphi ((designSite c' σ (f + 1 + j) : ℂ) - (ε (f + 1 + j) : ℂ) * Complex.I)
        ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) b) b‖ ≤
      ∑ j ∈ Finset.range (N - f), (K₂ * (|ε (f + 1 + j) ^ 2 - (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)|)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hcj := hpl j hj
    have hj' := Finset.mem_range.mp hj
    rw [iteratedDeriv_fun_add (hcd _ _ hcj.1 hcj.2.2.1) (hcd _ _ hcj.2.1 hcj.2.2.2),
      (hd i hi hb hcj.2.2.1 hcj.1).1, (hd i hi hb hcj.2.2.2 hcj.2.1).1]
    have hpj := hpair i hi hb (hA.site j hj') (hA.ref_site j hj') (hA.width j hj')
      (hA.ref_width j hj')
    have e : (combPhiDeriv i 0 ((designSite c' σ (f + 1 + j) : ℂ) +
          (ε (f + 1 + j) : ℂ) * Complex.I) b -
        combPhiDeriv i 0 ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) +
          ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) b) +
        (combPhiDeriv i 0 ((designSite c' σ (f + 1 + j) : ℂ) -
          (ε (f + 1 + j) : ℂ) * Complex.I) b -
        combPhiDeriv i 0 ((chiQuantile c' ((f + 1 + j : ℕ) : ℝ) : ℂ) -
          ((η₀ * siteGap c' (f + 1 + j) : ℝ) : ℂ) * Complex.I) b) =
        pairDeriv i (designSite c' σ (f + 1 + j)) (ε (f + 1 + j)) b -
          pairDeriv i (chiQuantile c' ((f + 1 + j : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + j)) b := by
      unfold pairDeriv; ring
    rw [e]
    refine hpj.trans ?_
    have := abs_nonneg (ε (f + 1 + j) ^ 2 - (η₀ * siteGap c' (f + 1 + j)) ^ 2)
    have := abs_nonneg (designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ))
    nlinarith
  have hmul : ∑ j ∈ Finset.range (N - f), (K₂ * (|ε (f + 1 + j) ^ 2 -
        (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)|)) =
      K₂ * ∑ j ∈ Finset.range (N - f), (|ε (f + 1 + j) ^ 2 -
        (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)|) :=
    (Finset.mul_sum _ _ _).symm
  rw [hmul] at h2
  unfold designPairChange
  have hS : 0 ≤ ∑ j ∈ Finset.range (N - f), (|ε (f + 1 + j) ^ 2 -
        (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)|) :=
    Finset.sum_nonneg fun j _ => by positivity
  have hF := abs_nonneg (designSite c' σ f - chiQuantile c' (f : ℝ))
  nlinarith

/-- The `i`-th `b`-derivative of `Δ_D` is bounded by `K` times the total displacement of the zeros.
(The linear form, a corollary of `iteratedDeriv_designDelta_le_sq`: widths are `≤ 1/8`.) -/
theorem iteratedDeriv_designDelta_le :
    ∃ K > 0, ∀ {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ} {b : ℂ} (i : ℕ), i ≤ 2 → b ∈ combNMid →
      DesignAdmissible c' f N η₀ σ ε →
      ‖iteratedDeriv i (designDelta c' f N η₀ σ ε) b‖ ≤
        K * (|designSite c' σ f - chiQuantile c' (f : ℝ)| +
          ∑ j ∈ Finset.range (N - f),
            (2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)| +
              2 * |ε (f + 1 + j) - η₀ * siteGap c' (f + 1 + j)|)) := by
  obtain ⟨K, hK, hsq⟩ := iteratedDeriv_designDelta_le_sq
  refine ⟨K, hK, fun {c' f N η₀ σ ε b} i hi hb hA => (hsq i hi hb hA).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hK.le
  unfold designPairChange
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  have := abs_sq_sub_sq_le (hA.width j hj') (hA.ref_width j hj')
  linarith

/-- The data of a finite modification are admissible for `c'` large, uniformly in the cut `N`, as soon
as the modified sites are `≥ 0` and the modified widths are `≤ 1/8` (the reference sites and widths
are then automatically admissible). -/
theorem designAdmissible_of_nonneg (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ), f ≤ N → 0 ≤ designSite c' σ f →
      (∀ i < N - f, 0 ≤ designSite c' σ (f + 1 + i)) → (∀ i < N - f, |ε (f + 1 + i)| ≤ 1 / 8) →
      DesignAdmissible c' f N η₀ σ ε := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  filter_upwards [h_ev, eventually_gt_atTop 0] with c'
    ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_1⟩ hc' N σ ε hfN hs0 hs hε
  exact
    { first := hs0
      ref_first := xiStar_pos.le.trans (refSite_bounds hc' hf hfN).1
      site := hs
      width := hε
      ref_site := fun i hi => xiStar_pos.le.trans
        (refSite_bounds (k := f + 1 + i) (N := N) hc' (by omega) (by omega)).1
      ref_width := fun i hi => by
        have hga := siteGap_nonneg hc' (by omega : 1 ≤ f + 1 + i)
        rw [abs_of_nonneg (mul_nonneg hη₀0 hga)]
        have hgk := hgap_k (f + 1 + i) (by omega)
        calc η₀ * siteGap c' (f + 1 + i) ≤ (1 / 4) * (1 / 2) :=
              mul_le_mul hη₀1 (hgk.trans hgap_1) hga (by norm_num)
          _ = 1 / 8 := by norm_num }

/-- Members of the compact family `|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ` are admissible for large `c'`. -/
theorem designAdmissible_eventually (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      DesignAdmissible c' f N η₀ σ ε := by
  have hlam_ev : ∀ᶠ c' in atTop, M * lambdaComb c' ≤ xiStar ∧ E * lambdaComb c' ≤ 1 / 8 := by
    have h1 := tendsto_lambdaComb_atTop.const_mul M
    have h3 := tendsto_lambdaComb_atTop.const_mul E
    simp only [mul_zero] at h1 h3
    exact (h1.eventually_le_const xiStar_pos).and (h3.eventually_le_const (by norm_num))
  filter_upwards [designAdmissible_of_nonneg f hf hη₀0 hη₀1, eventually_gt_atTop 0, hlam_ev] with c'
    hAd hc' ⟨hMlam, hElam⟩ σ ε hσ hε
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  have hMl1 : lambdaComb c' * M ≤ xiStar := by linarith [mul_comm M (lambdaComb c')]
  refine hAd N σ ε hfN (designSite_bounds hlam.le (hσ f le_rfl hfN) le_rfl hMl1).1
    (fun i hi => (designSite_bounds hlam.le (hσ (f + 1 + i) (by omega) (by omega)) le_rfl
      hMl1).1) (fun i hi => ?_)
  have h := hε (f + 1 + i) (by omega) (by omega)
  rw [abs_of_nonneg h.1]; linarith [h.2]

/-! ### 4. Lemma `Φ`(b) -/

/-- The content of Lemma `Φ`(b) for one finite modification, with derivative bound `B`:

1. on `𝒩`, `log B_ref^{(f)} + Δ_D = c' Φ₀ + Φ₁^{(f)} + Δ_D` (Lemma `K3`) and the exponential of it
   is `B_D^{(f)}`, so it is a logarithm of `B_D^{(f)}` on `𝒩`;
2. `exp Δ_D = B_D^{(f)} / B_ref^{(f)}` on `𝒩`;
3. `Re (Φ₁^{(f)} + Δ_D) = 0` on `E₊ = {Im b = 1/2}`;
4. `‖Δ_D^{(i)}‖ ≤ B` on `𝒩` for `i = 0, 1, 2`.

Here `Φ₀ = phi0` and `Φ₁^{(f)} = phi1Comb` are those of Lemma `K3`. -/
def DesignPhiDecomp (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (B : ℝ) : Prop :=
  (∀ b ∈ combN, logRefComb c' f η₀ b + designDelta c' f N η₀ σ ε b =
      (c' : ℂ) * phi0 b + phi1Comb c' f η₀ b + designDelta c' f N η₀ σ ε b ∧
    Complex.exp (logRefComb c' f η₀ b + designDelta c' f N η₀ σ ε b) =
      designComb c' f N η₀ σ ε b) ∧
  (∀ b ∈ combN, Complex.exp (designDelta c' f N η₀ σ ε b) =
      designComb c' f N η₀ σ ε b / refComb c' f η₀ b) ∧
  (∀ b : ℂ, b.im = 1 / 2 → (phi1Comb c' f η₀ b + designDelta c' f N η₀ σ ε b).re = 0) ∧
  (∀ i : ℕ, i ≤ 2 → ∀ b ∈ combN, ‖iteratedDeriv i (designDelta c' f N η₀ σ ε) b‖ ≤ B)

/-- `DesignPhiDecomp` is monotone in the derivative bound. -/
lemma DesignPhiDecomp.mono {c' : ℝ} {f N : ℕ} {η₀ : ℝ} {σ ε : ℕ → ℝ} {B B' : ℝ}
    (h : DesignPhiDecomp c' f N η₀ σ ε B) (hB : B ≤ B') : DesignPhiDecomp c' f N η₀ σ ε B' :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi b hb => (h.2.2.2 i hi b hb).trans hB⟩

/-- **Lemma `Φ`(b), uniform form, from a derivative bound.**  For fixed `f ≥ 1` and `η₀ ∈ [0, 1/4]`
there is `c₀` such that for every `c' ≥ c₀`, **every cut `N ≥ f`** and every admissible finite
modification, the first three items of `DesignPhiDecomp` hold, and the fourth with any constant `B`
bounding `‖∂_b^i Δ_D‖` on `𝒩`.  The threshold does not depend on `N` or on the data. -/
theorem designPhiDecomp_of_bound (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (B : ℝ), f ≤ N → DesignAdmissible c' f N η₀ σ ε →
      (∀ i : ℕ, i ≤ 2 → ∀ b ∈ combN,
        ‖iteratedDeriv i (designDelta c' f N η₀ σ ε) b‖ ≤ B) →
      DesignPhiDecomp c' f N η₀ σ ε B := by
  filter_upwards [refComb_eq_split_unif f hη₀0 hη₀1, cexp_logRefComb f hf hη₀0 hη₀1,
    logRefComb_eq_comb_decomp f hf hη₀0 hη₀1, re_phi1Comb_eq_zero_of_im_half f hf hη₀0 hη₀1]
    with c' hsp hexp hdec hre N σ ε B hfN hA hbd
  have hlogeq : ∀ b ∈ combN, logRefComb c' f η₀ b + designDelta c' f N η₀ σ ε b =
      (c' : ℂ) * phi0 b + phi1Comb c' f η₀ b + designDelta c' f N η₀ σ ε b := fun b hb => by
    rw [hdec (combN_subset_combNMid hb)]
  have hbim : ∀ b ∈ combN, |b.im| < 7 / 8 := fun b hb => by
    have := abs_le.mp (show |b.im - 1 / 2| ≤ 1 / 4 from hb)
    rw [abs_lt]; constructor <;> linarith
  have hDexp : ∀ b ∈ combN, refComb c' f η₀ b * Complex.exp (designDelta c' f N η₀ σ ε b) =
      designComb c' f N η₀ σ ε b := fun b hb =>
    refComb_mul_exp_designDelta hb hA (hsp N hfN (hbim b hb))
  have hrefne : ∀ b ∈ combN, refComb c' f η₀ b ≠ 0 := fun b hb => by
    rw [← hexp hb]; exact Complex.exp_ne_zero _
  unfold DesignPhiDecomp
  refine ⟨fun b hb => ⟨hlogeq b hb, ?_⟩, fun b hb => ?_, fun b hb_im => ?_, hbd⟩
  · rw [Complex.exp_add, hexp hb, hDexp b hb]
  · rw [eq_div_iff (hrefne b hb), mul_comm, hDexp b hb]
  · have hbN : b ∈ combN := by change |b.im - 1 / 2| ≤ 1 / 4; rw [hb_im]; norm_num
    have hD : (designDelta c' f N η₀ σ ε b).re = 0 := by
      unfold designDelta
      rw [Complex.add_re, Complex.sub_re, phiZeta_re_eq_zero_of_im_half hA.first hb_im,
        phiZeta_re_eq_zero_of_im_half hA.ref_first hb_im, Complex.re_sum]
      simp only [sub_self, zero_add]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [Complex.sub_re, re_psiPair_eq_zero hb_im (hA.site j hj') (hA.width j hj'),
        re_psiPair_eq_zero hb_im (hA.ref_site j hj') (hA.ref_width j hj'), sub_zero]
    rw [Complex.add_re, hre hb_im, hD, add_zero]

/-- **Lemma `Φ`(b) from the squared pair-change bound `(PC)`, uniform in the cut `N`.**  There is an
absolute `K > 0` such that for fixed `f ≥ 1` and `η₀ ∈ [0, 1/4]`, for `c'` large (threshold independent of
`N` and of the data), every `N ≥ f` and every admissible finite modification whose total pair change
`designPairChange` is at most `P`, `DesignPhiDecomp c' f N η₀ σ ε (K P)` holds: `log B_D = c' Φ₀ + Φ₁^{(f)} +
Δ_D` on `𝒩`, `Re (Φ₁^{(f)} + Δ_D) = 0` on `E₊`, `‖Δ_D^{(i)}‖ ≤ K P`, `i ≤ 2`. -/
theorem designPhiDecomp_of_pairChange :
    ∃ K > 0, ∀ (f : ℕ), 1 ≤ f → ∀ {η₀ : ℝ}, 0 ≤ η₀ → η₀ ≤ 1 / 4 →
      ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ ε : ℕ → ℝ) (P : ℝ), f ≤ N → DesignAdmissible c' f N η₀ σ ε →
        designPairChange c' f N η₀ σ ε ≤ P → DesignPhiDecomp c' f N η₀ σ ε (K * P) := by
  obtain ⟨K, hK, hsq⟩ := iteratedDeriv_designDelta_le_sq
  refine ⟨K, hK, fun f hf η₀ hη₀0 hη₀1 => ?_⟩
  filter_upwards [designPhiDecomp_of_bound f hf hη₀0 hη₀1] with c' h N σ ε P hfN hA hP
  exact h N σ ε (K * P) hfN hA fun i hi b hb =>
    (hsq i hi (combN_subset_combNMid hb) hA).trans (mul_le_mul_of_nonneg_left hP hK.le)

/-- The total pair change of a member of the compact family is `≤ C λ`. -/
lemma designPairChange_le_compact {c' : ℝ} (hc' : 0 < c') {f N : ℕ} (hf : 1 ≤ f) (hfN : f ≤ N)
    {M E Cg s : ℝ} {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) {σ ε : ℕ → ℝ}
    (hσ : ∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) (hε : ∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c')
    (hA : DesignAdmissible c' f N η₀ σ ε) (hMs : M ≤ s) (hΦs : phiQuantile ((N : ℝ) + 2) ≤ s)
    (hgap : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ Cg * lambdaComb c') :
    designPairChange c' f N η₀ σ ε ≤
      (2 * s + ((N - f : ℕ) : ℝ) * (4 * s + 2 * E + Cg / 2)) * lambdaComb c' := by
  have hfirst : |designSite c' σ f - chiQuantile c' (f : ℝ)| ≤ 2 * s * lambdaComb c' :=
    designSite_dist_le hc' hf hfN (hσ f le_rfl hfN) hMs hΦs
  have hterm : ∀ j ∈ Finset.range (N - f),
      |ε (f + 1 + j) ^ 2 - (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)| ≤
      (4 * s + 2 * E + Cg / 2) * lambdaComb c' := fun j hj => by
    have hj' := Finset.mem_range.mp hj
    have h1 := designSite_dist_le hc' (by omega : 1 ≤ f + 1 + j) (by omega)
      (hσ (f + 1 + j) (by omega) (by omega)) hMs hΦs
    have h2 := hε (f + 1 + j) (by omega) (by omega)
    have h3 : 0 ≤ η₀ * siteGap c' (f + 1 + j) ∧
        η₀ * siteGap c' (f + 1 + j) ≤ Cg / 4 * lambdaComb c' := by
      have hga := siteGap_nonneg hc' (by omega : 1 ≤ f + 1 + j)
      refine ⟨mul_nonneg hη₀0 hga, ?_⟩
      calc η₀ * siteGap c' (f + 1 + j) ≤ (1 / 4) * (Cg * lambdaComb c') :=
            mul_le_mul hη₀1 (hgap _ (by omega)) hga (by norm_num)
        _ = Cg / 4 * lambdaComb c' := by ring
    have h4 : |ε (f + 1 + j) - η₀ * siteGap c' (f + 1 + j)| ≤ (E + Cg / 4) * lambdaComb c' := by
      rw [abs_le]; constructor <;> nlinarith [h2.1, h2.2, h3.1, h3.2]
    have h5 := abs_sq_sub_sq_le (hA.width j hj') (hA.ref_width j hj')
    nlinarith [h1, h4, h5]
  have hsum : ∑ j ∈ Finset.range (N - f),
      (|ε (f + 1 + j) ^ 2 - (η₀ * siteGap c' (f + 1 + j)) ^ 2| +
        2 * |designSite c' σ (f + 1 + j) - chiQuantile c' ((f + 1 + j : ℕ) : ℝ)|) ≤
      ((N - f : ℕ) : ℝ) * ((4 * s + 2 * E + Cg / 2) * lambdaComb c') := by
    calc _ ≤ ∑ _j ∈ Finset.range (N - f), (4 * s + 2 * E + Cg / 2) * lambdaComb c' :=
          Finset.sum_le_sum hterm
      _ = _ := by simp
  unfold designPairChange
  nlinarith [hfirst, hsum]

/-- **Lemma `Φ`(b)** (`ut:Phi`, compact-family version, before the "Consequently").  Fix `f ≥ 1`,
`N ≥ f`, `M, E ≥ 0` and `η₀ ∈ [0, 1/4]`.  There is `C = C(N, M, E) ≥ 0` such that for `c'` large and
every finite modification `B_D^{(f)} = designComb c' f N η₀ σ ε` with `|σ_k| ≤ M` and
`0 ≤ ε'_k ≤ E λ`, uniformly in the family, `DesignPhiDecomp c' f N η₀ σ ε (C λ)` holds:
`log B_D^{(f)} = c' Φ₀ + Φ₁^{(f)} + Δ_D` on `𝒩`, `Re (Φ₁^{(f)} + Δ_D) = 0` on `E₊`, and
`sup_𝒩 |Δ_D^{(i)}| ≤ C λ` for `i = 0, 1, 2`. -/
theorem lemma_Phi_b (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) (hE : 0 ≤ E) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      DesignPhiDecomp c' f N η₀ σ ε (C * lambdaComb c') := by
  obtain ⟨K, hK, hKd⟩ := designPhiDecomp_of_pairChange
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  set s : ℝ := max (phiQuantile ((N : ℝ) + 2)) M with hs_def
  have hΦpos : 0 < phiQuantile ((N : ℝ) + 2) := by
    unfold phiQuantile
    apply Real.rpow_pos_of_pos
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hs : 0 < s := lt_of_lt_of_le hΦpos (le_max_left _ _)
  have hMs : M ≤ s := le_max_right _ _
  have hΦs : phiQuantile ((N : ℝ) + 2) ≤ s := le_max_left _ _
  refine ⟨K * (2 * s + ((N - f : ℕ) : ℝ) * (4 * s + 2 * E + Cg / 2)), by positivity, ?_⟩
  filter_upwards [hKd f hf hη₀0 hη₀1, designAdmissible_eventually f N hf hfN M E hη₀0 hη₀1, h_ev,
    eventually_gt_atTop 0] with c' hD hAd ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_1⟩ hc' σ ε hσ hε
  have hA := hAd σ ε hσ hε
  have hpc := designPairChange_le_compact hc' hf hfN hη₀0 hη₀1 hσ hε hA hMs hΦs
    (fun k hk => (hgap_k k hk).trans (hgap_1_bd.trans hcd1_bd))
  rw [mul_assoc]
  exact hD N σ ε _ hfN hA hpc

/-- **Lemma `Φ`(a) at fixed `N`** (`ut:Phi`(a)): for the `f = 1` design `D(N, η_*, d)` of
`Design.PerturbP`, `DesignPhiDecomp` holds with the derivative bound `C(N, η_*, d) λ`. -/
theorem lemma_Phi_a_fixedN (N : ℕ) (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar)
    (hη1 : etaStar ≤ 1 / 4) (d M : ℝ) (hM : ∀ k, 1 ≤ k → k ≤ N → |designSigma1 d k| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop,
      DesignPhiDecomp c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' etaStar)
        (C * lambdaComb c') := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  obtain ⟨C, hC, h⟩ := lemma_Phi_b 1 N le_rfl hN M Cg hCg.le (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, h_ev, eventually_gt_atTop 0] with c' hc'
    ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos
  refine hc' (designSigma1 d) (designWidth1 c' etaStar) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), ?_⟩)
  have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
  unfold designWidth1
  calc etaStar * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
        mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
    _ = Cg * lambdaComb c' := one_mul _

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_Phi_a_fixedN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Phi_a_fixedN

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_Phi_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Phi_b

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.iteratedDeriv_designDelta_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_designDelta_le_sq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.iteratedDeriv_designDelta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_designDelta_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designPhiDecomp_of_pairChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPhiDecomp_of_pairChange

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.designAdmissible_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designAdmissible_of_nonneg

end FormalResearch.ModularBootstrap.Upper.Design
