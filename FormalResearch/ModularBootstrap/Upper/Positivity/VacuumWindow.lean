module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumPrelim
public import FormalResearch.ModularBootstrap.Upper.Window.DesignBridge
public import FormalResearch.ModularBootstrap.Upper.Window.Identification
public import FormalResearch.ModularBootstrap.Upper.Window.Quadrature

/-!
# Proposition V: the window integral of the designs (`ut:Vac`, `ut:W`, `ut:ID`, `ut:G`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Proposition V (`ut:Vac`).

* `integral_sub_window`: the substitution `t = c'(ξ_* + λσ)²/3` (`dt = (2/3) c' x λ dσ`);
* `tildeW_designMod`: the window limit of the design `designMod N η d` is `C_* κ Re W(-κσ)` (`ut:ID`);
* `windowLimit_integral_tendsto`: `∫_{-n}^{Φ_{n+1}} W̃^{±(1)} dσ → C_* V_D` as `n → ∞`, with
  `V_D = ∫_ℝ Re W` the window integral of `ut:V`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Holes

/-- The substitution `t = c'(ξ_* + λσ)²/3`. -/
lemma integral_sub_window {c' : ℝ} (hc' : 0 ≤ c') (g : ℝ → ℝ) (hg : ContinuousOn g (Ici 0)) (a b : ℝ) :
    ∫ σ in a..b, g (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
        ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') =
      ∫ t in (c' * (xiStar + lambdaComb c' * a) ^ 2 / 3)..(c' * (xiStar + lambdaComb c' * b) ^ 2 / 3), g t := by
  have hd : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3)
      ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') σ := by
    intro σ
    have h1 : HasDerivAt (fun σ : ℝ => xiStar + lambdaComb c' * σ) (lambdaComb c') σ := by
      simpa using ((hasDerivAt_id σ).const_mul (lambdaComb c')).const_add xiStar
    have h2 := ((h1.pow 2).const_mul c').div_const 3
    convert h2 using 1
    simp only [Nat.cast_ofNat]
    ring
  have hcont : ContinuousOn (fun σ : ℝ => (2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c')
      (uIcc a b) := by fun_prop
  have himg : (fun σ : ℝ => c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) '' uIcc a b ⊆ Ici 0 := by
    rintro _ ⟨σ, _, rfl⟩
    exact mem_Ici.mpr (by positivity)
  exact intervalIntegral.integral_comp_mul_deriv'' (by fun_prop) (fun σ _ => (hd σ).hasDerivWithinAt)
    hcont (hg.mono himg)

lemma tildeW_congr {f : ℕ} {σf σf' : ℝ} {σS σS' εH εH' : ℕ → ℝ} (hσ : σf = σf')
    (hs : ∀ k, f < k → σS k = σS' k) (he : ∀ k, f < k → εH k = εH' k) (σ : ℝ) :
    tildeW f σf σS εH σ = tildeW f σf' σS' εH' σ := by
  subst hσ
  have key : ∀ K, windowFiniteProd f σf σS εH K σ = windowFiniteProd f σf σS' εH' K σ := fun K => by
    unfold windowFiniteProd
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    have := (Finset.mem_Icc.mp hk).1
    rw [hs k (by omega), he k (by omega)]
  simp only [tildeW, key]

/-! ### The Airy window of a finite modification with arbitrary offsets -/

/-- The Airy window `W` of the finite modification `sigMod N η σ`: first site `-κ σ_1`, sites `-κ σ_k`
(`2 ≤ k ≤ N`, arbitrary: displaced sites allowed), widths `κ η ℓ_k/λ → η gap_k`, reference tail. -/
noncomputable def sigWindowW (N : ℕ) (η : ℝ) (σ : ℕ → ℝ) (u : ℂ) : ℂ :=
  airyWindowProd 1 (-kappaAiry * (sigMod N η σ).sigmaFLim)
    (fun k => -kappaAiry * (sigMod N η σ).allSigmaLim k)
    (fun k => kappaAiry * (sigMod N η σ).allEpsLim k) u

lemma sigWindowW_tailHyp {N : ℕ} (hN : 1 ≤ N) (η : ℝ) (σ : ℕ → ℝ) :
    AiryProdTailHypothesis 1 (fun k => -kappaAiry * (sigMod N η σ).allSigmaLim k)
      (fun k => kappaAiry * (sigMod N η σ).allEpsLim k) :=
  airyProdTailHypothesis_of_tail (f := 1) (N := N) hN (C_t := 1) one_pos
    ((sigMod N η σ).tail_bound_all (by norm_num [sigMod]) (by norm_num [sigMod]))

theorem sigWindowW_differentiable {N : ℕ} (hN : 1 ≤ N) (η : ℝ) (σ : ℕ → ℝ) :
    Differentiable ℂ (sigWindowW N η σ) :=
  airyWindowProd_differentiable 1 le_rfl _ _ _ (sigWindowW_tailHyp hN η σ)

theorem sigWindowW_integrable {N : ℕ} (hN : 1 ≤ N) (η : ℝ) (σ : ℕ → ℝ) :
    Integrable (fun x : ℝ => sigWindowW N η σ (x : ℂ)) := by
  obtain ⟨C, hC, hbd⟩ := airyWindowProd_bound 1 le_rfl (-kappaAiry * (sigMod N η σ).sigmaFLim) _ _
    (sigWindowW_tailHyp hN η σ)
  have hbd' : ∀ u : ℂ, ‖sigWindowW N η σ u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u := fun u => by
    have := hbd u
    rw [show -((2 * ((1 : ℕ) : ℝ) - 1 / 2)) = -(3 / 2 : ℝ) by norm_num] at this
    exact this
  exact airy_integrable_real (sigWindowW_differentiable hN η σ) hC.le (by norm_num) hbd'

lemma continuous_sigWindowRe {N : ℕ} (hN : 1 ≤ N) (η : ℝ) (σ : ℕ → ℝ) :
    Continuous (fun u : ℝ => (sigWindowW N η σ (u : ℂ)).re) :=
  Complex.continuous_re.comp ((sigWindowW_differentiable hN η σ).continuous.comp Complex.continuous_ofReal)

/-- The window integral `V = ∫_ℝ Re W` of the modification `sigMod N η σ`. -/
noncomputable def windowIntegralSig (N : ℕ) (η : ℝ) (σ : ℕ → ℝ) : ℝ :=
  ∫ u : ℝ, (sigWindowW N η σ (u : ℂ)).re

/-- Lemma ID for `sigMod`: `W̃^{±(1)} = C_* κ Re W(-κσ)`. -/
theorem tildeW_sigMod (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (σ : ℕ → ℝ) (x : ℝ) :
    tildeW 1 (sigMod N η σ).sigmaFLim (sigMod N η σ).allSigmaLim (sigMod N η σ).allEpsLim x =
      CStar * kappaAiry * (sigWindowW N η σ ((-kappaAiry * x : ℝ) : ℂ)).re :=
  lemma_ID_mod N hN (sigMod N η σ) (by norm_num [sigMod]) (by norm_num [sigMod]) x

/-- The window of the design `D(N, η_*, d)` is the window of `sigMod` at `σ = designSigma1 d`. -/
lemma designWindowW_eq_sig (N : ℕ) (η d : ℝ) (u : ℂ) :
    designWindowW N η d u = sigWindowW N η (designSigma1 d) u := by
  have hκ := kappaAiry_pos
  have hκ_ne : kappaAiry ≠ 0 := hκ.ne'
  unfold designWindowW sigWindowW
  have huF : -kappaAiry * (sigMod N η (designSigma1 d)).sigmaFLim = airyZero 1 - d := by
    show -kappaAiry * designSigma1 d 1 = airyZero 1 - d
    unfold designSigma1 sNodeAiry
    simp only [↓reduceIte]
    rw [abs_of_neg (airyZero_neg 1)]
    field_simp [hκ_ne]
    ring
  rw [huF]
  refine airyWindowProd_congr (fun k hk => ?_) (fun k hk => ?_) u
  · unfold designSiteU ModifiedCombData.allSigmaLim sigMod
    by_cases hkN : k ≤ N
    · simp only [hkN, ↓reduceIte]
      show airyZero k = -kappaAiry * designSigma1 d k
      unfold designSigma1 sNodeAiry
      simp only [show k ≠ 1 by omega, ↓reduceIte]
      rw [abs_of_neg (airyZero_neg k)]
      field_simp [hκ_ne]
    · simp only [hkN, ↓reduceIte]
      rfl
  · unfold designWidthU ModifiedCombData.allEpsLim sigMod gapWKB uWKB phiWKB
    by_cases hkN : k ≤ N
    · simp only [hkN, ↓reduceIte]
      ring
    · simp only [hkN, ↓reduceIte]
      ring

/-- Lemma ID for the one-member family `designMod`: `W̃^{±(1)} = C_* κ Re W(-κσ)`. -/
theorem tildeW_designMod (N : ℕ) (hN : 1 ≤ N) (η d σ : ℝ) :
    tildeW 1 (designMod N η d).sigmaFLim (designMod N η d).allSigmaLim (designMod N η d).allEpsLim σ =
      CStar * kappaAiry * (designWindowW N η d ((-kappaAiry * σ : ℝ) : ℂ)).re := by
  rw [← lemma_ID_design N hN η d σ]
  refine tildeW_congr ?_ (fun k hk => ?_) (fun k hk => ?_) σ
  · show designSigma1 d 1 = sNodeAiry 1 + d / kappaAiry
    unfold designSigma1 sNodeAiry
    simp only [↓reduceIte]
    ring
  · unfold ModifiedCombData.allSigmaLim
    by_cases hkN : k ≤ N
    · simp only [hkN, ↓reduceIte]
      show designSigma1 d k = sNodeAiry k
      unfold designSigma1
      simp [show k ≠ 1 by omega]
    · simp only [hkN, ↓reduceIte]
  · unfold ModifiedCombData.allEpsLim
    by_cases hkN : k ≤ N
    · simp only [hkN, ↓reduceIte]
      rfl
    · simp only [hkN, ↓reduceIte]
      rfl

/-- The window integral `V_D = ∫_ℝ Re W` of the design `D(N, η_*, d)` (`ut:V`). -/
noncomputable def windowIntegralVD (N : ℕ) (η d : ℝ) : ℝ :=
  ∫ u : ℝ, (designWindowW N η d (u : ℂ)).re

lemma windowIntegralVD_eq_sig (N : ℕ) (η d : ℝ) :
    windowIntegralVD N η d = windowIntegralSig N η (designSigma1 d) := by
  unfold windowIntegralVD windowIntegralSig
  simp_rw [designWindowW_eq_sig]

lemma continuous_designWindowRe (N : ℕ) (η d : ℝ) :
    Continuous (fun u : ℝ => (designWindowW N η d (u : ℂ)).re) :=
  Complex.continuous_re.comp ((designWindowW_differentiable N η d).continuous.comp Complex.continuous_ofReal)

lemma phiWKB_succ_tendsto : Tendsto (fun n : ℕ => phiWKB (n + 1)) atTop atTop := by
  unfold phiWKB
  have h0 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) - 1 / 4) atTop atTop :=
    tendsto_atTop_add_const_right _ _ h0
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp h1

/-- `∫_{-n}^{Φ_{n+1}} W̃^{±(1)}(σ) dσ → C_* V` for the modification `sigMod N η σF`. -/
theorem windowLimit_integral_tendsto_sig (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (σF : ℕ → ℝ) :
    Tendsto (fun n : ℕ => ∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (sigMod N η σF).sigmaFLim (sigMod N η σF).allSigmaLim (sigMod N η σF).allEpsLim σ)
      atTop (𝓝 (CStar * windowIntegralSig N η σF)) := by
  have hκ := kappaAiry_pos
  have hint : Integrable (fun u : ℝ => (sigWindowW N η σF (u : ℂ)).re) := (sigWindowW_integrable hN η σF).re
  have hA : Tendsto (fun n : ℕ => -kappaAiry * phiWKB (n + 1)) atTop atBot := by
    have := tendsto_neg_atTop_atBot.comp (phiWKB_succ_tendsto.const_mul_atTop hκ)
    simpa [Function.comp_def, neg_mul] using this
  have hB : Tendsto (fun n : ℕ => kappaAiry * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hκ
  have ht := intervalIntegral_tendsto_integral hint hA hB
  have heq : ∀ n : ℕ, ∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (sigMod N η σF).sigmaFLim (sigMod N η σF).allSigmaLim
          (sigMod N η σF).allEpsLim σ =
      CStar * ∫ u in (-kappaAiry * phiWKB (n + 1))..(kappaAiry * (n : ℝ)),
        (sigWindowW N η σF (u : ℂ)).re := by
    intro n
    have h1 : ∀ σ : ℝ, tildeW 1 (sigMod N η σF).sigmaFLim (sigMod N η σF).allSigmaLim
        (sigMod N η σF).allEpsLim σ =
        (CStar * kappaAiry) * (fun u : ℝ => (sigWindowW N η σF (u : ℂ)).re) ((-kappaAiry) * σ) :=
      fun σ => tildeW_sigMod N hN η σF σ
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u : ℝ => (sigWindowW N η σF (u : ℂ)).re)
        (neg_ne_zero.mpr hκ.ne')]
    have e1 : (-kappaAiry) * (-(n : ℝ)) = kappaAiry * n := by ring
    rw [e1, smul_eq_mul, intervalIntegral.integral_symm (kappaAiry * (n : ℝ))]
    field_simp
  unfold windowIntegralSig
  simp_rw [heq]
  exact ht.const_mul CStar

/-- `∫_{-n}^{Φ_{n+1}} W̃^{±(1)}(σ) dσ → C_* V_D`. -/
theorem windowLimit_integral_tendsto (N : ℕ) (hN : 1 ≤ N) (η d : ℝ) :
    Tendsto (fun n : ℕ => ∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (designMod N η d).sigmaFLim (designMod N η d).allSigmaLim (designMod N η d).allEpsLim σ)
      atTop (𝓝 (CStar * windowIntegralVD N η d)) := by
  rw [windowIntegralVD_eq_sig]
  exact windowLimit_integral_tendsto_sig N hN η (designSigma1 d)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.windowLimit_integral_tendsto_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowLimit_integral_tendsto_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.windowLimit_integral_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowLimit_integral_tendsto

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.integral_sub_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_sub_window

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.tildeW_designMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tildeW_designMod

end FormalResearch.ModularBootstrap.Upper.Positivity
