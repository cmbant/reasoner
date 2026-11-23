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

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
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

/-- `∫_{-n}^{Φ_{n+1}} W̃^{±(1)}(σ) dσ → C_* V_D`. -/
theorem windowLimit_integral_tendsto (N : ℕ) (hN : 1 ≤ N) (η d : ℝ) :
    Tendsto (fun n : ℕ => ∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (designMod N η d).sigmaFLim (designMod N η d).allSigmaLim (designMod N η d).allEpsLim σ)
      atTop (𝓝 (CStar * windowIntegralVD N η d)) := by
  have hκ := kappaAiry_pos
  have hint : Integrable (fun u : ℝ => (designWindowW N η d (u : ℂ)).re) := (lemma_G_integrable N η d).re
  have hA : Tendsto (fun n : ℕ => -kappaAiry * phiWKB (n + 1)) atTop atBot := by
    have := tendsto_neg_atTop_atBot.comp (phiWKB_succ_tendsto.const_mul_atTop hκ)
    simpa [Function.comp_def, neg_mul] using this
  have hB : Tendsto (fun n : ℕ => kappaAiry * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hκ
  have ht := intervalIntegral_tendsto_integral hint hA hB
  have heq : ∀ n : ℕ, ∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (designMod N η d).sigmaFLim (designMod N η d).allSigmaLim
          (designMod N η d).allEpsLim σ =
      CStar * ∫ u in (-kappaAiry * phiWKB (n + 1))..(kappaAiry * (n : ℝ)),
        (designWindowW N η d (u : ℂ)).re := by
    intro n
    have h1 : ∀ σ : ℝ, tildeW 1 (designMod N η d).sigmaFLim (designMod N η d).allSigmaLim
        (designMod N η d).allEpsLim σ =
        (CStar * kappaAiry) * (fun u : ℝ => (designWindowW N η d (u : ℂ)).re) ((-kappaAiry) * σ) :=
      fun σ => tildeW_designMod N hN η d σ
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u : ℝ => (designWindowW N η d (u : ℂ)).re)
        (neg_ne_zero.mpr hκ.ne')]
    have e1 : (-kappaAiry) * (-(n : ℝ)) = kappaAiry * n := by ring
    rw [e1, smul_eq_mul, intervalIntegral.integral_symm (kappaAiry * (n : ℝ))]
    field_simp
  unfold windowIntegralVD
  simp_rw [heq]
  exact ht.const_mul CStar

/-! ### Axiom checks -/

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
