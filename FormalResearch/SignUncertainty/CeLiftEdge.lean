module

public import FormalResearch.SignUncertainty.ConvSourceTail

/-!
# The Cohn--Elkies pair as the two eigenfunction lifts of `D ± S` (M6, steps (2)-(3) of `thm:ce-hb-lift`)

For a one-level seed `D = airySeedU2 a b c₀` (the dual seed `D_c = -F_c`) and a source `S` with `ConvTailData`, the Hankel eigenfunctions
`f₊ = L₊[D + S]`, `f₋ = L₋[D - S]` (`exists_hankelEigenfn_lift_of_convTail`) give the profile `h = (f₊ + f₋)/2` and its Hankel transform
`ĥ = (f₊ - f₋)/2` with the edge representations
`c^{1/3} ρ₀(cξ) h(cξ) = I_main[D] + I_dual[S]` (`= -(I_main[F_c] + I_dual[-S_c])`, `-h = f[F_c, -S_c]`) and
`c^{1/3} ρ₀(cξ) ĥ(cξ) = I_main[S] + I_dual[D]` (`ĥ = f[S_c, D_c]`), and the origin values of `f_±` from the lift symbol.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

theorem iMain_seed_add_smul {D S : ℝ → ℝ} (hD : HasU2 D) (hS : HasU2 S) (τ : ℝ) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ)
    {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) :
    iMain (fun u => D u + τ * S u) δ₀ m c ξ = iMain D δ₀ m c ξ + (τ : ℂ) * iMain S δ₀ m c ξ := by
  rw [iMain_add hD (hS.smul τ) hδ m hc hξ, iMain_const_mul]

theorem iDual_seed_add_smul {D S : ℝ → ℝ} (hD : HasU2 D) (hS : HasU2 S) (τ : ℝ) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ)
    {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) :
    iDual (fun u => D u + τ * S u) δ₀ m c ξ = iDual D δ₀ m c ξ + (τ : ℂ) * iDual S δ₀ m c ξ := by
  rw [iDual_add hD (hS.smul τ) hδ m hc hξ, iDual_const_mul]

/-- **The eigenfunction pair** (see the module docstring). -/
theorem ceLift_pair {m : ℕ} (hm : 3 ≤ m) (a b c₀ : ℝ) {K c : ℝ} (hK : 1 ≤ K) (hc : 2000 ≤ c) (hcK : 8 * K ^ 3 ≤ c)
    {S : ℝ → ℝ} (hS : ConvTailData S (ceBeta1 * K * liftEps c / 2) m c) :
    ∃ fp fm : ℝ → ℝ, IsHankelEigenfn c 1 fp ∧ IsHankelEigenfn c (-1) fm ∧
      (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * ((fp (c * ξ) + fm (c * ξ)) / 2) : ℝ) : ℂ) =
        iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ + iDual S (ceBeta1 * K * liftEps c / 2) m c ξ) ∧
      (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * ((fp (c * ξ) - fm (c * ξ)) / 2) : ℝ) : ℂ) =
        iMain S (ceBeta1 * K * liftEps c / 2) m c ξ + iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ) ∧
      ((fp 0 : ℝ) : ℂ) = liftSymbol (fun u => airySeedU2 a b c₀ u + 1 * S u) (ceBeta1 * K * liftEps c / 2) m
          (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        liftSymbol (fun u => airySeedU2 a b c₀ u + 1 * S u) (ceBeta1 * K * liftEps c / 2) m 0 ∧
      ((fm 0 : ℝ) : ℂ) = liftSymbol (fun u => airySeedU2 a b c₀ u + (-1) * S u) (ceBeta1 * K * liftEps c / 2) m
          (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
        liftSymbol (fun u => airySeedU2 a b c₀ u + (-1) * S u) (ceBeta1 * K * liftEps c / 2) m 0 := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  obtain ⟨fp, hfp, hrp, -, hsp⟩ := exists_hankelEigenfn_lift_of_convTail hm a b c₀ hK hc hcK hS 1 (σ := 1) (Or.inl rfl)
  obtain ⟨fm, hfm, hrm, -, hsm⟩ := exists_hankelEigenfn_lift_of_convTail hm a b c₀ hK hc hcK hS (-1) (σ := -1) (Or.inr rfl)
  have hD := hasU2_airySeedU2 a b c₀
  refine ⟨fp, fm, hfp, hfm, fun ξ hξ => ?_, fun ξ hξ => ?_, ?_, ?_⟩
  · have e1 := hrp ξ hξ
    have e2 := hrm ξ hξ
    rw [iMain_seed_add_smul hD hS.hasU2 _ hδ m hc0 hξ, iDual_seed_add_smul hD hS.hasU2 _ hδ m hc0 hξ] at e1 e2
    push_cast at e1 e2 ⊢
    linear_combination (1 / 2 : ℂ) * e1 + (1 / 2 : ℂ) * e2
  · have e1 := hrp ξ hξ
    have e2 := hrm ξ hξ
    rw [iMain_seed_add_smul hD hS.hasU2 _ hδ m hc0 hξ, iDual_seed_add_smul hD hS.hasU2 _ hδ m hc0 hξ] at e1 e2
    push_cast at e1 e2 ⊢
    linear_combination (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * e2
  · simpa using hsp
  · simpa [sub_eq_add_neg] using hsm

/-- info: 'FormalResearch.SignUncertainty.ceLift_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceLift_pair

end FormalResearch.SignUncertainty
