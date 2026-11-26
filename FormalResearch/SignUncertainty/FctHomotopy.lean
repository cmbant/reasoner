/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCfuTheta

/-!
# The homotopy ODE of the compensated cubic chart (F2a, `fct:comp-cfu`)

Abstract algebra of the chart identity `ψ(p,z) = A(p) D(p,z) - z D(p,z)³/3` (`ψ = ℓ - κz + r`): along a parameter direction `v`
with `∂_v ψ = e z⁵ θ(p,z)`, the chart `V = 1/D(p, Z(p,Y))` (`Z D(p,Z)² = Y`, `A = d² B`, `d = D(p,B)`) satisfies the pointwise
homotopy ODE `(A - Y) ∂_v V = e U' (F_v(A) - F_v(Y))`, `U' = V + 2 Y ∂_Y V`, `F_v(Y) = Y⁵ V(Y)^{11} θ(p, Y V(Y)²)`
(paper `(fct:cfu-ode)` in the variable `Y`), including the envelope identity `∂_v A = e F_v(A)`.

Class: proved, no hypotheses beyond those stated (`ode_pointwise`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section Ode
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma ode_L1 {Ω : Set P} (hΩ : IsOpen Ω) {ψ D : P × ℝ → ℝ} {A : P → ℝ} (v : P) {θ : P × ℝ → ℝ} {e : ℝ}
    (hψ : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, fderiv ℝ ψ q (v, 0) = e * q.2 ^ 5 * θ q)
    (hD : DifferentiableOn ℝ D (Ω ×ˢ Ioo (-1 : ℝ) 6)) (hA : DifferentiableOn ℝ A Ω)
    (hid : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, ψ q = A q.1 * D q - q.2 * D q ^ 3 / 3)
    {q : P × ℝ} (hq : q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6) :
    e * q.2 ^ 5 * θ q = fderiv ℝ A q.1 v * D q + (A q.1 - q.2 * D q ^ 2) * fderiv ℝ D q (v, 0) := by
  have hO : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hDa : HasFDerivAt D (fderiv ℝ D q) q := (hD.differentiableAt (hO.mem_nhds hq)).hasFDerivAt
  have hAa : HasFDerivAt A (fderiv ℝ A q.1) q.1 := (hA.differentiableAt (hΩ.mem_nhds hq.1)).hasFDerivAt
  have hG := ((hAa.comp q hasFDerivAt_fst).mul hDa).sub
    ((hasFDerivAt_snd.mul (hDa.pow 3)).const_mul (1 / 3 : ℝ))
  have heq : ψ =ᶠ[𝓝 q] fun q => A q.1 * D q - (1 / 3 : ℝ) * (q.2 * D q ^ 3) :=
    Filter.eventually_of_mem (hO.mem_nhds hq) fun x hx => by rw [hid x hx]; ring
  rw [← hψ q hq, heq.fderiv_eq]
  have hG' : HasFDerivAt (fun q : P × ℝ => A q.1 * D q - (1 / 3 : ℝ) * (q.2 * D q ^ 3)) _ q := hG
  rw [hG'.fderiv]
  simp
  ring
lemma fderiv_split (L : P × ℝ →L[ℝ] ℝ) (a : P) (s : ℝ) : L (a, s) = L (a, 0) + s * L (0, 1) := by
  have : ((a, s) : P × ℝ) = (a, 0) + s • ((0 : P), (1 : ℝ)) := by simp
  rw [this, map_add, map_smul]; simp

/-- Differentiating `Z D(·,Z)² = Y` and `V = D(·,Z)⁻¹` along `w`. -/
lemma ode_L3 {Ω : Set P} (hΩ : IsOpen Ω) {Yi : Set ℝ} (hYi : IsOpen Yi) {D : P × ℝ → ℝ} {V Z : P × ℝ → ℝ}
    (hD : DifferentiableOn ℝ D (Ω ×ˢ Ioo (-1 : ℝ) 6)) (hZd : DifferentiableOn ℝ Z (Ω ×ˢ Yi))
    (hZm : ∀ y ∈ Ω ×ˢ Yi, Z y ∈ Ioo (-1 : ℝ) 6) (hZD : ∀ y ∈ Ω ×ˢ Yi, Z y * D (y.1, Z y) ^ 2 = y.2)
    (hV : ∀ y ∈ Ω ×ˢ Yi, V y = (D (y.1, Z y))⁻¹) (hD0 : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, D q ≠ 0)
    {y : P × ℝ} (hy : y ∈ Ω ×ˢ Yi) (w : P × ℝ) :
    fderiv ℝ Z y w * (D (y.1, Z y) ^ 2 + 2 * Z y * D (y.1, Z y) * fderiv ℝ D (y.1, Z y) (0, 1)) +
        2 * Z y * D (y.1, Z y) * fderiv ℝ D (y.1, Z y) (w.1, 0) = w.2 ∧
    fderiv ℝ V y w = -(D (y.1, Z y))⁻¹ ^ 2 * (fderiv ℝ D (y.1, Z y) (w.1, 0) +
        fderiv ℝ Z y w * fderiv ℝ D (y.1, Z y) (0, 1)) := by
  have hO' : IsOpen (Ω ×ˢ Yi) := hΩ.prod hYi
  have hO : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hq0 : (y.1, Z y) ∈ Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hy.1, hZm y hy⟩
  have hDa : HasFDerivAt D (fderiv ℝ D (y.1, Z y)) (y.1, Z y) :=
    (hD.differentiableAt (hO.mem_nhds hq0)).hasFDerivAt
  have hZa : HasFDerivAt Z (fderiv ℝ Z y) y := (hZd.differentiableAt (hO'.mem_nhds hy)).hasFDerivAt
  have hc : HasFDerivAt (fun y : P × ℝ => (y.1, Z y)) ((ContinuousLinearMap.fst ℝ P ℝ).prod (fderiv ℝ Z y)) y :=
    hasFDerivAt_fst.prodMk hZa
  have hDc : HasFDerivAt (fun y : P × ℝ => D (y.1, Z y))
      ((fderiv ℝ D (y.1, Z y)).comp ((ContinuousLinearMap.fst ℝ P ℝ).prod (fderiv ℝ Z y))) y :=
    hDa.comp y hc
  have hDcw : ∀ w : P × ℝ, ((fderiv ℝ D (y.1, Z y)).comp ((ContinuousLinearMap.fst ℝ P ℝ).prod (fderiv ℝ Z y))) w =
      fderiv ℝ D (y.1, Z y) (w.1, 0) + fderiv ℝ Z y w * fderiv ℝ D (y.1, Z y) (0, 1) := fun w => by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
    exact fderiv_split _ _ _
  constructor
  · have h1 : HasFDerivAt (fun y : P × ℝ => Z y * D (y.1, Z y) ^ 2) _ y := hZa.mul (hDc.pow 2)
    have heq : (fun y : P × ℝ => y.2) =ᶠ[𝓝 y] fun y => Z y * D (y.1, Z y) ^ 2 :=
      Filter.eventually_of_mem (hO'.mem_nhds hy) fun x hx => (hZD x hx).symm
    have h3 := h1.congr_of_eventuallyEq heq
    have h4 := h3.unique hasFDerivAt_snd
    have := congrArg (fun L => L w) h4
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, ContinuousLinearMap.coe_snd', add_apply, smul_apply] at this
    rw [fderiv_split (fderiv ℝ D (y.1, Z y)) w.1 (fderiv ℝ Z y w)] at this
    simp only [nsmul_eq_mul] at this
    rw [← this]; push_cast; ring
  · have h1 := (hasDerivAt_inv (hD0 _ hq0)).comp_hasFDerivAt y hDc
    have heq : V =ᶠ[𝓝 y] fun y => (D (y.1, Z y))⁻¹ :=
      Filter.eventually_of_mem (hO'.mem_nhds hy) hV
    have h2 := (h1.congr_of_eventuallyEq heq).fderiv
    rw [h2]
    simp [hDcw]

/-- `z ↦ z D(p,z)²` is injective on `(-1,6)` when its derivative is positive. -/
lemma ode_L5 {Ω : Set P} (hΩ : IsOpen Ω) {D : P × ℝ → ℝ}
    (hD : DifferentiableOn ℝ D (Ω ×ˢ Ioo (-1 : ℝ) 6))
    (hYz : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, 0 < D q ^ 2 + 2 * q.2 * D q * fderiv ℝ D q (0, 1))
    {p : P} (hp : p ∈ Ω) {z1 z2 : ℝ} (h1 : z1 ∈ Ioo (-1 : ℝ) 6) (h2 : z2 ∈ Ioo (-1 : ℝ) 6)
    (h : z1 * D (p, z1) ^ 2 = z2 * D (p, z2) ^ 2) : z1 = z2 := by
  have hO : IsOpen (Ω ×ˢ Ioo (-1 : ℝ) 6) := hΩ.prod isOpen_Ioo
  have hder : ∀ z ∈ Ioo (-1 : ℝ) 6, HasDerivAt (fun s => s * D (p, s) ^ 2)
      (D (p, z) ^ 2 + 2 * z * D (p, z) * fderiv ℝ D (p, z) (0, 1)) z := fun z hz => by
    have hdl := hasDerivAt_line (F := D) (y := p) (t := z) (hD.differentiableAt (hO.mem_nhds ⟨hp, hz⟩))
    have h : HasDerivAt (fun s : ℝ => s * D (p, s) ^ 2) _ z := (hasDerivAt_id z).mul (hdl.pow 2)
    refine h.congr_deriv ?_
    simp; ring
  have hsm : StrictMonoOn (fun s => s * D (p, s) ^ 2) (Ioo (-1 : ℝ) 6) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact fun z hz => (hder z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ioo] at hz
      rw [(hder z hz).deriv]
      exact hYz (p, z) ⟨hp, hz⟩
  exact hsm.injOn h1 h2 h

/-- Pointwise homotopy ODE `(A - Y) ∂_v V = e U' (F_v(A) - F_v(Y))`. -/
theorem ode_pointwise {Ω : Set P} (hΩ : IsOpen Ω) {Yi : Set ℝ} (hYi : IsOpen Yi)
    {ψ D V Z θ : P × ℝ → ℝ} {A B d : P → ℝ} (v : P) {e : ℝ}
    (hψ : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, fderiv ℝ ψ q (v, 0) = e * q.2 ^ 5 * θ q)
    (hD : DifferentiableOn ℝ D (Ω ×ˢ Ioo (-1 : ℝ) 6)) (hA : DifferentiableOn ℝ A Ω)
    (hid : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, ψ q = A q.1 * D q - q.2 * D q ^ 3 / 3)
    (hZd : DifferentiableOn ℝ Z (Ω ×ˢ Yi))
    (hZm : ∀ y ∈ Ω ×ˢ Yi, Z y ∈ Ioo (-1 : ℝ) 6) (hZD : ∀ y ∈ Ω ×ˢ Yi, Z y * D (y.1, Z y) ^ 2 = y.2)
    (hV : ∀ y ∈ Ω ×ˢ Yi, V y = (D (y.1, Z y))⁻¹) (hDpos : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, 0 < D q)
    (hYz : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, 0 < D q ^ 2 + 2 * q.2 * D q * fderiv ℝ D q (0, 1))
    (hB : ∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6 ∧ D (p, B p) = d p ∧ A p = d p ^ 2 * B p)
    {y : P × ℝ} (hy : y ∈ Ω ×ˢ Yi) (hAY : A y.1 ∈ Yi) :
    (A y.1 - y.2) * fderiv ℝ V y (v, 0) =
      e * (V y + 2 * y.2 * fderiv ℝ V y (0, 1)) *
        ((A y.1) ^ 5 * V (y.1, A y.1) ^ 11 * θ (y.1, A y.1 * V (y.1, A y.1) ^ 2) -
          y.2 ^ 5 * V y ^ 11 * θ (y.1, y.2 * V y ^ 2)) := by
  have hD0 : ∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, D q ≠ 0 := fun q hq => (hDpos q hq).ne'
  obtain ⟨hL3a, hL3b⟩ := ode_L3 hΩ hYi hD hZd hZm hZD hV hD0 hy (v, 0)
  obtain ⟨hL3a', hL3b'⟩ := ode_L3 hΩ hYi hD hZd hZm hZD hV hD0 hy (0, 1)
  have hq0 : (y.1, Z y) ∈ Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hy.1, hZm y hy⟩
  have hL1 := ode_L1 hΩ v hψ hD hA hid hq0
  have hpB := hB y.1 hy.1
  have hqB : (y.1, B y.1) ∈ Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hy.1, hpB.1⟩
  have hL1B := ode_L1 hΩ v hψ hD hA hid hqB
  have hyA : (y.1, A y.1) ∈ Ω ×ˢ Yi := ⟨hy.1, hAY⟩
  have hZA : Z (y.1, A y.1) = B y.1 := by
    refine ode_L5 hΩ hD hYz hy.1 (hZm _ hyA) hpB.1 ?_
    rw [hZD _ hyA]; simp only
    rw [hpB.2.1, hpB.2.2]; ring
  have hVA : V (y.1, A y.1) = (d y.1)⁻¹ := by
    rw [hV _ hyA]; simp only; rw [hZA, hpB.2.1]
  have hAB : A y.1 * (d y.1)⁻¹ ^ 2 = B y.1 := by
    have : d y.1 ≠ 0 := by rw [← hpB.2.1]; exact hD0 _ hqB
    rw [hpB.2.2]; field_simp
  have hDne : D (y.1, Z y) ≠ 0 := hD0 _ hq0
  have hYe : y.2 = Z y * D (y.1, Z y) ^ 2 := (hZD y hy).symm
  have hVy := hV y hy
  have hYV : y.2 * V y ^ 2 = Z y := by rw [hVy, hYe]; field_simp
  have hŶ := hYz _ hq0
  have hdne : d y.1 ≠ 0 := by rw [← hpB.2.1]; exact hD0 _ hqB
  have hDB : D (y.1, B y.1) = d y.1 := hpB.2.1
  rw [hVA, hAB, hYV]
  dsimp only at hL3a hL3b hL3a' hL3b' hL1 hL1B
  rw [hDB] at hL1B
  have hAeq : A y.1 = d y.1 ^ 2 * B y.1 := hpB.2.2
  have e1 : e * (B y.1 ^ 5 * θ (y.1, B y.1)) = fderiv ℝ A y.1 v * d y.1 := by
    have := hL1B
    rw [hAeq] at this; nlinarith [this]
  rw [Prod.mk_zero_zero, map_zero] at hL3a' hL3b'
  -- abbreviations
  set Dd := D (y.1, Z y) with hDd
  set z := Z y with hz
  set Dv := fderiv ℝ D (y.1, Z y) (v, 0) with hDv
  set Dz := fderiv ℝ D (y.1, Z y) (0, 1) with hDz
  set Zv := fderiv ℝ Z y (v, 0) with hZv
  set ZY := fderiv ℝ Z y (0, 1) with hZY
  set Av := fderiv ℝ A y.1 v with hAv
  set Ŷ := Dd ^ 2 + 2 * z * Dd * Dz with hŶdef
  have hZvv : Zv * Ŷ = -(2 * z * Dd * Dv) := by
    simp only [hŶdef]; linarith
  have hZYv : ZY * Ŷ = 1 := by
    simp only [hŶdef]; linarith
  have hŶne : Ŷ ≠ 0 := hŶ.ne'
  have hVv : fderiv ℝ V y (v, 0) = -Dv / Ŷ := by
    rw [hL3b]
    have : Zv = -(2 * z * Dd * Dv) / Ŷ := eq_div_of_mul_eq hŶne hZvv
    rw [this]; field_simp; simp only [hŶdef]; ring
  have hVY : fderiv ℝ V y (0, 1) = -Dz / (Dd ^ 2 * Ŷ) := by
    rw [hL3b']
    have : ZY = 1 / Ŷ := eq_div_of_mul_eq hŶne hZYv
    rw [this]; field_simp; ring
  rw [hVv, hVY, hVy, hYe]
  have e2 : e * (z ^ 5 * θ (y.1, z)) = Av * Dd + (A y.1 - z * Dd ^ 2) * Dv := by
    simpa [mul_assoc] using hL1
  have hθ1 : e * (A y.1 ^ 5 * (d y.1)⁻¹ ^ 11 * θ (y.1, B y.1)) = Av := by
    rw [hAeq]
    have : e * ((d y.1 ^ 2 * B y.1) ^ 5 * (d y.1)⁻¹ ^ 11 * θ (y.1, B y.1)) =
        (e * (B y.1 ^ 5 * θ (y.1, B y.1))) / d y.1 := by field_simp
    rw [this, e1]; field_simp
  have hθ2 : e * ((z * Dd ^ 2) ^ 5 * Dd⁻¹ ^ 11 * θ (y.1, z)) =
      (Av * Dd + (A y.1 - z * Dd ^ 2) * Dv) / Dd := by
    rw [← e2]; field_simp
  have hsplit : e * (Dd⁻¹ + 2 * (z * Dd ^ 2) * (-Dz / (Dd ^ 2 * Ŷ))) *
      (A y.1 ^ 5 * (d y.1)⁻¹ ^ 11 * θ (y.1, B y.1) - (z * Dd ^ 2) ^ 5 * Dd⁻¹ ^ 11 * θ (y.1, z)) =
      (Dd⁻¹ + 2 * (z * Dd ^ 2) * (-Dz / (Dd ^ 2 * Ŷ))) *
      (e * (A y.1 ^ 5 * (d y.1)⁻¹ ^ 11 * θ (y.1, B y.1)) - e * ((z * Dd ^ 2) ^ 5 * Dd⁻¹ ^ 11 * θ (y.1, z))) := by
    ring
  rw [hsplit, hθ1, hθ2]
  field_simp
  simp only [hŶdef]
  ring

/-- info: 'FormalResearch.SignUncertainty.ode_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ode_pointwise

end Ode
end FormalResearch.SignUncertainty
