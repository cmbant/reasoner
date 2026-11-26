module

public import FormalResearch.SignUncertainty.UctSeedEdgeAsm
public import FormalResearch.SignUncertainty.UctSeedWHolder
public import FormalResearch.SignUncertainty.StripAdmissTail

/-!
# `W^seed` satisfies `StripAdmissFullData (1/2)` (hypotheses (M1)-(M3) of `uct:admiss`) (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, `(uct:Wseed-def)`, "verifies hypotheses (M1)-(M3)".  **Proved.**

* `seedY`, `env2_seedY`: the smooth factor `Y(τ) = T(a)⁻¹ Z_ε(iτ) e^{-h(iτ)} T(a(1-iτ))` of the edge trace, with `Env2`
  envelope `C(1+|τ|)^{10}e^{-π|τ|}`;
* `stripEdge0_seedW`: `W^seed(iτ) = Y(τ) v(aτ)` with `v(q) = T(iq)` (`UctSeedEdgeV`);
* `seedW_stripEdge0`: (M3) at the left edge with `α = 1/2` (`edge_prod_near`, `edge_prod_far`);
* `seedW_stripEdge1`: (M3) at the right edge by parity `W(1-ζ) = ε W(ζ)`;
* `seedW_stripAdmissFull`: `StripAdmissFullData (1/2) (seedW ε δ c)` for `ε = ±1`, `0 ≤ δ ≤ 1`, `0 < c`.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

/-- The smooth part of the edge trace: `Y(τ) = T(a)⁻¹ Z_ε(iτ) e^{-h(iτ)} T(a(1-iτ))`. -/
noncomputable def seedY (ε δ c : ℝ) (τ : ℝ) : ℂ :=
  (seedT δ (seedScale c : ℂ))⁻¹ *
    (uctSeedZ ε (0 + Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ))) *
      seedT δ ((seedScale c : ℂ) * (1 - (0 + Complex.I * (τ : ℂ)))))

theorem env2_seedY (ε δ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ CY : ℝ, Env2 (seedY ε δ c) (fun τ => CY * ((1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)))) := by
  obtain ⟨CZ, hCZ0, hZ⟩ := env2_seedZi ε
  obtain ⟨aE, haE0, hE⟩ := env2_outerE
  obtain ⟨B, hB0, hT⟩ := env2_seedTi δ c hc
  set κ : ℂ := (seedT δ (seedScale c : ℂ))⁻¹ with hκ
  have h1 := (hZ.mul hE).mul hT
  have h2 := h1.const_mul κ
  refine ⟨4 * ‖κ‖ * (4 * (4 * CZ * aE) * B), h2.mono fun τ => le_of_eq ?_⟩
  have hx : Real.exp (-(π * |τ|)) = Real.exp (-(π * |τ|)) := rfl
  ring

lemma stripEdge0_seedW (ε δ c : ℝ) (τ : ℝ) :
    stripEdge0 (seedW ε δ c) τ = seedY ε δ c τ * seedV δ (seedScale c * τ) := by
  unfold stripEdge0 seedW seedY seedV
  have e1 : ((τ : ℂ) * Complex.I) = 0 + Complex.I * (τ : ℂ) := by ring
  have e2 : (((seedScale c * τ : ℝ) : ℂ) * Complex.I) = (seedScale c : ℂ) * ((τ : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e2, e1]
  ring

theorem seedW_stripEdge0 {ε δ c : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 < c) :
    StripEdge0 (1 / 2 : ℝ) (seedW ε δ c) := by
  have ha := seedScale_pos hc
  obtain ⟨CY, hY⟩ := env2_seedY ε δ hc
  have hfun : stripEdge0 (seedW ε δ c) = fun t : ℝ => seedY ε δ c t * seedV δ (seedScale c * t) :=
    funext (stripEdge0_seedW ε δ c)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact edge_prod_c2 hY ha
  · obtain ⟨C, hC⟩ := edge_prod_near hY hδ0 hδ1 ha
    exact ⟨C, by rw [hfun]; exact hC⟩
  · obtain ⟨C, hC⟩ := edge_prod_far (δ := δ) hY ha
    exact ⟨C, by rw [hfun]; exact hC⟩

lemma StripEdge0.const_mul {α : ℝ} {W : ℂ → ℂ} (h : StripEdge0 α W) (k : ℂ) :
    StripEdge0 α (fun ζ => k * W ζ) := by
  have hf : stripEdge0 (fun ζ => k * W ζ) = fun τ => k * stripEdge0 W τ := rfl
  have hd1 : deriv (stripEdge0 (fun ζ => k * W ζ)) = fun τ => k * deriv (stripEdge0 W) τ := by
    rw [hf]; funext τ; exact deriv_const_mul_field k
  have hd2 : deriv (deriv (stripEdge0 (fun ζ => k * W ζ))) = fun τ => k * deriv (deriv (stripEdge0 W)) τ := by
    rw [hd1]; funext τ; exact deriv_const_mul_field k
  obtain ⟨C1, hC1⟩ := h.near
  obtain ⟨C2, hC2⟩ := h.far
  refine ⟨?_, ⟨‖k‖ * C1, fun τ hτ hτ1 => ?_⟩, ⟨‖k‖ * C2, fun τ hτ => ?_⟩⟩
  · rw [hf]; exact contDiffOn_const.mul h.c2
  · obtain ⟨a1, a2, a3⟩ := hC1 τ hτ hτ1
    rw [hd2, hd1, hf]
    simp only [← mul_sub, norm_mul]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [norm_nonneg k, mul_le_mul_of_nonneg_left a1 (norm_nonneg k),
      mul_le_mul_of_nonneg_left a2 (norm_nonneg k), mul_le_mul_of_nonneg_left a3 (norm_nonneg k)]
  · obtain ⟨a1, a2, a3⟩ := hC2 τ hτ
    rw [hd2, hd1, hf]
    simp only [norm_mul]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [norm_nonneg k, mul_le_mul_of_nonneg_left a1 (norm_nonneg k),
      mul_le_mul_of_nonneg_left a2 (norm_nonneg k), mul_le_mul_of_nonneg_left a3 (norm_nonneg k)]

theorem seedW_stripEdge1 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ c : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 < c) :
    StripEdge1 (1 / 2 : ℝ) (seedW ε δ c) := by
  have h0 := (seedW_stripEdge0 (ε := ε) hδ0 hδ1 hc).const_mul (ε : ℂ)
  unfold StripEdge1
  have hfun : stripEdge0 (fun ζ : ℂ => seedW ε δ c (1 - ζ)) =
      stripEdge0 (fun ζ : ℂ => (ε : ℂ) * seedW ε δ c ζ) := by
    funext τ
    unfold stripEdge0
    have hcl : ((τ : ℂ) * Complex.I) ∈ closedStrip := ⟨by simp, by simp⟩
    exact seedW_oneSub hε δ c hcl
  have hW : StripEdge0 (1 / 2 : ℝ) (fun ζ : ℂ => (ε : ℂ) * seedW ε δ c ζ) := h0
  obtain ⟨a, b, d⟩ := hW
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact a
  · rw [hfun]; exact b
  · rw [hfun]; exact d

/-- **`W^seed` satisfies (M1)-(M3)**: `StripAdmissFullData (1/2) (seedW ε δ c)` for `ε = ±1`, `0 ≤ δ ≤ 1`, `c > 0`. -/
theorem seedW_stripAdmissFull {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ c : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 < c) :
    StripAdmissFullData (1 / 2 : ℝ) (seedW ε δ c) where
  toStripM1 := seedW_stripM1 hc
  holder1 := seedW_holder1 hε hδ0 hδ1 hc
  edge0 := seedW_stripEdge0 hδ0 hδ1 hc
  holder0 := seedW_holder0 hδ0 hδ1 hc
  edge1 := seedW_stripEdge1 hε hδ0 hδ1 hc

/-- info: 'FormalResearch.SignUncertainty.env2_seedY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env2_seedY

/-- info: 'FormalResearch.SignUncertainty.seedW_stripEdge0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedW_stripEdge0

/-- info: 'FormalResearch.SignUncertainty.seedW_stripEdge1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedW_stripEdge1

/-- info: 'FormalResearch.SignUncertainty.seedW_stripAdmissFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedW_stripAdmissFull

end FormalResearch.SignUncertainty
