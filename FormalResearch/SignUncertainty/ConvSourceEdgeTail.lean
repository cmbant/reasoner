module

public import FormalResearch.SignUncertainty.ConvSourceEdgeTrace
public import FormalResearch.SignUncertainty.ConvSourceEdgeLap
public import FormalResearch.SignUncertainty.ConvSourceTail

/-!
# The logarithmic tails of `I_main`, `I_dual` and `ConvTailData` for the convolution source (M6, `ceo:O11ak`, `ceo:conv` (7), `GT.2b`)

`exists_hankelEigenfn_lift_general` (`MellinLiftGeneral`) takes the tail structure `ConvTailData S δ₀ m c` as an input:
`‖I_main[S](ξ)‖, ‖I_dual[S](ξ)‖ ≤ C ξ⁻¹ (log π²ξ)^{-3/2}` for large `ξ`.  This module proves it for the convolution source `S_c` of `ceo:conv`
from `edge_integral_tail` (the oscillatory edge integral of `K₀` against an edge trace with `StripEdge0 α`, `α = 1/2`):

* `edge_tail_of_trace`: for `c ≥ 8` and an `EdgeTrace V` (`ConvSourceEdgeTrace`), `(2πξ)⁻¹ ∫ K₀(iεv, ξ) V(v) dv = O(ξ⁻¹ (log π²ξ)^{-3/2})`
  (substitution `τ = εv`, `StripEdge0 (1/2)` of `τ ↦ V(τ/ε)`, `edge_integral_tail`);
* `iDual_tail_of_hasU2`: **the dual tail for every seed with `HasU2`**, every `δ₀ ≥ 0`, every `m`, `c ≥ 8` (the reflected edge `ζ = 1` is interior);
* `iMain_tail_of_gt1`: the main tail for every seed whose symbol has the `GT.1` bounds (`Gt1Bounds`);
* `convTailData_of_gt1`, `convTailData_airySeedU2` (every one-level seed, `m ≥ 3`, `δ₀ ∈ [0,2]`, `c ≥ 8`; replaces `convTailData_of_oneLevel` and `iMain_add_iDual_tail`
  for the separate tails) and **`convTailData_convSource`** (`ConvTailData` for `S_c`, the `tail` field of `CeSourceFamily`).

Class: proved (no hypothesis structure), from `gt1BasisInput` (`GT.1` for `g_1`), `lapBounds_convWc` (`(ceo:conv.5)` on the boundary) and `edge_integral_tail`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma liftEps_le_half {c : ℝ} (hc : 8 ≤ c) : liftEps c ≤ 1 / 2 := by
  have hc0 : 0 < c := by linarith
  have h := liftEps_cube_mul hc0
  by_contra hlt
  rw [not_le] at hlt
  have h3 : (1 / 2 : ℝ) ^ 3 < liftEps c ^ 3 := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  nlinarith

lemma liftEps_mul_le_half {K c : ℝ} (hc : 8 ≤ c) (hcK : 8 * K ^ 3 ≤ c) : K * liftEps c ≤ 1 / 2 := by
  have hc0 : 0 < c := by linarith
  have h := liftEps_cube_mul hc0
  have hε := liftEps_pos hc0
  by_contra hlt
  rw [not_le] at hlt
  have h3 : (1 / 2 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  have : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [h, mul_one]
  nlinarith

/-- **The logarithmic tail of an edge integral against an `EdgeTrace`**: for `c ≥ 8`,
`‖(2πξ)⁻¹ ∫ K₀(iεv, ξ) V(v) dv‖ ≤ C ξ⁻¹ (log π²ξ)^{-3/2}` for `ξ ≥ ξ₀`, `ε = c^{-1/3}`. -/
theorem edge_tail_of_trace {c : ℝ} (hc : 8 ≤ c) {V : ℝ → ℂ} (hV : EdgeTrace V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, mellinK0 c (((liftEps c * v : ℝ) : ℂ) * Complex.I) ξ * V v‖ ≤
        C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hε0 := liftEps_pos hc0
  have hεhalf := liftEps_le_half hc
  set ε : ℝ := liftEps c with hεdef
  have hE := stripEdge0_of_edgeTrace hV hε0 hεhalf
  have hstrip : stripEdge0 (fun ζ : ℂ => V (ε⁻¹ * ζ.im)) = fun τ : ℝ => V (ε⁻¹ * τ) := by
    funext τ; simp [stripEdge0]
  have hcont : Continuous (stripEdge0 (fun ζ : ℂ => V (ε⁻¹ * ζ.im))) := by
    rw [hstrip]; exact hV.cont.comp (continuous_const.mul continuous_id)
  obtain ⟨C0, hC0, hC⟩ := edge_integral_tail (c := c) (α := 1 / 2) (by linarith) (by norm_num) (by norm_num) hcont hE
  refine ⟨C0 * ε⁻¹ / (2 * Real.pi), by positivity, Real.exp 4 / Real.pi ^ 2, by positivity, fun ξ hξ => ?_⟩
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
  have hexp4 : Real.exp 4 ≤ Real.pi ^ 2 * ξ := by
    rw [div_le_iff₀ hπ] at hξ; linarith
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ) with hL
  have hL4 : 4 ≤ L := (Real.le_log_iff_exp_le (by positivity)).mpr hexp4
  have hexpL : Real.exp L / Real.pi ^ 2 = ξ := by
    rw [hL, Real.exp_log (by positivity)]; field_simp
  have hint := hC L hL4
  rw [hexpL] at hint
  -- the substitution `τ = ε v`
  have hsub := Measure.integral_comp_mul_left
    (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * V (ε⁻¹ * τ)) ε
  have hlhs : ∀ v : ℝ, mellinK0 c (((ε * v : ℝ) : ℂ) * Complex.I) ξ * V (ε⁻¹ * (ε * v)) =
      mellinK0 c (((ε * v : ℝ) : ℂ) * Complex.I) ξ * V v := fun v => by
    rw [inv_mul_cancel_left₀ hε0.ne']
  simp_rw [hlhs] at hsub
  have hrhs : (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * V (ε⁻¹ * τ)) =
      ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * (fun ζ : ℂ => V (ε⁻¹ * ζ.im)) ((τ : ℂ) * Complex.I) := by
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp
  rw [hrhs] at hsub
  rw [hsub]
  have hnorm : ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (|ε⁻¹| • ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      (fun ζ : ℂ => V (ε⁻¹ * ζ.im)) ((τ : ℂ) * Complex.I))‖ ≤
      (2 * Real.pi * ξ)⁻¹ * ε⁻¹ * (C0 * L ^ (-(1 + 1 / 2 : ℝ))) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi * ξ), abs_of_pos (inv_pos.mpr hε0)]
    have := mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ (2 * Real.pi * ξ)⁻¹ * ε⁻¹)
    calc (2 * Real.pi * ξ)⁻¹ * (ε⁻¹ * ‖∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          (fun ζ : ℂ => V (ε⁻¹ * ζ.im)) ((τ : ℂ) * Complex.I)‖)
        = (2 * Real.pi * ξ)⁻¹ * ε⁻¹ * ‖∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          (fun ζ : ℂ => V (ε⁻¹ * ζ.im)) ((τ : ℂ) * Complex.I)‖ := by ring
      _ ≤ _ := this
  refine hnorm.trans (le_of_eq ?_)
  have e : -(1 + 1 / 2 : ℝ) = -(3 / 2 : ℝ) := by norm_num
  rw [e]
  field_simp

/-- **The dual tail of every `U.2` seed**: for `HasU2 X`, `δ₀ ≥ 0`, any `m` and `c ≥ 8`,
`‖I_dual[X](ξ)‖ ≤ C ξ⁻¹ (log π²ξ)^{-3/2}` for large `ξ` (`GT.2b`; the reflected edge `ζ = 1` is interior to the strip, so only holomorphy and the `U.2` bound are used). -/
theorem iDual_tail_of_hasU2 {X : ℝ → ℝ} (hX : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c : ℝ} (hc : 8 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iDual X δ₀ m c ξ‖ ≤ C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) :=
  edge_tail_of_trace hc (edgeTrace_dual hX hδ m (by linarith))

/-- **The main tail of every seed with the `GT.1` bounds**: `Gt1Bounds A (liftW X δ₀ m)` and `c ≥ 8` give `‖I_main[X](ξ)‖ ≤ C ξ⁻¹ (log π²ξ)^{-3/2}`. -/
theorem iMain_tail_of_gt1 {X : ℝ → ℝ} {δ₀ : ℝ} {m : ℕ} {A c : ℝ} (hG : Gt1Bounds A (liftW X δ₀ m)) (hc : 8 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iMain X δ₀ m c ξ‖ ≤ C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) :=
  edge_tail_of_trace hc (EdgeTrace.of_gt1 hG)

/-- `ConvTailData` from the `GT.1` bounds of the symbol (and `HasU2`): `δ₀ ≥ 0`, `c ≥ 8`. -/
theorem convTailData_of_gt1 {X : ℝ → ℝ} (hX : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) {m : ℕ} {A c : ℝ}
    (hG : Gt1Bounds A (liftW X δ₀ m)) (hc : 8 ≤ c) : ConvTailData X δ₀ m c :=
  ⟨hX, iMain_tail_of_gt1 hG hc, iDual_tail_of_hasU2 hX hδ m hc⟩

/-- **`ConvTailData` for every one-level seed** `a f₁ + b g₁ + c₀ g₁'`: spline order `m ≥ 3`, width `δ₀ ∈ [0, 2]`, `c ≥ 8`.  The main and dual tails are proved
separately (this replaces the use of `iMain_add_iDual_tail` and its restriction `c ≥ 2000`, `8K³ ≤ c` for the tails of `iMain`, `iDual`). -/
theorem convTailData_airySeedU2 {m : ℕ} (hm : 3 ≤ m) (a b c₀ : ℝ) {δ₀ : ℝ} (hδ : δ₀ ∈ Icc (0 : ℝ) 2) {c : ℝ} (hc : 8 ≤ c) :
    ConvTailData (airySeedU2 a b c₀) δ₀ m c := by
  obtain ⟨A, hA, hb⟩ := gt1Bounds_airySeedU2 (gt1BasisInput m hm)
  exact convTailData_of_gt1 (hasU2_airySeedU2 a b c₀) hδ.1 (hb a b c₀ δ₀ hδ) hc

/-- **`ConvTailData` for the convolution source `S_c`** (`ceo:conv`, `p ∈ (1/2, 1)`, `h > 0`, arbitrary `γ ε`, `θ`): at spline order `m = 4`, width `δ₀ = β₁ K ε_c / 2`
and `c ≥ 2000`, `8K³ ≤ c`, `K ≥ 1` (the range of `CeSourceFamily.tail`), `ε_c = c^{-1/3}`.  Both tails are `O(ξ⁻¹ (log π²ξ)^{-3/2})` (the constants depend on all parameters). -/
theorem convTailData_convSource {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) {K c : ℝ} (hK : 1 ≤ K)
    (hc : 2000 ≤ c) (hcK : 8 * K ^ 3 ≤ c) :
    ConvTailData (convSource p γ θ ε h) (ceBeta1 * K * liftEps c / 2) 4 c := by
  have hc0 : 0 < c := by linarith
  have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hδ2 : ceBeta1 * K * liftEps c / 2 ≤ 2 := by
    have h1 := liftEps_mul_le_half (by linarith) hcK
    have h2 := ceBeta1_lt_eight
    have h3 := ceBeta1_pos
    have : ceBeta1 * (K * liftEps c) ≤ 8 * (1 / 2) := by
      calc ceBeta1 * (K * liftEps c) ≤ 8 * (K * liftEps c) := by
            gcongr; exact (mul_nonneg (by linarith) (liftEps_pos hc0).le)
        _ ≤ 8 * (1 / 2) := by gcongr
    linarith [mul_assoc ceBeta1 K (liftEps c)]
  obtain ⟨A, hA, hb⟩ := gt1Bounds_convSource (p := p) (γ := γ) (θ := θ) (ε := ε) hp hp1 (m := 4) (by norm_num)
  exact convTailData_of_gt1 (hasU2_convSource hp hp1 hh) hδ0 (hb h hh _ ⟨hδ0, hδ2⟩) (by linarith)

/-- The `tail` field of `CeSourceFamily` for the convolution-source family `c ↦ S_c = convSource p γ θ (c^{-1/3}) (λ c^{-2/3})` (`h = λ ε²`, `λ > 0`). -/
theorem ceSourceFamily_tail_convSource {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hlam : 0 < lam) :
    ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c →
      ConvTailData ((fun c u => convSource p γ θ (liftEps c) (lam * liftEps c ^ 2) u) c) (ceBeta1 * K * liftEps c / 2) 4 c := by
  intro K c hK hc hcK
  have hc0 : 0 < c := by linarith
  have := liftEps_pos hc0
  exact convTailData_convSource hp hp1 (by positivity) hK hc hcK

/-- info: 'FormalResearch.SignUncertainty.edge_tail_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_tail_of_trace

/-- info: 'FormalResearch.SignUncertainty.iDual_tail_of_hasU2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iDual_tail_of_hasU2

/-- info: 'FormalResearch.SignUncertainty.iMain_tail_of_gt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iMain_tail_of_gt1

/-- info: 'FormalResearch.SignUncertainty.convTailData_airySeedU2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convTailData_airySeedU2

/-- info: 'FormalResearch.SignUncertainty.convTailData_convSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convTailData_convSource

/-- info: 'FormalResearch.SignUncertainty.ceSourceFamily_tail_convSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceSourceFamily_tail_convSource

end FormalResearch.SignUncertainty
