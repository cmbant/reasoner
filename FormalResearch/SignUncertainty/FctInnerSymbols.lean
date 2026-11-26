/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FormalResearch.Special.AiryBiReal
public import FormalResearch.Special.AiryZeroOrder

/-!
# Lemma `fct:inner-symbols` (FCT.5b): the symbol map `𝒮[·]` and the inner amplitude (statements and named inputs)

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols`.

**Definitions** (exact):
* `FctSymClsOn D n p B κ` (`κ ∈ 𝒮^p(B)` on `D`): `κ : ℝ → ℂ` is `C^n` on `D` with `‖κ^{(r)}(u)‖ ≤ B (1+u)^{p-r}` for `0 ≤ r ≤ n`; `FctSymCls = FctSymClsOn (Ici 0)`
  (the paper's `𝒮^p(B)` is `n = 8`).
* `fctSEps û ε κ = e^{-iπ/4} ∫₀^∞ u^{-1/2} e^{-i(û u + u³/12) - ε u²} κ(u) du`, `FctSLimit û κ L` (`ε ↓ 0` limit exists and is `L`), `fctS û κ = 𝒮[κ]`
  (`limUnder`; meaningful where the limit exists, which (a) asserts).
* `fctG0 û = 2π^{3/2}(Ai(û)² - i Ai(û) Bi(û))`.

**Part (a), split into three named inputs** (none is proved in Lean; the dependency is `fct:edge-ibp`-type integration by parts with the cubic phase):
* `FctInnerSymbolsA`: existence of the Abel limit, the bound `|𝒮[κ]| ≤ C_{M,n,p} B` and the tail bound `C B u_*^{p+1/2-3n}`;
* `FctInnerSymbolsMonomial`: `𝒮[u^k] = i^k ∂_û^k 𝒮[1]` (differentiation of the regularised integrals);
* `FctInnerSymbolsG0`: `𝒮[1] = G_0` (contour rotation to `arg u = -π/6`, the ODE `G_0''' = 4ûG_0' + 2G_0`, uniqueness).
`fctInnerSymbolsA_box` is the "in particular" clause of (a) (`|û - a₁| ≤ 1`, `n = 8`, `p ≤ 21`, tail exponent `p - 47/2`), proved from `FctInnerSymbolsA`.

**Part (b)** (`FctInnerB2Symbol` is a Prop proved in `FctInnerB2` (`fctInnerB2Symbol`); `FctInnerB3`, `FctInnerB4`: named inputs about the inner amplitude family; `(b1)` is proved in `FctInnerCoord`/`FctInnerB1` for an
abstract perturbed phase): (b2) is stated for the concrete objects (`T̃(u) = s V(Y)`, `χ = χ_in(T/τ₁)`; its support, size and plateau clauses are proved in `FctInnerB2`); (b3) and (b4) are stated for an abstract family
`FctInnerFamily` of amplitudes `μ`, `e_A`, `e_B` attached to the admissible pairs `(c, L₁, α)` (the objects `𝔞`, `ω₁`, `ω₂`, `J`, `v₁`, `B_c`, `φ_kill` of the
paper are not yet defined in Lean as functions of `(c, L₁, α)`, so the identity linking `μ` to `𝔞` is part of the instantiation, not of these Props).

Class: definitions; (a), (b3), (b4) are named inputs (open); `fctInnerSymbolsA_box` and the class lemmas are proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### The symbol classes `𝒮^p(B)` -/

/-- `κ ∈ 𝒮^p(B)` on `D` with `n` derivatives: `κ ∈ C^n(D)` and `‖κ^{(r)}(u)‖ ≤ B (1 + u)^{p - r}` for `0 ≤ r ≤ n`, `u ∈ D ⊆ [0, ∞)`
(`fct:inner-symbols`: the paper's `𝒮^p(B)` is `D = [0, ∞)`, `n = 8`; in (b3)-(b4) `D = [0, U_c]`). -/
def FctSymClsOn (D : Set ℝ) (n : ℕ) (p B : ℝ) (κ : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ n κ D ∧ ∀ r : ℕ, r ≤ n → ∀ u ∈ D, ‖iteratedDerivWithin r κ D u‖ ≤ B * (1 + u) ^ (p - r)

/-- `𝒮^p(B)` on `[0, ∞)`. -/
abbrev FctSymCls (n : ℕ) (p B : ℝ) (κ : ℝ → ℂ) : Prop := FctSymClsOn (Ici 0) n p B κ

lemma FctSymClsOn.mono_p {D : Set ℝ} (hD : D ⊆ Ici 0) {n : ℕ} {p p' B : ℝ} {κ : ℝ → ℂ} (h : FctSymClsOn D n p B κ) (hB : 0 ≤ B)
    (hp : p ≤ p') : FctSymClsOn D n p' B κ := by
  refine ⟨h.1, fun r hr u hu => (h.2 r hr u hu).trans ?_⟩
  have hu0 : (0 : ℝ) ≤ u := hD hu
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hB

lemma FctSymClsOn.mono_B {D : Set ℝ} (hD : D ⊆ Ici 0) {n : ℕ} {p B B' : ℝ} {κ : ℝ → ℂ} (h : FctSymClsOn D n p B κ) (hB : B ≤ B') :
    FctSymClsOn D n p B' κ := by
  refine ⟨h.1, fun r hr u hu => (h.2 r hr u hu).trans ?_⟩
  have hu0 : (0 : ℝ) ≤ u := hD hu
  exact mul_le_mul_of_nonneg_right hB (Real.rpow_pos_of_pos (by linarith) _).le

/-! ### The symbol map `𝒮[·]` -/

/-- The regularised integral `e^{-iπ/4} ∫₀^∞ u^{-1/2} e^{-i(û u + u³/12) - ε u²} κ(u) du` of `fct:inner-symbols` (a). -/
noncomputable def fctSEps (û ε : ℝ) (κ : ℝ → ℂ) : ℂ :=
  Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
    ∫ u in Ioi (0 : ℝ), ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * κ u

/-- `L` is the Abel limit `lim_{ε ↓ 0}` of the regularised integrals: `𝒮[κ] = L`. -/
def FctSLimit (û : ℝ) (κ : ℝ → ℂ) (L : ℂ) : Prop :=
  Tendsto (fun ε : ℝ => fctSEps û ε κ) (𝓝[>] (0 : ℝ)) (𝓝 L)

/-- `𝒮[κ]` (the limit when it exists, which `FctInnerSymbolsA` asserts for the symbols considered). -/
noncomputable def fctS (û : ℝ) (κ : ℝ → ℂ) : ℂ := limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => fctSEps û ε κ)

lemma FctSLimit.fctS_eq {û : ℝ} {κ : ℝ → ℂ} {L : ℂ} (h : FctSLimit û κ L) : fctS û κ = L := h.limUnder_eq

/-- `G_0(û) = 2π^{3/2}(Ai(û)² - i Ai(û) Bi(û))` (`fct:inner-symbols` (a)). -/
noncomputable def fctG0 (û : ℝ) : ℂ :=
  ((2 * π ^ (3 / 2 : ℝ) * (FormalResearch.Special.airyAi û) ^ 2 : ℝ) : ℂ) -
    Complex.I * ((2 * π ^ (3 / 2 : ℝ) * (FormalResearch.Special.airyAi û * FormalResearch.Special.airyBi û) : ℝ) : ℂ)

/-- **`fct:inner-symbols` (a), existence and bounds** (named input).  For `M > 0`, `n ≥ 1`, `p < 3n - 1/2` there is `C = C_{M,n,p}` such that for `|û| ≤ M`
and `κ ∈ C^n([0,∞))` with `|κ^{(r)}(u)| ≤ B(1+u)^{p-r}` (`r ≤ n`): the Abel limit exists, `|𝒮[κ]| ≤ C B`, and, if `κ = 0` on `[0, u_*]` with `u_* ≥ U₀ = max(6, √(8M))`,
`|𝒮[κ]| ≤ C B u_*^{p+1/2-3n}`.  (Paper proof: `n` integrations by parts with `𝒟g = -∂_u(g/(iψ'))`, `ψ = -(ûu + u³/12)`, `|ψ'| ≥ u²/8` for `u ≥ U₀`.) -/
def FctInnerSymbolsA : Prop :=
  ∀ (M : ℝ) (n : ℕ) (p : ℝ), 0 < M → 1 ≤ n → p < 3 * n - 1 / 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (û B : ℝ) (κ : ℝ → ℂ), |û| ≤ M → 0 ≤ B → FctSymCls n p B κ →
      (∃ L, FctSLimit û κ L) ∧ ‖fctS û κ‖ ≤ C * B ∧
      ∀ ustar : ℝ, max 6 (√(8 * M)) ≤ ustar → (∀ u ∈ Icc (0 : ℝ) ustar, κ u = 0) →
        ‖fctS û κ‖ ≤ C * B * ustar ^ (p + 1 / 2 - 3 * n)

/-- **`fct:inner-symbols` (a), monomials** (named input): `𝒮[u^k] = i^k ∂_û^k 𝒮[1]` for every `k` and real `û` (differentiation of the regularised
integrals under the Abel limit, `∂_û^k 𝒮[1] = 𝒮[(-iu)^k]`, uniformly on compact `û`-intervals by sufficiently many integrations by parts). -/
def FctInnerSymbolsMonomial : Prop :=
  ∀ (k : ℕ) (û : ℝ), FctSLimit û (fun u => (u : ℂ) ^ k)
    (Complex.I ^ k * iteratedDeriv k (fun w : ℝ => fctS w (fun _ => 1)) û)

/-- **`fct:inner-symbols` (a), closed form** (named input): `𝒮[1] = G_0 = 2π^{3/2}(Ai² - i Ai Bi)` on the real line (rotate the regularised integral to
`arg u = -π/6`; the ODE `y''' = 4ûy' + 2y` by integrating `∂_u(u^{1/2} e^{-i(ûu+u³/12)})`; `Ai²`, `Ai Bi` solve the same equation; the Gamma-integral initial
values at `û = 0` agree, DLMF 9.2.3-9.2.6; uniqueness for the third-order equation, `CtAiry.ode3_eq_zero`). -/
def FctInnerSymbolsG0 : Prop := ∀ û : ℝ, FctSLimit û (fun _ => 1) (fctG0 û)

/-- **The "in particular" clause of `fct:inner-symbols` (a)** (`|û - a₁| ≤ 1`, `n = 8`, `U₀ = 6`, tail exponent `p - 47/2`), from `FctInnerSymbolsA`:
for `p ≤ 21` there is `C` with `|𝒮[κ]| ≤ C B` and, if `κ = 0` on `[0, u_*]`, `u_* ≥ 6`, `|𝒮[κ]| ≤ C B u_*^{p - 47/2}`, for every `κ ∈ 𝒮^p(B)` (`n = 8`) and
`|û - a₁| ≤ 1`, `a₁ = airyZero 1`. -/
theorem fctInnerSymbolsA_box (hA : FctInnerSymbolsA) {p : ℝ} (hp : p ≤ 21) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (û B : ℝ) (κ : ℝ → ℂ), |û - FormalResearch.Special.airyZero 1| ≤ 1 → 0 ≤ B → FctSymCls 8 p B κ →
      (∃ L, FctSLimit û κ L) ∧ ‖fctS û κ‖ ≤ C * B ∧
      ∀ ustar : ℝ, 6 ≤ ustar → (∀ u ∈ Icc (0 : ℝ) ustar, κ u = 0) → ‖fctS û κ‖ ≤ C * B * ustar ^ (p - 47 / 2) := by
  obtain ⟨C, hC0, hC⟩ := hA 3.35 8 p (by norm_num) (by norm_num) (by push_cast; linarith)
  refine ⟨C, hC0, fun û B κ hû hB hκ => ?_⟩
  have ha := FormalResearch.Special.airyZero_one
  have hûM : |û| ≤ 3.35 := by
    have h1 : |û| ≤ |û - FormalResearch.Special.airyZero 1| + |FormalResearch.Special.airyZero 1| := by
      calc |û| = |(û - FormalResearch.Special.airyZero 1) + FormalResearch.Special.airyZero 1| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h2 : |FormalResearch.Special.airyZero 1| ≤ 2.35 := by
      rw [abs_of_neg (by linarith [ha.2])]; linarith [ha.1]
    linarith
  obtain ⟨hex, hb1, hb2⟩ := hC û B κ hûM hB hκ
  refine ⟨hex, hb1, fun ustar hu hz => ?_⟩
  have h8 : √(8 * (3.35 : ℝ)) ≤ 6 := by
    apply Real.sqrt_le_iff.2; constructor <;> norm_num
  have := hb2 ustar (max_le hu (h8.trans hu)) hz
  have e : p + 1 / 2 - 3 * ((8 : ℕ) : ℝ) = p - 47 / 2 := by push_cast; ring
  rwa [e] at this

/-! ### Part (b): the inner amplitude -/

/-- `τ₁ = c^{-1/4}`. -/
noncomputable def fctTau1 (c : ℝ) : ℝ := c ^ (-(1 / 4 : ℝ))

/-- `U_c = 2.96 c^{1/12}`. -/
noncomputable def fctUc (c : ℝ) : ℝ := 2.96 * c ^ ((1 : ℝ) / 12)

/-- `u_* = 2.7 c^{1/12}`. -/
noncomputable def fctUstar (c : ℝ) : ℝ := 2.7 * c ^ ((1 : ℝ) / 12)

/-- `T(u) = T̃(s; L₁) = s V(Y)`, `s = 2^{-2/3} c^{-1/3} u`, `Y = s²/τ₁² = 2^{-4/3} c^{-1/6} u²` (`fct:inner-symbols` (b)). -/
noncomputable def fctInnerT (c : ℝ) (V : ℝ → ℝ) (u : ℝ) : ℝ :=
  ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u) * V ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2)

/-- `χ(u) = χ_in(T/τ₁)`. -/
noncomputable def fctInnerChi (χin : ℝ → ℝ) (c : ℝ) (V : ℝ → ℝ) (u : ℝ) : ℝ := χin (fctInnerT c V u / fctTau1 c)

/-- The even cutoff `χ_in ∈ C_c^∞((-1.98, 1.98))`, `χ_in ≡ 1` on `[-1.85, 1.85]` of the paper (`(2)` of the proof of `fct:splitting`), values in `[0, 1]`. -/
structure FctCutoffIn (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞' χ
  zero : ∀ x, 1.98 ≤ |x| → χ x = 0
  one : ∀ x, |x| ≤ 1.85 → χ x = 1
  mem : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1

/-- `‖V - τ_*‖_{C^{14}([0, 3.6])} ≤ K c^{-1/2}`, `τ_* = (12/π²)^{1/3}` (`fct:comp-cfu`: `V = V_1(·; ℓ₁)`, `Y ∈ [0, 3.6)`; `Y ≤ 2^{-4/3}·9 < 3.6` on `[0, U_c]`). -/
def FctVJets (K c : ℝ) (V : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 14 V (Icc (0 : ℝ) 3.6) ∧ ∀ j : ℕ, j ≤ 14 → ∀ Y ∈ Icc (0 : ℝ) 3.6,
    |iteratedDerivWithin j (fun Y => V Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc (0 : ℝ) 3.6) Y| ≤ K * c ^ (-(1 / 2 : ℝ))

/-- **`fct:inner-symbols` (b2), symbol part** (statement; proved as `fctInnerB2Symbol` in `FctInnerB2`; the paper's Faà di Bruno argument for `χ_in(T/τ₁)` with the symbol bounds of `T/τ₁`,
`|∂_u^r(T/τ₁)| ≤ C c^{-1/12}(1+u)^{1-r}`): for the cutoff `χ_in` and `‖V - τ_*‖_{C^{14}} ≤ K c^{-1/2}`, for `c` large, `χ, 1 - χ ∈ 𝒮⁰(C)` on `[0, U_c]`.
The support, size and plateau statements of (b2) are proved in `FctInnerB2` (`fctInnerB2`). -/
def FctInnerB2Symbol : Prop :=
  ∀ χin : ℝ → ℝ, FctCutoffIn χin → ∀ K : ℝ, 0 ≤ K → ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ V : ℝ → ℝ, FctVJets K c V →
    FctSymClsOn (Icc 0 (fctUc c)) 8 0 C (fun u => ((fctInnerChi χin c V u : ℝ) : ℂ)) ∧
    FctSymClsOn (Icc 0 (fctUc c)) 8 0 C (fun u => ((1 - fctInnerChi χin c V u : ℝ) : ℂ))

/-- **The inner-amplitude family** of Lemma `fct:inner-symbols` (b): for every `c` and admissible `(L₁, α)` (`adm`: the paper's "admissible", `|û - a₁| ≤ c^{-7/6}`,
`|α̃| ≤ c^{-7/6}`) the amplitude `μ(u)` of (b3), the constant `c₂ = 2^{-4/3} V(0)²`, and the error terms `e_A`, `e_B` of (b4).  The paper's objects (`𝔞`, `ω₁`, `ω₂`, `J`, `v₁`,
`B_c`, `φ_kill`, `ϑ^{(1)}`) are not yet functions of `(c, L₁, α)` in Lean, so this is the interface that `(fct:RI-bounds)` consumes; the defining identities
(`𝔞(T) T̃'(s) = (π²/12) √V(0) s^{-1/2} μ(u)`, `c^{2/3} ω₁(T) = c_2^* u² + e_B`, `ω₂(T)/û_L = -iu + e_A`) belong to the instantiation. -/
structure FctInnerFamily where
  adm : ℝ → ℝ → ℝ → Prop
  mu : ℝ → ℝ → ℝ → ℝ → ℂ
  c2 : ℝ → ℝ → ℝ → ℝ
  eA : ℝ → ℝ → ℝ → ℝ → ℂ
  eB : ℝ → ℝ → ℝ → ℝ → ℂ

/-- **`fct:inner-symbols` (b3)** (named input): `δμ = μ - 1 - α̃ c₂ u²` (`α̃ = c^{-2/3} α`) satisfies `|∂_u^r δμ| ≤ C c^{-4/3}(1+u)^{10-r}` on `[0, U_c]`, `0 ≤ r ≤ 8`,
uniformly over admissible pairs. -/
def FctInnerB3 (F : FctInnerFamily) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ L1 α : ℝ, F.adm c L1 α →
    FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C * c ^ (-(4 / 3 : ℝ)))
      (fun u => F.mu c L1 α u - 1 - ((c ^ (-(2 / 3 : ℝ)) * α * F.c2 c L1 α * u ^ 2 : ℝ) : ℂ))

/-- **`fct:inner-symbols` (b4)** (named input): `e_B ∈ 𝒮^{11}(C c^{-1/2})` and `e_A ∈ 𝒮^{3}(C c^{-2/3})` on `[0, U_c]` (`n = 8`), uniformly over admissible pairs. -/
def FctInnerB4 (F : FctInnerFamily) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ L1 α : ℝ, F.adm c L1 α →
    FctSymClsOn (Icc 0 (fctUc c)) 8 11 (C * c ^ (-(1 / 2 : ℝ))) (F.eB c L1 α) ∧
    FctSymClsOn (Icc 0 (fctUc c)) 8 3 (C * c ^ (-(2 / 3 : ℝ))) (F.eA c L1 α)

/-- Step 3 consumption of (a) (`fct:warp-asymp` (1), `(fct:RI-bounds)`): with `u_* = 2.7 c^{1/12}` (`c ≥ 15000` so that `u_* ≥ 6`) a symbol `κ ∈ 𝒮^p(B)` vanishing on
`[0, u_*]`, `p ≤ 21`, has `|𝒮[κ]| ≤ C B c^{(p - 47/2)/12}` (`p = 2, 3, 4`: `c^{-43/24}`, `c^{-41/24}`, `c^{-39/24}`, as in Step 3). -/
theorem fctInnerSymbolsA_tail_c (hA : FctInnerSymbolsA) {p : ℝ} (hp : p ≤ 21) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 15000 ≤ c → ∀ (û B : ℝ) (κ : ℝ → ℂ), |û - FormalResearch.Special.airyZero 1| ≤ 1 → 0 ≤ B →
      FctSymCls 8 p B κ → (∀ u ∈ Icc (0 : ℝ) (fctUstar c), κ u = 0) → ‖fctS û κ‖ ≤ C * B * c ^ ((p - 47 / 2) / 12) := by
  obtain ⟨C, hC0, hC⟩ := fctInnerSymbolsA_box hA hp
  refine ⟨C * 2.7 ^ (p - 47 / 2), mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _), fun c hc û B κ hû hB hκ hz => ?_⟩
  have hc0 : 0 < c := by linarith
  set x : ℝ := c ^ ((1 : ℝ) / 12) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hc0 _
  have hcx : c = x ^ 12 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hx6 : (2.223 : ℝ) ≤ x := by
    by_contra hlt
    push Not at hlt
    have : x ^ 12 < 2.223 ^ 12 := pow_lt_pow_left₀ hlt hxpos.le (by norm_num)
    have h2 : (2.223 : ℝ) ^ 12 < 15000 := by norm_num
    linarith
  have hu6 : 6 ≤ fctUstar c := by unfold fctUstar; rw [← hx]; linarith
  obtain ⟨-, -, hb2⟩ := hC û B κ hû hB hκ
  have := hb2 (fctUstar c) hu6 hz
  refine this.trans ?_
  have e : fctUstar c ^ (p - 47 / 2) = 2.7 ^ (p - 47 / 2) * c ^ ((p - 47 / 2) / 12) := by
    unfold fctUstar
    rw [← hx, Real.mul_rpow (by norm_num) hxpos.le]
    congr 1
    rw [hx, ← Real.rpow_mul hc0.le]; congr 1; ring
  rw [e]
  apply le_of_eq
  ring

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsA_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsA_box

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsA_tail_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsA_tail_c

end FormalResearch.SignUncertainty
