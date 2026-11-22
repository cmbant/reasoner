module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.InvX0
public import FormalResearch.JacobiEigenvectors.TheoremA.InvPoly

/-!
# Paper J, Layer 2: regularity of the recursion `x_r` (L2.E, `InvCoeffs`)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(iii): `x_r in C^{M+1-r}([0, pi L])`, "uniformly in `mu in K`".

## Proved here

* `invC`, `xs`: the Taylor coefficients `c_{jk}(y) = S_j^{(k)}(x_0 y)/k!` and the stage sequences of `InvAlg.st` at the point `y`.
* `InvCtx.invC_bd`, `InvCtx.invC01` (`|c_{01}| >= 3c_0/2`).
* **`InvCtx.reg`**: for `n <= M`, `r <= n`: `xs mu n r` is `BD (M+1-n)` with a constant independent of `mu` (induction on `n`: the new coefficient is `-coeff_{n+1}(Qp)/c_{01}`, `PB.Qp_exists`, `BD.inv_exists`, `BD.mul_exists`).

## Differences from the paper

None in substance; the uniformity is by explicit constants.

## Not formalised

Nothing for this file.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology FormalResearch.JacobiEigenvectors.Setting InvBD InvAlg

variable {Par : Type*} [TopologicalSpace Par]

/-- The Taylor coefficients `c_{jk}(y) = S_j^{(k)}(x_0(y))/k!`. -/
def invC (F : SymbolFamily Par) (S : ℕ → Par → ℝ → ℝ) (δ δ' : ℝ) (j k : ℕ) (μ : Par) (y : ℝ) : ℝ :=
  (k.factorial : ℝ)⁻¹ * invW F S δ δ' j k μ y

/-- The stage sequences of the recursion at the point `y`. -/
def xs (F : SymbolFamily Par) (S : ℕ → Par → ℝ → ℝ) (δ δ' : ℝ) (M : ℕ) (μ : Par) (n r : ℕ) (y : ℝ) : ℝ :=
  st M (fun j k => invC F S δ δ' j k μ y) (invX0 F S δ' μ y) n r

section Reg

variable {F : SymbolFamily Par} {K : Set Par} {M : ℕ} {S : ℕ → Par → ℝ → ℝ} {δ Cn c0 : ℝ} (ctx : InvCtx F K M S δ Cn c0)

include ctx

lemma InvCtx.invC_bd (m : ℕ) : ∃ C : ℝ, ∀ μ ∈ K, ∀ j ≤ M, ∀ k : ℕ, k + m ≤ M + 1 →
    BD (Icc 0 (Real.pi * F.L)) m C (invC F S δ (invDelta δ Cn c0) j k μ) := by
  obtain ⟨Cw, hCw⟩ := ctx.w_bd m
  have hk : ∀ k : ℕ, ∃ Ck, ∀ g : ℝ → ℝ, BD (Icc 0 (Real.pi * F.L)) m Cw g → BD (Icc 0 (Real.pi * F.L)) m Ck (fun y => (k.factorial : ℝ)⁻¹ * g y) := by
    intro k
    obtain ⟨C3, h3⟩ := BD.mul_exists (I := Icc 0 (Real.pi * F.L)) m |(k.factorial : ℝ)⁻¹| Cw
    exact ⟨C3, fun g hg => h3 _ g (BD.const m _) hg⟩
  choose Ck hCk using hk
  refine ⟨∑ k ∈ range (M + 2), |Ck k|, fun μ hμ j hj k hkm => ?_⟩
  have hkM : k ∈ range (M + 2) := Finset.mem_range.2 (by omega)
  refine (hCk k _ (hCw μ hμ j hj k hkm)).mono_C ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun k => |Ck k|) (fun i _ => abs_nonneg _) hkM

lemma InvCtx.invC01 {μ : Par} (hμ : μ ∈ K) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    3 * c0 / 2 ≤ |invC F S δ (invDelta δ Cn c0) 0 1 μ y| := by
  have hX := ctx.x0_mem hμ hy
  unfold invC invW
  rw [ctx.iter_one (ctx.Iprime_sub hX)]
  have := ctx.slope hμ hX
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
  rw [abs_of_nonpos (by linarith [ctx.hc0])]
  linarith

/-- **Regularity of the recursion**: `x_r in C^{M + 1 - r}` with bounds uniform in `mu` (for `n <= M`, the stage `n` sequences are `C^{M+1-n}`). -/
theorem InvCtx.reg {Cb : ℝ} (hB : ∀ μ ∈ K, |F.bandLo μ| ≤ Cb ∧ |F.bandHi μ| ≤ Cb) :
    ∀ n : ℕ, n ≤ M → ∃ C : ℝ, ∀ μ ∈ K, ∀ r ≤ n,
      BD (Icc 0 (Real.pi * F.L)) (M + 1 - n) C (xs F S δ (invDelta δ Cn c0) M μ n r) := by
  have hI : (Icc (0 : ℝ) (Real.pi * F.L)).Nonempty := ⟨0, le_rfl, by have := F.L_pos; positivity⟩
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨C0, hC0⟩ := ctx.x0_bd hB
    refine ⟨C0, fun μ hμ r hr => ?_⟩
    have hr0 : r = 0 := by omega
    subst hr0
    have : xs F S δ (invDelta δ Cn c0) M μ 0 0 = invX0 F S (invDelta δ Cn c0) μ := by
      funext y; simp [xs, st]
    rw [this]
    simpa using hC0 μ hμ
  | succ n ih =>
    intro hn
    obtain ⟨Cn0, hCn0⟩ := ih (by omega)
    obtain ⟨C1, hC1⟩ := ctx.invC_bd (M - n)
    set Cn' := max Cn0 0 with hCn'
    obtain ⟨C3, hC3⟩ := PB.Qp_exists hI M (M - n) (n + 1) (n + 1) C1 Cn'
    obtain ⟨Ci, hCi⟩ := BD.inv_exists (I := Icc 0 (Real.pi * F.L)) (M - n) C1 (3 * c0 / 2) (by have := ctx.hc0; positivity)
    obtain ⟨C4, hC4⟩ := BD.mul_exists (I := Icc 0 (Real.pi * F.L)) (M - n) C3 Ci
    refine ⟨max Cn' C4, fun μ hμ r hr => ?_⟩
    have hlev : M + 1 - n = (M - n) + 1 := by omega
    have hlev' : M + 1 - (n + 1) = M - n := by omega
    rw [hlev']
    -- the previous stage, as `BD` at level `M - n`
    have hprev : ∀ r', 1 ≤ r' → r' ≤ M → BD (Icc 0 (Real.pi * F.L)) (M - n) Cn' (xs F S δ (invDelta δ Cn c0) M μ n r') := by
      intro r' _ hr'M
      by_cases hrn : r' ≤ n
      · have := hCn0 μ hμ r' hrn
        rw [hlev] at this
        exact this.mono_m.mono_C (le_max_left _ _)
      · have : xs F S δ (invDelta δ Cn c0) M μ n r' = fun _ => 0 := by
          funext y; exact st_gt M _ _ n r' (by omega)
        rw [this]
        exact (BD.const (I := Icc 0 (Real.pi * F.L)) (M - n) 0).mono_C (by simp [hCn'])
    have hcbd : ∀ j ≤ M, ∀ k ≤ n + 1, k ≤ M - j → BD (Icc 0 (Real.pi * F.L)) (M - n) C1 (fun y => invC F S δ (invDelta δ Cn c0) j k μ y) :=
      fun j hj k hk _ => hC1 μ hμ j hj k (by omega)
    have hPB := hC3 (fun j k y => invC F S δ (invDelta δ Cn c0) j k μ y) (fun r' y => xs F S δ (invDelta δ Cn c0) M μ n r' y) hcbd hprev
    have hcoef := hPB (n + 1) le_rfl
    have hc01 : BD (Icc 0 (Real.pi * F.L)) (M - n) C1 (invC F S δ (invDelta δ Cn c0) 0 1 μ) := hC1 μ hμ 0 (Nat.zero_le _) 1 (by omega)
    have hinv := hCi _ hc01 (fun y hy => ctx.invC01 hμ hy)
    have hnew : BD (Icc 0 (Real.pi * F.L)) (M - n) C4 (xs F S δ (invDelta δ Cn c0) M μ (n + 1) (n + 1)) := by
      have e : xs F S δ (invDelta δ Cn c0) M μ (n + 1) (n + 1) = fun y =>
          (-(fun y => ((Qp M (fun j k => invC F S δ (invDelta δ Cn c0) j k μ y) (n + 1)
            (Dp M (fun r' => xs F S δ (invDelta δ Cn c0) M μ n r' y))).coeff (n + 1))) y) *
          (invC F S δ (invDelta δ Cn c0) 0 1 μ y)⁻¹ := by
        funext y
        simp only [xs, Pi.neg_apply]
        rw [st_succ_self, neg_div, div_eq_mul_inv, neg_mul]
      rw [e]
      exact hC4 _ _ (BD.neg hcoef) hinv
    by_cases hrn : r = n + 1
    · subst hrn
      exact hnew.mono_C (le_max_right _ _)
    · have hrn' : r ≤ n := by omega
      have : xs F S δ (invDelta δ Cn c0) M μ (n + 1) r = xs F S δ (invDelta δ Cn c0) M μ n r := by
        funext y; exact st_succ_of_ne M _ _ (by omega)
      rw [this]
      have h := hCn0 μ hμ r hrn'
      rw [hlev] at h
      exact h.mono_m.mono_C (le_trans (le_max_left _ _) (le_max_left _ _))

end Reg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.reg

end FormalResearch.JacobiEigenvectors.TheoremA
