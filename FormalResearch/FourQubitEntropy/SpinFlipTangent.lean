import Mathlib

/-!
# The abstract tangent-line lemma (`lem:fivecopy-tangent-line`)

Source: `ResearchNotes/QI/seven_qubit_entanglement/five_copy_repair_certificate.tex`,
`lem:fivecopy-tangent-line` (QIprojects PR #200).  This is the *abstract* convex/linear-algebra core of the
equality case of the seven-qubit purity minimum; it holds for any copy number and any number of qubits.

Setting.  `M` is a real vector space (the paper: finite dimensional, of moments), `X : Z → M` the normalised
averaged moment map of the pure states `z ∈ Z`, `ν : M → ℝ` the normalisation functional, `X_*, X_*' ∈ M` the
moment of the minimiser and its derivative along a curve (`ν X_* = 1`, `ν X_*' = 0`, `X_*' ≠ 0`).  Faces: for each
`b` in a finite index type, a linear map `Γ_b : M → Mat(κ_b)` and a matrix `W_b` (`κ_b × r_b`).

* `tangent_line` : if every functional `f` with `f X_* = f X_*' = 0` is of
  the form `X ↦ Σ_b tr[W_b S_b W_bᵀ Γ_b(X)]` (hypothesis `hspan`, a *weaker* hypothesis than the paper's
  `S_b` symmetric), then `W_bᵀ Γ_b(X z) W_b = 0 ∀ b` forces (positivity is not needed here) `X z = X_* + t X_*'` for some real `t`.
* `tangent_line_eq`: if moreover `Γ_b(X_*) W_b = 0 ∀ b` and `Γ_{b₀}(X_*') W_{b₀} ≠ 0` for one `b₀`, then
  `X z = X_*`.

The lemma uses no property of the copy number, the number of qubits or the target (as the paper says); the
finite dimensionality of `M` is not needed (a real vector space separates points by linear functionals).
Claim class: **proved**.
-/

open Matrix

namespace FormalResearch.FourQubitEntropy.SpinFlip

section

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
  {ι : Type*} [Fintype ι] {κ r : ι → Type*}
  [∀ b, Fintype (κ b)] [∀ b, DecidableEq (κ b)] [∀ b, Fintype (r b)] [∀ b, DecidableEq (r b)]

/-- If `A ⪰ 0` and `Wᵀ A W = 0` then `A W = 0`. -/
theorem psd_mul_eq_zero {κ r : Type*} [Fintype κ] [DecidableEq κ] [Fintype r] [DecidableEq r]
    {A : Matrix κ κ ℝ} (hA : A.PosSemidef) {W : Matrix κ r ℝ} (h : Wᵀ * A * W = 0) :
    A * W = 0 := by
  ext i j
  have hcol : A *ᵥ (fun k => W k j) = 0 := by
    apply (hA.dotProduct_mulVec_zero_iff).mp
    have h1 := congrFun (congrFun h j) j
    have h2 : (Wᵀ * A * W) j j = star (fun k => W k j) ⬝ᵥ A *ᵥ (fun k => W k j) := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, dotProduct, Matrix.mulVec]
    rw [← h2]; exact h1
  have := congrFun hcol i
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

/-- **`lem:fivecopy-tangent-line`, first assertion.** -/
theorem tangent_line {Z : Type*} (X : Z → M) (ν : M →ₗ[ℝ] ℝ)
    (Γ : ∀ b, M →ₗ[ℝ] Matrix (κ b) (κ b) ℝ) (W : ∀ b, Matrix (κ b) (r b) ℝ)
    (Xs Xs' : M)
    (hν : ∀ z, ν (X z) = 1) (hνs : ν Xs = 1) (hνs' : ν Xs' = 0)
    (hspan : ∀ f : M →ₗ[ℝ] ℝ, f Xs = 0 → f Xs' = 0 →
      ∃ S : ∀ b, Matrix (r b) (r b) ℝ,
        ∀ Y, f Y = ∑ b, ((W b * S b * (W b)ᵀ) * Γ b Y).trace)
    (z : Z) (hz : ∀ b, (W b)ᵀ * Γ b (X z) * W b = 0) :
    ∃ t : ℝ, X z = Xs + t • Xs' := by
  have hmem : X z ∈ Submodule.span ℝ ({Xs, Xs'} : Set M) := by
    by_contra hnot
    obtain ⟨f, hf, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hfs : f Xs = 0 := by
      have : f Xs ∈ (Submodule.span ℝ ({Xs, Xs'} : Set M)).map f :=
        ⟨Xs, Submodule.subset_span (by simp), rfl⟩
      rw [hfp] at this; simpa using this
    have hfs' : f Xs' = 0 := by
      have : f Xs' ∈ (Submodule.span ℝ ({Xs, Xs'} : Set M)).map f :=
        ⟨Xs', Submodule.subset_span (by simp), rfl⟩
      rw [hfp] at this; simpa using this
    obtain ⟨S, hS⟩ := hspan f hfs hfs'
    apply hf
    rw [hS]
    refine Finset.sum_eq_zero fun b _ => ?_
    have h0 := hz b
    -- tr(W S Wᵀ Γ) = tr(S (Wᵀ Γ W)) = 0
    have : ((W b * S b * (W b)ᵀ) * Γ b (X z)).trace = (S b * ((W b)ᵀ * Γ b (X z) * W b)).trace := by
      rw [show (W b * S b * (W b)ᵀ) * Γ b (X z) = W b * (S b * ((W b)ᵀ * Γ b (X z))) by
        simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm, show (S b * ((W b)ᵀ * Γ b (X z))) * W b
        = S b * ((W b)ᵀ * Γ b (X z) * W b) by simp only [Matrix.mul_assoc]]
    rw [this, h0]; simp
  obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp hmem
  have h1 : a = 1 := by
    have := congrArg ν hac
    rw [map_add, map_smul, map_smul, hνs, hνs', hν] at this
    simpa using this
  exact ⟨c, by rw [← hac, h1, one_smul]⟩

/-- **`lem:fivecopy-tangent-line`, second assertion.** -/
theorem tangent_line_eq {Z : Type*} (X : Z → M) (ν : M →ₗ[ℝ] ℝ)
    (Γ : ∀ b, M →ₗ[ℝ] Matrix (κ b) (κ b) ℝ) (W : ∀ b, Matrix (κ b) (r b) ℝ)
    (Xs Xs' : M)
    (hν : ∀ z, ν (X z) = 1) (hνs : ν Xs = 1) (hνs' : ν Xs' = 0)
    (hpsd : ∀ z b, (Γ b (X z)).PosSemidef)
    (hspan : ∀ f : M →ₗ[ℝ] ℝ, f Xs = 0 → f Xs' = 0 →
      ∃ S : ∀ b, Matrix (r b) (r b) ℝ,
        ∀ Y, f Y = ∑ b, ((W b * S b * (W b)ᵀ) * Γ b Y).trace)
    (hGs : ∀ b, Γ b Xs * W b = 0)
    (b₀ : ι) (hb₀ : Γ b₀ Xs' * W b₀ ≠ 0)
    (z : Z) (hz : ∀ b, (W b)ᵀ * Γ b (X z) * W b = 0) :
    X z = Xs := by
  obtain ⟨t, ht⟩ := tangent_line X ν Γ W Xs Xs' hν hνs hνs' hspan z hz
  have h0 : Γ b₀ (X z) * W b₀ = 0 := psd_mul_eq_zero (hpsd z b₀) (hz b₀)
  rw [ht, map_add, map_smul, Matrix.add_mul, Matrix.smul_mul, hGs b₀, zero_add] at h0
  have : t = 0 := by
    by_contra htz
    exact hb₀ (by
      have := congrArg (fun m => t⁻¹ • m) h0
      simpa [smul_smul, inv_mul_cancel₀ htz] using this)
  rw [ht, this, zero_smul, add_zero]

end

end FormalResearch.FourQubitEntropy.SpinFlip
