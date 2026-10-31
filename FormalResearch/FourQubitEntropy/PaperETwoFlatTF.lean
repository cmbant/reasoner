import FormalResearch.FourQubitEntropy.PaperECriticalTwoFlat
import FormalResearch.FourQubitEntropy.PaperETwoFlatEq
import FormalResearch.FourQubitEntropy.SpectralSpinFlip

/-!
# Two-flat rigidity (TF) in the paper's ordered-spectrum form, for every unit state

Paper E, `renyi_uncapped_reduction.tex`, `prop:fqe-two-flat-rigidity`. For a unit four-qubit state `ψ`,
a balanced cut `k` with ordered spectrum `λ₁ ≥ λ₂ ≥ λ₃ ≥ λ₄ ≥ 0` and `λ₁ ≥ 1/2`,
`Δ_k = Σ_{j≠k}(p_j - 1/4)` (`p_j = tr ρ_{1j}²`):

`Δ_k ≥ W₁/4 + 2(λ₂λ₃ + λ₂λ₄ + λ₃λ₄) ≥ W₁/4 + (λ₃ + λ₄)²`.

* `IsSpectrumListing R hR lam`: `lam : Fin 4 → ℝ` lists the spectrum of `R` with multiplicity
  (`exists_listing`: an antitone listing exists, from Mathlib's `eigenvalues₀`; it is unique).
* `two_flat_TF_12`, `_13`, `_14` (**proved**): both inequalities of `(TF)` for the cuts `12|34`,
  `13|24`, `14|23`, with the `W₁/4` term, for every unit state (not only critical). Here
  `lam` is an antitone listing of the cut spectrum, `lam 0 = λ₁`, ..., `lam 3 = λ₄`.
* `two_flat_eq_iff_12`, `_13`, `_14` (**proved**): on the critical locus, in a normal form
  `ψ ≃ G(v)`, equality in the first inequality holds iff every other `v_j²` has the phase opposite to the
  square of the largest amplitude (`v_j² = -t v_i²`, `t ≥ 0`; for the cuts `13|24`, `14|23` the amplitudes
  are those of `wp v`, `wm v`).
* `two_flat_sharp_critical` (**proved**): sharpness of the first inequality on the critical locus for every
  ordered spectrum with `λ₁ ≥ 1/2` (`G(√λ₁, i√λ₂, i√λ₃, i√λ₄)`, opposite phases).
* `two_flat_sharp_noncritical` (**proved**): the noncritical sharpness family
  `(x|00⟩ + y|11⟩)_{12} ⊗ (|00⟩ + |11⟩)_{34}/√2` of `prop:fqe-spectral-spinflip` also attains the first
  inequality (with `W₁ = 2(x² - y²)² ≠ 0`).

Together with `PaperECriticalTwoFlat.lean` (`two_flat_rank`: two maximally mixed cuts force Schmidt rank
at most two on the third) and `tau_eq_iff` (`PaperETwoFlatEq.lean`), this formalises the inequalities, the
equality classification and the sharpness of `prop:fqe-two-flat-rigidity`. NOT formalised: the final
identification of every state with two maximally mixed balanced cuts with the cluster-to-Bell family
`(eq:fqe-quadratic-family)` up to local unitaries and a permutation of the cuts, and hence the Rényi
envelope consequence.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-! ### Ordered spectrum -/

/-- `lam` lists the spectrum of the Hermitian `R` (with multiplicity). -/
def IsSpectrumListing {R : Mat4} (hR : R.IsHermitian) (lam : Fin 4 → ℝ) : Prop :=
  Multiset.map lam Finset.univ.val = Multiset.map hR.eigenvalues Finset.univ.val

theorem map_univ_val_equiv {α β γ : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → γ) :
    Multiset.map (f ∘ e) Finset.univ.val = Multiset.map f Finset.univ.val := by
  have h : (Finset.univ : Finset α).map e.toEmbedding = Finset.univ := Finset.map_univ_equiv e
  have h2 : Multiset.map e Finset.univ.val = Finset.univ.val := by
    have := congrArg Finset.val h
    rwa [Finset.map_val] at this
  rw [← Multiset.map_map, h2]

theorem sum_listing {R : Mat4} {hR : R.IsHermitian} {lam : Fin 4 → ℝ} (h : IsSpectrumListing hR lam)
    (f : ℝ → ℝ) : ∑ a, f (lam a) = ∑ i, f (hR.eigenvalues i) := by
  have h1 : ∑ a, f (lam a) = (Multiset.map f (Multiset.map lam Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  have h2 : ∑ i, f (hR.eigenvalues i) = (Multiset.map f (Multiset.map hR.eigenvalues Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  rw [h1, h2, h]

theorem exists_eig_of_listing {R : Mat4} {hR : R.IsHermitian} {lam : Fin 4 → ℝ}
    (h : IsSpectrumListing hR lam) (a : Fin 4) : ∃ i, hR.eigenvalues i = lam a := by
  have : lam a ∈ Multiset.map lam Finset.univ.val := Multiset.mem_map_of_mem _ (Finset.mem_univ a)
  rw [h] at this
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp this
  exact ⟨i, hi⟩

theorem exists_listing {R : Mat4} (hR : R.IsHermitian) :
    ∃ lam : Fin 4 → ℝ, Antitone lam ∧ IsSpectrumListing hR lam := by
  have hc : Fintype.card (Fin 2 × Fin 2) = 4 := by simp
  let e : Fin 4 ≃ Fin (Fintype.card (Fin 2 × Fin 2)) := finCongr hc.symm
  refine ⟨hR.eigenvalues₀ ∘ e, ?_, ?_⟩
  · intro a b hab
    exact hR.eigenvalues₀_antitone (by simpa [e] using hab)
  · unfold IsSpectrumListing
    rw [map_univ_val_equiv e hR.eigenvalues₀]
    have : hR.eigenvalues = hR.eigenvalues₀ ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm := rfl
    rw [this, map_univ_val_equiv]

/-! ### The scalar (TF) -/

theorem tf_ordered (R : Mat4) (hR : R.IsHermitian) (hpsd : R.PosSemidef)
    (htr : (Matrix.trace R).re = 1) (lam : Fin 4 → ℝ) (hanti : Antitone lam)
    (hlist : IsSpectrumListing hR lam) (ha : 1 / 2 ≤ lam 0) (W P q : ℝ)
    (hP : P = (Matrix.trace (R * R)).re + q)
    (hb : ∀ i, (max (2 * hR.eigenvalues i - 1) 0) ^ 2 ≤ 2 * (P - 1) - W / 2) :
    W / 4 + (lam 2 + lam 3) ^ 2 ≤ W / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ∧
    W / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ≤ q - 1 / 2 := by
  have hs : ∑ a, lam a = 1 := by
    have := sum_listing hlist (fun x => x)
    rw [this, sum_eig_eq_trace hR, htr]
  have hc : ∑ a, lam a ^ 2 = (Matrix.trace (R * R)).re := by
    have := sum_listing hlist (fun x => x ^ 2)
    rw [this, sum_eigenvalues_pow hR 2, pow_two]
  simp only [Fin.sum_univ_four] at hs hc
  obtain ⟨i0, hi0⟩ := exists_eig_of_listing hlist 0
  obtain ⟨i3, hi3⟩ := exists_eig_of_listing hlist 3
  have h3 : 0 ≤ lam 3 := hi3 ▸ hpsd.eigenvalues_nonneg i3
  have h01 : lam 1 ≤ lam 0 := hanti (by decide)
  have h12 : lam 2 ≤ lam 1 := hanti (by decide)
  have h23 : lam 3 ≤ lam 2 := hanti (by decide)
  have hb0 := hb i0
  rw [hi0, max_eq_left (by linarith)] at hb0
  constructor
  · nlinarith [mul_nonneg h3 (sub_nonneg.2 h23), mul_nonneg h3 (sub_nonneg.2 h12),
      mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 h23), mul_nonneg h3 (sub_nonneg.2 h23)]
  · nlinarith

/-! ### `(TF)` for the three cuts of every unit state -/

/-- **`prop:fqe-two-flat-rigidity`, bound `(TF)`**, cut `12|34`, every unit state: for an ordered
listing `λ₁ ≥ λ₂ ≥ λ₃ ≥ λ₄` of the spectrum of `ρ₁₂` with `λ₁ ≥ 1/2`,
`Δ_{12} ≥ W₁/4 + 2(λ₂λ₃ + λ₂λ₄ + λ₃λ₄) ≥ W₁/4 + (λ₃ + λ₄)²`
(`lam 0 = λ₁`, ..., `lam 3 = λ₄`; `Δ_{12} = (p₁₃ - 1/4) + (p₁₄ - 1/4)`). -/
theorem two_flat_TF_12 (ψ : Psi) (hn : normSqPsi ψ = 1) (lam : Fin 4 → ℝ) (hanti : Antitone lam)
    (hlist : IsSpectrumListing (red12_herm ψ) lam) (ha : 1 / 2 ≤ lam 0) :
    blochSq ψ / 4 + (lam 2 + lam 3) ^ 2 ≤
        blochSq ψ / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ∧
      blochSq ψ / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ≤
        (cutPurity13 ψ - 1 / 4) + (cutPurity14 ψ - 1 / 4) := by
  have := tf_ordered (red12 ψ) (red12_herm ψ) (red12_psd ψ) (by rw [trace_red12, hn]; simp) lam hanti
    hlist ha (blochSq ψ) (purity ψ) (cutPurity13 ψ + cutPurity14 ψ)
    (by rw [purity_eq_cuts]; unfold cutPurity12; ring) (spectral_spinflip_12_purity ψ hn)
  constructor
  · exact this.1
  · linarith [this.2]

/-- `(TF)` for the cut `13|24`. -/
theorem two_flat_TF_13 (ψ : Psi) (hn : normSqPsi ψ = 1) (lam : Fin 4 → ℝ) (hanti : Antitone lam)
    (hlist : IsSpectrumListing (red13_herm ψ) lam) (ha : 1 / 2 ≤ lam 0) :
    blochSq ψ / 4 + (lam 2 + lam 3) ^ 2 ≤
        blochSq ψ / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ∧
      blochSq ψ / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ≤
        (cutPurity12 ψ - 1 / 4) + (cutPurity14 ψ - 1 / 4) := by
  have := tf_ordered (red13 ψ) (red13_herm ψ) (red13_psd ψ) (by rw [trace_red13, hn]; simp) lam hanti
    hlist ha (blochSq ψ) (purity ψ) (cutPurity12 ψ + cutPurity14 ψ)
    (by rw [purity_eq_cuts]; unfold cutPurity13; ring) (spectral_spinflip_13_purity ψ hn)
  constructor
  · exact this.1
  · linarith [this.2]

/-- `(TF)` for the cut `14|23`. -/
theorem two_flat_TF_14 (ψ : Psi) (hn : normSqPsi ψ = 1) (lam : Fin 4 → ℝ) (hanti : Antitone lam)
    (hlist : IsSpectrumListing (red14_herm ψ) lam) (ha : 1 / 2 ≤ lam 0) :
    blochSq ψ / 4 + (lam 2 + lam 3) ^ 2 ≤
        blochSq ψ / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ∧
      blochSq ψ / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ≤
        (cutPurity12 ψ - 1 / 4) + (cutPurity13 ψ - 1 / 4) := by
  have := tf_ordered (red14 ψ) (red14_herm ψ) (red14_psd ψ) (by rw [trace_red14, hn]; simp) lam hanti
    hlist ha (blochSq ψ) (purity ψ) (cutPurity12 ψ + cutPurity13 ψ)
    (by rw [purity_eq_cuts]; unfold cutPurity14; ring) (spectral_spinflip_14_purity ψ hn)
  constructor
  · exact this.1
  · linarith [this.2]

/-! ### Equality on the critical locus -/

/-- Scalar form: with `2P = 2 + |Σ w²|²` and `q = P - Σ λ²`, the first inequality of `(TF)` is an
equality iff `|Σ w²|² = (2λ_i - 1)²`, i.e. (by `tau_eq_iff`) iff the other `w_j²` are opposite in phase. -/
theorem crossCost_eq_iff (w : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (w k) = 1) (P q : ℝ)
    (hP : 2 * P = 2 + Complex.normSq (∑ k, w k ^ 2))
    (hq : q = P - ∑ k, Complex.normSq (w k) ^ 2) (i : Fin 2 × Fin 2)
    (hi : 1 / 2 ≤ Complex.normSq (w i)) :
    crossCost w i = q - 1 / 2 ↔
      ∀ j, j ≠ i → ∃ t : ℝ, 0 ≤ t ∧ w j ^ 2 = -(t : ℂ) * w i ^ 2 := by
  rw [← tau_eq_iff w hn i hi]
  have h2 : ∑ j ∈ Finset.univ.erase i, Complex.normSq (w j) = 1 - Complex.normSq (w i) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hn]
  have h3 : ∑ j ∈ Finset.univ.erase i, Complex.normSq (w j) ^ 2
      = ∑ k, Complex.normSq (w k) ^ 2 - Complex.normSq (w i) ^ 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  unfold crossCost
  rw [h2, h3, hq]
  constructor <;> intro h <;> nlinarith

/-- Data of a critical state in a normal form `ψ ≃ G(v)`. -/
theorem critical_data (ψ : Psi) (v : Fin 2 × Fin 2 → ℂ) (hv : LUEquiv (Gv v) ψ)
    (hnv : ∑ k, Complex.normSq (v k) = 1) :
    2 * purity ψ = 2 + Complex.normSq (∑ k, v k ^ 2) ∧
    cutPurity12 ψ = ∑ k, Complex.normSq (v k) ^ 2 ∧
    cutPurity13 ψ = ∑ k, Complex.normSq (wp v k) ^ 2 ∧
    cutPurity14 ψ = ∑ k, Complex.normSq (wm v k) ^ 2 := by
  obtain ⟨e12, e13, e14⟩ := cutPurities_LUEquiv hv
  obtain ⟨c12, c13, c14⟩ := Gv_cutPurities v
  refine ⟨?_, by rw [e12, c12], by rw [e13, c13], by rw [e14, c14]⟩
  have h := Gv_purity_tau v hnv
  have : purity ψ = purity (Gv v) := by
    rw [purity_eq_cuts, purity_eq_cuts, e12, e13, e14]
  rw [this]; exact h

/-- **Equality case of `(TF)`, cut `12|34`, critical states**: for `ψ ≃ G(v)` (unit `v`) and `i` with
`|v_i|² ≥ 1/2`, the first inequality `2e₂(other three) ≤ Δ_{12}` is an equality iff every other
`v_j²` has the phase opposite to `v_i²` (`v_j² = -t v_i²`, `t ≥ 0`, so a zero `v_j` is allowed). -/
theorem two_flat_eq_iff_12 (ψ : Psi) (v : Fin 2 × Fin 2 → ℂ) (hv : LUEquiv (Gv v) ψ)
    (hnv : ∑ k, Complex.normSq (v k) = 1) (i : Fin 2 × Fin 2) (hi : 1 / 2 ≤ Complex.normSq (v i)) :
    crossCost v i = (cutPurity13 ψ - 1 / 4) + (cutPurity14 ψ - 1 / 4) ↔
      ∀ j, j ≠ i → ∃ t : ℝ, 0 ≤ t ∧ v j ^ 2 = -(t : ℂ) * v i ^ 2 := by
  obtain ⟨hP, c12, c13, c14⟩ := critical_data ψ v hv hnv
  have := crossCost_eq_iff v hnv (purity ψ) (cutPurity13 ψ + cutPurity14 ψ) hP
    (by rw [purity_eq_cuts, c12]; ring) i hi
  rw [← this]
  constructor <;> intro h <;> linarith

/-- Equality case of `(TF)`, cut `13|24`: the normal-form amplitudes of this cut are `wp v`. -/
theorem two_flat_eq_iff_13 (ψ : Psi) (v : Fin 2 × Fin 2 → ℂ) (hv : LUEquiv (Gv v) ψ)
    (hnv : ∑ k, Complex.normSq (v k) = 1) (i : Fin 2 × Fin 2)
    (hi : 1 / 2 ≤ Complex.normSq (wp v i)) :
    crossCost (wp v) i = (cutPurity12 ψ - 1 / 4) + (cutPurity14 ψ - 1 / 4) ↔
      ∀ j, j ≠ i → ∃ t : ℝ, 0 ≤ t ∧ wp v j ^ 2 = -(t : ℂ) * wp v i ^ 2 := by
  obtain ⟨hP, c12, c13, c14⟩ := critical_data ψ v hv hnv
  have hn' : ∑ k, Complex.normSq (wp v k) = 1 := (wp_normSq_sum v).trans hnv
  have := crossCost_eq_iff (wp v) hn' (purity ψ) (cutPurity12 ψ + cutPurity14 ψ)
    (by rw [wp_sq_sum]; exact hP) (by rw [purity_eq_cuts, c13]; ring) i hi
  rw [← this]
  constructor <;> intro h <;> linarith

/-- Equality case of `(TF)`, cut `14|23`: the normal-form amplitudes of this cut are `wm v`. -/
theorem two_flat_eq_iff_14 (ψ : Psi) (v : Fin 2 × Fin 2 → ℂ) (hv : LUEquiv (Gv v) ψ)
    (hnv : ∑ k, Complex.normSq (v k) = 1) (i : Fin 2 × Fin 2)
    (hi : 1 / 2 ≤ Complex.normSq (wm v i)) :
    crossCost (wm v) i = (cutPurity12 ψ - 1 / 4) + (cutPurity13 ψ - 1 / 4) ↔
      ∀ j, j ≠ i → ∃ t : ℝ, 0 ≤ t ∧ wm v j ^ 2 = -(t : ℂ) * wm v i ^ 2 := by
  obtain ⟨hP, c12, c13, c14⟩ := critical_data ψ v hv hnv
  have hn' : ∑ k, Complex.normSq (wm v k) = 1 := (wm_normSq_sum v).trans hnv
  have := crossCost_eq_iff (wm v) hn' (purity ψ) (cutPurity12 ψ + cutPurity13 ψ)
    (by rw [wm_sq_sum]; exact hP) (by rw [purity_eq_cuts, c14]; ring) i hi
  rw [← this]
  constructor <;> intro h <;> linarith

/-! ### Sharpness on the critical locus -/

theorem roots_charpoly_diagonal_real (d : Fin 2 × Fin 2 → ℝ) :
    (Matrix.diagonal (fun k => ((d k : ℝ) : ℂ)) : Mat4).charpoly.roots =
      Multiset.map (fun k => ((d k : ℝ) : ℂ)) Finset.univ.val := by
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp

/-- If `zmat φ = B diag(w) Bᵀ`, the spectrum of `red12 φ` is `{|w_k|²}`. -/
theorem listing_of_diag (φ : Psi) (w : Fin 2 × Fin 2 → ℂ)
    (h : zmat φ = magicB * Matrix.diagonal w * magicBᵀ) (lam : Fin 4 → ℝ)
    (hl : Multiset.map lam Finset.univ.val =
      Multiset.map (fun k => Complex.normSq (w k)) Finset.univ.val) :
    IsSpectrumListing (red12_herm φ) lam := by
  unfold IsSpectrumListing
  rw [hl]
  have hR := red12_of_diag φ w h
  have hD : Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) =
      (Matrix.diagonal (fun k => ((Complex.normSq (w k) : ℝ) : ℂ)) : Mat4) := by
    congr 1; ext k; exact Complex.mul_conj (w k)
  rw [hD] at hR
  have hc : (red12 φ).charpoly = (Matrix.diagonal (fun k => ((Complex.normSq (w k) : ℝ) : ℂ)) : Mat4).charpoly := by
    rw [hR, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, magicB_unitary, Matrix.one_mul]
  have h1 := (red12_herm φ).roots_charpoly_eq_eigenvalues
  rw [hc, roots_charpoly_diagonal_real] at h1
  have h2 : Multiset.map (fun k => ((Complex.normSq (w k) : ℝ) : ℂ)) Finset.univ.val =
      Multiset.map Complex.ofReal (Multiset.map (fun k => Complex.normSq (w k)) Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  have h3 : Multiset.map (RCLike.ofReal ∘ (red12_herm φ).eigenvalues) Finset.univ.val =
      Multiset.map Complex.ofReal (Multiset.map (red12_herm φ).eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [h2, h3] at h1
  exact Multiset.map_injective Complex.ofReal_injective h1

/-- Normal-form amplitudes `(√λ₁, i√λ₂, i√λ₃, i√λ₄)`: the other three squares are opposite in phase to
the first. -/
noncomputable def specAmp (a b c d : ℝ) : Fin 2 × Fin 2 → ℂ := fun k =>
  if k = (0, 0) then ((Real.sqrt a : ℝ) : ℂ)
  else if k = (0, 1) then Complex.I * (Real.sqrt b : ℝ)
  else if k = (1, 0) then Complex.I * (Real.sqrt c : ℝ)
  else Complex.I * (Real.sqrt d : ℝ)

theorem normSq_specAmp (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Complex.normSq (specAmp a b c d (0, 0)) = a ∧ Complex.normSq (specAmp a b c d (0, 1)) = b ∧
    Complex.normSq (specAmp a b c d (1, 0)) = c ∧ Complex.normSq (specAmp a b c d (1, 1)) = d := by
  simp [specAmp, Complex.normSq_apply, Real.mul_self_sqrt, ha, hb, hc, hd]

theorem sq_specAmp (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    specAmp a b c d (0, 0) ^ 2 = (a : ℂ) ∧ specAmp a b c d (0, 1) ^ 2 = -(b : ℂ) ∧
    specAmp a b c d (1, 0) ^ 2 = -(c : ℂ) ∧ specAmp a b c d (1, 1) ^ 2 = -(d : ℂ) := by
  have e : ∀ x : ℝ, 0 ≤ x → (((Real.sqrt x : ℝ) : ℂ)) ^ 2 = (x : ℂ) := fun x hx => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hx]
  simp only [specAmp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mul_pow, e _ ha, e _ hb, e _ hc, e _ hd]

/-- **Sharpness of the first inequality of `(TF)` on the critical locus**: for every ordered spectrum
`λ₁ ≥ λ₂ ≥ λ₃ ≥ λ₄ ≥ 0`, `Σ λ = 1`, `λ₁ ≥ 1/2`, the critical state `G(√λ₁, i√λ₂, i√λ₃, i√λ₄)` has
`ρ₁₂`-spectrum `(λ₁, λ₂, λ₃, λ₄)` and attains `Δ_{12} = W₁/4 + 2(λ₂λ₃ + λ₂λ₄ + λ₃λ₄)` (`W₁ = 0`). -/
theorem two_flat_sharp_critical (a b c d : ℝ) (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) (hd : 0 ≤ d)
    (hs : a + b + c + d = 1) (ha : 1 / 2 ≤ a) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ blochSq ψ = 0 ∧
      IsSpectrumListing (red12_herm ψ) ![a, b, c, d] ∧
      blochSq ψ / 4 + 2 * (b * c + b * d + c * d) =
        (cutPurity13 ψ - 1 / 4) + (cutPurity14 ψ - 1 / 4) := by
  have hc : 0 ≤ c := hd.trans hcd
  have hb : 0 ≤ b := hc.trans hbc
  have ha0 : 0 < a := by linarith
  obtain ⟨n1, n2, n3, n4⟩ := normSq_specAmp a b c d ha0.le hb hc hd
  obtain ⟨s1, s2, s3, s4⟩ := sq_specAmp a b c d ha0.le hb hc hd
  set v := specAmp a b c d with hv
  have hnv : ∑ k, Complex.normSq (v k) = 1 := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, n1, n2, n3, n4]; linarith
  refine ⟨Gv v, by rw [Gv_n]; exact hnv, blochSq_zero_of_LU_Gv v _ (LUEquiv.refl _), ?_, ?_⟩
  · refine listing_of_diag (Gv v) v (zmat_Gv v) _ ?_
    let e : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm
    have hf : (fun k => Complex.normSq (v k)) ∘ e = ![a, b, c, d] := by
      have h0 : e 0 = (0, 0) := by decide
      have h1 : e 1 = (0, 1) := by decide
      have h2 : e 2 = (1, 0) := by decide
      have h3 : e 3 = (1, 1) := by decide
      funext x
      fin_cases x
      · show Complex.normSq (v (e 0)) = a
        rw [h0]; exact n1
      · show Complex.normSq (v (e 1)) = b
        rw [h1]; exact n2
      · show Complex.normSq (v (e 2)) = c
        rw [h2]; exact n3
      · show Complex.normSq (v (e 3)) = d
        rw [h3]; exact n4
    rw [← hf, map_univ_val_equiv e (fun k => Complex.normSq (v k))]
  · have hi : 1 / 2 ≤ Complex.normSq (v (0, 0)) := by rw [n1]; exact ha
    have := (two_flat_eq_iff_12 (Gv v) v (LUEquiv.refl _) hnv (0, 0) hi).mpr (by
      intro j hj
      have hj' : j = (0, 1) ∨ j = (1, 0) ∨ j = (1, 1) := by
        revert j; decide
      rcases hj' with rfl | rfl | rfl
      · exact ⟨b / a, div_nonneg hb ha0.le, by rw [s2, s1]; push_cast; field_simp⟩
      · exact ⟨c / a, div_nonneg hc ha0.le, by rw [s3, s1]; push_cast; field_simp⟩
      · exact ⟨d / a, div_nonneg hd ha0.le, by rw [s4, s1]; push_cast; field_simp⟩)
    rw [crossCost_eq v (0, 0) (0, 1) (1, 0) (1, 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), n2, n3, n4] at this
    rw [blochSq_zero_of_LU_Gv v _ (LUEquiv.refl _)]
    linarith

/-! ### The noncritical sharpness family -/

/-- `ψ = (x|00⟩ + y|11⟩)_{12} ⊗ r (|00⟩ + |11⟩)_{34}`; with `r = √2/2` and `x² + y² = 1` this is the
noncritical sharpness family of `prop:fqe-spectral-spinflip`. -/
noncomputable def tfFam (x y r : ℝ) : Psi := fun a b c d =>
  (if a = b then (if a = 0 then (x : ℂ) else (y : ℂ)) else 0) * (if c = d then (r : ℂ) else 0)

theorem tfFam_norm (x y r : ℝ) : normSqPsi (tfFam x y r) = (x ^ 2 + y ^ 2) * (2 * r ^ 2) := by
  simp [normSqPsi, tfFam, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem tfFam_bloch (x y r : ℝ) :
    blochSq (tfFam x y r) = 2 * (x ^ 2 - y ^ 2) ^ 2 * (2 * r ^ 2) ^ 2 := by
  simp [blochSq, expectation, actOn, tfFam, Fin.sum_univ_two, Fin.sum_univ_four, pauliX, pauliY,
    pauliZ]
  ring

theorem tfFam_p13 (x y r : ℝ) : cutPurity13 (tfFam x y r) = 2 * r ^ 4 * (x ^ 4 + y ^ 4) := by
  simp [cutPurity13, red13, tfFam, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type]
  ring

theorem tfFam_p14 (x y r : ℝ) : cutPurity14 (tfFam x y r) = 2 * r ^ 4 * (x ^ 4 + y ^ 4) := by
  simp [cutPurity14, red14, tfFam, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type]
  ring

theorem tfFam_eig (x y r : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) (hr : 2 * r ^ 2 = 1) :
    ∃ i, (red12_herm (tfFam x y r)).eigenvalues i = 1 := by
  refine exists_eigenvalue_one _ _
    (fun i => if i.1 = i.2 then (if i.1 = 0 then (x : ℂ) else (y : ℂ)) else 0) ?_ ?_
  · intro h
    have h0 := congrFun h (0, 0)
    have h1 := congrFun h (1, 1)
    simp at h0 h1
    have : x ^ 2 + y ^ 2 = 0 := by rw [h0, h1]; ring
    linarith
  · have hx : (x : ℂ) ^ 2 + (y : ℂ) ^ 2 = 1 := by exact_mod_cast hxy
    have hr' : 2 * (r : ℂ) ^ 2 = 1 := by exact_mod_cast hr
    ext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [red12, tfFam, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fintype.sum_prod_type]
    · linear_combination ((x : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) * hr' + (x : ℂ) * hx
    · linear_combination ((y : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) * hr' + (y : ℂ) * hx

/-- **The noncritical sharpness family attains the first inequality of `(TF)`**: for real `x, y` with
`x² + y² = 1`, `ψ = (x|00⟩ + y|11⟩)_{12} ⊗ (|00⟩ + |11⟩)_{34}/√2` is a unit state with
`W₁ = 2(x² - y²)²` (noncritical unless `x² = y²`), cut `12|34` spectrum `(1, 0, 0, 0)`
(`λ₁ ≥ 1/2`), and equality `Δ_{12} = W₁/4 + 2(λ₂λ₃ + λ₂λ₄ + λ₃λ₄)` for the ordered listing. -/
theorem two_flat_sharp_noncritical (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ blochSq ψ = 2 * (x ^ 2 - y ^ 2) ^ 2 ∧
      ∃ lam : Fin 4 → ℝ, Antitone lam ∧ IsSpectrumListing (red12_herm ψ) lam ∧ 1 / 2 ≤ lam 0 ∧
        blochSq ψ / 4 + 2 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) =
          (cutPurity13 ψ - 1 / 4) + (cutPurity14 ψ - 1 / 4) := by
  set r : ℝ := Real.sqrt 2 / 2 with hrdef
  have hr : 2 * r ^ 2 = 1 := by
    rw [hrdef, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hn : normSqPsi (tfFam x y r) = 1 := by rw [tfFam_norm, hxy, hr]; norm_num
  have hW : blochSq (tfFam x y r) = 2 * (x ^ 2 - y ^ 2) ^ 2 := by rw [tfFam_bloch, hr]; ring
  obtain ⟨lam, hanti, hlist⟩ := exists_listing (red12_herm (tfFam x y r))
  obtain ⟨i1, hi1⟩ := tfFam_eig x y r hxy hr
  have hnn : ∀ a, 0 ≤ lam a := by
    intro a
    obtain ⟨i, hi⟩ := exists_eig_of_listing hlist a
    rw [← hi]; exact (red12_psd _).eigenvalues_nonneg i
  have hsum : lam 0 + lam 1 + lam 2 + lam 3 = 1 := by
    have h := sum_listing hlist (fun t => t)
    have h2 : ∑ i, (red12_herm (tfFam x y r)).eigenvalues i = 1 := by
      rw [sum_eig_eq_trace, trace_red12, hn]; simp
    simpa [Fin.sum_univ_four, h2] using h.trans h2
  have h1mem : (1 : ℝ) ∈ Multiset.map lam Finset.univ.val := by
    rw [hlist]; exact Multiset.mem_map.mpr ⟨i1, Finset.mem_univ i1, hi1⟩
  obtain ⟨a1, -, ha1⟩ := Multiset.mem_map.mp h1mem
  have hle : lam a1 ≤ lam 0 := hanti (Fin.zero_le a1)
  have l0 : lam 0 = 1 := by linarith [hnn 1, hnn 2, hnn 3]
  have l1 : lam 1 = 0 := by linarith [hnn 1, hnn 2, hnn 3]
  have l2 : lam 2 = 0 := by linarith [hnn 1, hnn 2, hnn 3]
  have l3 : lam 3 = 0 := by linarith [hnn 1, hnn 2, hnn 3]
  refine ⟨tfFam x y r, hn, hW, lam, hanti, hlist, by rw [l0]; norm_num, ?_⟩
  rw [l1, l2, l3, tfFam_p13, tfFam_p14, hW]
  have hr4 : r ^ 4 = 1 / 4 := by nlinarith
  rw [hr4]
  have : (x ^ 2 - y ^ 2) ^ 2 = 1 - 4 * x ^ 2 * y ^ 2 := by
    have : y ^ 2 = 1 - x ^ 2 := by linarith
    rw [this]; ring
  have h4 : x ^ 4 + y ^ 4 = 1 - 2 * x ^ 2 * y ^ 2 := by
    have : (x ^ 2 + y ^ 2) ^ 2 = 1 := by rw [hxy]; norm_num
    nlinarith
  rw [h4, this]; ring

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.exists_listing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exists_listing

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_TF_12' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_TF_12

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_TF_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_TF_13

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_TF_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_TF_14

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_eq_iff_12' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_eq_iff_12

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_eq_iff_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_eq_iff_13

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_eq_iff_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_eq_iff_14

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_sharp_critical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_sharp_critical

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.two_flat_sharp_noncritical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_flat_sharp_noncritical

end FormalResearch.FourQubitEntropy.PaperECritical
