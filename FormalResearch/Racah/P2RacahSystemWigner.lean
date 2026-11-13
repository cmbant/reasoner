module

public import FormalResearch.Racah.P2RacahSystem

/-!
# The exact finite Racah-to-Wigner spectral map, abstract form
(Weyl P2, `prop:6jRacahTransmutation`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, *Exact Racah-to-Wigner transmutation*,
`eq:6jRacahSpectralMap`-`eq:6jRacahIntertwine`.

The paper's continuum side consists of the normalised Wigner modes `u_f = √((2f+1)/2) d^f_{nm}(arccos x)`
in `L²(-1,1)`, orthonormal and with `H_0 u_f = f(f+1) u_f`; the corollary then follows "from the
continuum and finite orthonormal eigenbases and their common simple spectrum".  This file formalises
exactly that algebraic content for an arbitrary real inner-product space `E` containing an orthonormal
family `u : Fin (D+1) → E` of eigenvectors `H_0 u_j = f_j(f_j+1) u_j`, `f_j = f_0 + j`:

* `SRmap u x = ∑_j ⟨u_j, x⟩ v_j`  (`S_R`, `eq:6jRacahSpectralMap`; in the paper's realisation
  `(S_R g)(c) = ∫ K_R(c,x) g(x) dx`, `K_R(c,x) = ∑_f (2f+1)/2 Φ_f(c) d^f_{nm}(arccos x)`, `eq:6jRacahKernel`);
* `SRmap_u`: `S_R u_j = v_j`;
* `SRmap_isometry`: `S_R` is isometric from `V = span{u_j}` into `ℓ²(𝒞, ω)`;
* `SRmap_surjective`, `SRinv_SRmap`, `SRmap_SRinv`: `S_R : V → ℓ²(𝒞, ω)` is bijective with inverse
  `SRinv q = ∑_j ⟨v_j, q⟩_ω u_j` (`eq:6jRacahInverse`, the weighted adjoint);
* `SRmap_intertwine`: `H_R S_R = S_R H_0` on `V` (`eq:6jRacahIntertwine`).

Not formalised: the identification of `E` with `L²(-1,1)` and of `u_f` with the Wigner `d`-functions
(analysis of the Wigner `d` function; the corollary's content beyond this algebra).
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `S_R x = ∑_j ⟨u_j, x⟩ v_j` (`eq:6jRacahSpectralMap`, `eq:6jRacahKernel`). -/
noncomputable def SRmap (a b m n : ℚ) {D : ℕ} (u : Fin (D + 1) → E) (x : E) :
    Fin (D + 1) → ℝ :=
  ∑ j, inner ℝ (u j) x • vR a b m n j

/-- `S_R⁻¹ q = ∑_j ⟨v_j, q⟩_ω u_j` (`eq:6jRacahInverse`). -/
noncomputable def SRinv (a b m n : ℚ) {D : ℕ} (u : Fin (D + 1) → E) (q : Fin (D + 1) → ℝ) : E :=
  ∑ j, ipR a b m n (vR a b m n j) q • u j

lemma SRmap_sum (a b m n : ℚ) {D : ℕ} {u : Fin (D + 1) → E} (hu : Orthonormal ℝ u)
    (c : Fin (D + 1) → ℝ) :
    SRmap a b m n u (∑ k, c k • u k) = ∑ k, c k • vR a b m n k := by
  unfold SRmap
  apply Finset.sum_congr rfl
  intro j _
  rw [hu.inner_right_fintype c j]

/-- `S_R u_j = v_j`. -/
theorem SRmap_u (a b m n : ℚ) {D : ℕ} {u : Fin (D + 1) → E} (hu : Orthonormal ℝ u)
    (l : Fin (D + 1)) : SRmap a b m n u (u l) = vR a b m n l := by
  have := SRmap_sum a b m n hu (fun k => if k = l then 1 else 0)
  simpa using this

lemma ipR_sum_left (a b m n : ℚ) {D : ℕ} (c : Fin (D + 1) → ℝ) (x : Fin (D + 1) → Fin (D + 1) → ℝ)
    (y : Fin (D + 1) → ℝ) :
    ipR a b m n (∑ k, c k • x k) y = ∑ k, c k * ipR a b m n (x k) y := by
  simp only [ipR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _
  ring

lemma ipR_sum_right (a b m n : ℚ) {D : ℕ} (c : Fin (D + 1) → ℝ) (x : Fin (D + 1) → ℝ)
    (y : Fin (D + 1) → Fin (D + 1) → ℝ) :
    ipR a b m n x (∑ k, c k • y k) = ∑ k, c k * ipR a b m n x (y k) := by
  simp only [ipR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _
  ring

lemma ipR_sum_vR {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (c c' : Fin (D + 1) → ℝ) :
    ipR a b m n (∑ k, c k • vR a b m n k) (∑ k, c' k • vR a b m n k) = ∑ k, c k * c' k := by
  rw [ipR_sum_left]
  apply Finset.sum_congr rfl; intro k _
  rw [ipR_sum_right]
  simp only [vR_orthonormal h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- `S_R` is isometric on `V = span{u_j}`: `⟨S_R x, S_R y⟩_ω = ⟨x, y⟩`. -/
theorem SRmap_isometry {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) {u : Fin (D + 1) → E}
    (hu : Orthonormal ℝ u) {x y : E} (hx : x ∈ Submodule.span ℝ (Set.range u))
    (hy : y ∈ Submodule.span ℝ (Set.range u)) :
    ipR a b m n (SRmap a b m n u x) (SRmap a b m n u y) = inner ℝ x y := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hx
  obtain ⟨c', rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hy
  rw [SRmap_sum a b m n hu, SRmap_sum a b m n hu, ipR_sum_vR h]
  have := hu.inner_sum c c' Finset.univ
  simpa using this.symm

/-- `S_R : V → ℓ²(𝒞, ω)` is onto, with `S_R (S_R⁻¹ q) = q`. -/
theorem SRmap_SRinv {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) {u : Fin (D + 1) → E}
    (hu : Orthonormal ℝ u) (q : Fin (D + 1) → ℝ) :
    SRmap a b m n u (SRinv a b m n u q) = q := by
  unfold SRinv
  rw [SRmap_sum a b m n hu]
  exact (vR_expansion h q).symm

/-- `S_R⁻¹` is a left inverse of `S_R` on `V`. -/
theorem SRinv_SRmap {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) {u : Fin (D + 1) → E}
    (hu : Orthonormal ℝ u) {x : E} (hx : x ∈ Submodule.span ℝ (Set.range u)) :
    SRinv a b m n u (SRmap a b m n u x) = x := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hx
  rw [SRmap_sum a b m n hu]
  unfold SRinv
  apply Finset.sum_congr rfl
  intro k _
  have : ipR a b m n (vR a b m n k) (∑ l, c l • vR a b m n l) = c k := by
    have := ipR_sum_vR h (fun l => if l = k then 1 else 0) c
    have e : (∑ l : Fin (D + 1), (if l = k then (1 : ℝ) else 0) • vR a b m n l) = vR a b m n k := by
      simp
    rw [e] at this
    simpa using this
  rw [this]

/-- **`eq:6jRacahIntertwine`**: if `H_0 u_j = f_j(f_j+1) u_j` then `H_R S_R = S_R H_0` on
`V = span{u_j}`. -/
theorem SRmap_intertwine {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) {u : Fin (D + 1) → E}
    (hu : Orthonormal ℝ u) (H0 : E →ₗ[ℝ] E) (hH0 : ∀ j, H0 (u j) = lamR m n j • u j) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range u)) :
    (HR a b m n D).mulVec (SRmap a b m n u x) = SRmap a b m n u (H0 x) := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hx
  have e : H0 (∑ k, c k • u k) = ∑ k, (c k * lamR m n k) • u k := by
    rw [map_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [map_smul, hH0, smul_smul]
  rw [e, SRmap_sum a b m n hu, SRmap_sum a b m n hu, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [Matrix.mulVec_smul, vR_eigen h, smul_smul]
  congr 1

/-- info: 'FormalResearch.Racah.SixJ.SRmap_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SRmap_intertwine

/-- info: 'FormalResearch.Racah.SixJ.SRmap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SRmap_isometry

/-- info: 'FormalResearch.Racah.SixJ.SRmap_SRinv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SRmap_SRinv

/-- info: 'FormalResearch.Racah.SixJ.SRinv_SRmap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SRinv_SRmap

end FormalResearch.Racah.SixJ
