import FormalResearch.FourQubitEntropy.RenyiOrderTransfer

/-!
# Single crossing of the Rényi entropies: first variations of `φ = v_q - κ_q u_q`

Paper: `lem:fqe-renyi-single-crossing` (renyi_single_crossing.tex), the maximiser analysis of its proof
(used by `RenyiSingleCrossing.lean`).

Mass transfer between two coordinates of a four-point vector `![x, y, r, s]` is the one-variable function
`sxPF q cW cZ x y = (cW + h(x) + h(y)) / (cZ + p(x) + p(y)) - κ ln (cZ + p(x) + p(y))` with
`h(x) = x^q ln x`, `p(x) = x^q`, `cW = h(r) + h(s)`, `cZ = p(r) + p(s)`. This file proves
* `sxPhiVec q ![x,y,r,s] = sxPF q (h r + h s) (p r + p s) x y` and the invariance of `φ` under permutations
  of the coordinates;
* the derivative of `t ↦ sxPF (x+t) (y-t)` at a point with `x+t, y-t > 0`:
  `(g(x+t) - g(y-t))/Z` with `g(z) = z^{q-1}(q ln z + C)`, `C = 1 - q(v + κ)` (`sxPF_hasDerivAt`);
* the right derivative at `x = 0 < y`, equal to `-g(y)/Z` (`sxPF_hasDerivWithinAt_zero`), and its
  consequence that a positive right derivative contradicts maximality (`exists_gt_of_hasDerivWithinAt`).
-/

namespace FormalResearch.FourQubitEntropy

open Real Filter Topology

/-- `h(x) = x^q ln x`. -/
noncomputable def sxh (q x : ℝ) : ℝ := x ^ q * Real.log x

/-- `p(x) = x^q`. -/
noncomputable def sxp (q x : ℝ) : ℝ := x ^ q

/-- `g_C(x) = x^{q-1}(q ln x + C)`. -/
noncomputable def sxG (q C x : ℝ) : ℝ := x ^ (q - 1) * (q * Real.log x + C)

/-- Mass transfer function: `φ` of `![x, y, r, s]` with `cW = h r + h s`, `cZ = p r + p s`. -/
noncomputable def sxPF (q cW cZ x y : ℝ) : ℝ :=
  (cW + sxh q x + sxh q y) / (cZ + sxp q x + sxp q y)
    - sxKappa q * Real.log (cZ + sxp q x + sxp q y)

/-! ### Vectors and permutations -/

theorem sxPhiVec_four (q : ℝ) (x y r s : ℝ) :
    sxPhiVec q ![x, y, r, s]
      = sxPF q (sxh q r + sxh q s) (sxp q r + sxp q s) x y := by
  unfold sxPhiVec sxV sxU sxZ sxPF
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, sxh, sxp]
  have e1 : x ^ q + y ^ q + r ^ q + s ^ q = (r ^ q + s ^ q) + x ^ q + y ^ q := by ring
  have e2 : x ^ q * Real.log x + y ^ q * Real.log y + r ^ q * Real.log r + s ^ q * Real.log s
      = (r ^ q * Real.log r + s ^ q * Real.log s) + x ^ q * Real.log x + y ^ q * Real.log y := by ring
  rw [e1, e2]

theorem sxZ_perm (q : ℝ) (l : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) : sxZ q (l ∘ e) = sxZ q l := by
  unfold sxZ
  exact Equiv.sum_comp e (fun i => l i ^ q)

theorem sxPhiVec_perm (q : ℝ) (l : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) :
    sxPhiVec q (l ∘ e) = sxPhiVec q l := by
  unfold sxPhiVec sxV sxU
  rw [sxZ_perm]
  have := Equiv.sum_comp e (fun i => l i ^ q * Real.log (l i))
  simp only [Function.comp_apply]
  rw [this]

theorem isProb4_perm {l : Fin 4 → ℝ} (hl : IsProb4 l) (e : Equiv.Perm (Fin 4)) :
    IsProb4 (l ∘ e) :=
  ⟨fun i => hl.1 _, by have := Equiv.sum_comp e l; simp only [Function.comp_apply]; rw [this]; exact hl.2⟩

theorem exists_perm_pair : ∀ i j : Fin 4, i ≠ j → ∃ e : Equiv.Perm (Fin 4), e 0 = i ∧ e 1 = j := by
  decide

/-! ### Derivatives of `h` and `p` -/

theorem sxp_hasDerivAt (q : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sxp q) (q * x ^ (q - 1)) x :=
  Real.hasDerivAt_rpow_const (Or.inl hx.ne')

theorem sxh_hasDerivAt (q : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sxh q) (x ^ (q - 1) * (q * Real.log x + 1)) x := by
  have h := (sxp_hasDerivAt q hx).mul (Real.hasDerivAt_log hx.ne')
  refine h.congr_deriv ?_
  have : x ^ q = x ^ (q - 1) * x := by
    rw [Real.rpow_sub_one hx.ne']; field_simp
  simp only [sxp]
  rw [this]; field_simp

theorem sxG_hasDerivAt (q C : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sxG q C) (x ^ (q - 2) * ((q - 1) * (q * Real.log x + C) + q)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (q - 1)) ((q - 1) * x ^ (q - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun x : ℝ => q * Real.log x + C) (q * x⁻¹) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul q).add_const C
  have h := h1.mul h2
  refine h.congr_deriv ?_
  have e1 : x ^ (q - 1 - 1) = x ^ (q - 2) := by congr 1; ring
  have e2 : x ^ (q - 1) = x ^ (q - 2) * x := by
    rw [show q - 1 = (q - 2) + 1 by ring, Real.rpow_add_one hx.ne']
  rw [e1, e2]; field_simp

/-- The derivative of the mass-transfer function along `(x + τ, y - τ)`. -/
theorem sxPF_hasDerivAt (q cW cZ x y t : ℝ) (hx : 0 < x + t) (hy : 0 < y - t)
    (hZ : 0 < cZ + sxp q (x + t) + sxp q (y - t)) :
    HasDerivAt (fun τ => sxPF q cW cZ (x + τ) (y - τ))
      ((sxG q (1 - q * ((cW + sxh q (x + t) + sxh q (y - t)) / (cZ + sxp q (x + t) + sxp q (y - t))
          + sxKappa q)) (x + t)
        - sxG q (1 - q * ((cW + sxh q (x + t) + sxh q (y - t))
            / (cZ + sxp q (x + t) + sxp q (y - t)) + sxKappa q)) (y - t))
        / (cZ + sxp q (x + t) + sxp q (y - t))) t := by
  have hxd : HasDerivAt (fun τ : ℝ => x + τ) 1 t := (hasDerivAt_id t).const_add x
  have hyd : HasDerivAt (fun τ : ℝ => y - τ) (-1) t := (hasDerivAt_id t).const_sub y
  have hh1 := (sxh_hasDerivAt q hx).comp t hxd
  have hh2 := (sxh_hasDerivAt q hy).comp t hyd
  have hp1 := (sxp_hasDerivAt q hx).comp t hxd
  have hp2 := (sxp_hasDerivAt q hy).comp t hyd
  have hN := (hh1.const_add cW).add hh2
  have hD := (hp1.const_add cZ).add hp2
  have hdiv := hN.div hD hZ.ne'
  have hlog := hD.log hZ.ne'
  have h := hdiv.sub (hlog.const_mul (sxKappa q))
  unfold sxPF
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.add_apply, sxG]
  have hZ' := hZ.ne'
  field_simp
  ring

/-! ### The boundary `x = 0` -/

theorem sxh_zero (q : ℝ) : sxh q 0 = 0 := by simp [sxh]

theorem sxp_zero {q : ℝ} (hq : 0 < q) : sxp q 0 = 0 := Real.zero_rpow hq.ne'

theorem sxp_hasDerivWithinAt_zero {q : ℝ} (hq : 1 < q) :
    HasDerivWithinAt (sxp q) 0 (Set.Ioi 0) 0 := by
  have := (Real.hasDerivAt_rpow_const (x := 0) (p := q) (Or.inr hq.le)).hasDerivWithinAt
    (s := Set.Ioi 0)
  unfold sxp
  simpa [Real.zero_rpow (by linarith : q - 1 ≠ 0)] using this

theorem sxh_hasDerivWithinAt_zero {q : ℝ} (hq : 1 < q) :
    HasDerivWithinAt (sxh q) 0 (Set.Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := q - 1) (by linarith)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx : 0 < x := hx
  rw [slope_def_field, sxh_zero, sub_zero, sub_zero, sxh]
  have : x ^ q = x ^ (q - 1) * x := by rw [Real.rpow_sub_one hx.ne']; field_simp
  rw [this]; field_simp

/-- The right derivative of `τ ↦ φ(τ, y - τ, r, s)` at `τ = 0`, `y > 0`. -/
theorem sxPF_hasDerivWithinAt_zero {q : ℝ} (hq : 1 < q) (cW cZ y : ℝ) (hy : 0 < y)
    (hZ : 0 < cZ + sxp q y) :
    HasDerivWithinAt (fun τ => sxPF q cW cZ τ (y - τ))
      ((- sxG q (1 - q * ((cW + sxh q y) / (cZ + sxp q y) + sxKappa q)) y)
        / (cZ + sxp q y)) (Set.Ioi 0) 0 := by
  have hyd : HasDerivAt (fun τ : ℝ => y - τ) (-1) 0 := (hasDerivAt_id 0).const_sub y
  have hy' : 0 < y - 0 := by linarith
  have hh1 := sxh_hasDerivWithinAt_zero hq
  have hp1 := sxp_hasDerivWithinAt_zero hq
  have hh2 := ((sxh_hasDerivAt q hy').comp 0 hyd).hasDerivWithinAt (s := Set.Ioi 0)
  have hp2 := ((sxp_hasDerivAt q hy').comp 0 hyd).hasDerivWithinAt (s := Set.Ioi 0)
  have hZ0 : 0 < cZ + sxp q 0 + sxp q (y - 0) := by
    rw [sxp_zero (by linarith), sub_zero]; linarith
  have hN := (hh1.const_add cW).add hh2
  have hD := (hp1.const_add cZ).add hp2
  have hdiv := hN.div hD hZ0.ne'
  have hlog := hD.log hZ0.ne'
  have h := hdiv.sub (hlog.const_mul (sxKappa q))
  unfold sxPF
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.add_apply, sxG, sub_zero, sxh_zero, sxp_zero (by linarith : (0:ℝ) < q)]
  have hZ' := hZ.ne'
  have h0 : (0 : ℝ) ^ (q - 1) = 0 := Real.zero_rpow (by linarith)
  simp only [add_zero, zero_add, mul_neg, mul_one] at *
  field_simp
  ring

/-- A positive right derivative contradicts maximality at `0`. -/
theorem exists_gt_of_hasDerivWithinAt {F : ℝ → ℝ} {D : ℝ} (hD : HasDerivWithinAt F D (Set.Ioi 0) 0)
    (hpos : 0 < D) {δ : ℝ} (hδ : 0 < δ) : ∃ τ, 0 < τ ∧ τ < δ ∧ F 0 < F τ := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hD
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < slope F 0 τ :=
    hD.eventually (lt_mem_nhds hpos)
  obtain ⟨ε, hε, hεs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  have hε' : 0 < ε := hε
  have hm : 0 < min (ε / 2) (δ / 2) := lt_min (by linarith) (by linarith)
  refine ⟨min (ε / 2) (δ / 2), hm, ?_, ?_⟩
  · have := min_le_right (ε / 2) (δ / 2); linarith
  · have hτ : min (ε / 2) (δ / 2) ∈ Set.Ioo (0 : ℝ) ε := by
      refine ⟨hm, ?_⟩
      have := min_le_left (ε / 2) (δ / 2)
      linarith
    have h1 : 0 < slope F 0 (min (ε / 2) (δ / 2)) := hεs hτ
    rw [slope_def_field, sub_zero] at h1
    have := (div_pos_iff_of_pos_right hm).mp h1
    linarith

end FormalResearch.FourQubitEntropy
