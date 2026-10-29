import FormalResearch.FourQubitEntropy.PaperECriticalZeroSet
import FormalResearch.FourQubitEntropy.ClassifyMain
import FormalResearch.FourQubitEntropy.Tradeoff
import FormalResearch.FourQubitEntropy.Checks

/-!
# Zero set of the sextic `F` (`prop:fqe-moment-zeros`)

Paper E (four-qubit entropy), `sextic_identity.tex`. Assembles the local-unitary classification of the
zeros of `F = 17 n P - 12 T - 12 n³` on unit vectors:

* `LU_bell2_of_single` (case A): `G(w)` with a single nonzero coordinate (unit norm) is in the orbit
  of `bell2 = G(e_{00})` (`LU_single`: permuting coordinates is realised by `SO(4)`, `Real4`);
* `LU_bell_of_caseB` (case B): all `|v_k|² = 1/4`, `v_k²` equal; one of `wp v`, `wm v`
  (the `13|24`, `14|23` cut coordinates) is single, so `G(v)` is in the orbit of `bell13` or `bell14`
  (`swap23`, `swap24` transport of case A);
* `LU_M4_of_caseC` (case C): `|v_k|² ∈ {1/6, 1/2}`, `Σ v_k² = 0`; applies `classify`;
* `moment_zeros_of_critical`: on `blochSq ψ = 0`, `F ψ = 0 ↔ ZeroOrbit ψ`. **Proved, axiom-free**
  (only `propext`, `Classical.choice`, `Quot.sound`);
* `moment_zeros`: for every unit `ψ`, `F ψ = 0 ↔ ZeroOrbit ψ`. Both directions use only the standard
  axioms; the direction `⇒` uses `sexticF_zero_bloch` (zeros of `F` have vanishing Bloch vectors),
  whose polynomial identity is kernel-checked (`Identity.lean`), to reach the critical locus.

The algebraic zero classification itself is `Gv_zero_cases` (`PaperECriticalZeroSet.lean`).
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- The single-coordinate vector `c e_k`. -/
def single (k : Fin 2 × Fin 2) (c : ℂ) : Fin 2 × Fin 2 → ℂ := fun j => if j = k then c else 0

set_option maxHeartbeats 4000000 in
theorem Gv_single_zero : Gv (single (0, 0) 1) = bell2 := by
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact rt_mul_rt
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Gv, ofZmat, single, bell2, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    magicB, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
  first | done | (rw [← pow_two, hrt2]; norm_num) | (ring_nf; simp only [hrt2]; ring_nf)

theorem exists_real4_map (p q : Fin 2 × Fin 2) :
    ∃ R : RMat4, Real4 R ∧ ∀ i, R i p = if i = q then 1 else 0 := by
  have unit : ∀ q : Fin 2 × Fin 2, ∑ j, (fun j => if j = q then (1 : ℝ) else 0) j ^ 2 = 1 := by
    intro q; simp [Finset.sum_ite_eq']
  obtain ⟨Rq, hRq, hRqe⟩ := exists_real4_column _ (unit q)
  obtain ⟨Rp, hRp, hRpe⟩ := exists_real4_column _ (unit p)
  refine ⟨Rq * Rpᵀ, hRq.mul hRp.transpose, fun i => ?_⟩
  have h1 : ∀ l, Rp p l = if l = sing then 1 else 0 := by
    intro l
    have := congrFun (congrFun hRp.orth l) sing
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hRpe, Matrix.one_apply] at this
    simpa [Finset.sum_ite_eq'] using this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, h1]
  simp [Finset.sum_ite_eq', hRqe]


theorem Gv_smul (c : ℂ) (v : Fin 2 × Fin 2 → ℂ) :
    Gv (fun j => c * v j) = fun a b c' d => c * Gv v a b c' d := by
  have : Matrix.diagonal (fun j => c * v j) = c • Matrix.diagonal v := by
    ext i j; by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  funext a b c' d
  simp [Gv, ofZmat, this, Matrix.mul_smul, Matrix.smul_mul]

theorem LU_single (p q : Fin 2 × Fin 2) (c : ℂ) :
    LUEquiv (Gv (single p c)) (Gv (single q c)) := by
  obtain ⟨R, hR, hRe⟩ := exists_real4_map p q
  refine LU_of_normal_form _ R R _ hR.orth hR.orth hR.det hR.det ?_
  rw [coord_Gv]
  ext i j
  simp [rc, single, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, hRe]
  by_cases hi : i = q <;> by_cases hj : j = q
  · subst hi; subst hj; simp
  · simp [hi, hj] <;> (intro h; simp_all)
  · simp [hi, hj] <;> (intro h; simp_all)
  · simp [hi, hj]


theorem normSq_unit {c : ℂ} (h : Complex.normSq c = 1) : (starRingEnd ℂ) c * c = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, h]; simp

/-- Case (A): a unit vector with a single nonzero coordinate gives the `12|34` Bell-pair product. -/
theorem LU_bell2_of_single (w : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (w k) = 1)
    (hs : ∃ k, ∀ j, j ≠ k → w j = 0) : LUEquiv bell2 (Gv w) := by
  obtain ⟨k, hk⟩ := hs
  have hw : w = single k (w k) := by
    funext j; by_cases h : j = k
    · subst h; simp [single]
    · simp [single, h, hk j h]
  have hnk : Complex.normSq (w k) = 1 := by
    have := hn
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hk j hj]) (by simp)] at this
    exact this
  have h1 : LUEquiv bell2 (Gv (single k 1)) := by
    rw [← Gv_single_zero]; exact LU_single _ _ _
  have h2 : Gv (single k (w k)) = fun a b c d => w k * Gv (single k 1) a b c d := by
    rw [← Gv_smul]; congr 1; funext j; by_cases h : j = k <;> simp [single, h]
  rw [hw, h2]
  exact h1.trans (LUEquiv.symm (LUEquiv_scalar (normSq_unit hnk) _))


theorem LUEquiv.swap23 {ψ φ : Psi} (h : LUEquiv ψ φ) : LUEquiv (swap23 ψ) (swap23 φ) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact ⟨a, c, b, d, ha, hc, hb, hd, (swap23_localApply a c b d ψ).symm ▸ rfl⟩

theorem LUEquiv.swap24 {ψ φ : Psi} (h : LUEquiv ψ φ) : LUEquiv (swap24 ψ) (swap24 φ) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact ⟨a, d, c, b, ha, hd, hc, hb, (swap24_localApply a d c b ψ).symm ▸ rfl⟩

theorem swap23_swap23 (ψ : Psi) : swap23 (swap23 ψ) = ψ := rfl
theorem swap24_swap24 (ψ : Psi) : swap24 (swap24 ψ) = ψ := rfl

theorem swap23_bell2 : swap23 bell2 = bell13 := by
  funext a b c d; simp [swap23, bell2, bell13]

theorem swap24_bell2 : swap24 bell2 = bell14 := by
  funext a b c d; simp only [swap24, bell2, bell14]
  by_cases h1 : a = d <;> by_cases h2 : b = c <;> simp [h1, h2, eq_comm]

theorem swap23_Gv (v : Fin 2 × Fin 2 → ℂ) : swap23 (Gv v) = Gv (wp v) := by
  rw [← ofZmat_zmat (swap23 (Gv v)), zmat_swap23_Gv]; rfl

theorem swap24_Gv (v : Fin 2 × Fin 2 → ℂ) : swap24 (Gv v) = Gv (wm v) := by
  rw [← ofZmat_zmat (swap24 (Gv v)), zmat_swap24_Gv]; rfl

theorem LU_bell13_of_wp (v : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (wp v k) = 1)
    (hs : ∃ k, ∀ j, j ≠ k → wp v j = 0) : LUEquiv bell13 (Gv v) := by
  have := LUEquiv.swap23 (LU_bell2_of_single _ hn hs)
  have e : swap23 (Gv (wp v)) = Gv v := by rw [← swap23_Gv v]; rfl
  rwa [swap23_bell2, e] at this

theorem LU_bell14_of_wm (v : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (wm v k) = 1)
    (hs : ∃ k, ∀ j, j ≠ k → wm v j = 0) : LUEquiv bell14 (Gv v) := by
  have := LUEquiv.swap24 (LU_bell2_of_single _ hn hs)
  have e : swap24 (Gv (wm v)) = Gv v := by rw [← swap24_Gv v]; rfl
  rwa [swap24_bell2, e] at this


theorem normSq_two_mul (z : ℂ) (h : Complex.normSq z = 1 / 4) : Complex.normSq (2 * z) = 1 := by
  rw [map_mul, h]; simp [Complex.normSq_apply]; norm_num

theorem sum_normSq_single (w : Fin 2 × Fin 2 → ℂ) (k : Fin 2 × Fin 2) (hz : ∀ j, j ≠ k → w j = 0)
    (hk : Complex.normSq (w k) = 1) : ∑ j, Complex.normSq (w j) = 1 := by
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hz j hj]) (by simp)]; exact hk

theorem normSq_pm {z a : ℂ} (h : z = 2 * a ∨ z = -(2 * a)) (ha : Complex.normSq a = 1 / 4) :
    Complex.normSq z = 1 := by
  rcases h with h | h <;> rw [h]
  · exact normSq_two_mul a ha
  · rw [Complex.normSq_neg]; exact normSq_two_mul a ha

theorem wp_case (v : Fin 2 × Fin 2 → ℂ) (k : Fin 2 × Fin 2) (hz : ∀ j, j ≠ k → wp v j = 0)
    (hk : wp v k = 2 * v (0, 0) ∨ wp v k = -(2 * v (0, 0))) (h00 : Complex.normSq (v (0, 0)) = 1 / 4) :
    LUEquiv bell13 (Gv v) :=
  LU_bell13_of_wp v (sum_normSq_single _ k hz (normSq_pm hk h00)) ⟨k, hz⟩

theorem wm_case (v : Fin 2 × Fin 2 → ℂ) (k : Fin 2 × Fin 2) (hz : ∀ j, j ≠ k → wm v j = 0)
    (hk : wm v k = 2 * v (0, 0) ∨ wm v k = -(2 * v (0, 0))) (h00 : Complex.normSq (v (0, 0)) = 1 / 4) :
    LUEquiv bell14 (Gv v) :=
  LU_bell14_of_wm v (sum_normSq_single _ k hz (normSq_pm hk h00)) ⟨k, hz⟩

set_option maxHeartbeats 4000000 in
/-- Case (B): all `|v_k|² = 1/4` and all `v_k²` equal: `G(v)` lies in the orbit of `bell13` or `bell14`. -/
theorem LU_bell_of_caseB (v : Fin 2 × Fin 2 → ℂ) (h1 : ∀ k, Complex.normSq (v k) = 1 / 4)
    (h2 : ∀ k, v k ^ 2 = v (0, 0) ^ 2) : LUEquiv bell13 (Gv v) ∨ LUEquiv bell14 (Gv v) := by
  have h00 := h1 (0, 0)
  have s : ∀ k, v k = v (0, 0) ∨ v k = -v (0, 0) := fun k => sq_eq_sq_iff_eq_or_eq_neg.mp (h2 k)
  rcases s (0, 1) with e1 | e1 <;> rcases s (1, 0) with e2 | e2 <;> rcases s (1, 1) with e3 | e3
  · exact Or.inl (wp_case v (1, 0)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wp] <;> ring)
      (Or.inl (by simp [wp, e1, e2, e3]; ring)) h00)
  · exact Or.inr (wm_case v (1, 1)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wm] <;> ring)
      (Or.inr (by simp [wm, e1, e2, e3]; ring)) h00)
  · exact Or.inr (wm_case v (1, 0)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wm] <;> ring)
      (Or.inr (by simp [wm, e1, e2, e3]; ring)) h00)
  · exact Or.inl (wp_case v (1, 1)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wp] <;> ring)
      (Or.inr (by simp [wp, e1, e2, e3]; ring)) h00)
  · exact Or.inr (wm_case v (0, 1)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wm] <;> ring)
      (Or.inr (by simp [wm, e1, e2, e3]; ring)) h00)
  · exact Or.inl (wp_case v (0, 0)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wp] <;> ring)
      (Or.inl (by simp [wp, e1, e2, e3]; ring)) h00)
  · exact Or.inl (wp_case v (0, 1)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wp] <;> ring)
      (Or.inr (by simp [wp, e1, e2, e3]; ring)) h00)
  · exact Or.inr (wm_case v (0, 0)
      (by rintro ⟨j1, j2⟩ hj; fin_cases j1 <;> fin_cases j2 <;> simp_all [wm] <;> ring)
      (Or.inl (by simp [wm, e1, e2, e3]; ring)) h00)


theorem magic_conj_sub (D : Mat4) (c : ℂ) :
    magicB * D * magicBᴴ - c • (1 : Mat4) = magicB * (D - c • 1) * magicBᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    magicB_unitary']

theorem magic_conj_mul (D E : Mat4) :
    magicB * D * magicBᴴ * (magicB * E * magicBᴴ) = magicB * (D * E) * magicBᴴ := by
  calc _ = magicB * D * (magicBᴴ * magicB) * E * magicBᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [magicB_unitary]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- Case (C): `|v_k|² ∈ {1/6, 1/2}`, `Σ v_k² = 0` (unit norm): `G(v)` is in the orbit of `M₄`
or `conj M₄`. -/
theorem LU_M4_of_caseC (v : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (v k) = 1)
    (hp : ∀ k, Complex.normSq (v k) = 1 / 6 ∨ Complex.normSq (v k) = 1 / 2)
    (hs : ∑ k, v k ^ 2 = 0) : LUEquiv M4 (Gv v) ∨ LUEquiv (Psi.conj M4) (Gv v) := by
  have hn' : normSqPsi (Gv v) = 1 := (Gv_n v).trans hn
  have hW : blochSq (Gv v) = 0 := blochSq_zero_of_LU_Gv v (Gv v) (LUEquiv.refl _)
  have hq : (red12 (Gv v) - (1 / 6 : ℂ) • 1) * (red12 (Gv v) - (1 / 2 : ℂ) • 1) = 0 := by
    rw [red12_of_diag (Gv v) v (zmat_Gv v), magic_conj_sub, magic_conj_sub, magic_conj_mul]
    have hd : ∀ c : ℂ, Matrix.diagonal (fun k => v k * (starRingEnd ℂ) (v k)) - c • (1 : Mat4)
        = Matrix.diagonal (fun k => v k * (starRingEnd ℂ) (v k) - c) := by
      intro c; ext i j; by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, Matrix.one_apply]
    rw [hd, hd, Matrix.diagonal_mul_diagonal]
    have : (fun k => (v k * (starRingEnd ℂ) (v k) - 1 / 6) * (v k * (starRingEnd ℂ) (v k) - 1 / 2))
        = fun _ => 0 := by
      funext k
      rw [Complex.mul_conj]
      rcases hp k with h | h <;> rw [h] <;> push_cast <;> ring
    rw [this]; simp
  have hτ : spinFlipForm (Gv v) = 0 := by
    rw [spinFlip_coord, coord_Gv, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    simp [Matrix.trace, ← pow_two, hs]
  rcases classify (Gv v) hn' hW hq hτ with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm


/-- A unit vector with the three cut quadratics has `F = 0` (the `M₄` computation of
`M4_invariants`, without the Bloch-vector conclusion). -/
theorem sexticF_zero_of_cutQuadratics (ψ : Psi) (hn : normSqPsi ψ = 1) (hq : CutQuadratics ψ) :
    sexticF ψ = 0 := by
  have t12 : Matrix.trace (red12 ψ) = 1 := by rw [trace_red12, hn]; simp
  have t13 : Matrix.trace (red13 ψ) = 1 := by rw [trace_red13, hn]; simp
  have t14 : Matrix.trace (red14 ψ) = 1 := by rw [trace_red14, hn]; simp
  obtain ⟨a12, b12⟩ := quad_traces hq.q12 t12
  obtain ⟨a13, b13⟩ := quad_traces hq.q13 t13
  obtain ⟨a14, b14⟩ := quad_traces hq.q14 t14
  have hP : purity ψ = 1 := by unfold purity; rw [a12, a13, a14]; norm_num
  have hT : cubicMoment ψ = 5 / 12 := by unfold cubicMoment; rw [b12, b13, b14]; norm_num
  unfold sexticF; rw [hn, hP, hT]; norm_num

theorem sexticF_M4 : sexticF M4 = 0 := sexticF_zero_of_cutQuadratics M4 M4_unit M4_cutQuadratics

theorem sexticF_M4_conj : sexticF (Psi.conj M4) = 0 :=
  sexticF_zero_of_cutQuadratics _ (by rw [normSqPsi_conj]; exact M4_unit) M4_cutQuadratics.conj

/-- The five local-unitary orbits of zeros of `F`. -/
def ZeroOrbit (ψ : Psi) : Prop :=
  LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ ∨ LUEquiv bell2 ψ ∨ LUEquiv bell13 ψ ∨ LUEquiv bell14 ψ

/-- Every member of the five orbits is a zero of `F` (proved, no `native_decide`). -/
theorem sexticF_zero_of_orbit (ψ : Psi) (h : ZeroOrbit ψ) : sexticF ψ = 0 := by
  rcases h with h | h | h | h | h
  · rw [sexticF_LUEquiv h, sexticF_M4]
  · rw [sexticF_LUEquiv h, sexticF_M4_conj]
  · rw [sexticF_LUEquiv h, bell2_F]
  · rw [sexticF_LUEquiv h, bell13_F]
  · rw [sexticF_LUEquiv h, bell14_F]

/-- **`prop:fqe-moment-zeros` on the critical locus** (proved, no `native_decide`): for a unit
vector with all one-qubit marginals maximally mixed (`blochSq ψ = 0`), `F ψ = 0` iff `ψ` lies in one
of the five local-unitary orbits. -/
theorem moment_zeros_of_critical (ψ : Psi) (hn : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    sexticF ψ = 0 ↔ ZeroOrbit ψ := by
  refine ⟨fun hF => ?_, sexticF_zero_of_orbit ψ⟩
  obtain ⟨v, hv⟩ := critical_LU_Gv ψ hW
  have hFv : sexticF (Gv v) = 0 := by rw [← sexticF_LUEquiv hv]; exact hF
  have hnv : ∑ k, Complex.normSq (v k) = 1 := by
    rw [← Gv_n, ← normSqPsi_LUEquiv hv]; exact hn
  rw [sexticF_Gv] at hFv
  rcases Gv_zero_cases v hnv hFv with hA | ⟨hB1, hB2⟩ | ⟨hC1, hC2⟩
  · exact Or.inr (Or.inr (Or.inl ((LU_bell2_of_single v hnv hA).trans hv)))
  · rcases LU_bell_of_caseB v hB1 hB2 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h.trans hv))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h.trans hv))))
  · rcases LU_M4_of_caseC v hnv hC1 hC2 with h | h
    · exact Or.inl (h.trans hv)
    · exact Or.inr (Or.inl (h.trans hv))

/-- **`prop:fqe-moment-zeros`** (zero set of the sextic `F`): for a unit vector `ψ`,
`F ψ = 0` iff `ψ` is local-unitarily equivalent to `M₄`, `conj M₄`, or one of the three
Bell-pair products `bell2 (12|34)`, `bell13`, `bell14`.

The direction `⇐` does not use the sextic identity; the direction `⇒` uses `sexticF_zero_bloch` (zeros
of `F` are critical), whose polynomial identity is kernel-checked; the remainder is proved. -/
theorem moment_zeros (ψ : Psi) (hn : normSqPsi ψ = 1) : sexticF ψ = 0 ↔ ZeroOrbit ψ :=
  ⟨fun hF => (moment_zeros_of_critical ψ hn (sexticF_zero_bloch ψ hn hF)).mp hF,
    sexticF_zero_of_orbit ψ⟩

end FormalResearch.FourQubitEntropy.PaperECritical
