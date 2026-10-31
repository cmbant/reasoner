import FormalResearch.FourQubitEntropy.CriticalOrbitSharp
import FormalResearch.FourQubitEntropy.PaperEGenDefect

/-!
# The genuine orbit distance `d(ψ)` and the orbit-stability estimates

Paper E, `lu_orbit_stability.tex`: `thm:fqe-orbit-stability`, `cor:fqe-orbit-spectral`,
`thm:fqe-critical-orbit-sharp` and the definition of `d` and `Φ` that precedes `thm:fqe-global-overlap`.

**Defined and proved here (no hypothesis).**
* `InM` is the paper's set `𝓜 = {e^{iθ}(U₁⊗⋯⊗U₄)ξ : U_i ∈ SU(2), ξ ∈ {M₄, conj M₄}}`
  (phase included, parties labelled); `inM_iff_inOrbit : InM χ ↔ InOrbit χ` identifies it with the
  union of the two unitary LU orbits used for `Φ` (`CO.InOrbit`, `CO.Phi`).
* `orbitDist ψ = inf {‖ψ - χ‖ : χ ∈ 𝓜}` with `‖φ‖ = hsNorm φ = √(Σ|φ_x|²)` the Hilbert-space norm.
* `isCompact_orbit`: the unitary orbit is compact; `exists_closest`, `orbitDist_attained`: the infimum is
  a minimum; `Phi_attained`: `Φ(ψ) = max_{χ ∈ 𝓜} |⟨ψ,χ⟩|²` is attained.
* `orbitDist_sq`: for a unit `ψ`, **`d(ψ)² = 2 - 2√Φ(ψ)`** (so `dist2 = d²`, `orbitDist_sq_eq_dist2`).
* `one_sub_Phi_eq`: `1 - Φ = ((1+√Φ)/2) d²`.

**Restated in terms of `d(ψ)²`, with two explicit named hypotheses.**
`GlobalOverlap ψ` is the comparison `Q ≥ 1 - Φ` of `thm:fqe-global-overlap` (exact rational
certificate in the paper, not proved in Lean).  `FidelityFloor ψ` is `Φ ≥ 1/6`, the weakened form of
`lem:fqe-hs-fidelity-floor` (`Φ ≥ (1+√τ)/6`; real-SVD argument in the paper, not proved in Lean; for critical
states it is discharged by `CO.Phi_ge_quarter`).  Under them: `orbitDist_sq_le_Q`
(`Q ≥ ((6+√6)/12) d²`), `entropy_gap_orbit_stability_dist` (`δ ≥ k((6+√6)/12) d² > d²/20`),
`majorant_gap_orbit`, `tsallis_gap_orbit` (`cor:fqe-orbit-spectral`).  For critical states
(`blochSq ψ = 0`), `critical_orbit_sharp_dist`, `majorant_gap_orbit_critical`, `entropy_gap_critical_orbit`
restate `thm:fqe-critical-orbit-sharp` with genuine `d`; their only hypothesis is the global comparison for
`Φ ≥ 1/2`.

**Not covered.** The sharper `τ`-dependent constant `(6+√(6(1+√τ)))/12` (needs `Φ ≥ (1+√τ)/6`), the local
radius statements (`d ≤ 1/20 ⟹ δ ≥ 3d²/10`, `d ≤ 2⁻¹⁰ ⟹ Q ≥ 3d²`), `thm:fqe-p1-sharp`, and the Rényi `1<q≤5/4`
clause.
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.OD
open CO

/-- `SU(2)`: `2×2` unitary of determinant one. -/
def SU2 (a : Op1) : Prop := aᴴ * a = 1 ∧ a.det = 1

/-- The paper's set `𝓜 = {e^{iθ} (U₁⊗⋯⊗U₄) ξ : U_i ∈ SU(2), ξ ∈ {M₄, conj M₄}}`. -/
def InM (χ : Psi) : Prop :=
  ∃ (θ : ℝ) (a b c d : Op1), SU2 a ∧ SU2 b ∧ SU2 c ∧ SU2 d ∧
    (∃ ξ : Psi, (ξ = M4 ∨ ξ = Psi.conj M4) ∧
      χ = Complex.exp (θ * Complex.I) • localApply a b c d ξ)

theorem localApply_smul_a (s : ℂ) (a b c d : Op1) (ξ : Psi) :
    localApply (s • a) b c d ξ = s • localApply a b c d ξ := by
  funext p q r t
  simp only [localApply_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem localApply_smul_b (s : ℂ) (a b c d : Op1) (ξ : Psi) :
    localApply a (s • b) c d ξ = s • localApply a b c d ξ := by
  funext p q r t
  simp only [localApply_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem localApply_smul_c (s : ℂ) (a b c d : Op1) (ξ : Psi) :
    localApply a b (s • c) d ξ = s • localApply a b c d ξ := by
  funext p q r t
  simp only [localApply_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem localApply_smul_d (s : ℂ) (a b c d : Op1) (ξ : Psi) :
    localApply a b c (s • d) ξ = s • localApply a b c d ξ := by
  funext p q r t
  simp only [localApply_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- A `2×2` unitary is a phase times an `SU(2)` matrix. -/
theorem unitary_phase_su {a : Op1} (ha : aᴴ * a = 1) :
    ∃ (t : ℝ) (a' : Op1), SU2 a' ∧ a = Complex.exp (t * Complex.I) • a' := by
  have hdet1 : star a.det * a.det = 1 := by
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    exact this
  set D := a.det with hD
  have hn : Complex.normSq D = 1 := by
    have h : (Complex.normSq D : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; exact hdet1
    exact_mod_cast h
  have hnorm : ‖D‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg D]
  have hexp : Complex.exp (Complex.arg D * Complex.I) = D := by
    have := Complex.norm_mul_exp_arg_mul_I D
    rwa [hnorm, Complex.ofReal_one, one_mul] at this
  set t : ℝ := Complex.arg D / 2 with ht
  set u : ℂ := Complex.exp (((-t : ℝ) : ℂ) * Complex.I) with hu
  have hu1 : (starRingEnd ℂ) u * u = 1 := by
    rw [hu, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  have hu2 : u * u * D = 1 := by
    rw [hu, ← Complex.exp_add, ← hexp, ← Complex.exp_add]
    rw [← Complex.exp_zero]; congr 1
    rw [ht]; push_cast; ring
  refine ⟨t, u • a, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha]
    rw [show star u * u = 1 from hu1, one_smul]
  · rw [Matrix.det_smul, ← hD, Fintype.card_fin]
    simpa [pow_two] using hu2
  · rw [smul_smul, hu, ← Complex.exp_add]
    simp

theorem phase_unitary (θ : ℝ) {a : Op1} (ha : SU2 a) :
    (Complex.exp (θ * Complex.I) • a)ᴴ * (Complex.exp (θ * Complex.I) • a) = 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha.1]
  have : star (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
    show (starRingEnd ℂ) _ * _ = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]; simp
  rw [this, one_smul]

theorem inOrbit_of_inM {χ : Psi} (h : InM χ) : InOrbit χ := by
  obtain ⟨θ, a, b, c, d, ha, hb, hc, hd, ξ, hξ, rfl⟩ := h
  have hu : ((Complex.exp (θ * Complex.I)) • a)ᴴ * ((Complex.exp (θ * Complex.I)) • a) = 1 :=
    phase_unitary θ ha
  have key : Complex.exp (θ * Complex.I) • localApply a b c d ξ =
      localApply (Complex.exp (θ * Complex.I) • a) b c d ξ := (localApply_smul_a _ _ _ _ _ _).symm
  rw [key]
  rcases hξ with rfl | rfl
  · exact Or.inl ⟨_, b, c, d, hu, hb.1, hc.1, hd.1, rfl⟩
  · exact Or.inr ⟨_, b, c, d, hu, hb.1, hc.1, hd.1, rfl⟩

theorem inM_of_inOrbit {χ : Psi} (h : InOrbit χ) : InM χ := by
  have key : ∀ ξ, (ξ = M4 ∨ ξ = Psi.conj M4) → LUEquiv ξ χ → InM χ := by
    intro ξ hξ ⟨a, b, c, d, ha, hb, hc, hd, hχ⟩
    obtain ⟨ta, a', ha', rfl⟩ := unitary_phase_su ha
    obtain ⟨tb, b', hb', rfl⟩ := unitary_phase_su hb
    obtain ⟨tc, c', hc', rfl⟩ := unitary_phase_su hc
    obtain ⟨td, d', hd', rfl⟩ := unitary_phase_su hd
    refine ⟨ta + tb + tc + td, a', b', c', d', ha', hb', hc', hd', ξ, hξ, ?_⟩
    rw [← hχ, localApply_smul_a, localApply_smul_b, localApply_smul_c, localApply_smul_d,
      smul_smul, smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 3; push_cast; ring
  rcases h with h | h
  · exact key M4 (Or.inl rfl) h
  · exact key _ (Or.inr rfl) h

theorem inM_iff_inOrbit (χ : Psi) : InM χ ↔ InOrbit χ := ⟨inOrbit_of_inM, inM_of_inOrbit⟩

/-! ### Compactness of the orbits -/

def Ucl : Set Op1 := {a | aᴴ * a = 1}

theorem isCompact_Ucl : IsCompact Ucl := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hcl : IsClosed Ucl := by
    have : Continuous fun a : Op1 => aᴴ * a :=
      Continuous.matrix_mul (Continuous.matrix_conjTranspose continuous_id) continuous_id
    exact isClosed_eq this continuous_const
  refine IsCompact.of_isClosed_subset (s := (Set.pi Set.univ fun _ : Fin 2 =>
      Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : ℂ) 1 : Set Op1)) hc hcl ?_
  intro a0 ha i _ j _
  let a : Op1 := a0
  have ha' : aᴴ * a = 1 := ha
  have h := congrFun (congrFun ha' j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ∑ k, Complex.normSq (a k j) = 1 := by
    have : ((∑ k, Complex.normSq (a k j) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    exact_mod_cast this
  have h3 : Complex.normSq (a i j) ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (a k j))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Complex.normSq_eq_norm_sq] at h3
  nlinarith [norm_nonneg (a i j)]

theorem continuous_localApply (ξ : Psi) :
    Continuous fun x : Op1 × Op1 × Op1 × Op1 => localApply x.1 x.2.1 x.2.2.1 x.2.2.2 ξ := by
  refine continuous_pi fun p => continuous_pi fun q => continuous_pi fun r => continuous_pi fun t => ?_
  simp only [localApply_apply]
  refine continuous_finsetSum _ fun p' _ => continuous_finsetSum _ fun q' _ =>
    continuous_finsetSum _ fun r' _ => continuous_finsetSum _ fun t' _ => ?_
  fun_prop

theorem isCompact_LU (ξ : Psi) : IsCompact {χ : Psi | LUEquiv ξ χ} := by
  have hK : IsCompact (Ucl ×ˢ Ucl ×ˢ Ucl ×ˢ Ucl) :=
    isCompact_Ucl.prod (isCompact_Ucl.prod (isCompact_Ucl.prod isCompact_Ucl))
  convert hK.image (continuous_localApply ξ) using 1
  ext χ
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
    exact ⟨(a, b, c, d), ⟨ha, hb, hc, hd⟩, rfl⟩
  · rintro ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd⟩, rfl⟩
    exact ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩

theorem isCompact_orbit : IsCompact {χ : Psi | InOrbit χ} := by
  have : {χ : Psi | InOrbit χ} = {χ | LUEquiv M4 χ} ∪ {χ | LUEquiv (Psi.conj M4) χ} := rfl
  rw [this]
  exact (isCompact_LU _).union (isCompact_LU _)

theorem continuous_normSqPsi_sub (ψ : Psi) : Continuous fun χ : Psi => normSqPsi (ψ - χ) := by
  simp only [normSqPsi]
  fun_prop

theorem normSqPsi_sub_eq {ψ χ : Psi} (hψ : normSqPsi ψ = 1) (hχ : normSqPsi χ = 1) :
    normSqPsi (ψ - χ) = 2 - 2 * (ip ψ χ).re := by
  have h := ip_self (ψ - (1 : ℂ) • χ)
  rw [ip_sub_smul_left, ip_sub_smul_right, ip_sub_smul_right, ip_self, ip_self, hψ, hχ,
    ip_comm χ ψ] at h
  have h2 := congrArg Complex.re h
  simp only [one_smul, map_one, one_mul, Complex.sub_re, Complex.ofReal_re, Complex.conj_re,
    Complex.one_re] at h2
  linarith

theorem ip_smul_right (c : ℂ) (φ χ : Psi) : ip φ (c • χ) = c * ip φ χ := by
  simp only [ip, vecOf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem inM_phase {χ : Psi} (θ : ℝ) (h : InM χ) : InM (Complex.exp (θ * Complex.I) • χ) := by
  obtain ⟨θ0, a, b, c, d, ha, hb, hc, hd, ξ, hξ, rfl⟩ := h
  refine ⟨θ + θ0, a, b, c, d, ha, hb, hc, hd, ξ, hξ, ?_⟩
  rw [smul_smul, ← Complex.exp_add]; push_cast; rw [add_mul]

theorem inOrbit_phase {χ : Psi} (θ : ℝ) (h : InOrbit χ) :
    InOrbit (Complex.exp (θ * Complex.I) • χ) :=
  inOrbit_of_inM (inM_phase θ (inM_of_inOrbit h))

/-- The best phase: `‖s‖ = Re (e^{iθ} s)`. -/
theorem exists_phase (s : ℂ) : ∃ θ : ℝ, (Complex.exp (θ * Complex.I) * s).re = ‖s‖ := by
  refine ⟨-Complex.arg s, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I s
  have : Complex.exp (((-Complex.arg s : ℝ) : ℂ) * Complex.I) * s = (‖s‖ : ℂ) := by
    conv_lhs => rw [← h]
    rw [mul_left_comm, ← Complex.exp_add]
    push_cast
    simp
  rw [this]; simp

/-! ### The distance `d(ψ)` and `d² = 2 - 2√Φ` -/

/-- The Hilbert-space norm `‖φ‖ = √(Σ |φ_x|²)` (the ambient `Psi` carries the sup norm, which is not
meant). -/
noncomputable def hsNorm (φ : Psi) : ℝ := Real.sqrt (normSqPsi φ)

/-- `d(ψ) = min_{χ ∈ 𝓜} ‖ψ - χ‖`, as an infimum (attainment is `orbitDist_attained`). -/
noncomputable def orbitDist (ψ : Psi) : ℝ := sInf {r | ∃ χ, InM χ ∧ r = hsNorm (ψ - χ)}

theorem ip_norm_le_sqrt_Phi {ψ χ : Psi} (hψ : normSqPsi ψ = 1) (hχ : InOrbit χ) :
    ‖ip ψ χ‖ ≤ Real.sqrt (Phi ψ) := by
  refine Real.le_sqrt_of_sq_le ?_
  rw [← Complex.normSq_eq_norm_sq]
  exact le_Phi hψ hχ

/-- The minimum of `‖ψ - χ‖²` over `𝓜` equals `2 - 2√Φ`: lower bound for every `χ ∈ 𝓜`. -/
theorem two_sub_sqrt_Phi_le {ψ χ : Psi} (hψ : normSqPsi ψ = 1) (hχ : InOrbit χ) :
    2 - 2 * Real.sqrt (Phi ψ) ≤ normSqPsi (ψ - χ) := by
  rw [normSqPsi_sub_eq hψ (normSqPsi_InOrbit hχ)]
  have h1 := ip_norm_le_sqrt_Phi hψ hχ
  have h2 : (ip ψ χ).re ≤ ‖ip ψ χ‖ := Complex.re_le_norm _
  linarith

/-- A minimiser of `‖ψ - χ‖²` over the orbits has value `2 - 2√Φ`. -/
theorem min_value {ψ χ₀ : Psi} (hψ : normSqPsi ψ = 1) (h0 : InOrbit χ₀)
    (hmin : ∀ χ, InOrbit χ → normSqPsi (ψ - χ₀) ≤ normSqPsi (ψ - χ)) :
    normSqPsi (ψ - χ₀) = 2 - 2 * Real.sqrt (Phi ψ) := by
  refine le_antisymm ?_ (two_sub_sqrt_Phi_le hψ h0)
  set m₀ := normSqPsi (ψ - χ₀) with hm₀
  have hB : ∀ χ, InOrbit χ → ‖ip ψ χ‖ ≤ (2 - m₀) / 2 := by
    intro χ hχ
    obtain ⟨θ, hθ⟩ := exists_phase (ip ψ χ)
    have hχ' := inOrbit_phase θ hχ
    have h := hmin _ hχ'
    rw [normSqPsi_sub_eq hψ (normSqPsi_InOrbit hχ'), ip_smul_right, hθ] at h
    linarith
  have hB0 : 0 ≤ (2 - m₀) / 2 := le_trans (norm_nonneg _) (hB M4 InOrbit_M4)
  have hΦ : Phi ψ ≤ ((2 - m₀) / 2) ^ 2 := by
    refine csSup_le ⟨_, M4, InOrbit_M4, rfl⟩ ?_
    rintro _ ⟨χ, hχ, rfl⟩
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB χ hχ) 2
  have : Real.sqrt (Phi ψ) ≤ (2 - m₀) / 2 := Real.sqrt_le_iff.2 ⟨hB0, hΦ⟩
  linarith

/-- **Attainment.** For a unit `ψ` there is `χ₀ ∈ 𝓜` (a closest point) with
`‖ψ - χ₀‖² = 2 - 2√Φ(ψ) ≤ ‖ψ - χ‖²` for all `χ ∈ 𝓜`; `𝓜` is compact. -/
theorem exists_closest {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    ∃ χ₀, InM χ₀ ∧ normSqPsi (ψ - χ₀) = 2 - 2 * Real.sqrt (Phi ψ) ∧
      ∀ χ, InM χ → normSqPsi (ψ - χ₀) ≤ normSqPsi (ψ - χ) := by
  obtain ⟨χ₀, hχ₀, hmin⟩ := isCompact_orbit.exists_isMinOn ⟨M4, InOrbit_M4⟩
    (continuous_normSqPsi_sub ψ).continuousOn
  have hmin' : ∀ χ, InOrbit χ → normSqPsi (ψ - χ₀) ≤ normSqPsi (ψ - χ) := fun χ hχ => hmin hχ
  refine ⟨χ₀, inM_of_inOrbit hχ₀, min_value hψ hχ₀ hmin', fun χ hχ => hmin' χ (inOrbit_of_inM hχ)⟩

/-- `Φ(ψ) = max_{χ ∈ 𝓜} |⟨ψ, χ⟩|²` is attained (compactness). -/
theorem Phi_attained {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    ∃ χ, InM χ ∧ Complex.normSq (ip ψ χ) = Phi ψ ∧ ∀ χ', InM χ' → Complex.normSq (ip ψ χ') ≤ Phi ψ := by
  obtain ⟨χ₀, h0, hv, -⟩ := exists_closest hψ
  have ho := inOrbit_of_inM h0
  rw [normSqPsi_sub_eq hψ (normSqPsi_InOrbit ho)] at hv
  have h1 := ip_norm_le_sqrt_Phi hψ ho
  have h2 : (ip ψ χ₀).re ≤ ‖ip ψ χ₀‖ := Complex.re_le_norm _
  have h3 : ‖ip ψ χ₀‖ = Real.sqrt (Phi ψ) := by linarith
  refine ⟨χ₀, h0, ?_, fun χ' hχ' => le_Phi hψ (inOrbit_of_inM hχ')⟩
  rw [Complex.normSq_eq_norm_sq, h3]
  exact Real.sq_sqrt (le_trans (Complex.normSq_nonneg _) (le_Phi hψ InOrbit_M4))

theorem isLeast_of_closest {ψ χ₀ : Psi} (h0 : InM χ₀)
    (hmin : ∀ χ, InM χ → normSqPsi (ψ - χ₀) ≤ normSqPsi (ψ - χ)) :
    IsLeast {r | ∃ χ, InM χ ∧ r = hsNorm (ψ - χ)} (hsNorm (ψ - χ₀)) := by
  refine ⟨⟨χ₀, h0, rfl⟩, ?_⟩
  rintro _ ⟨χ, hχ, rfl⟩
  exact Real.sqrt_le_sqrt (hmin χ hχ)

/-- **`d(ψ) = min_{χ ∈ 𝓜} ‖ψ - χ‖` is attained.** -/
theorem orbitDist_attained {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    ∃ χ₀, InM χ₀ ∧ orbitDist ψ = hsNorm (ψ - χ₀) ∧ ∀ χ, InM χ → orbitDist ψ ≤ hsNorm (ψ - χ) := by
  obtain ⟨χ₀, h0, -, hmin⟩ := exists_closest hψ
  have hl := isLeast_of_closest h0 hmin
  refine ⟨χ₀, h0, hl.csInf_eq, fun χ hχ => ?_⟩
  unfold orbitDist; rw [hl.csInf_eq]; exact hl.2 ⟨χ, hχ, rfl⟩

/-- **`d(ψ)² = 2 - 2√Φ(ψ)`**, where `d` is the genuine Hilbert-space distance to `𝓜`
(`lu_orbit_stability.tex`, definition of `d`). -/
theorem orbitDist_sq {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    orbitDist ψ ^ 2 = 2 - 2 * Real.sqrt (Phi ψ) := by
  obtain ⟨χ₀, h0, hv, hmin⟩ := exists_closest hψ
  have hl := isLeast_of_closest h0 hmin
  have : orbitDist ψ = hsNorm (ψ - χ₀) := hl.csInf_eq
  rw [this, hsNorm, Real.sq_sqrt (normSqPsi_nonneg' _), hv]

theorem orbitDist_sq_eq_dist2 {ψ : Psi} (hψ : normSqPsi ψ = 1) : orbitDist ψ ^ 2 = dist2 ψ :=
  orbitDist_sq hψ

theorem orbitDist_nonneg (ψ : Psi) : 0 ≤ orbitDist ψ :=
  Real.sInf_nonneg (by rintro _ ⟨χ, -, rfl⟩; exact Real.sqrt_nonneg _)

/-! ### The orbit-stability estimates in terms of the genuine `d(ψ)²` -/

/-- **Named hypothesis: the global overlap comparison** `Q ≥ 1 - Φ`, the first inequality of
`thm:fqe-global-overlap` (exact rational certificate GO-1--GO-3 in the paper; **not proved in
Lean**). -/
def GlobalOverlap (ψ : Psi) : Prop := 1 - Phi ψ ≤ sexticQ ψ

/-- **Named hypothesis: the HS fidelity floor** `Φ ≥ 1/6` (`lem:fqe-hs-fidelity-floor`, the weakened
form of `Φ ≥ (1+√τ)/6`; **not proved in Lean** for general states -- for critical states it follows
from `Phi_ge_quarter`).  Equivalently `d² ≤ 2(1 - 1/√6)`. -/
def FidelityFloor (ψ : Psi) : Prop := 1 / 6 ≤ Phi ψ

theorem fidelityFloor_of_critical {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    FidelityFloor ψ := le_trans (by norm_num) (Phi_ge_quarter hψ hW)

/-- `FidelityFloor` is the paper's `d² ≤ 2(1 - 1/√6)`. -/
theorem orbitDist_sq_le_of_floor {ψ : Psi} (hψ : normSqPsi ψ = 1) (hf : FidelityFloor ψ) :
    orbitDist ψ ^ 2 ≤ 2 * (1 - 1 / Real.sqrt 6) := by
  rw [orbitDist_sq hψ]
  have : 1 / Real.sqrt 6 ≤ Real.sqrt (Phi ψ) := by
    rw [one_div, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by have h : 1 / 6 ≤ Phi ψ := hf; rwa [one_div] at h)
  linarith

theorem sqrt6_div_six_le {ψ : Psi} (hf : FidelityFloor ψ) : Real.sqrt 6 / 6 ≤ Real.sqrt (Phi ψ) := by
  have hf' : 1 / 6 ≤ Phi ψ := hf
  apply Real.le_sqrt_of_sq_le
  have : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h : (Real.sqrt 6 / 6) ^ 2 = 1 / 6 := by rw [div_pow, this]; norm_num
  rw [h]; exact hf

/-- The identity `1 - Φ = ((1 + √Φ)/2) d²` and the resulting
`((6+√6)/12) d² ≤ 1 - Φ` (the middle inequalities of `eq:fqe-global-overlap-sharp`). -/
theorem one_sub_Phi_eq {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    1 - Phi ψ = (1 + Real.sqrt (Phi ψ)) / 2 * orbitDist ψ ^ 2 := by
  have hΦ : 0 ≤ Phi ψ := le_trans (Complex.normSq_nonneg _) (le_Phi hψ InOrbit_M4)
  have := Real.sq_sqrt hΦ
  rw [orbitDist_sq hψ]; nlinarith

theorem overlap_ge_dist {ψ : Psi} (hψ : normSqPsi ψ = 1) (hf : FidelityFloor ψ) :
    (6 + Real.sqrt 6) / 12 * orbitDist ψ ^ 2 ≤ 1 - Phi ψ := by
  rw [one_sub_Phi_eq hψ]
  have h1 := sqrt6_div_six_le hf
  refine mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- **`thm:fqe-global-overlap`, distance consequences** (given its comparison `Q ≥ 1 - Φ` and the
fidelity floor): `Q ≥ ((6+√6)/12) d²`, i.e. `d² ≤ (12/(6+√6)) Q`, with `(6+√6)/12 > 7/10`. -/
theorem orbitDist_sq_le_Q {ψ : Psi} (hψ : normSqPsi ψ = 1) (hg : GlobalOverlap ψ)
    (hf : FidelityFloor ψ) :
    (6 + Real.sqrt 6) / 12 * orbitDist ψ ^ 2 ≤ sexticQ ψ ∧
      orbitDist ψ ^ 2 ≤ 12 / (6 + Real.sqrt 6) * sexticQ ψ ∧ 7 / 10 < (6 + Real.sqrt 6) / 12 := by
  have h := le_trans (overlap_ge_dist hψ hf) hg
  have hpos : 0 < 6 + Real.sqrt 6 := by positivity
  refine ⟨h, ?_, orbit_const_gt⟩
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith

/-- **`thm:fqe-orbit-stability`** (global part), in terms of the genuine distance
`d(ψ) = min_{χ ∈ 𝓜} ‖ψ - χ‖`: for every unit state with the overlap comparison `Q ≥ 1 - Φ`
(`thm:fqe-global-overlap`, hypothesis `hg`) and the fidelity floor (hypothesis `hf`),
`δ(ψ) = 1 + ½ log₂ 3 - E(ψ) ≥ k ((6+√6)/12) d(ψ)²` with `k((6+√6)/12) > 1/20`, so `δ ≥ d²/20`;
also `d² ≤ (12/(6+√6)) Q`. -/
theorem entropy_gap_orbit_stability_dist {ψ : Psi} (hψ : normSqPsi ψ = 1) (hg : GlobalOverlap ψ)
    (hf : FidelityFloor ψ) :
    orbitDist ψ ^ 2 ≤ 12 / (6 + Real.sqrt 6) * sexticQ ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) * ((6 + Real.sqrt 6) / 12 * orbitDist ψ ^ 2)
        ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ ∧
      1 / 20 < (Real.log 3 - 1) / (2 * Real.log 2) * ((6 + Real.sqrt 6) / 12) ∧
      1 / 20 * orbitDist ψ ^ 2 ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ := by
  obtain ⟨hQ, hd, -⟩ := orbitDist_sq_le_Q hψ hg hf
  obtain ⟨h1, h2, h3⟩ := entropy_gap_orbit_stability ψ hψ (sq_nonneg _) hQ
  rw [meanEntropy_M4] at h1 h3
  exact ⟨hd, h1, h2, h3⟩

/-- **`cor:fqe-orbit-spectral`** (global constant `c_O = (6+√6)/12`), genuine `d`:
for `a ≥ 0`, `α = -b - 17a/12 ≥ 0`,
`E_f(M₄) - E_f(ψ) ≥ (c_O/3) min(α/6, a/12) d(ψ)²`. -/
theorem majorant_gap_orbit {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d)
    (ha : 0 ≤ a) (hα : 0 ≤ -b - 17 * a / 12) {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (hg : GlobalOverlap ψ) (hf : FidelityFloor ψ) :
    (6 + Real.sqrt 6) / 12 / 3 * min ((-b - 17 * a / 12) / 6) (a / 12) * orbitDist ψ ^ 2 ≤
      meanSpec f M4 - meanSpec f ψ := by
  have h := majorant_gap_of_overlap hM ha hα ψ hψ (orbitDist_sq_le_Q hψ hg hf).1
  linarith

/-- The Tsallis case of `cor:fqe-orbit-spectral`, `0 < q < 2`, `q ≠ 1`, genuine `d`. -/
theorem tsallis_gap_orbit {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) {ψ : Psi}
    (hψ : normSqPsi ψ = 1) (hg : GlobalOverlap ψ) (hf : FidelityFloor ψ) :
    0 < min ((-tsB q - 17 * tsA q / 12) / 6) (tsA q / 12) ∧
    (6 + Real.sqrt 6) / 12 / 3 * min ((-tsB q - 17 * tsA q / 12) / 6) (tsA q / 12) *
        orbitDist ψ ^ 2 ≤ tsallisCeiling q - meanTsallis q ψ := by
  obtain ⟨hp, h⟩ := tsallis_gap_of_overlap h0 h2 h1 ψ hψ (orbitDist_sq_le_Q hψ hg hf).1
  exact ⟨hp, by linarith⟩

/-! ### Critical states: the same statements with genuine `d` -/

/-- `thm:fqe-critical-orbit-sharp`, with the genuine distance in place of `dist2`
(`dist2 = d²` is `orbitDist_sq_eq_dist2`).  The only hypothesis is the global overlap comparison for
`Φ ≥ 1/2`. -/
theorem critical_orbit_sharp_dist {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) ≤ sexticQ ψ ∧
    (2 + Real.sqrt 2) / 4 * orbitDist ψ ^ 2 ≤ sexticQ ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) *
        (max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) *
        ((2 + Real.sqrt 2) / 4 * orbitDist ψ ^ 2 + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ := by
  have h := critical_orbit_sharp hψ hW hglob
  rw [meanEntropy_M4] at h
  rw [orbitDist_sq_eq_dist2 hψ]
  exact h

/-- **`cor:fqe-orbit-spectral`, critical states** (`c_O` replaced by `(2+√2)/4`), genuine `d`. -/
theorem majorant_gap_orbit_critical {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d)
    (ha : 0 ≤ a) (hα : 0 ≤ -b - 17 * a / 12) {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (hW : blochSq ψ = 0) (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    (2 + Real.sqrt 2) / 4 / 3 * min ((-b - 17 * a / 12) / 6) (a / 12) * orbitDist ψ ^ 2 ≤
      meanSpec f M4 - meanSpec f ψ := by
  have hQ : (2 + Real.sqrt 2) / 4 * orbitDist ψ ^ 2 ≤ sexticQ ψ := by
    rw [orbitDist_sq_eq_dist2 hψ]; exact critical_distance hψ hW hglob
  have h := majorant_gap_of_overlap hM ha hα ψ hψ hQ
  linarith

/-- Critical entropy stability, with `d` genuine and the floor discharged. -/
theorem entropy_gap_critical_orbit {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    (Real.log 3 - 1) / (2 * Real.log 2) * ((2 + Real.sqrt 2) / 4 * orbitDist ψ ^ 2)
      ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ := by
  have h := (critical_orbit_sharp_dist hψ hW hglob).2.2.2
  have hk := entropy_coeff_pos
  have : 0 ≤ Complex.normSq (spinFlipForm ψ) := Complex.normSq_nonneg _
  nlinarith [mul_nonneg hk.le this]

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.OD.inM_iff_inOrbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inM_iff_inOrbit

/-- info: 'FormalResearch.FourQubitEntropy.OD.orbitDist_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitDist_attained

/-- info: 'FormalResearch.FourQubitEntropy.OD.Phi_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi_attained

/-- info: 'FormalResearch.FourQubitEntropy.OD.orbitDist_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitDist_sq

/-- info: 'FormalResearch.FourQubitEntropy.OD.entropy_gap_orbit_stability_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_gap_orbit_stability_dist

/-- info: 'FormalResearch.FourQubitEntropy.OD.majorant_gap_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms majorant_gap_orbit

/-- info: 'FormalResearch.FourQubitEntropy.OD.tsallis_gap_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tsallis_gap_orbit

/-- info: 'FormalResearch.FourQubitEntropy.OD.critical_orbit_sharp_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms critical_orbit_sharp_dist

/-- info: 'FormalResearch.FourQubitEntropy.OD.majorant_gap_orbit_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms majorant_gap_orbit_critical

end FormalResearch.FourQubitEntropy.OD
