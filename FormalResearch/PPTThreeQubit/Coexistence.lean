module

public import FormalResearch.PPTThreeQubit.FamilyGME

/-!
# One support, both phases: `thm:ppt3-phase-coexistence` and `prop:ppt3-exposed-transition`

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/phase_coexistence.tex`
(`thm:ppt3-phase-coexistence`, `eq:ppt3-bs-same-support`, `prop:ppt3-exposed-transition`,
`eq:ppt3-exposed-state`, `eq:ppt3-exact-phase-line`), with `B = B_1`, `q_1`, `H_5` of `family.tex`.

Notation.  For `z : ℂ` let `N(z) = ‖B q_1(z)‖²` (`Nrm`).  The cut-product mixture of the paper is
`Γ_z = (1/6) ∑_{j=0}^2 ∑_{ε=±1} Π^j |p_{εz}⟩⟨p_{εz}| Π^{-j}` with `p_z = B q_1(z)/‖B q_1(z)‖`; here
`Gam z` is this operator, the cyclic images `Π^j B q_1(εz)` being written as `B (phase_j ⊙ q_1(εz))`
(the coordinate phases `(1,1,1,ω,ω)`, `(1,1,1,ω²,ω²)` of `Witness.lean`).  `Gc z` is its
coefficient matrix: `Γ_z = B Gc(z) B†`.

Covered (all proved, exact algebra over `ℂ`; no numerics):
* `σ_BS = B X_BS B†` (`eq:ppt3-bs-same-support`) equals `(1/3)(|111⟩⟨111| + Γ_2 + Γ_{2i})` and is
  biseparable (`sigmaBS_biseparable`), has trace one, while `ρ_{10/3}` (same support) is GME
  (`ppt3_coexistence_core`).
* `σ_∂ = B X_∂ B†` (`eq:ppt3-exposed-state`) equals `(1/5)Γ_1 + (1/2)Γ_i + (3/10)Γ_{i√5}`, is
  biseparable with trace one and `tr(H_5 X_∂) = 0` (`sigma_exposed_core`).
* The line `σ(t) = (1-t)σ_∂ + tσ_BS` is biseparable for `0 ≤ t ≤ 1` and GME for `-1/200 ≤ t < 0`
  (in fact for every `t < 0`), with `tr(H_5(X_∂ + tX_Δ)) = t·25082/54375`
  (`ppt3_exposed_transition`).

Not covered: strict positivity of the partial transposes (the Sylvester-minor tables and the
`‖Δ‖₂` perturbation bound; no partial-transpose definition is used here), positive definiteness
of `X_BS`, `X_∂`, the rank-five / rank-profile statements, and the relative-interior assertions of
`thm:ppt3-phase-coexistence`.  Consequently only the biseparable/GME and the `tr(H_5 ·)` parts of
the statements are formalised, not the clause that every state on the line is strictly PPT.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-! ### Closure properties of `IsBiseparable` and of cut-products -/

theorem IsProdA.smul {x : Fin 8 → ℂ} (h : IsProdA x) (c : ℂ) : IsProdA (c • x) := by
  obtain ⟨α, μ, hx⟩ := h
  exact ⟨c • α, μ, fun i => by simp [hx i, mul_assoc]⟩

theorem IsProdB.smul {x : Fin 8 → ℂ} (h : IsProdB x) (c : ℂ) : IsProdB (c • x) := by
  obtain ⟨α, μ, hx⟩ := h
  exact ⟨c • α, μ, fun i => by simp [hx i, mul_assoc]⟩

theorem IsProdC.smul {x : Fin 8 → ℂ} (h : IsProdC x) (c : ℂ) : IsProdC (c • x) := by
  obtain ⟨α, μ, hx⟩ := h
  exact ⟨c • α, μ, fun i => by simp [hx i, mul_assoc]⟩

theorem IsCutProduct.smul {x : Fin 8 → ℂ} (h : IsCutProduct x) (c : ℂ) :
    IsCutProduct (c • x) := by
  rcases h with h | h | h
  exacts [Or.inl (h.smul c), Or.inr (Or.inl (h.smul c)), Or.inr (Or.inr (h.smul c))]

/-- A rank-one operator on a cut-product vector is biseparable. -/
theorem isBiseparable_rankOne {x : Fin 8 → ℂ} (h : IsCutProduct x) :
    IsBiseparable (vecMulVec x (star x)) :=
  ⟨1, fun _ => x, fun _ => h, by simp⟩

theorem isBiseparable_zero : IsBiseparable (0 : Matrix (Fin 8) (Fin 8) ℂ) :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem IsBiseparable.add {ρ σ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : IsBiseparable ρ)
    (hσ : IsBiseparable σ) : IsBiseparable (ρ + σ) := by
  obtain ⟨n, φ, hφ, rfl⟩ := hρ
  obtain ⟨m, ψ, hψ, rfl⟩ := hσ
  refine ⟨n + m, Fin.append φ ψ, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hφ, hψ]
  · rw [Fin.sum_univ_add]; simp

/-- Nonnegative real multiples of biseparable operators are biseparable. -/
theorem IsBiseparable.smul_real {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : IsBiseparable ρ) {w : ℝ}
    (hw : 0 ≤ w) : IsBiseparable ((w : ℂ) • ρ) := by
  obtain ⟨n, φ, hφ, rfl⟩ := hρ
  refine ⟨n, fun i => ((Real.sqrt w : ℝ) : ℂ) • φ i, fun i => (hφ i).smul _, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a b
  have hs : star ((Real.sqrt w : ℝ) : ℂ) = ((Real.sqrt w : ℝ) : ℂ) := Complex.conj_ofReal _
  have h2 : ((Real.sqrt w : ℝ) : ℂ) * ((Real.sqrt w : ℝ) : ℂ) = (w : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw]
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul', hs,
    Matrix.smul_apply]
  linear_combination (-(φ i a * star (φ i b))) * h2

theorem IsBiseparable.sum {ι : Type*} (s : Finset ι) {f : ι → Matrix (Fin 8) (Fin 8) ℂ}
    (h : ∀ i ∈ s, IsBiseparable (f i)) : IsBiseparable (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsBiseparable (fun _ _ => IsBiseparable.add) isBiseparable_zero h

/-! ### Cyclic transport: from the cut `A|BC` to the cuts `B|AC`, `C|AB` -/

theorem prodA_cycC {y : Fin 8 → ℂ} (h : IsProdA y) : IsProdB (fun i => y (σC i)) := by
  obtain ⟨α, μ, hx⟩ := h
  refine ⟨α, fun j => μ ⟨2 * (j.val % 2) + j.val / 2, by omega⟩, fun i => ?_⟩
  fin_cases i <;> exact hx _

theorem prodA_cycB {y : Fin 8 → ℂ} (h : IsProdA y) : IsProdC (fun i => y (σB i)) := by
  obtain ⟨α, μ, hx⟩ := h
  refine ⟨α, μ, fun i => ?_⟩
  fin_cases i <;> exact hx _

/-- Phase multipliers: `ph 0 = 1`, `ph 1 = (1,1,1,ω,ω)`, `ph 2 = (1,1,1,ω²,ω²)`. -/
def ph : Fin 3 → Fin 5 → ℂ := ![fun _ => 1, phaseB, phaseC]

/-- If `B_s c` is an `A|BC`-product then every cyclic image `B_s (ph_j ⊙ c)` is a cut-product. -/
theorem cutProduct_cyc {s : ℝ} {c : Fin 5 → ℂ} (h : IsProdA (Bs s *ᵥ c)) (j : Fin 3) :
    IsCutProduct (Bs s *ᵥ fun a => ph j a * c a) := by
  fin_cases j
  · have e : (fun a => ph 0 a * c a) = c := by funext a; simp [ph]
    change IsCutProduct (Bs s *ᵥ fun a => ph 0 a * c a)
    rw [e]; exact Or.inl h
  · right; right
    have := prodA_cycB h
    rw [Bs_cycB] at this
    simpa [ph] using this
  · right; left
    have := prodA_cycC h
    rw [Bs_cycC] at this
    simpa [ph] using this

/-! ### The cut-product mixture `Γ_z` -/

/-- `ε`-sign: `sgn 0 = 1`, `sgn 1 = -1`. -/
def sgn : Fin 2 → ℂ := ![1, -1]

/-- The six coefficient vectors `ph_j ⊙ q_1(ε z)`, `j ∈ ℤ/3`, `ε = ±1`. -/
def cv (z : ℂ) (j : Fin 3) (ε : Fin 2) : Fin 5 → ℂ := fun a => ph j a * qs 1 (sgn ε * z) a

/-- `N(z) = ‖B q_1(z)‖²`. -/
def Nrm (z : ℂ) : ℝ := ∑ i, Complex.normSq ((Bs 1 *ᵥ qs 1 z) i)

theorem Nrm_nonneg (z : ℂ) : 0 ≤ Nrm z :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The six-term sum `∑_{j,ε} |ph_j ⊙ q_1(εz)⟩⟨…|` in coefficient space. -/
def sixSum (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  ∑ j, ∑ ε, vecMulVec (cv z j ε) (star (cv z j ε))

/-- The cyclic-parity average of `c c†`: only the blocks `{u}, {v,w}, {e}, {o}` survive. -/
def symAvg (c : Fin 5 → ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![c 0 * star (c 0), 0, 0, 0, 0;
     0, c 1 * star (c 1), c 1 * star (c 2), 0, 0;
     0, c 2 * star (c 1), c 2 * star (c 2), 0, 0;
     0, 0, 0, c 3 * star (c 3), 0;
     0, 0, 0, 0, c 4 * star (c 4)]

/-- Coefficient matrix `Gc z` of `Γ_z`. -/
def Gc (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  ((1 / (6 * Nrm z) : ℝ) : ℂ) • sixSum z

/-- The operator `Γ_z` of `thm:ppt3-phase-coexistence`. -/
def Gam (z : ℂ) : Matrix (Fin 8) (Fin 8) ℂ := Bs 1 * Gc z * (Bs 1)ᴴ

/-- Conjugation by `B` sends `|c⟩⟨c|` to `|Bc⟩⟨Bc|`. -/
theorem Bs_conj_vecMulVec (s : ℝ) (c : Fin 5 → ℂ) :
    Bs s * vecMulVec c (star c) * (Bs s)ᴴ = vecMulVec (Bs s *ᵥ c) (star (Bs s *ᵥ c)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- `Γ_z` is a normalised sum of cut-product rank-ones, hence biseparable. -/
theorem Gam_biseparable (z : ℂ) : IsBiseparable (Gam z) := by
  have h6 : Gam z = ((1 / (6 * Nrm z) : ℝ) : ℂ) •
      ∑ j, ∑ ε, vecMulVec (Bs 1 *ᵥ cv z j ε) (star (Bs 1 *ᵥ cv z j ε)) := by
    simp only [Gam, Gc, sixSum, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum,
      Matrix.sum_mul, Bs_conj_vecMulVec]
  rw [h6]
  refine IsBiseparable.smul_real (IsBiseparable.sum _ fun j _ => IsBiseparable.sum _ fun ε _ => ?_)
    (by have := Nrm_nonneg z; positivity)
  apply isBiseparable_rankOne
  exact cutProduct_cyc (prodA_of_qs 1 _) j

/-! ### The cyclic-parity average -/

theorem qs_neg (z : ℂ) : qs 1 (-z) = fun a => (![-1, 1, 1, -1, 1] : Fin 5 → ℂ) a * qs 1 z a := by
  funext a; fin_cases a <;> simp [qs]

theorem sixSum_eq (z : ℂ) : sixSum z = (6 : ℂ) • symAvg (qs 1 z) := by
  have hω := ω_sq_add_ω_add_one
  have hω2 : ω ^ 2 = -1 - ω := by linear_combination hω
  have hs : star ω = ω ^ 2 := star_ω
  have hs2 : star (ω ^ 2) = ω := by rw [star_pow, hs]; linear_combination ω * ω_cube
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sixSum, symAvg, cv, ph, sgn, phaseB, phaseC, Fin.sum_univ_three, Fin.sum_univ_two,
      vecMulVec_apply, qs_neg, hs, hs2] <;> (try ring_nf) <;> (try simp only [ω_cube, hω2]) <;> ring

theorem Gc_eq (z : ℂ) : Gc z = ((1 / Nrm z : ℝ) : ℂ) • symAvg (qs 1 z) := by
  unfold Gc
  rw [sixSum_eq, smul_smul]
  by_cases h : Nrm z = 0
  · simp [h]
  · congr 1
    push_cast
    field_simp

/-! ### Norms: `B†B = diag(4,1,3,3,3)` -/

/-- `‖B c‖² = 4|c₀|² + |c₁|² + 3(|c₂|² + |c₃|² + |c₄|²)`. -/
theorem normSq_Bs (c : Fin 5 → ℂ) :
    ∑ i, Complex.normSq ((Bs 1 *ᵥ c) i) =
      4 * Complex.normSq (c 0) + Complex.normSq (c 1) +
        3 * (Complex.normSq (c 2) + Complex.normSq (c 3) + Complex.normSq (c 4)) := by
  have hω := ω_sq_add_ω_add_one
  have hω2 : ω ^ 2 = -1 - ω := by linear_combination hω
  have hs : (starRingEnd ℂ) ω = ω ^ 2 := star_ω
  have hs2 : (starRingEnd ℂ) (ω ^ 2) = ω := by
    rw [map_pow, hs]; linear_combination ω * ω_cube
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj, Fin.sum_univ_eight, Bs_mulVec]
  simp [map_add, map_mul, map_neg, hs, hs2]
  ring_nf
  simp only [ω_cube, hω2]
  ring

theorem Nrm_eq (z : ℂ) :
    Nrm z = 4 * Complex.normSq (qs 1 z 0) + Complex.normSq (qs 1 z 1) +
      3 * (Complex.normSq (qs 1 z 2) + Complex.normSq (qs 1 z 3) + Complex.normSq (qs 1 z 4)) :=
  normSq_Bs _

/-! ### Explicit data -/

/-- `z = i√5` of `eq:ppt3-exposed-state`. -/
def z5 : ℂ := Complex.I * ((Real.sqrt 5 : ℝ) : ℂ)

theorem z5_sq : z5 ^ 2 = -5 := by
  have : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [z5, mul_pow, this, Complex.I_sq]; norm_num

theorem qs_two : qs 1 2 = ![4, -28, 3, -10, 5] := by
  funext a; fin_cases a <;> simp [qs] <;> norm_num

theorem qs_two_I : qs 1 (2 * Complex.I) = ![4 * Complex.I, -4, -5, 6 * Complex.I, -3] := by
  funext a; fin_cases a <;> simp [qs, mul_pow] <;> norm_num <;> ring_nf

theorem qs_one : qs 1 1 = ![2, -4, 0, -2, 2] := by
  funext a; fin_cases a <;> simp [qs] <;> norm_num

theorem qs_I : qs 1 Complex.I = ![2 * Complex.I, 2, -2, 0, 0] := by
  funext a; fin_cases a <;> simp [qs] <;> norm_num

theorem qs_z5 : qs 1 z5 = ![2 * z5, -10, -6, 4 * z5, -4] := by
  funext a; fin_cases a <;> simp [qs, z5_sq] <;> norm_num; ring

theorem normSq_z5 : Complex.normSq z5 = 5 := by
  simp [z5, Complex.normSq_mul]

theorem Nrm_two : Nrm 2 = 1250 := by
  rw [Nrm_eq, qs_two]; simp [Complex.normSq_apply]; norm_num

theorem Nrm_two_I : Nrm (2 * Complex.I) = 290 := by
  rw [Nrm_eq, qs_two_I]; simp [Complex.normSq_apply]; norm_num

theorem Nrm_one : Nrm 1 = 56 := by
  rw [Nrm_eq, qs_one]; simp [Complex.normSq_apply]; norm_num

theorem Nrm_I : Nrm Complex.I = 32 := by
  rw [Nrm_eq, qs_I]; simp [Complex.normSq_apply]; norm_num

theorem Nrm_z5 : Nrm z5 = 576 := by
  rw [Nrm_eq, qs_z5]; simp [Complex.normSq_mul, normSq_z5]; norm_num

/-- `X_BS` of `eq:ppt3-bs-same-support`. -/
def XBS : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 54375 : ℂ) • !![1232, 0, 0, 0, 0; 0, 30493, 32, 0, 0; 0, 32, 1693, 0, 0;
    0, 0, 0, 3700, 0; 0, 0, 0, 0, 925]

/-- `X_∂` of `eq:ppt3-exposed-state`. -/
def Xd : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 3360 : ℂ) • !![293, 0, 0, 0, 0; 0, 577, -105, 0, 0; 0, -105, 273, 0, 0;
    0, 0, 0, 188, 0; 0, 0, 0, 0, 76]

/-- The coefficient matrix `|e_v⟩⟨e_v|` of `|111⟩⟨111|`. -/
def Evv : Matrix (Fin 5) (Fin 5) ℂ := vecMulVec (Pi.single 1 1) (star (Pi.single 1 1))

theorem XBS_eq : XBS = (1 / 3 : ℂ) • (Evv + Gc 2 + Gc (2 * Complex.I)) := by
  rw [Gc_eq, Gc_eq, Nrm_two, Nrm_two_I, qs_two, qs_two_I]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [XBS, Evv, symAvg, vecMulVec_apply, Complex.ext_iff] <;> norm_num

theorem Xd_eq : Xd = (1 / 5 : ℂ) • Gc 1 + (1 / 2 : ℂ) • Gc Complex.I + (3 / 10 : ℂ) • Gc z5 := by
  have hz5 : z5.re * z5.re + z5.im * z5.im = 5 := by
    simpa [Complex.normSq_apply] using normSq_z5
  rw [Gc_eq, Gc_eq, Gc_eq, Nrm_one, Nrm_I, Nrm_z5, qs_one, qs_I, qs_z5]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Xd, symAvg, Complex.ext_iff] <;> norm_num <;> (try constructor) <;> nlinarith [hz5]

/-! ### The states `σ_BS`, `σ_∂` -/

/-- `σ_BS = B X_BS B†` (`eq:ppt3-bs-same-support`). -/
def sigmaBS : Matrix (Fin 8) (Fin 8) ℂ := Bs 1 * XBS * (Bs 1)ᴴ

/-- `σ_∂ = B X_∂ B†` (`eq:ppt3-exposed-state`). -/
def sigmaD : Matrix (Fin 8) (Fin 8) ℂ := Bs 1 * Xd * (Bs 1)ᴴ

/-- `|111⟩⟨111|` as `B |e_v⟩⟨e_v| B†`. -/
theorem Bs_Evv : Bs 1 * Evv * (Bs 1)ᴴ = vecMulVec vVec (star vVec) := by
  have : Bs 1 *ᵥ (Pi.single 1 1 : Fin 5 → ℂ) = vVec := by
    ext i; fin_cases i <;> simp [Bs, bCols, mulVec, dotProduct, Pi.single_apply,
      uVec, vVec, wVec, eVec, oVec]
  rw [Evv, Bs_conj_vecMulVec, this]

theorem isBiseparable_vVec : IsBiseparable (vecMulVec vVec (star vVec)) := by
  apply isBiseparable_rankOne
  have := prodA_of_v 1
  have e : Bs 1 *ᵥ (Pi.single 1 1 : Fin 5 → ℂ) = vVec := by
    ext i; fin_cases i <;> simp [Bs, bCols, mulVec, dotProduct, Pi.single_apply,
      uVec, vVec, wVec, eVec, oVec]
  rw [e] at this
  exact Or.inl this

theorem isBiseparable_of_smul {w : ℝ} (hw : 0 ≤ w) {ρ σ : Matrix (Fin 8) (Fin 8) ℂ}
    (h : IsBiseparable ρ) (e : σ = (w : ℂ) • ρ) : IsBiseparable σ := e ▸ h.smul_real hw

/-- `σ_BS = (1/3)(|111⟩⟨111| + Γ_2 + Γ_{2i})` (proof of `thm:ppt3-phase-coexistence`). -/
theorem sigmaBS_decomp :
    sigmaBS = (1 / 3 : ℂ) • (vecMulVec vVec (star vVec) + Gam 2 + Gam (2 * Complex.I)) := by
  rw [sigmaBS, XBS_eq, ← Bs_Evv]
  simp only [Gam, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

/-- `σ_∂ = (1/5)Γ_1 + (1/2)Γ_i + (3/10)Γ_{i√5}` (`eq:ppt3-exposed-state`). -/
theorem sigmaD_decomp :
    sigmaD = (1 / 5 : ℂ) • Gam 1 + (1 / 2 : ℂ) • Gam Complex.I + (3 / 10 : ℂ) • Gam z5 := by
  rw [sigmaD, Xd_eq]
  simp only [Gam, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

theorem sigmaBS_biseparable : IsBiseparable sigmaBS := by
  have h := (isBiseparable_vVec.add (Gam_biseparable 2)).add (Gam_biseparable (2 * Complex.I))
  have h' := h.smul_real (w := 1 / 3) (by norm_num)
  rw [sigmaBS_decomp]
  push_cast at h'
  exact h'

theorem sigmaD_biseparable : IsBiseparable sigmaD := by
  rw [sigmaD_decomp]
  refine IsBiseparable.add (IsBiseparable.add ?_ ?_) ?_
  · exact isBiseparable_of_smul (w := 1 / 5) (by norm_num) (Gam_biseparable 1) (by push_cast; rfl)
  · exact isBiseparable_of_smul (w := 1 / 2) (by norm_num) (Gam_biseparable _) (by push_cast; rfl)
  · exact isBiseparable_of_smul (w := 3 / 10) (by norm_num) (Gam_biseparable _) (by push_cast; rfl)

/-! ### Traces -/

theorem BsH_mul_Bs : (Bs 1)ᴴ * Bs 1 = Matrix.diagonal ![4, 1, 3, 3, 3] := by
  have hω := ω_sq_add_ω_add_one
  have hω2 : ω ^ 2 = -1 - ω := by linear_combination hω
  have hs : star ω = ω ^ 2 := star_ω
  have hs2 : star (ω ^ 2) = ω := by rw [star_pow, hs]; linear_combination ω * ω_cube
  have hs' : (starRingEnd ℂ) ω = ω ^ 2 := hs
  have hs2' : (starRingEnd ℂ) (ω ^ 2) = ω := hs2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_eight, Bs, bCols, uVec, vVec, wVec,
      eVec, oVec, hs', hs2'] <;> (try ring_nf) <;>
    (try simp only [ω_cube, hω2]) <;> ring

theorem trace_BXBH (X : Matrix (Fin 5) (Fin 5) ℂ) :
    (Bs 1 * X * (Bs 1)ᴴ).trace = 4 * X 0 0 + X 1 1 + 3 * (X 2 2 + X 3 3 + X 4 4) := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, BsH_mul_Bs]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_five, Matrix.diagonal_mul]
  ring

theorem trace_sigmaBS : sigmaBS.trace = 1 := by
  rw [sigmaBS, trace_BXBH]; simp [XBS]; norm_num

theorem trace_sigmaD : sigmaD.trace = 1 := by
  rw [sigmaD, trace_BXBH]; simp [Xd]; norm_num

/-- `tr(H_5 X_BS) = 25082/54375`. -/
theorem trace_H5_XBS : (Hs 1 * XBS).trace = ((25082 / 54375 : ℝ) : ℂ) := by
  simp [Hs, XBS, Matrix.trace, Matrix.diag, Fin.sum_univ_five, hDiag, Matrix.diagonal_mul]
  norm_num

/-- `tr(H_5 X_∂) = 0`. -/
theorem trace_H5_Xd : (Hs 1 * Xd).trace = 0 := by
  simp [Hs, Xd, Matrix.trace, Matrix.diag, Fin.sum_univ_five, hDiag, Matrix.diagonal_mul]
  norm_num

/-- `tr ρ_t = 1` for `t + 3 ≠ 0`. -/
theorem trace_rhoT (t : ℝ) (ht : t + 3 ≠ 0) : (rhoT t).trace = 1 := by
  rw [rhoT, trace_BXBH]
  have h : (t : ℂ) + 3 ≠ 0 := by exact_mod_cast ht
  simp [Xt]
  field_simp
  ring

/-- **`thm:ppt3-phase-coexistence`** (biseparable and GME states on the support `R = ran B`).
`σ_BS = B X_BS B†` with `X_BS` of `eq:ppt3-bs-same-support` is a trace-one biseparable state,
equal to `(1/3)(|111⟩⟨111| + Γ_2 + Γ_{2i})`, while `ρ_{10/3} = B X_{10/3} B†` (the GME member of
`thm:ppt3-family`) is a trace-one GME state with the same support.  Not covered: the strict
positivity of the partial transposes, the rank statements and the relative interiors. -/
theorem ppt3_phase_coexistence :
    sigmaBS = Bs 1 * XBS * (Bs 1)ᴴ ∧ rhoT (10 / 3) = Bs 1 * Xt (10 / 3) * (Bs 1)ᴴ ∧
    sigmaBS = (1 / 3 : ℂ) • (vecMulVec vVec (star vVec) + Gam 2 + Gam (2 * Complex.I)) ∧
    sigmaBS.trace = 1 ∧ (rhoT (10 / 3)).trace = 1 ∧
    IsBiseparable sigmaBS ∧ IsGME (rhoT (10 / 3)) :=
  ⟨rfl, rfl, sigmaBS_decomp, trace_sigmaBS, trace_rhoT _ (by norm_num), sigmaBS_biseparable,
    ppt3_family_gme _ (by norm_num)⟩

/-- Part of **`prop:ppt3-exposed-transition`**: `σ_∂ = B X_∂ B†` of `eq:ppt3-exposed-state` is the
stated mixture of the `Γ_z`, is a trace-one biseparable state, and `tr(H_5 X_∂) = 0`. -/
theorem ppt3_exposed_state :
    sigmaD = Bs 1 * Xd * (Bs 1)ᴴ ∧
    sigmaD = (1 / 5 : ℂ) • Gam 1 + (1 / 2 : ℂ) • Gam Complex.I + (3 / 10 : ℂ) • Gam z5 ∧
    sigmaD.trace = 1 ∧ IsBiseparable sigmaD ∧ (Hs 1 * Xd).trace = 0 :=
  ⟨rfl, sigmaD_decomp, trace_sigmaD, sigmaD_biseparable, trace_H5_Xd⟩

/-! ### The exact phase line -/

/-- `σ(t) = (1-t)σ_∂ + tσ_BS` of `eq:ppt3-exact-phase-line`. -/
def sigmaLine (t : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  ((1 - t : ℝ) : ℂ) • sigmaD + (t : ℂ) • sigmaBS

/-- Coefficient matrix `X_∂ + t X_Δ = (1-t)X_∂ + tX_BS` of `σ(t)`. -/
def Xline (t : ℝ) : Matrix (Fin 5) (Fin 5) ℂ := ((1 - t : ℝ) : ℂ) • Xd + (t : ℂ) • XBS

theorem sigmaLine_eq (t : ℝ) : sigmaLine t = Bs 1 * Xline t * (Bs 1)ᴴ := by
  simp only [sigmaLine, Xline, sigmaD, sigmaBS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]

theorem trace_sigmaLine (t : ℝ) : (sigmaLine t).trace = 1 := by
  rw [sigmaLine, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace_sigmaD,
    trace_sigmaBS]
  simp

/-- `tr(H_5 (X_∂ + t X_Δ)) = t · 25082/54375`. -/
theorem trace_H5_Xline (t : ℝ) : (Hs 1 * Xline t).trace = ((t * (25082 / 54375) : ℝ) : ℂ) := by
  rw [Xline, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, trace_H5_Xd, trace_H5_XBS]
  push_cast; ring

/-- **`prop:ppt3-exposed-transition`** (biseparable/GME dichotomy along the line).  Along
`σ(t) = (1-t)σ_∂ + tσ_BS`, `σ(t)` is a trace-one operator `B (X_∂ + tX_Δ) B†` with
`tr(H_5(X_∂ + tX_Δ)) = t·25082/54375`, biseparable for `0 ≤ t ≤ 1` and GME for
`-1/200 ≤ t < 0` (the proof of GME uses only `t < 0`).  Not covered: strict positivity of the
partial transposes and of `X_∂ + tX_Δ` along the line. -/
theorem ppt3_exposed_transition :
    (∀ t : ℝ, (sigmaLine t).trace = 1 ∧ sigmaLine t = Bs 1 * Xline t * (Bs 1)ᴴ ∧
      (Hs 1 * Xline t).trace = ((t * (25082 / 54375) : ℝ) : ℂ)) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → IsBiseparable (sigmaLine t)) ∧
    (∀ t : ℝ, -1 / 200 ≤ t → t < 0 → IsGME (sigmaLine t)) := by
  refine ⟨fun t => ⟨trace_sigmaLine t, sigmaLine_eq t, trace_H5_Xline t⟩, ?_, ?_⟩
  · intro t h0 h1
    exact (sigmaD_biseparable.smul_real (by linarith)).add (sigmaBS_biseparable.smul_real h0)
  · intro t _ ht hb
    rw [sigmaLine_eq] at hb
    have h := trace_Hs_nonneg_of_biseparable (s := 1) one_pos (Xline t) hb
    rw [trace_H5_Xline, Complex.ofReal_re] at h
    nlinarith

end

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_phase_coexistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_phase_coexistence

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_exposed_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_exposed_state

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_exposed_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_exposed_transition

end FormalResearch.PPTThreeQubit
