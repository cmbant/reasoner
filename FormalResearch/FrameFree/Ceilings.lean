import FormalResearch.FrameFree.Foundations
import FormalResearch.FourQubitEntropy.Attainment

/-!
# Ceilings on frame-free chirality (Paper P: `sec3_many_spins`, `sec7_outlook`, `app_a_toolkit`, `app_c_critical`, `app_f_depth_codes`)

Namespace `FormalResearch.FrameFree.Ceilings`.  It builds on `FrameFree.Foundations` (`Ψ n`, `rot`, `ip`,
`nsq`, `cj`, `Θ`, `FK`, `FKΘ`, `CK`, `tens`, `FKΘ_tens`, `CK_tens`, ...) and does not redefine them.  The
only other import is `FourQubitEntropy.Attainment` (for the vector `M₄`).

Claim classes follow `AGENTS.md`: everything below is **proved** (Lean, no admitted goals, no `ofReduceBool`-style tactics, no
new axioms) unless a hypothesis is displayed in the statement; the hypotheses are:

* `RealRep3` -- the Dur-Vidal-Cirac fact (recalled here; proved in `RealRep3Discharge`): every three-qubit vector is in the
  `GL(2,C)^3` orbit of a real vector.
* `h49 : FKΘ M4v = 4/9` -- `F_K(M₄) = 4/9`.  Its lower bound is proved in `FrameFree/PhysicalBridge.lean`
  (`four_ninths_le_rotOverlap_M4`); the upper bound is the recalled Weyl-vertex input R7 (`FKmag` is the
  rotation overlap).  It is not assumed silently: it is a hypothesis of each statement that uses it.
* `hle : FCΘ M4v ≤ 1/2` -- the heavy half of `thm:m4support` (not formalised).
* `hc : CK β = c3` -- attainment of `c₃ = sup C_K` on three qubits (computer-assisted in the paper).

## Contents

**Filter overlap `F_C`.** `FCset`, `FC`, `FCΘ` (supremum over `SL(2,C)^n` of the normalised overlap);
`le_FC_of_path` (limit principle), `peel_le_FC` (contracting one qubit with a unit bra cannot increase
`F_C(ψ,ψ̄)`; the limit filter `e eᵀ + s e' e'ᵀ`, `s → 0`), `FC_tens`, `FCΘ_tens` (`prop:mult`, filter part).

**`thm:ceiling` and `thm:entceiling`** (under `RealRep3`).  `FC_three_ge`, `entceiling_contract` (any
contraction of any `n-3` parties by any unit vectors: `F_C(ψ,ψ̄) ≥ ‖ψ_{e_S}‖²`), `ceiling_lmax`
(`F_C ≥ λmax(ρ_j)` on four qubits), `ceiling_half` (`F_C ≥ 1/2`), `FCΘ_eq_one_of_le_three`,
`FCΘ_ge_pow`, `FCΘ_ge_eight` (`F_C ≥ 8·2^{-n}`), `normSq_ip_pv_le_FCΘ`, `negLog_FC_le_EG`,
`negLog_FC_le_log2` (`-log F_C ≤ min(E_G, (n-3) log 2)`; the proved part of `prop:s3-geomconverse`).

**`prop:exponentdepth`.** (a) `negLog_FC_le_producible` (under `RealRep3`).  (b) `CK_le_producible_three`
(`C_K ≤ ⌊n/3⌋ c₃` for `3`-producible states, unconditional) and `exists_producible_three_attaining`
(sharpness, given `hc`).  Producibility is the inductive predicate `Producible m` (tensor products of unit
states on consecutive blocks of at most `m` qubits).

**`prop:phaseaverage` and `thm:chiralEG`.**  `ipr_le_FK_cj`, `ipr_rot_le_FKΘ` (`F_K ≥ Σ_x |ψ_x|⁴` in every
product basis), `Lam_sq_le_FKΘ` (`F_K ≥ Λ²`), `CK_le_two_EG` (`C_K ≤ 2 E_G`).  For an odd `k`-copy
observable (`OddObs`: Hermitian contraction `A` on `k` copies, `Ā = -A`, value invariant under local
unitaries): `OddObs.sq_le` (`|⟨ψ|uψ̄⟩|^{2k} ≤ 1 - a²`), `OddObs.FKΘ_pow_le` (`F_K^k ≤ 1 - a²`),
`OddObs.neg_log_le_CK` (`-(1/k) log(1-a²) ≤ C_K`), `OddObs.chiralEG_chain`
(`-(1/2k) log(1-a²) ≤ C_K/2 ≤ E_G`).  Local-unitary invariance of the value is a field of `OddObs`
(it is the consequence `a(uφ) = a(φ)` of `[A, u^{⊗k}] = 0`).

**`thm:chiraldepth` (a).**  `svd_lite` (Schmidt decomposition in the form `U₀ M̄ U₁ᵀ = μ M`, via the
Hermitian spectral theorem), `FKΘ_eq_one_of_le_two` (`F_K = 1` for one or two qubits),
`Producible.FKΘ_eq_one`, `not_producible_two_of_FKΘ_lt_one`, `OddObs.FKΘ_lt_one`,
`OddObs.not_producible_two` (`a(ψ) ≠ 0` implies `ψ` is not `2`-producible).

**`M₄`** (`thm:m4support`, `thm:m4exponent`; `toN`, `M4v`, `M4pow`).  `half_le_FCΘ_M4` (`F_C(M₄) ≥ 1/2`,
under `RealRep3`), `M4_uncalibrated` (`F_K < F_C`, given `h49`), `CK_M4pow` (`C_K(M₄^{⊗m}) = m log(9/4)`,
given `h49`), `FCΘ_M4pow_ge`, `FCΘ_M4pow_eq` (exactly `2^{-m}` given `hle`), `M4pow_window`
(`-log F_C = m log 2 < C_K`, given `hle`, `h49`).

**`prop:nozfpchirality`.**  `nozfp_chirality`: a `k`-copy effect `E ≥ 0` with
`⟨φ^{⊗k}|E|φ^{⊗k}⟩ = 0` on all real unit vectors vanishes on every `φ^{⊗k}` (polynomial interpolation
in a real parameter plus positivity).

## Not formalised, and why

* `thm:chiraldepth` (b), (c): need the first copy number `k_*` with a conjugation-odd invariant for blocks
  of three parties (Kronecker multiplicities, Schur-Weyl, an `S_4` finite check) -- a separate project.
* `cor:mixeddepth`: mixed states and trace-norm duality (`‖π^{⊗j} - π'^{⊗j}‖₁`), not set up here.
* (Partly superseded: `XiInvUnconditional` and `Converse*` prove the `ξ_inv` statements for `ψ₊`, `M₄` and its
  powers, modulo `h49`.)  Formerly: everything involving `ξ_inv` and Helstrom errors (the window `ξ_inv ≥ C_K/2`, `E_G ≥ ξ_inv`,
  `thm:expceiling`, the equalities `ξ_inv(M₄) = log 2` in `thm:m4exponent`, `thm:calgeom-tensorisation`
  upper bound, `cor:calgeom-spin1extensive`).  Only the `F_C`/`F_K` halves are proved.
* `F_C(M₄) ≤ 1/2` (the Cayley-Hamilton frame identities of `m4_support_proof.tex`) and
  `thm:ceilinglocus` (computer-assisted).
* The sharpness half of `thm:chiralEG` (Rudin-Shapiro vectors, the constant `(3-√5)/2` for three qubits)
  and the unconditional sharpness of `prop:exponentdepth` (b) (the three-qubit minimiser is
  computer-assisted).
* `thm:onecopy`, scalar chirality, the planar sign inequality and frame sharing are in
  `ScalarChirality.lean`, `PlanarSign.lean`, `Sharing.lean`.
* `PhysicalBridge` is not imported: its `FormalResearch.FrameFree.ip` and `SU2` would shadow the
  `NQubit` ones inside this namespace.  The identification `rotOverlap M₄ = F_K(M4v)` is therefore not
  made here, and `h49` is a hypothesis.
-/


open scoped ComplexConjugate Matrix BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.Ceilings

/-! ### Splitting off one qubit -/

theorem sum_insertNth {n : ℕ} (j : Fin (n + 1)) (f : (Fin (n + 1) → Fin 2) → ℂ) :
    ∑ x, f x = ∑ a : Fin 2, ∑ y : Fin n → Fin 2, f (Fin.insertNth j a y) := by
  rw [← (Fin.insertNthEquiv (fun _ => Fin 2) j).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_insertNth_real {n : ℕ} (j : Fin (n + 1)) (f : (Fin (n + 1) → Fin 2) → ℝ) :
    ∑ x, f x = ∑ a : Fin 2, ∑ y : Fin n → Fin 2, f (Fin.insertNth j a y) := by
  rw [← (Fin.insertNthEquiv (fun _ => Fin 2) j).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Contraction of qubit `j` with the bra `⟨e|`. -/
def peel {n : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ) (ψ : Ψ (n + 1)) : Ψ n :=
  fun y => ∑ a, conj (e a) * ψ (Fin.insertNth j a y)

/-! ### Filter overlap -/

def FCset {n : ℕ} (ψ φ : Ψ n) : Set ℝ :=
  {r | ∃ g : Fin n → Op1, (∀ i, (g i).det = 1) ∧ nsq (rot g φ) ≠ 0 ∧
        r = Complex.normSq (ip ψ (rot g φ)) / nsq (rot g φ)}

noncomputable def FC {n : ℕ} (ψ φ : Ψ n) : ℝ := sSup (FCset ψ φ)

noncomputable def FCΘ {n : ℕ} (ψ : Ψ n) : ℝ := FC ψ (Θ ψ)

theorem nsq_nonneg' {n : ℕ} (ψ : Ψ n) : 0 ≤ nsq ψ :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem FCset_bddAbove {n : ℕ} (ψ φ : Ψ n) : BddAbove (FCset ψ φ) := by
  refine ⟨nsq ψ, ?_⟩
  rintro r ⟨g, -, hne, rfl⟩
  have hpos : 0 < nsq (rot g φ) := lt_of_le_of_ne (nsq_nonneg' _) (Ne.symm hne)
  rw [div_le_iff₀ hpos]
  have := normSq_ip_le ψ (rot g φ)
  linarith

theorem rot_smul_local {n : ℕ} (c : Fin n → ℂ) (g : Fin n → Op1) (φ : Ψ n) :
    rot (fun i => c i • g i) φ = (∏ i, c i) • rot g φ := by
  funext x
  simp only [rot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  ring

theorem le_FC_det {n : ℕ} (ψ φ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, (g i).det ≠ 0)
    (hne : nsq (rot g φ) ≠ 0) :
    Complex.normSq (ip ψ (rot g φ)) / nsq (rot g φ) ≤ FC ψ φ := by
  have hc : ∀ i, ∃ z : ℂ, z ^ 2 = ((g i).det)⁻¹ := fun i =>
    IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
  choose c hc using hc
  have hdet : ∀ i, (c i • g i).det = 1 := by
    intro i
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin]
    rw [hc i]
    exact inv_mul_cancel₀ (hg i)
  have hcne : ∀ i, c i ≠ 0 := by
    intro i h
    have := hc i
    rw [h] at this
    simp at this
    exact hg i (by simpa using this.symm)
  have hC : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hcne i
  have hrot := rot_smul_local c g φ
  have hnsq : nsq (rot (fun i => c i • g i) φ) = Complex.normSq (∏ i, c i) * nsq (rot g φ) := by
    rw [hrot]
    simp only [nsq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]
  have hip : ip ψ (rot (fun i => c i • g i) φ) = (∏ i, c i) * ip ψ (rot g φ) := by
    rw [hrot]
    simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hCpos : 0 < Complex.normSq (∏ i, c i) := Complex.normSq_pos.mpr hC
  have hne' : nsq (rot (fun i => c i • g i) φ) ≠ 0 := by
    rw [hnsq]; exact mul_ne_zero hCpos.ne' hne
  have hmem : Complex.normSq (ip ψ (rot g φ)) / nsq (rot g φ) ∈ FCset ψ φ := by
    refine ⟨fun i => c i • g i, hdet, hne', ?_⟩
    rw [hip, hnsq, Complex.normSq_mul]
    field_simp
  exact le_csSup (FCset_bddAbove ψ φ) hmem


theorem FCset_rot {n : ℕ} (ψ φ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, (g i).det = 1) :
    FCset ψ (rot g φ) = FCset ψ φ := by
  ext r
  constructor
  · rintro ⟨u, hu, hne, rfl⟩
    refine ⟨fun i => u i * g i, fun i => by rw [Matrix.det_mul, hu i, hg i, one_mul], ?_, ?_⟩
    · rwa [← rot_comp]
    · rw [← rot_comp]
  · rintro ⟨v, hv, hne, rfl⟩
    have hinv : ∀ i, (g i)⁻¹ * g i = 1 := fun i =>
      Matrix.nonsing_inv_mul _ (by rw [hg i]; exact isUnit_one)
    have hcomp : rot (fun i => v i * (g i)⁻¹) (rot g φ) = rot v φ := by
      rw [rot_comp]
      congr 1
      funext i
      rw [Matrix.mul_assoc, hinv i, Matrix.mul_one]
    refine ⟨fun i => v i * (g i)⁻¹, fun i => ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hv i, Matrix.det_nonsing_inv, hg i]; simp
    · rwa [hcomp]
    · rw [hcomp]

theorem FC_rot {n : ℕ} (ψ φ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, (g i).det = 1) :
    FC ψ (rot g φ) = FC ψ φ := by
  unfold FC; rw [FCset_rot ψ φ g hg]

theorem eps_det : eps.det = 1 := SU2_eps.2

/-- `F_C(ψ,Θψ) = F_C(ψ,ψ̄)`. -/
theorem FCΘ_eq_FC_cj {n : ℕ} (ψ : Ψ n) : FCΘ ψ = FC ψ (cj ψ) := by
  unfold FCΘ
  rw [Θ_eq_rot]
  exact FC_rot ψ (cj ψ) (fun _ => eps) (fun _ => eps_det)

/-! ### Continuity and the limit principle -/

theorem continuous_rot_apply {n : ℕ} (φ : Ψ n) (x : Fin n → Fin 2) :
    Continuous (fun u : Fin n → Op1 => rot u φ x) := by
  unfold rot
  refine continuous_finsetSum _ fun y _ => ?_
  refine Continuous.mul ?_ continuous_const
  refine continuous_finsetProd _ fun i _ => ?_
  exact (continuous_apply (y i)).comp ((continuous_apply (x i)).comp (continuous_apply i))

theorem continuous_ip_rot {n : ℕ} (ψ φ : Ψ n) :
    Continuous (fun u : Fin n → Op1 => ip ψ (rot u φ)) := by
  unfold ip
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_rot_apply φ x)

theorem continuous_nsq_rot {n : ℕ} (φ : Ψ n) :
    Continuous (fun u : Fin n → Op1 => nsq (rot u φ)) := by
  unfold nsq
  exact continuous_finsetSum _ fun x _ => Complex.continuous_normSq.comp (continuous_rot_apply φ x)

/-- **Limit principle.** If a continuous path of local operators is invertible for `s > 0` and
`rot (g 0) φ ≠ 0`, the filtered overlap at the endpoint `g 0` is a lower bound for `F_C`. -/
theorem le_FC_of_path {n : ℕ} (ψ φ : Ψ n) (g : ℝ → Fin n → Op1) (hg : Continuous g)
    (hdet : ∀ s : ℝ, 0 < s → ∀ i, (g s i).det ≠ 0) (h0 : nsq (rot (g 0) φ) ≠ 0) :
    Complex.normSq (ip ψ (rot (g 0) φ)) / nsq (rot (g 0) φ) ≤ FC ψ φ := by
  have hnum : Continuous (fun s : ℝ => Complex.normSq (ip ψ (rot (g s) φ))) :=
    Complex.continuous_normSq.comp ((continuous_ip_rot ψ φ).comp hg)
  have hden : Continuous (fun s : ℝ => nsq (rot (g s) φ)) := (continuous_nsq_rot φ).comp hg
  have hcont : ContinuousAt (fun s : ℝ => Complex.normSq (ip ψ (rot (g s) φ)) / nsq (rot (g s) φ)) 0 :=
    hnum.continuousAt.div hden.continuousAt h0
  have hev : ∀ᶠ s in nhds (0 : ℝ), nsq (rot (g s) φ) ≠ 0 :=
    hden.continuousAt.eventually_ne h0
  have hev' : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), nsq (rot (g s) φ) ≠ 0 ∧ 0 < s :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  have hT : Filter.Tendsto (fun s : ℝ => Complex.normSq (ip ψ (rot (g s) φ)) / nsq (rot (g s) φ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Complex.normSq (ip ψ (rot (g 0) φ)) / nsq (rot (g 0) φ))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hT ?_
  filter_upwards [hev'] with s hs
  exact le_FC_det ψ φ (g s) (hdet s hs.2) hs.1


theorem FC_nonneg {n : ℕ} (ψ φ : Ψ n) : 0 ≤ FC ψ φ := by
  refine Real.sSup_nonneg ?_
  rintro r ⟨g, -, hne, rfl⟩
  exact div_nonneg (Complex.normSq_nonneg _) (nsq_nonneg' _)

/-! ### The peeling lemma -/

/-- The one-qubit operator `|e⟩⟨ē| + s |e'⟩⟨ē'|`, `e' = (-ē₁, ē₀)`, written `e eᵀ + s e' e'ᵀ`. -/
noncomputable def Gpath (e : Fin 2 → ℂ) (s : ℝ) : Op1 :=
  Matrix.of fun a b => e a * e b + (s : ℂ) * (![-conj (e 1), conj (e 0)] a * ![-conj (e 1), conj (e 0)] b)

theorem Gpath_zero (e : Fin 2 → ℂ) : Gpath e 0 = Matrix.of fun a b => e a * e b := by
  ext a b; simp [Gpath]

theorem Gpath_det (e : Fin 2 → ℂ) (he : Complex.normSq (e 0) + Complex.normSq (e 1) = 1) (s : ℝ) :
    (Gpath e s).det = s := by
  have h1 : e 0 * conj (e 0) + e 1 * conj (e 1) = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) he
    simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using this
  simp only [Gpath, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (s : ℂ) * (e 0 * conj (e 0) + e 1 * conj (e 1) + 1) * h1

theorem continuous_Gpath (e : Fin 2 → ℂ) : Continuous (Gpath e) := by
  unfold Gpath
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  fun_prop

theorem rot_insertNth {n : ℕ} (j : Fin (n + 1)) (G : Op1) (h : Fin n → Op1) (φ : Ψ (n + 1))
    (a : Fin 2) (x' : Fin n → Fin 2) :
    rot (Fin.insertNth j G h) φ (Fin.insertNth j a x') =
      ∑ b, ∑ y' : Fin n → Fin 2, G a b * (∏ i, h i (x' i) (y' i)) * φ (Fin.insertNth j b y') := by
  unfold rot
  rw [sum_insertNth j]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y' _ => ?_
  rw [Fin.prod_univ_succAbove _ j]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, mul_assoc]


theorem cj_peel_apply {n : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ) (ψ : Ψ (n + 1))
    (y : Fin n → Fin 2) :
    cj (peel j e ψ) y = ∑ b, e b * conj (ψ (Fin.insertNth j b y)) := by
  simp [cj, peel]

theorem rot_G0 {n : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ) (h : Fin n → Op1) (ψ : Ψ (n + 1))
    (x : Fin (n + 1) → Fin 2) :
    rot (Fin.insertNth j (Gpath e 0) h) (cj ψ) x =
      e (x j) * rot h (cj (peel j e ψ)) (Fin.removeNth j x) := by
  conv_lhs => rw [← Fin.insertNth_self_removeNth j x]
  rw [rot_insertNth]
  simp only [Gpath_zero, Matrix.of_apply, rot, cj_peel_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [cj]
  ring

theorem ip_G0 {n : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ) (h : Fin n → Op1) (ψ : Ψ (n + 1)) :
    ip ψ (rot (Fin.insertNth j (Gpath e 0) h) (cj ψ)) =
      ip (peel j e ψ) (rot h (cj (peel j e ψ))) := by
  unfold ip
  rw [sum_insertNth j]
  simp only [rot_G0, Fin.insertNth_apply_same, Fin.removeNth_insertNth]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp only [peel, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem nsq_G0 {n : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ)
    (he : Complex.normSq (e 0) + Complex.normSq (e 1) = 1) (h : Fin n → Op1) (ψ : Ψ (n + 1)) :
    nsq (rot (Fin.insertNth j (Gpath e 0) h) (cj ψ)) = nsq (rot h (cj (peel j e ψ))) := by
  have hs : ∀ f : Fin 2 → ℝ, ∑ a, f a = f 0 + f 1 := fun f => Fin.sum_univ_two f
  unfold nsq
  rw [sum_insertNth_real j]
  simp only [rot_G0, Fin.insertNth_apply_same, Fin.removeNth_insertNth, Complex.normSq_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hs, he, one_mul]


/-- **Peeling one qubit.** Filtering qubit `j` of `ψ̄` onto the branch `⟨e|ψ`:
`F_C(ψ_e, ψ̄_e) ≤ F_C(ψ, ψ̄)` (unnormalised branch `ψ_e`). -/
theorem peel_le_FC {n : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ)
    (he : Complex.normSq (e 0) + Complex.normSq (e 1) = 1) (ψ : Ψ (n + 1)) :
    FC (peel j e ψ) (cj (peel j e ψ)) ≤ FC ψ (cj ψ) := by
  refine Real.sSup_le ?_ (FC_nonneg _ _)
  rintro r ⟨h, hh, hne, rfl⟩
  have hdet : ∀ s : ℝ, 0 < s → ∀ i, (Fin.insertNth (α := fun _ => Op1) j (Gpath e s) h i).det ≠ 0 := by
    intro s hs i
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i', rfl⟩
    · simp [Gpath_det e he, hs.ne']
    · simp [hh i']
  have hcont : Continuous (fun s : ℝ => (Fin.insertNth (α := fun _ => Op1) j (Gpath e s) h : Fin (n+1) → Op1)) := by
    have : Continuous (fun s : ℝ => Gpath e s) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [Gpath, Matrix.of_apply]
      fun_prop
    exact Continuous.finInsertNth j this continuous_const
  have h0 : nsq (rot ((fun s : ℝ => (Fin.insertNth (α := fun _ => Op1) j (Gpath e s) h : Fin (n+1) → Op1)) 0) (cj ψ)) ≠ 0 := by
    show nsq (rot (Fin.insertNth j (Gpath e 0) h) (cj ψ)) ≠ 0
    rw [nsq_G0 j e he]; exact hne
  have := le_FC_of_path ψ (cj ψ) (fun s : ℝ => (Fin.insertNth (α := fun _ => Op1) j (Gpath e s) h : Fin (n+1) → Op1)) hcont hdet h0
  rwa [ip_G0, nsq_G0 j e he] at this


theorem FC_le {n : ℕ} (ψ φ : Ψ n) : FC ψ φ ≤ nsq ψ := by
  refine Real.sSup_le ?_ (nsq_nonneg' _)
  rintro r ⟨g, -, hne, rfl⟩
  have hpos : 0 < nsq (rot g φ) := lt_of_le_of_ne (nsq_nonneg' _) (Ne.symm hne)
  rw [div_le_iff₀ hpos]
  have := normSq_ip_le ψ (rot g φ)
  linarith

theorem FCΘ_le {n : ℕ} (ψ : Ψ n) : FCΘ ψ ≤ nsq ψ := FC_le _ _

theorem FCΘ_nonneg {n : ℕ} (ψ : Ψ n) : 0 ≤ FCΘ ψ := FC_nonneg _ _

/-! ### Real representatives of three-qubit states (hypothesis) -/

/-- Dür–Vidal–Cirac: every three-qubit vector lies in the `GL(2,ℂ)^3` orbit of a real vector
(all six SLOCC classes have real representatives).  Standard input of `thm:ceiling`,
`thm:entceiling`; taken as a hypothesis. -/
def RealRep3 : Prop :=
  ∀ φ : Ψ 3, ∃ A : Fin 3 → Op1, (∀ i, (A i).det ≠ 0) ∧ ∃ r : Ψ 3, cj r = r ∧ φ = rot A r

theorem FC_three_ge (hR : RealRep3) (φ : Ψ 3) : nsq φ ≤ FC φ (cj φ) := by
  by_cases h0 : nsq φ = 0
  · rw [h0]; exact FC_nonneg _ _
  obtain ⟨A, hA, r, hr, rfl⟩ := hR φ
  set φ := rot A r with hφ
  have hcj : cj φ = rot (fun i => (A i).map conj) r := by
    rw [hφ, conj_rot, hr]
  have hAc : ∀ i, ((A i).map conj).det ≠ 0 := by
    intro i
    have : ((A i).map conj).det = conj (A i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [this]; simpa using hA i
  have hinv : ∀ i, (A i * ((A i).map conj)⁻¹) * (A i).map conj = A i := by
    intro i
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hAc i)), Matrix.mul_one]
  have hh : rot (fun i => A i * ((A i).map conj)⁻¹) (cj φ) = φ := by
    rw [hcj, rot_comp]
    simp only [hinv]
    rfl
  have hdet : ∀ i, (A i * ((A i).map conj)⁻¹).det ≠ 0 := by
    intro i
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    simp [hA i, hAc i]
  have := le_FC_det φ (cj φ) _ hdet (by rw [hh]; exact h0)
  rw [hh, ip_self] at this
  have h' : Complex.normSq (nsq φ : ℂ) / nsq φ = nsq φ := by
    rw [Complex.normSq_ofReal]; field_simp
  rwa [h'] at this

/-! ### Iterated contraction -/

/-- `φ` is obtained from `ψ` by contracting some qubits with unit one-qubit bras. -/
inductive Contract : ∀ {n m : ℕ}, Ψ n → Ψ m → Prop
  | refl {n : ℕ} (ψ : Ψ n) : Contract ψ ψ
  | step {n m : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ)
      (he : Complex.normSq (e 0) + Complex.normSq (e 1) = 1) (ψ : Ψ (n + 1)) (φ : Ψ m) :
      Contract (peel j e ψ) φ → Contract ψ φ

theorem FC_contract_le {n m : ℕ} {ψ : Ψ n} {φ : Ψ m} (h : Contract ψ φ) :
    FC φ (cj φ) ≤ FC ψ (cj ψ) := by
  induction h with
  | refl ψ => exact le_rfl
  | step j e he ψ φ _ ih => exact ih.trans (peel_le_FC j e he ψ)


theorem entceiling_contract (hR : RealRep3) {n : ℕ} {ψ : Ψ n} {φ : Ψ 3} (h : Contract ψ φ) :
    nsq φ ≤ FCΘ ψ := by
  rw [FCΘ_eq_FC_cj]
  exact (FC_three_ge hR φ).trans (FC_contract_le h)

/-- The one-qubit marginal `ρ_j = tr_{≠j} |ψ⟩⟨ψ|` (unnormalised). -/
def marg {n : ℕ} (j : Fin (n + 1)) (ψ : Ψ (n + 1)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun a b => ∑ y, ψ (Fin.insertNth j a y) * conj (ψ (Fin.insertNth j b y))

/-- `⟨e|ρ|e⟩`. -/
noncomputable def qf (ρ : Matrix (Fin 2) (Fin 2) ℂ) (e : Fin 2 → ℂ) : ℝ :=
  (∑ a, ∑ b, conj (e a) * ρ a b * e b).re

/-- `λ_max(ρ_j) = sup_{‖e‖=1} ⟨e|ρ_j|e⟩`. -/
noncomputable def lmax {n : ℕ} (j : Fin (n + 1)) (ψ : Ψ (n + 1)) : ℝ :=
  sSup {r | ∃ e : Fin 2 → ℂ, Complex.normSq (e 0) + Complex.normSq (e 1) = 1 ∧
    r = qf (marg j ψ) e}

theorem qf_marg_eq {n : ℕ} (j : Fin (n + 1)) (e : Fin 2 → ℂ) (ψ : Ψ (n + 1)) :
    qf (marg j ψ) e = nsq (peel j e ψ) := by
  have h : (nsq (peel j e ψ) : ℂ) = ∑ a, ∑ b, conj (e a) * marg j ψ a b * e b := by
    simp only [nsq, marg, peel, Matrix.of_apply]
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self, map_sum, map_mul, Complex.conj_conj,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  unfold qf
  rw [← h]; simp

/-- **Theorem `thm:ceiling`, first inequality** (four qubits): `F_C(ψ) ≥ λ_max(ρ_j)` for every
qubit `j`, given the real representatives of three-qubit states. -/
theorem ceiling_lmax (hR : RealRep3) (j : Fin 4) (ψ : Ψ 4) : lmax j ψ ≤ FCΘ ψ := by
  refine Real.sSup_le ?_ (FCΘ_nonneg ψ)
  rintro r ⟨e, he, rfl⟩
  rw [qf_marg_eq, FCΘ_eq_FC_cj]
  exact (FC_three_ge hR (peel j e ψ)).trans (peel_le_FC j e he ψ)

theorem nsq_peel_delta {n : ℕ} (j : Fin (n + 1)) (ψ : Ψ (n + 1)) :
    nsq (peel j (fun a => if a = 0 then 1 else 0) ψ) + nsq (peel j (fun a => if a = 1 then 1 else 0) ψ)
      = nsq ψ := by
  have h0 : ∀ y, peel j (fun a => if a = 0 then 1 else 0) ψ y = ψ (Fin.insertNth j 0 y) := by
    intro y; simp [peel]
  have h1 : ∀ y, peel j (fun a => if a = 1 then 1 else 0) ψ y = ψ (Fin.insertNth j 1 y) := by
    intro y; simp [peel]
  unfold nsq
  simp only [h0, h1]
  rw [sum_insertNth_real j (fun x => Complex.normSq (ψ x)), Fin.sum_univ_two]

theorem delta_unit : ∀ b : Fin 2, Complex.normSq ((fun a : Fin 2 => if a = b then (1:ℂ) else 0) 0) +
    Complex.normSq ((fun a : Fin 2 => if a = b then (1:ℂ) else 0) 1) = 1 := by
  intro b; fin_cases b <;> simp

/-- **Theorem `thm:ceiling`, second inequality**: every four-qubit unit state has `F_C ≥ 1/2`. -/
theorem ceiling_half (hR : RealRep3) (ψ : Ψ 4) (hψ : nsq ψ = 1) : 1 / 2 ≤ FCΘ ψ := by
  have hb : ∀ b : Fin 2, nsq (peel 0 (fun a : Fin 2 => if a = b then (1:ℂ) else 0) ψ) ≤ FCΘ ψ := by
    intro b
    rw [FCΘ_eq_FC_cj]
    exact (FC_three_ge hR _).trans (peel_le_FC 0 _ (delta_unit b) ψ)
  have hsum := nsq_peel_delta (0 : Fin 4) ψ
  have h0 := hb 0
  have h1 := hb 1
  rw [hψ] at hsum
  linarith


theorem FCΘ_ge_three (hR : RealRep3) (ψ : Ψ 3) : nsq ψ ≤ FCΘ ψ := by
  rw [FCΘ_eq_FC_cj]; exact FC_three_ge hR ψ

/-- Contracting `m` qubits with the basis bras and keeping the heavier branch each time:
`F_C(ψ) ≥ 2^{-m} ‖ψ‖²` on `m + 3` qubits. -/
theorem FCΘ_ge_pow (hR : RealRep3) : ∀ (m : ℕ) (ψ : Ψ (m + 3)), (1 / 2 : ℝ) ^ m * nsq ψ ≤ FCΘ ψ
  | 0, ψ => by simpa using FCΘ_ge_three hR ψ
  | m + 1, ψ => by
    have hb : ∀ b : Fin 2, (1 / 2 : ℝ) ^ m *
        nsq (peel (0 : Fin (m + 3 + 1)) (fun a : Fin 2 => if a = b then (1:ℂ) else 0) ψ)
          ≤ FCΘ ψ := by
      intro b
      refine (FCΘ_ge_pow hR m _).trans ?_
      rw [FCΘ_eq_FC_cj, FCΘ_eq_FC_cj]
      exact peel_le_FC _ _ (delta_unit b) ψ
    have hsum := nsq_peel_delta (0 : Fin (m + 3 + 1)) ψ
    have h0 := hb 0
    have h1 := hb 1
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
    rw [pow_succ]
    nlinarith

/-- `F_C ≥ 8 · 2^{-n}` on `n ≥ 3` qubits (`thm:entceiling`, last claim). -/
theorem FCΘ_ge_eight (hR : RealRep3) (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) :
    8 * (1 / 2 : ℝ) ^ (m + 3) ≤ FCΘ ψ := by
  have := FCΘ_ge_pow hR m ψ
  rw [hψ] at this
  have e : 8 * (1 / 2 : ℝ) ^ (m + 3) = (1 / 2 : ℝ) ^ m := by
    rw [pow_add]; norm_num; ring
  rw [e]; linarith

/-! ### Product vectors and the geometric entanglement -/

/-- The product vector `e₁ ⊗ ⋯ ⊗ eₙ`. -/
def pv {n : ℕ} (e : Fin n → Fin 2 → ℂ) : Ψ n := fun x => ∏ i, e i (x i)

theorem nsq_pv {n : ℕ} (e : Fin n → Fin 2 → ℂ) :
    nsq (pv e) = ∏ i, (Complex.normSq (e i 0) + Complex.normSq (e i 1)) := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
    (fun i b => Complex.normSq (e i b))
  simp only [Fintype.piFinset_univ] at h
  unfold nsq pv
  simp only [map_prod]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact Fin.sum_univ_two _

theorem nsq_pv_unit {n : ℕ} (e : Fin n → Fin 2 → ℂ)
    (he : ∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) : nsq (pv e) = 1 := by
  rw [nsq_pv]; simp [he]

theorem ip_pv_peel {n : ℕ} (j : Fin (n + 1)) (e : Fin (n + 1) → Fin 2 → ℂ) (ψ : Ψ (n + 1)) :
    ip (pv e) ψ = ip (pv (fun i => e (j.succAbove i))) (peel j (e j) ψ) := by
  unfold ip
  rw [sum_insertNth j]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [pv, peel, Fin.prod_univ_succAbove _ j, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **`thm:entceiling`, product-vector form.** For every unit product vector `e`,
`|⟨e|ψ⟩|² ≤ F_C(ψ)` on `m + 3` qubits; equivalently `-log F_C ≤ E_G`. -/
theorem normSq_ip_pv_le_FCΘ (hR : RealRep3) : ∀ (m : ℕ) (ψ : Ψ (m + 3))
    (e : Fin (m + 3) → Fin 2 → ℂ), (∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) →
    Complex.normSq (ip (pv e) ψ) ≤ FCΘ ψ
  | 0, ψ, e, he => by
    have h1 := normSq_ip_le (pv e) ψ
    rw [nsq_pv_unit e he, one_mul] at h1
    exact h1.trans (FCΘ_ge_three hR ψ)
  | m + 1, ψ, e, he => by
    have hstep := ip_pv_peel (0 : Fin (m + 3 + 1)) e ψ
    have ih := normSq_ip_pv_le_FCΘ hR m (peel (0 : Fin (m + 3 + 1)) (e 0) ψ)
      (fun i => e ((0 : Fin (m + 3 + 1)).succAbove i)) (fun i => he _)
    rw [hstep]
    refine ih.trans ?_
    rw [FCΘ_eq_FC_cj, FCΘ_eq_FC_cj]
    exact peel_le_FC _ _ (he 0) ψ


/-- `Λ(ψ) = max_{e product unit} |⟨e|ψ⟩|²`. -/
noncomputable def Lam {n : ℕ} (ψ : Ψ n) : ℝ :=
  sSup {r | ∃ e : Fin n → Fin 2 → ℂ, (∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) ∧
    r = Complex.normSq (ip (pv e) ψ)}

/-- Geometric entanglement `E_G(ψ) = -log Λ(ψ)`. -/
noncomputable def EG {n : ℕ} (ψ : Ψ n) : ℝ := - Real.log (Lam ψ)

theorem Lam_bddAbove {n : ℕ} (ψ : Ψ n) :
    BddAbove {r | ∃ e : Fin n → Fin 2 → ℂ,
      (∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) ∧
        r = Complex.normSq (ip (pv e) ψ)} := by
  refine ⟨nsq ψ, ?_⟩
  rintro r ⟨e, he, rfl⟩
  have := normSq_ip_le (pv e) ψ
  rwa [nsq_pv_unit e he, one_mul] at this

theorem Lam_pos {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : 0 < Lam ψ := by
  have : ∃ x, ψ x ≠ 0 := by
    by_contra h
    push Not at h
    have : nsq ψ = 0 := by simp [nsq, h]
    rw [hψ] at this; norm_num at this
  obtain ⟨x, hx⟩ := this
  have hmem : Complex.normSq (ψ x) ∈ {r | ∃ e : Fin n → Fin 2 → ℂ,
      (∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) ∧
        r = Complex.normSq (ip (pv e) ψ)} := by
    refine ⟨fun i b => if b = x i then 1 else 0, fun i => ?_, ?_⟩
    · rcases (by decide : ∀ c : Fin 2, c = 0 ∨ c = 1) (x i) with h | h <;> simp [h]
    · congr 1
      have hpv : pv (fun i (b : Fin 2) => if b = x i then (1:ℂ) else 0) = fun y => if y = x then 1 else 0 := by
        funext y
        simp only [pv]
        by_cases hy : y = x
        · subst hy; simp
        · obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
            by_contra hc; push Not at hc; exact hy (funext hc)
          simp only [hy, ↓reduceIte]
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      rw [hpv]
      simp [ip]
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hx) (le_csSup (Lam_bddAbove ψ) hmem)

theorem Lam_le_FCΘ (hR : RealRep3) (m : ℕ) (ψ : Ψ (m + 3)) : Lam ψ ≤ FCΘ ψ := by
  refine Real.sSup_le ?_ (FCΘ_nonneg ψ)
  rintro r ⟨e, he, rfl⟩
  exact normSq_ip_pv_le_FCΘ hR m ψ e he

theorem FCΘ_pos (hR : RealRep3) (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) : 0 < FCΘ ψ :=
  lt_of_lt_of_le (Lam_pos ψ hψ) (Lam_le_FCΘ hR m ψ)

/-- **`thm:entceiling`**: for unit `ψ` on `m + 3` qubits, `-log F_C(ψ) ≤ E_G(ψ)` and
`-log F_C(ψ) ≤ m log 2`. -/
theorem negLog_FC_le_EG (hR : RealRep3) (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) :
    -Real.log (FCΘ ψ) ≤ EG ψ := by
  unfold EG
  have := Real.log_le_log (Lam_pos ψ hψ) (Lam_le_FCΘ hR m ψ)
  linarith

theorem negLog_FC_le_log2 (hR : RealRep3) (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) :
    -Real.log (FCΘ ψ) ≤ m * Real.log 2 := by
  have h := FCΘ_ge_eight hR m ψ hψ
  have hpos : (0 : ℝ) < 8 * (1 / 2 : ℝ) ^ (m + 3) := by positivity
  have := Real.log_le_log hpos h
  have e : Real.log (8 * (1 / 2 : ℝ) ^ (m + 3)) = -(m * Real.log 2) := by
    have : 8 * (1 / 2 : ℝ) ^ (m + 3) = (1 / 2 : ℝ) ^ m := by
      rw [pow_add]; norm_num; ring
    rw [this, Real.log_pow, one_div, Real.log_inv]; ring
  linarith


/-! ### Multiplicativity of `F_C` (`prop:mult`, filter part) -/

theorem FCset_tens {m n : ℕ} (ψ₁ φ₁ : Ψ m) (ψ₂ φ₂ : Ψ n) :
    FCset (tens ψ₁ ψ₂) (tens φ₁ φ₂) =
      {r | ∃ a ∈ FCset ψ₁ φ₁, ∃ b ∈ FCset ψ₂ φ₂, r = a * b} := by
  ext r
  constructor
  · rintro ⟨g, hg, hne, rfl⟩
    rw [rot_tens, nsq_tens] at hne
    have h1 : nsq (rot (fun i => g (Fin.castAdd n i)) φ₁) ≠ 0 := left_ne_zero_of_mul hne
    have h2 : nsq (rot (fun j => g (Fin.natAdd m j)) φ₂) ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨_, ⟨fun i => g (Fin.castAdd n i), fun i => hg _, h1, rfl⟩,
      _, ⟨fun j => g (Fin.natAdd m j), fun j => hg _, h2, rfl⟩, ?_⟩
    rw [rot_tens, ip_tens, nsq_tens, Complex.normSq_mul, div_mul_div_comm]
  · rintro ⟨_, ⟨g₁, hg₁, hne₁, rfl⟩, _, ⟨g₂, hg₂, hne₂, rfl⟩, rfl⟩
    refine ⟨Fin.append g₁ g₂, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa using hg₁ i
      · simpa using hg₂ j
    · rw [rot_tens, nsq_tens]
      simpa using mul_ne_zero hne₁ hne₂
    · rw [rot_tens, ip_tens, nsq_tens, Complex.normSq_mul, div_mul_div_comm]
      simp

theorem FCset_nonempty {n : ℕ} (ψ φ : Ψ n) (h : nsq φ ≠ 0) : (FCset ψ φ).Nonempty := by
  refine ⟨_, fun _ => 1, fun _ => by simp, ?_, rfl⟩
  rwa [rot_one]

theorem FCset_nonneg {n : ℕ} {ψ φ : Ψ n} : ∀ r ∈ FCset ψ φ, 0 ≤ r := by
  rintro r ⟨g, -, -, rfl⟩
  exact div_nonneg (Complex.normSq_nonneg _) (nsq_nonneg' _)

/-- **`prop:mult`** (filter part): `F_C(ψ₁⊗ψ₂, φ₁⊗φ₂) = F_C(ψ₁,φ₁) F_C(ψ₂,φ₂)`. -/
theorem FC_tens {m n : ℕ} (ψ₁ φ₁ : Ψ m) (ψ₂ φ₂ : Ψ n) (h₁ : nsq φ₁ ≠ 0) (h₂ : nsq φ₂ ≠ 0) :
    FC (tens ψ₁ ψ₂) (tens φ₁ φ₂) = FC ψ₁ φ₁ * FC ψ₂ φ₂ := by
  unfold FC
  rw [FCset_tens]
  exact sSup_mul_of_independent (FCset_nonempty _ _ h₁) (FCset_nonempty _ _ h₂)
    FCset_nonneg FCset_nonneg (FCset_bddAbove _ _) (FCset_bddAbove _ _)

theorem FCΘ_tens {m n : ℕ} (ψ₁ : Ψ m) (ψ₂ : Ψ n) (h₁ : nsq ψ₁ ≠ 0) (h₂ : nsq ψ₂ ≠ 0) :
    FCΘ (tens ψ₁ ψ₂) = FCΘ ψ₁ * FCΘ ψ₂ := by
  unfold FCΘ
  rw [Θ_tens, FC_tens _ _ _ _ (by rwa [nsq_Θ]) (by rwa [nsq_Θ])]

/-- The basis vector `|0⋯0⟩`. -/
def zeroVec (n : ℕ) : Ψ n := fun x => if x = 0 then 1 else 0

theorem nsq_zeroVec (n : ℕ) : nsq (zeroVec n) = 1 := by
  simp [nsq, zeroVec]

theorem cj_zeroVec (n : ℕ) : cj (zeroVec n) = zeroVec n := by
  funext x; simp [cj, zeroVec]

theorem FCΘ_zeroVec (n : ℕ) : FCΘ (zeroVec n) = 1 := by
  apply le_antisymm
  · have := FCΘ_le (zeroVec n); rwa [nsq_zeroVec] at this
  · rw [FCΘ_eq_FC_cj, cj_zeroVec]
    have := le_FC_det (zeroVec n) (zeroVec n) (fun _ => 1) (fun _ => by simp)
      (by rw [rot_one, nsq_zeroVec]; norm_num)
    rw [rot_one, ip_self, nsq_zeroVec] at this
    simpa using this

/-- For one, two or three qubits, `F_C = 1` (`thm:entceiling`, `n ≤ 3`; `thm:hierarchy`(i)). -/
theorem FCΘ_eq_one_of_le_three (hR : RealRep3) {n : ℕ} (hn : n ≤ 3) (ψ : Ψ n) (hψ : nsq ψ = 1) :
    FCΘ ψ = 1 := by
  apply le_antisymm
  · have := FCΘ_le ψ; rwa [hψ] at this
  · interval_cases n
    · have h := FCΘ_ge_three hR (tens ψ (zeroVec 3))
      rw [nsq_tens, hψ, nsq_zeroVec, one_mul, FCΘ_tens _ _ (by rw [hψ]; norm_num) (by rw [nsq_zeroVec]; norm_num),
        FCΘ_zeroVec, mul_one] at h
      exact h
    · have h := FCΘ_ge_three hR (tens ψ (zeroVec 2))
      rw [nsq_tens, hψ, nsq_zeroVec, one_mul, FCΘ_tens _ _ (by rw [hψ]; norm_num) (by rw [nsq_zeroVec]; norm_num),
        FCΘ_zeroVec, mul_one] at h
      exact h
    · have h := FCΘ_ge_three hR (tens ψ (zeroVec 1))
      rw [nsq_tens, hψ, nsq_zeroVec, one_mul, FCΘ_tens _ _ (by rw [hψ]; norm_num) (by rw [nsq_zeroVec]; norm_num),
        FCΘ_zeroVec, mul_one] at h
      exact h
    · have h := FCΘ_ge_three hR ψ
      rwa [hψ] at h


/-! ### Producible states and `prop:exponentdepth` (a) -/

/-- `ψ` is a tensor product of unit states on consecutive blocks of between `1` and `m` qubits.
(Blocks on non-adjacent qubits are the same up to a permutation of the qubits, which commutes
with every quantity considered.) -/
inductive Producible (m : ℕ) : ∀ {n : ℕ}, Ψ n → Prop
  | single {b : ℕ} (hb1 : 1 ≤ b) (hbm : b ≤ m) (φ : Ψ b) (hφ : nsq φ = 1) : Producible m φ
  | cons {b n : ℕ} (hb1 : 1 ≤ b) (hbm : b ≤ m) (φ : Ψ b) (hφ : nsq φ = 1) (χ : Ψ n) :
      Producible m χ → Producible m (tens φ χ)

theorem Producible.nsq_eq_one {m n : ℕ} {ψ : Ψ n} (h : Producible m ψ) : nsq ψ = 1 := by
  induction h with
  | single hb1 hbm φ hφ => exact hφ
  | cons hb1 hbm φ hφ χ _ ih => rw [nsq_tens, hφ, ih, one_mul]

/-- A block of `b ≥ 1` qubits has `F_C ≥ 2^{-(b-3)_+}`. -/
theorem block_FC_ge (hR : RealRep3) {b : ℕ} (hb : 1 ≤ b) (φ : Ψ b) (hφ : nsq φ = 1) :
    (1 / 2 : ℝ) ^ (b - 3) ≤ FCΘ φ := by
  by_cases h3 : b ≤ 3
  · rw [Nat.sub_eq_zero_of_le h3, pow_zero, FCΘ_eq_one_of_le_three hR h3 φ hφ]
  · obtain ⟨m, rfl⟩ : ∃ m, b = m + 3 := ⟨b - 3, by omega⟩
    have := FCΘ_ge_pow hR m φ
    rw [hφ, mul_one] at this
    simpa using this

theorem block_FC_pos (hR : RealRep3) {b : ℕ} (hb : 1 ≤ b) (φ : Ψ b) (hφ : nsq φ = 1) :
    0 < FCΘ φ :=
  lt_of_lt_of_le (by positivity) (block_FC_ge hR hb φ hφ)

/-- **`prop:exponentdepth` (a)**: a pure `m`-producible state of `n` qubits, `m ≥ 3`, has
`-log F_C ≤ n (1 - 3/m) log 2`. -/
theorem negLog_FC_le_producible (hR : RealRep3) {m : ℕ} (hm : 3 ≤ m) {n : ℕ} {ψ : Ψ n}
    (h : Producible m ψ) :
    0 < FCΘ ψ ∧ -Real.log (FCΘ ψ) ≤ n * (1 - 3 / (m : ℝ)) * Real.log 2 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the block estimate
  have blk : ∀ {b : ℕ} (hb1 : 1 ≤ b) (hbm : b ≤ m) (φ : Ψ b) (hφ : nsq φ = 1),
      0 < FCΘ φ ∧ -Real.log (FCΘ φ) ≤ b * (1 - 3 / (m : ℝ)) * Real.log 2 := by
    intro b hb1 hbm φ hφ
    refine ⟨block_FC_pos hR hb1 φ hφ, ?_⟩
    have hlow := block_FC_ge hR hb1 φ hφ
    have hl := Real.log_le_log (by positivity) hlow
    rw [Real.log_pow, one_div, Real.log_inv] at hl
    have hbm' : (b : ℝ) ≤ m := by exact_mod_cast hbm
    have hfac : (b : ℝ) * (1 - 3 / (m : ℝ)) = b - 3 * b / m := by field_simp
    have hbb : (b : ℝ) * 3 / m ≤ 3 := by
      rw [div_le_iff₀ hmpos]; nlinarith
    by_cases h3 : b ≤ 3
    · rw [Nat.sub_eq_zero_of_le h3] at hl
      simp at hl
      have : 0 ≤ (b : ℝ) * (1 - 3 / (m : ℝ)) := by
        apply mul_nonneg (by positivity)
        rw [sub_nonneg, div_le_one hmpos]; exact hm'
      nlinarith
    · have hcast : ((b - 3 : ℕ) : ℝ) = b - 3 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [hcast] at hl
      have : -Real.log (FCΘ φ) ≤ ((b : ℝ) - 3) * Real.log 2 := by linarith
      refine this.trans ?_
      apply mul_le_mul_of_nonneg_right _ hlog2.le
      rw [hfac]
      have : (b : ℝ) * 3 / m = 3 * b / m := by ring
      linarith
  induction h with
  | single hb1 hbm φ hφ => exact blk hb1 hbm φ hφ
  | cons hb1 hbm φ hφ χ hχ ih =>
    obtain ⟨hp1, hl1⟩ := blk hb1 hbm φ hφ
    obtain ⟨hp2, hl2⟩ := ih
    have hχ1 := hχ.nsq_eq_one
    rw [FCΘ_tens φ χ (by rw [hφ]; norm_num) (by rw [hχ1]; norm_num)]
    refine ⟨mul_pos hp1 hp2, ?_⟩
    rw [Real.log_mul hp1.ne' hp2.ne']
    push_cast
    nlinarith


/-! ### Left rotation invariance and `SU(2)` conjugates -/

theorem SU2_map_conj {u : Op1} (h : SU2 u) : SU2 (u.map conj) := by
  constructor
  · have hu : u * uᴴ = 1 := mul_eq_one_comm.mp h.1
    have h2 := congrArg Matrix.transpose hu
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h2
    have e1 : (uᴴ)ᵀ = u.map conj := by ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (u.map conj)ᴴ = uᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
    rw [e1] at h2
    rw [e2]
    exact mul_eq_one_comm.mp h2
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h.2]; simp


theorem rot_adj_rot {n : ℕ} (g : Fin n → Op1) (hg : ∀ i, SU2 (g i)) (χ : Ψ n) :
    rot g (rot (fun i => (g i)ᴴ) χ) = χ := by
  rw [rot_comp]
  have : (fun i => g i * (g i)ᴴ) = fun _ => (1 : Op1) := by
    funext i; exact mul_eq_one_comm.mp (hg i).1
  rw [this, rot_one]

theorem rotSet_rot_left {n : ℕ} (ψ φ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, SU2 (g i)) :
    rotSet (rot g ψ) φ = rotSet ψ φ := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => (g i)ᴴ * u i, fun i => SU2_mul (SU2_adjoint (hg i)) (hu i), ?_⟩
    rw [← rot_comp]
    have := ip_rot g (fun i => (hg i).1) ψ (rot (fun i => (g i)ᴴ) (rot u φ))
    rw [rot_adj_rot g hg] at this
    rw [this]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun i => g i * v i, fun i => SU2_mul (hg i) (hv i), ?_⟩
    rw [← rot_comp, ip_rot g (fun i => (hg i).1)]

theorem FK_rot_left {n : ℕ} (ψ φ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, SU2 (g i)) :
    FK (rot g ψ) φ = FK ψ φ := by
  unfold FK; rw [rotSet_rot_left ψ φ g hg]

/-- `F_K(ψ,ψ̄)` is invariant under rotating `ψ`. -/
theorem FK_cj_rot {n : ℕ} (ψ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, SU2 (g i)) :
    FK (rot g ψ) (cj (rot g ψ)) = FK ψ (cj ψ) := by
  rw [conj_rot, FK_rot _ _ _ (fun i => SU2_map_conj (hg i)), FK_rot_left _ _ _ hg]

/-! ### Phase averaging: `F_K ≥ ∑_x |ψ_x|⁴` -/

/-- `diag(1,1)` or `diag(i,-i)`: the `SU(2)` elements `i^b Z^b`. -/
def Dz (b : Fin 2) : Op1 :=
  Matrix.of fun a c => if a = c then (if b = 0 then 1 else (if a = 0 then Complex.I else -Complex.I)) else 0

theorem SU2_Dz (b : Fin 2) : SU2 (Dz b) := by
  fin_cases b
  · constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Dz, Matrix.mul_apply]
    · simp [Dz, Matrix.det_fin_two]
  · constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Dz, Matrix.mul_apply]
    · simp [Dz, Matrix.det_fin_two]

theorem rot_diag {n : ℕ} (d : Fin n → Fin 2 → ℂ) (u : Fin n → Op1)
    (hu : ∀ i a c, u i a c = if a = c then d i a else 0) (ψ : Ψ n) (x : Fin n → Fin 2) :
    rot u ψ x = (∏ i, d i (x i)) * ψ x := by
  unfold rot
  rw [Finset.sum_eq_single x]
  · congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [hu]; simp
  · intro y _ hy
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
      by_contra hc; push Not at hc; exact hy (funext hc)
    have : ∏ i, u i (x i) (y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hu]; simp [Ne.symm hi])
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- Sign character `(-1)^{z·x}` and phase `i^{|z|}`. -/
def sgn' {n : ℕ} (z x : Fin n → Fin 2) : ℂ := ∏ i, (if z i = 1 ∧ x i = 1 then (-1 : ℂ) else 1)
def ph' {n : ℕ} (z : Fin n → Fin 2) : ℂ := ∏ i, (if z i = 0 then (1 : ℂ) else Complex.I)

theorem Dz_apply_diag (b a : Fin 2) :
    Dz b a a = (if b = 0 then (1 : ℂ) else Complex.I) * (if b = 1 ∧ a = 1 then (-1 : ℂ) else 1) := by
  fin_cases b <;> fin_cases a <;> simp [Dz]

theorem normSq_ph' {n : ℕ} (z : Fin n → Fin 2) : Complex.normSq (ph' z) = 1 := by
  unfold ph'
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs <;> simp

theorem rot_Dz_cj {n : ℕ} (z : Fin n → Fin 2) (ψ : Ψ n) (x : Fin n → Fin 2) :
    rot (fun i => Dz (z i)) (cj ψ) x = ph' z * sgn' z x * conj (ψ x) := by
  rw [rot_diag (fun i a => Dz (z i) a a) _ (by
    intro i a c; simp only [Dz, Matrix.of_apply]; split_ifs with h h' <;> simp_all)]
  simp only [Dz_apply_diag, Finset.prod_mul_distrib]
  simp [cj, ph', sgn', mul_assoc]

theorem ip_Dz {n : ℕ} (z : Fin n → Fin 2) (ψ : Ψ n) :
    Complex.normSq (ip ψ (rot (fun i => Dz (z i)) (cj ψ))) =
      Complex.normSq (∑ x, sgn' z x * (conj (ψ x)) ^ 2) := by
  have : ip ψ (rot (fun i => Dz (z i)) (cj ψ)) = ph' z * ∑ x, sgn' z x * (conj (ψ x)) ^ 2 := by
    simp only [ip, rot_Dz_cj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this, Complex.normSq_mul, normSq_ph', one_mul]

theorem sum_sgn_mul {n : ℕ} (x y : Fin n → Fin 2) :
    ∑ z : Fin n → Fin 2, sgn' z x * sgn' z y = if x = y then (2 : ℂ) ^ n else 0 := by
  have h1 : ∀ z : Fin n → Fin 2, sgn' z x * sgn' z y =
      ∏ i, ((if z i = 1 ∧ x i = 1 then (-1 : ℂ) else 1) * (if z i = 1 ∧ y i = 1 then (-1 : ℂ) else 1)) := by
    intro z; unfold sgn'; rw [Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [sum_prod_pi (fun i b => (if b = 1 ∧ x i = 1 then (-1 : ℂ) else 1) * (if b = 1 ∧ y i = 1 then (-1 : ℂ) else 1))]
  have h2 : ∀ i, ∑ b : Fin 2, ((if b = 1 ∧ x i = 1 then (-1 : ℂ) else 1) *
      (if b = 1 ∧ y i = 1 then (-1 : ℂ) else 1)) = if x i = y i then 2 else 0 := by
    intro i
    rcases (by decide : ∀ c : Fin 2, c = 0 ∨ c = 1) (x i) with hx | hx <;>
      rcases (by decide : ∀ c : Fin 2, c = 0 ∨ c = 1) (y i) with hy | hy <;>
      simp [Fin.sum_univ_two, hx, hy] <;> norm_num
  simp_rw [h2]
  by_cases hxy : x = y
  · subst hxy; simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc; push Not at hc; exact hxy (funext hc)
    simp only [hxy, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem parseval_sgn {n : ℕ} (w : (Fin n → Fin 2) → ℂ) :
    ∑ z : Fin n → Fin 2, Complex.normSq (∑ x, sgn' z x * w x) =
      2 ^ n * ∑ x, Complex.normSq (w x) := by
  have hs : ∀ (z x : Fin n → Fin 2), conj (sgn' z x) = sgn' z x := by
    intro z x
    unfold sgn'
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have h : ((∑ z : Fin n → Fin 2, Complex.normSq (∑ x, sgn' z x * w x) : ℝ) : ℂ) =
      ((2 ^ n * ∑ x, Complex.normSq (w x) : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self, map_sum, map_mul, hs]
    have e1 : ∀ z : Fin n → Fin 2, (∑ x, sgn' z x * conj (w x)) * (∑ y, sgn' z y * w y) =
        ∑ x, ∑ y, conj (w x) * w y * (sgn' z x * sgn' z y) := by
      intro z
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    simp_rw [e1]
    have e2 : ∑ z : Fin n → Fin 2, ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2,
          conj (w x) * w y * (sgn' z x * sgn' z y) =
        ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2, conj (w x) * w y *
          ∑ z : Fin n → Fin 2, (sgn' z x * sgn' z y) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
    rw [e2]
    simp_rw [sum_sgn_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [mul_comm]
  exact_mod_cast h


/-- **`prop:phaseaverage`**: `F_K(ψ,ψ̄) ≥ ∑_x |ψ_x|⁴` (inverse participation ratio in the product basis). -/
theorem ipr_le_FK_cj {n : ℕ} (ψ : Ψ n) :
    ∑ x, (Complex.normSq (ψ x)) ^ 2 ≤ FK ψ (cj ψ) := by
  have hpar := parseval_sgn (fun x => (conj (ψ x)) ^ 2)
  have hle : ∀ z : Fin n → Fin 2, Complex.normSq (∑ x, sgn' z x * (conj (ψ x)) ^ 2) ≤ FK ψ (cj ψ) := by
    intro z
    rw [← ip_Dz]
    exact le_FK ψ (cj ψ) _ (fun i => SU2_Dz _)
  have hsum : ∑ z : Fin n → Fin 2, Complex.normSq (∑ x, sgn' z x * (conj (ψ x)) ^ 2) ≤
      ∑ z : Fin n → Fin 2, FK ψ (cj ψ) := Finset.sum_le_sum fun z _ => hle z
  rw [hpar, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have h2 : ∀ x, Complex.normSq ((conj (ψ x)) ^ 2) = (Complex.normSq (ψ x)) ^ 2 := by
    intro x; rw [map_pow, Complex.normSq_conj]
  simp only [h2] at hsum
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  push_cast at hsum
  exact le_of_mul_le_mul_left hsum hpos

/-! ### Product vectors as rotated basis vectors -/

/-- The `SU(2)` matrix with first column `e`. -/
def Wmat (e : Fin 2 → ℂ) : Op1 := !![e 0, -conj (e 1); e 1, conj (e 0)]

theorem SU2_Wmat (e : Fin 2 → ℂ) (he : Complex.normSq (e 0) + Complex.normSq (e 1) = 1) :
    SU2 (Wmat e) := by
  have h1 : e 0 * conj (e 0) + e 1 * conj (e 1) = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) he
    simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using this
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Wmat, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
      first | (linear_combination h1) | ring
  · simp only [Wmat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination h1


theorem rot_Wmat_zero {n : ℕ} (e : Fin n → Fin 2 → ℂ) :
    rot (fun i => Wmat (e i)) (zeroVec n) = pv e := by
  funext x
  unfold rot pv zeroVec
  rw [Finset.sum_eq_single (0 : Fin n → Fin 2)]
  · simp only [↓reduceIte, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases (by decide : ∀ c : Fin 2, c = 0 ∨ c = 1) (x i) with h | h <;> simp [Wmat, h]
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ip_zeroVec {n : ℕ} (χ : Ψ n) : ip (zeroVec n) χ = χ 0 := by
  simp [ip, zeroVec]

theorem ip_pv_eq {n : ℕ} (e : Fin n → Fin 2 → ℂ)
    (he : ∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) (ψ : Ψ n) :
    ip (pv e) ψ = (rot (fun i => (Wmat (e i))ᴴ) ψ) 0 := by
  have hW : ∀ i, SU2 (Wmat (e i)) := fun i => SU2_Wmat _ (he i)
  rw [← rot_Wmat_zero e]
  have := ip_rot (fun i => Wmat (e i)) (fun i => (hW i).1) (zeroVec n)
    (rot (fun i => (Wmat (e i))ᴴ) ψ)
  rw [rot_adj_rot _ hW] at this
  rw [this, ip_zeroVec]

/-- **`thm:chiralEG`, geometric part:** `|⟨e|ψ⟩|⁴ ≤ F_K(ψ)` for every product unit vector `e`. -/
theorem normSq_ip_pv_sq_le_FKΘ {n : ℕ} (e : Fin n → Fin 2 → ℂ)
    (he : ∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) (ψ : Ψ n) :
    (Complex.normSq (ip (pv e) ψ)) ^ 2 ≤ FKΘ ψ := by
  have hW : ∀ i, SU2 (Wmat (e i)) := fun i => SU2_Wmat _ (he i)
  have hV : ∀ i, SU2 ((Wmat (e i))ᴴ) := fun i => SU2_adjoint (hW i)
  rw [FKΘ_eq_FK_cj, ← FK_cj_rot ψ _ hV]
  refine le_trans ?_ (ipr_le_FK_cj _)
  rw [ip_pv_eq e he ψ]
  exact Finset.single_le_sum (f := fun x => (Complex.normSq ((rot (fun i => (Wmat (e i))ᴴ) ψ) x)) ^ 2)
    (fun x _ => by positivity) (Finset.mem_univ (0 : Fin n → Fin 2))

theorem Lam_sq_le_FKΘ {n : ℕ} (ψ : Ψ n) : Lam ψ ^ 2 ≤ FKΘ ψ := by
  have hF : 0 ≤ FKΘ ψ := FK_nonneg _ _
  have h1 : Lam ψ ≤ Real.sqrt (FKΘ ψ) := by
    refine Real.sSup_le ?_ (Real.sqrt_nonneg _)
    rintro r ⟨e, he, rfl⟩
    exact Real.le_sqrt_of_sq_le (normSq_ip_pv_sq_le_FKΘ e he ψ)
  have h0 : 0 ≤ Lam ψ := by
    refine Real.sSup_nonneg ?_
    rintro r ⟨e, he, rfl⟩
    exact Complex.normSq_nonneg _
  calc Lam ψ ^ 2 ≤ Real.sqrt (FKΘ ψ) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = FKΘ ψ := Real.sq_sqrt hF

/-- **`thm:chiralEG`: `C_K ≤ 2 E_G`** (qubits; `F_K ≥ Λ²`). -/
theorem CK_le_two_EG {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : CK ψ ≤ 2 * EG ψ := by
  unfold CK EG
  have hL := Lam_pos ψ hψ
  have := Real.log_le_log (by positivity) (Lam_sq_le_FKΘ ψ)
  rw [Real.log_pow] at this
  push_cast at this
  linarith


/-! ### `k`-copy odd observables (`thm:chiraldepth`, `thm:chiralEG`) -/

/-- Basis labels of `k` copies of an `n`-qubit system. -/
abbrev Copies (k n : ℕ) := Fin k → Fin n → Fin 2

/-- `ψ^{⊗k}` on `k` copies. -/
def kpow (k : ℕ) {n : ℕ} (φ : Ψ n) : Copies k n → ℂ := fun x => ∏ c, φ (x c)

/-- Inner product on `k`-copy vectors. -/
def kip {k n : ℕ} (v w : Copies k n → ℂ) : ℂ := ∑ x, conj (v x) * w x

/-- Squared norm on `k`-copy vectors. -/
def knsq {k n : ℕ} (v : Copies k n → ℂ) : ℝ := ∑ x, Complex.normSq (v x)

/-- The matrix element `⟨v|A|w⟩`. -/
def kform {k n : ℕ} (A : Matrix (Copies k n) (Copies k n) ℂ) (v w : Copies k n → ℂ) : ℂ :=
  ∑ x, ∑ y, conj (v x) * A x y * w y

theorem kip_kpow (k : ℕ) {n : ℕ} (φ χ : Ψ n) : kip (kpow k φ) (kpow k χ) = ip φ χ ^ k := by
  unfold kip kpow ip
  have := sum_prod_pi (ι := Fin k) (κ := Fin n → Fin 2) (fun _ b => conj (φ b) * χ b)
  simp only [map_prod, ← Finset.prod_mul_distrib]
  rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem kip_self {k n : ℕ} (v : Copies k n → ℂ) : kip v v = (knsq v : ℂ) := by
  unfold kip knsq
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]

theorem knsq_kpow (k : ℕ) {n : ℕ} (φ : Ψ n) : knsq (kpow k φ) = nsq φ ^ k := by
  have := kip_kpow k φ φ
  rw [kip_self, ip_self] at this
  exact_mod_cast this

theorem knsq_add {k n : ℕ} (v w : Copies k n → ℂ) :
    knsq (v + w) = knsq v + knsq w + 2 * (kip v w).re := by
  unfold knsq kip
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.add_apply, Complex.normSq_add]
  have : (v x * conj (w x)).re = (conj (v x) * w x).re := by
    rw [← Complex.conj_re (v x * conj (w x))]; simp
  rw [this]

theorem knsq_sub {k n : ℕ} (v w : Copies k n → ℂ) :
    knsq (v - w) = knsq v + knsq w - 2 * (kip v w).re := by
  unfold knsq kip
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.sub_apply, Complex.normSq_sub]
  have : (v x * conj (w x)).re = (conj (v x) * w x).re := by
    rw [← Complex.conj_re (v x * conj (w x))]; simp
  rw [this]

theorem knsq_smul {k n : ℕ} (c : ℂ) (v : Copies k n → ℂ) :
    knsq (c • v) = Complex.normSq c * knsq v := by
  unfold knsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Complex.normSq_mul]

theorem kip_smul_right {k n : ℕ} (c : ℂ) (v w : Copies k n → ℂ) :
    kip v (c • w) = c * kip v w := by
  unfold kip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem kform_smul_self {k n : ℕ} (A : Matrix (Copies k n) (Copies k n) ℂ) (c : ℂ)
    (v : Copies k n → ℂ) : kform A (c • v) (c • v) = (conj c * c) * kform A v v := by
  unfold kform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

/-- The identity `⟨v-w|A|v+w⟩ + ⟨v+w|A|v-w⟩ = 2(⟨v|A|v⟩ - ⟨w|A|w⟩)`. -/
theorem kform_polar {k n : ℕ} (A : Matrix (Copies k n) (Copies k n) ℂ) (v w : Copies k n → ℂ) :
    kform A (v - w) (v + w) + kform A (v + w) (v - w) = 2 * (kform A v v - kform A w w) := by
  unfold kform
  rw [← Finset.sum_add_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub]; ring

/-- Core pure-state estimate: for a contraction `A`,
`|⟨v|A|v⟩ - ⟨w|A|w⟩|² ≤ ‖v+w‖² ‖v-w‖²`. -/
theorem kform_diff_le {k n : ℕ} (A : Matrix (Copies k n) (Copies k n) ℂ)
    (hA : ∀ v w, Complex.normSq (kform A v w) ≤ knsq v * knsq w) (v w : Copies k n → ℂ) :
    Complex.normSq (kform A v v - kform A w w) ≤ knsq (v + w) * knsq (v - w) := by
  set M := knsq (v + w) * knsq (v - w) with hM
  have hM0 : 0 ≤ M := mul_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  have h1 : ‖kform A (v - w) (v + w)‖ ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    rw [← Complex.normSq_eq_norm_sq]
    have := hA (v - w) (v + w)
    rw [hM, mul_comm]; exact this
  have h2 : ‖kform A (v + w) (v - w)‖ ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    rw [← Complex.normSq_eq_norm_sq]
    exact hA (v + w) (v - w)
  have h3 : ‖2 * (kform A v v - kform A w w)‖ ≤ 2 * Real.sqrt M := by
    rw [← kform_polar]
    calc _ ≤ ‖kform A (v - w) (v + w)‖ + ‖kform A (v + w) (v - w)‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have h4 : ‖2 * (kform A v v - kform A w w)‖ ^ 2 ≤ (2 * Real.sqrt M) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_mul, h2n, mul_pow, mul_pow, Real.sq_sqrt hM0] at h4
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

theorem exists_phase (z : ℂ) : ∃ c : ℂ, conj c * c = 1 ∧ c * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    refine ⟨(‖z‖ : ℂ) / z, ?_, by field_simp⟩
    rw [map_div₀, Complex.conj_ofReal]
    have h : conj z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have hz' : conj z ≠ 0 := by simpa using hz
    field_simp
    exact h.symm

/-- A `k`-copy observable (Hermitian contraction `A`, odd under complex conjugation, with
local-unitarily invariant value).  `inv` is the consequence `a(uφ) = a(φ)` of `[A, u^{⊗k}] = 0`. -/
structure OddObs (n k : ℕ) where
  A : Matrix (Copies k n) (Copies k n) ℂ
  herm : Aᴴ = A
  bound : ∀ v w, Complex.normSq (kform A v w) ≤ knsq v * knsq w
  odd : A.map conj = -A
  inv : ∀ u : Fin n → Op1, (∀ i, SU2 (u i)) → ∀ φ : Ψ n,
    kform A (kpow k (rot u φ)) (kpow k (rot u φ)) = kform A (kpow k φ) (kpow k φ)

/-- The value `a(φ) = ⟨φ^{⊗k}|A|φ^{⊗k}⟩`. -/
def OddObs.a {n k : ℕ} (O : OddObs n k) (φ : Ψ n) : ℂ := kform O.A (kpow k φ) (kpow k φ)

theorem kpow_cj (k : ℕ) {n : ℕ} (φ : Ψ n) : kpow k (cj φ) = fun x => conj (kpow k φ x) := by
  funext x; simp [kpow, cj, map_prod]

theorem OddObs.a_cj {n k : ℕ} (O : OddObs n k) (φ : Ψ n) : O.a (cj φ) = - conj (O.a φ) := by
  have hA : ∀ x y, conj (O.A x y) = - O.A x y := fun x y => by
    have := congrFun (congrFun O.odd x) y
    simpa using this
  unfold OddObs.a kform
  rw [kpow_cj]
  simp only [map_sum, map_mul, Complex.conj_conj, hA, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem OddObs.a_im {n k : ℕ} (O : OddObs n k) (φ : Ψ n) : (O.a φ).im = 0 := by
  have hA : ∀ x y, conj (O.A x y) = O.A y x := fun x y => by
    have := congrFun (congrFun O.herm y) x
    simpa [Matrix.conjTranspose_apply] using this
  have h : conj (O.a φ) = O.a φ := by
    unfold OddObs.a kform
    simp only [map_sum, map_mul, Complex.conj_conj, hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have := congrArg Complex.im h
  simp at this
  linarith

/-- For unit `ψ` and any local rotation `u`: `|⟨ψ|u ψ̄⟩|^{2k} ≤ 1 - a(ψ)²`
(the pure-state estimate `2|a| ≤ ‖ψ^{⊗k} - (uψ̄)^{⊗k}‖₁`). -/
theorem OddObs.sq_le {n k : ℕ} (O : OddObs n k) (ψ : Ψ n) (hψ : nsq ψ = 1)
    (u : Fin n → Op1) (hu : ∀ i, SU2 (u i)) :
    (Complex.normSq (ip ψ (rot u (cj ψ)))) ^ k ≤ 1 - (O.a ψ).re ^ 2 := by
  set q0 := rot u (cj ψ) with hq0
  have hq1 : nsq q0 = 1 := by rw [hq0, nsq_rot u hu, nsq_cj, hψ]
  set z := ip ψ q0 ^ k with hz
  obtain ⟨c, hc1, hcz⟩ := exists_phase z
  have hcn : Complex.normSq c = 1 := by
    have := Complex.normSq_eq_conj_mul_self (z := c)
    rw [hc1] at this; exact_mod_cast this
  set p := kpow k ψ with hp
  set q := c • kpow k q0 with hq
  have hpn : knsq p = 1 := by rw [hp, knsq_kpow, hψ, one_pow]
  have hqn : knsq q = 1 := by rw [hq, knsq_smul, hcn, knsq_kpow, hq1, one_pow, one_mul]
  have hpq : kip p q = (‖z‖ : ℂ) := by
    rw [hq, kip_smul_right, hp, kip_kpow, ← hz, hcz]
  have hr : (kip p q).re = ‖z‖ := by rw [hpq]; simp
  have hplus : knsq (p + q) = 2 + 2 * ‖z‖ := by rw [knsq_add, hpn, hqn, hr]; ring
  have hminus : knsq (p - q) = 2 - 2 * ‖z‖ := by rw [knsq_sub, hpn, hqn, hr]; ring
  have hd := kform_diff_le O.A O.bound p q
  rw [hplus, hminus] at hd
  have haq : kform O.A q q = - conj (O.a ψ) := by
    rw [hq, kform_smul_self, hc1, one_mul]
    have := O.inv u hu (cj ψ)
    rw [← hq0] at this
    rw [this]
    exact O.a_cj ψ
  have hap : kform O.A p p = O.a ψ := rfl
  rw [hap, haq] at hd
  have hre : (O.a ψ - - conj (O.a ψ)) = ((2 * (O.a ψ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  rw [hre, Complex.normSq_ofReal] at hd
  have hz2 : ‖z‖ ^ 2 = (Complex.normSq (ip ψ q0)) ^ k := by
    rw [hz, norm_pow, ← pow_mul, mul_comm, pow_mul, Complex.normSq_eq_norm_sq]
  nlinarith


/-- `F_K(ψ)^k ≤ 1 - a(ψ)²` for a unit vector and an odd `k`-copy observable (`k ≥ 1`). -/
theorem OddObs.FKΘ_pow_le {n k : ℕ} (O : OddObs n k) (hk : 1 ≤ k) (ψ : Ψ n) (hψ : nsq ψ = 1) :
    FKΘ ψ ^ k ≤ 1 - (O.a ψ).re ^ 2 := by
  rw [FKΘ_eq_FK_cj]
  set B := 1 - (O.a ψ).re ^ 2 with hB
  have h : ∀ r ∈ rotSet ψ (cj ψ), r ^ k ≤ B := by
    rintro r ⟨u, hu, rfl⟩
    exact O.sq_le ψ hψ u hu
  have hB0 : 0 ≤ B := by
    have := h _ ⟨fun _ => 1, fun _ => SU2_one, rfl⟩
    exact le_trans (pow_nonneg (Complex.normSq_nonneg _) _) this
  have hk0 : k ≠ 0 := by omega
  set c := B ^ ((k : ℝ)⁻¹) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hB0 _
  have hck : c ^ k = B := Real.rpow_inv_natCast_pow hB0 hk0
  have hF : FK ψ (cj ψ) ≤ c := by
    refine csSup_le (rotSet_nonempty _ _) fun r hr => ?_
    refine le_of_pow_le_pow_left₀ hk0 hc0 ?_
    rw [hck]; exact h r hr
  calc FK ψ (cj ψ) ^ k ≤ c ^ k := pow_le_pow_left₀ (FK_nonneg _ _) hF k
    _ = B := hck

/-- **`thm:chiralEG`, the odd-observable bound:** `-(1/k) log(1 - a(ψ)²) ≤ C_K(ψ)`. -/
theorem OddObs.neg_log_le_CK {n k : ℕ} (O : OddObs n k) (hk : 1 ≤ k) (ψ : Ψ n) (hψ : nsq ψ = 1) :
    -(1 / (k : ℝ)) * Real.log (1 - (O.a ψ).re ^ 2) ≤ CK ψ := by
  have h := O.FKΘ_pow_le hk ψ hψ
  have hp : 0 < FKΘ ψ := FKΘ_pos ψ hψ
  have h2 := Real.log_le_log (pow_pos hp k) h
  rw [Real.log_pow] at h2
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold CK
  have : (k : ℝ) * Real.log (FKΘ ψ) ≤ Real.log (1 - (O.a ψ).re ^ 2) := h2
  rw [neg_mul, one_div, neg_le_neg_iff, ← mul_le_mul_iff_of_pos_left hk']
  rw [← mul_assoc, mul_inv_cancel₀ hk'.ne', one_mul]
  linarith

/-- **`thm:chiraldepth` (a), first half:** a nonzero odd observable value forces `F_K < 1`. -/
theorem OddObs.FKΘ_lt_one {n k : ℕ} (O : OddObs n k) (hk : 1 ≤ k) (ψ : Ψ n) (hψ : nsq ψ = 1)
    (ha : O.a ψ ≠ 0) : FKΘ ψ < 1 := by
  have h := O.FKΘ_pow_le hk ψ hψ
  have hre : (O.a ψ).re ≠ 0 := by
    intro h0
    apply ha
    exact Complex.ext h0 (O.a_im ψ)
  have hpos : 0 < (O.a ψ).re ^ 2 := by positivity
  by_contra hcon
  have : 1 ≤ FKΘ ψ ^ k := one_le_pow₀ (not_lt.1 hcon)
  linarith


/-! ### One- and two-qubit vectors are locally conjugation-invariant (`FK = 1`) -/

/-- The `SU(2)` matrix with first column `(a₀, a₁)` (for a unit vector). -/
def colSU (a0 a1 : ℂ) : Op1 := !![a0, -conj a1; a1, conj a0]

theorem normSq_cast_eq {a0 a1 : ℂ} (h : Complex.normSq a0 + Complex.normSq a1 = 1) :
    conj a0 * a0 + conj a1 * a1 = 1 := by
  have : ((Complex.normSq a0 + Complex.normSq a1 : ℝ) : ℂ) = 1 := by exact_mod_cast h
  push_cast at this
  simpa [Complex.normSq_eq_conj_mul_self] using this

theorem colSU_SU2 (a0 a1 : ℂ) (h : Complex.normSq a0 + Complex.normSq a1 = 1) :
    SU2 (colSU a0 a1) := by
  have h' := normSq_cast_eq h
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [colSU, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    · linear_combination h'
    · ring
    · ring
    · linear_combination h'
  · simp only [colSU, Matrix.det_fin_two_of]
    linear_combination h'

theorem exists_SU2_map (a b : Fin 2 → ℂ)
    (h : Complex.normSq (a 0) + Complex.normSq (a 1) = Complex.normSq (b 0) + Complex.normSq (b 1)) :
    ∃ u : Op1, SU2 u ∧ u.mulVec a = b := by
  by_cases hs : Complex.normSq (a 0) + Complex.normSq (a 1) = 0
  · have ha0 : a 0 = 0 := by
      have := Complex.normSq_nonneg (a 0); have := Complex.normSq_nonneg (a 1)
      exact Complex.normSq_eq_zero.1 (by linarith)
    have ha1 : a 1 = 0 := by
      have := Complex.normSq_nonneg (a 0); have := Complex.normSq_nonneg (a 1)
      exact Complex.normSq_eq_zero.1 (by linarith)
    have hb0 : b 0 = 0 := by
      have := Complex.normSq_nonneg (b 0); have := Complex.normSq_nonneg (b 1)
      exact Complex.normSq_eq_zero.1 (by linarith)
    have hb1 : b 1 = 0 := by
      have := Complex.normSq_nonneg (b 0); have := Complex.normSq_nonneg (b 1)
      exact Complex.normSq_eq_zero.1 (by linarith)
    refine ⟨1, SU2_one, ?_⟩
    funext i; fin_cases i <;> simp [ha0, ha1, hb0, hb1]
  · have hpos : 0 < Complex.normSq (a 0) + Complex.normSq (a 1) :=
      lt_of_le_of_ne (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Ne.symm hs)
    set s := Complex.normSq (a 0) + Complex.normSq (a 1) with hsdef
    set r := Real.sqrt s with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = s := Real.sq_sqrt hpos.le
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hA : Complex.normSq (a 0 / r) + Complex.normSq (a 1 / r) = 1 := by
      simp only [map_div₀, Complex.normSq_ofReal]
      field_simp
      nlinarith
    have hB : Complex.normSq (b 0 / r) + Complex.normSq (b 1 / r) = 1 := by
      simp only [map_div₀, Complex.normSq_ofReal]
      field_simp
      nlinarith
    refine ⟨colSU (b 0 / r) (b 1 / r) * (colSU (a 0 / r) (a 1 / r))ᴴ,
      SU2_mul (colSU_SU2 _ _ hB) (SU2_adjoint (colSU_SU2 _ _ hA)), ?_⟩
    have hs' : conj (a 0) * a 0 + conj (a 1) * a 1 = (r : ℂ) ^ 2 := by
      have : ((s : ℝ) : ℂ) = (r : ℂ) ^ 2 := by exact_mod_cast hr2.symm
      rw [← this, hsdef]; push_cast
      simp [Complex.normSq_eq_conj_mul_self]
    funext i
    fin_cases i <;>
      simp [colSU, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two]
    · field_simp
      linear_combination (b 0) * hs'
    · field_simp
      linear_combination (b 1) * hs'


theorem mulVec_conj_map (u : Op1) (a : Fin 2 → ℂ) :
    (u.map conj).mulVec a = fun i => conj (u.mulVec (fun j => conj (a j)) i) := by
  funext i; simp [Matrix.mulVec, dotProduct, map_mul]

theorem normSq_sum_pos {a : Fin 2 → ℂ} (ha : a ≠ 0) :
    0 < Complex.normSq (a 0) + Complex.normSq (a 1) := by
  by_contra h
  apply ha
  have h0 := Complex.normSq_nonneg (a 0)
  have h1 := Complex.normSq_nonneg (a 1)
  funext i
  fin_cases i
  · exact Complex.normSq_eq_zero.1 (by simp only [Fin.zero_eta, Fin.isValue]; linarith)
  · exact Complex.normSq_eq_zero.1 (by simp only [Fin.mk_one, Fin.isValue]; linarith)

/-- Two orthogonal vectors `a ≠ 0`, `b` in `ℂ²`: one `SU(2)` element and phase `λ` with
`u ā = λ a` and `u b̄ = λ b`. -/
theorem exists_su2_pair (a b : Fin 2 → ℂ) (ha : a ≠ 0)
    (hab : conj (a 0) * b 0 + conj (a 1) * b 1 = 0) :
    ∃ u : Op1, SU2 u ∧ ∃ lam : ℂ, conj lam * lam = 1 ∧
      u.mulVec (fun j => conj (a j)) = lam • a ∧ u.mulVec (fun j => conj (b j)) = lam • b := by
  have hspos := normSq_sum_pos ha
  have hs : conj (a 0) * a 0 + conj (a 1) * a 1 ≠ 0 := by
    intro h
    have : ((Complex.normSq (a 0) + Complex.normSq (a 1) : ℝ) : ℂ) = 0 := by
      push_cast
      simpa [Complex.normSq_eq_conj_mul_self] using h
    have := (Complex.ofReal_eq_zero.1 this)
    linarith
  set s := conj (a 0) * a 0 + conj (a 1) * a 1 with hsdef
  set t := (a 1 * b 0 - a 0 * b 1) / s with htdef
  have hb0 : b 0 = t * conj (a 1) := by
    rw [htdef]; field_simp; linear_combination (a 0) * hab
  have hb1 : b 1 = -t * conj (a 0) := by
    rw [htdef]; field_simp; linear_combination (a 1) * hab
  clear_value t s
  by_cases ht : t = 0
  · have hb0' : b 0 = 0 := by rw [hb0, ht]; ring
    have hb1' : b 1 = 0 := by rw [hb1, ht]; ring
    obtain ⟨u, hu, hua⟩ := exists_SU2_map (fun j => conj (a j)) a (by simp)
    refine ⟨u, hu, 1, by simp, by simpa using hua, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, hb0', hb1']
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (conj t / t) (n := 2) (by norm_num)
    have htn : Complex.normSq t ≠ 0 := by simpa using ht
    have hzn : Complex.normSq z = 1 := by
      have h1 : Complex.normSq (z ^ 2) = 1 := by
        rw [hz, map_div₀, Complex.normSq_conj]; field_simp
      rw [map_pow] at h1
      have h2 := Complex.normSq_nonneg z
      nlinarith
    have hz1 : conj z * z = 1 := by
      have := Complex.normSq_eq_conj_mul_self (z := z)
      rw [hzn] at this; exact_mod_cast this.symm
    obtain ⟨u, hu, hua⟩ := exists_SU2_map (fun j => conj (a j)) (z • a) (by
      simp [Complex.normSq_mul, hzn])
    refine ⟨u, hu, z, hz1, hua, ?_⟩
    have hzt : conj t * conj z = z * t := by
      have h3 : conj t = z ^ 2 * t := by rw [hz]; field_simp
      rw [h3]
      linear_combination (z * t) * hz1
    have hbar : (fun j => conj (b j)) = (conj t) • eps.mulVec a := by
      funext i
      fin_cases i <;> simp [eps, dotProduct, hb0, hb1]
    have key : u.mulVec (eps.mulVec a) = eps.mulVec ((u.map conj).mulVec a) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← SU2_eps_conj hu]
    rw [hbar, Matrix.mulVec_smul, key, mulVec_conj_map, hua]
    funext i
    fin_cases i <;> simp [eps, dotProduct, hb0, hb1]
    · linear_combination (conj (a 1)) * hzt
    · linear_combination (conj (a 0)) * hzt


theorem exists_unitary_diag (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ, Vᴴ * V = 1 ∧ (Vᴴ * H * V) 0 1 = 0 := by
  have h := hH.conjStarAlgAut_star_eigenvectorUnitary
  set U := hH.eigenvectorUnitary with hU
  refine ⟨(U : Matrix (Fin 2) (Fin 2) ℂ), ?_, ?_⟩
  · exact Unitary.coe_star_mul_self U
  · have h2 : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * H * (U : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using h
    rw [h2]; simp

theorem mat_of_cols (u K : Op1) (lam : ℂ)
    (h0 : u.mulVec (fun l => conj (K l 0)) = lam • fun l => K l 0)
    (h1 : u.mulVec (fun l => conj (K l 1)) = lam • fun l => K l 1) :
    u * K.map conj = lam • K := by
  ext i j
  fin_cases j
  · have := congrFun h0 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · have := congrFun h1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- Schmidt decomposition, in the form needed: `M̄` and `M` are related by local `SU(2)`
rotations up to a phase (`ψ` and `ψ̄` are locally equivalent for two qubits). -/
theorem svd_lite (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ≠ 0) :
    ∃ U0 U1 : Op1, SU2 U0 ∧ SU2 U1 ∧ ∃ μ : ℂ, conj μ * μ = 1 ∧
      U0 * M.map conj * U1ᵀ = μ • M := by
  obtain ⟨V, hV, hoff⟩ := exists_unitary_diag (Mᴴ * M) (Matrix.isHermitian_conjTranspose_mul_self M)
  have hVV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  set K := M * V with hK
  have hMK : M = K * Vᴴ := by rw [hK, Matrix.mul_assoc, hVV', Matrix.mul_one]
  have hKK : (Kᴴ * K) 0 1 = 0 := by
    have : Kᴴ * K = Vᴴ * (Mᴴ * M) * V := by
      rw [hK, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this]; exact hoff
  have hortho : conj (K 0 0) * K 0 1 + conj (K 1 0) * K 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using hKK
  have hKne : K ≠ 0 := by intro h; apply hM; rw [hMK, h, Matrix.zero_mul]
  have hu : ∃ u : Op1, SU2 u ∧ ∃ lam : ℂ, conj lam * lam = 1 ∧ u * K.map conj = lam • K := by
    by_cases h0 : (fun i => K i 0) = 0
    · have h1 : (fun i => K i 1) ≠ 0 := by
        intro h1; apply hKne; ext i j; fin_cases j
        · exact congrFun h0 i
        · exact congrFun h1 i
      have e0 : K 0 0 = 0 := congrFun h0 0
      have e1 : K 1 0 = 0 := congrFun h0 1
      obtain ⟨u, hu, lam, hl, ha, hb⟩ := exists_su2_pair (fun i => K i 1) (fun i => K i 0) h1
        (by simp [e0, e1])
      exact ⟨u, hu, lam, hl, mat_of_cols u K lam hb ha⟩
    · obtain ⟨u, hu, lam, hl, ha, hb⟩ := exists_su2_pair (fun i => K i 0) (fun i => K i 1) h0
        (by simpa using hortho)
      exact ⟨u, hu, lam, hl, mat_of_cols u K lam ha hb⟩
  obtain ⟨u0, hu0, lam, hl, hK2⟩ := hu
  set Vc := V.map conj with hVc
  have hVtV : Vᵀ * Vc = 1 := by
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.map conj) hV
    simp only [Matrix.map_mul, Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)] at this
    have e : (Vᴴ).map conj = Vᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
    rwa [e] at this
  set d := V.det with hd
  have hd1 : conj d * d = 1 := by
    have := congrArg Matrix.det hV
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    simpa using this
  have hcT : Vcᵀ = Vᴴ := rfl
  have hHT : (Vᴴ)ᵀ = Vc := by ext i j; simp [Matrix.conjTranspose_apply, hVc]
  refine ⟨u0, d • (Vc * Vᴴ), hu0, ⟨?_, ?_⟩, lam * d, ?_, ?_⟩
  · -- unitarity of `d • (V̄ Vᴴ)`
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    have h1 : (Vᴴ)ᴴ * (Vc)ᴴ * (Vc * Vᴴ) = 1 := by
      have e : (Vc)ᴴ = Vᵀ := by ext i j; simp [Matrix.conjTranspose_apply, hVc]
      rw [e, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ,
        hVtV, Matrix.one_mul, hVV']
    rw [h1]
    have : star d * d = 1 := hd1
    rw [this, one_smul]
  · rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_conjTranspose]
    have : Vc.det = conj d := by
      rw [hVc, hd]
      exact (RingHom.map_det (starRingEnd ℂ) V).symm
    simp only [Fintype.card_fin, this]
    have h2 : (d * conj d) = 1 := by rw [mul_comm]; exact hd1
    calc d ^ 2 * (conj d * star d) = (d * conj d) ^ 2 := by simp; ring
      _ = 1 := by rw [h2]; norm_num
  · rw [map_mul, mul_comm (conj lam), ← mul_assoc, mul_comm (conj d)]
    calc _ = (conj lam * lam) * (conj d * d) := by ring
      _ = 1 := by rw [hl, hd1, one_mul]
  · have hMc : M.map conj = K.map conj * Vᵀ := by
      conv_lhs => rw [hMK]
      rw [Matrix.map_mul]
      congr 1
      ext i j; simp [Matrix.conjTranspose_apply]
    have hTr : (d • (Vc * Vᴴ))ᵀ = d • (Vc * Vᴴ) := by
      rw [Matrix.transpose_smul, Matrix.transpose_mul, hcT, hHT]
    rw [hTr, hMc]
    calc u0 * (K.map conj * Vᵀ) * (d • (Vc * Vᴴ))
        = d • ((u0 * K.map conj) * (Vᵀ * Vc) * Vᴴ) := by
          simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (lam * d) • M := by
          rw [hK2, hVtV, Matrix.mul_one, Matrix.smul_mul, ← hMK, smul_smul, mul_comm d]


/-- Two-qubit vector from a `2 × 2` coefficient matrix. -/
def vec2 (M : Matrix (Fin 2) (Fin 2) ℂ) : Ψ 2 := fun x => M (x 0) (x 1)

/-- One-qubit vector from its two amplitudes. -/
def vec1 (a : Fin 2 → ℂ) : Ψ 1 := fun x => a (x 0)

theorem rot_vec2 (u : Fin 2 → Op1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rot u (vec2 M) = vec2 (u 0 * M * (u 1)ᵀ) := by
  funext x
  simp only [rot, vec2]
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 2) _
    (fun p : Fin 2 × Fin 2 => (u 0 (x 0) p.1 * u 1 (x 1) p.2) * M p.1 p.2)]
  · rw [Fintype.sum_prod_type]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  · intro y
    simp [Fin.prod_univ_two, piFinTwoEquiv]

theorem rot_vec1 (u : Fin 1 → Op1) (a : Fin 2 → ℂ) :
    rot u (vec1 a) = vec1 ((u 0).mulVec a) := by
  funext x
  simp only [rot, vec1]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _
    (fun b : Fin 2 => u 0 (x 0) b * a b)]
  · simp [Matrix.mulVec, dotProduct]
  · intro y
    simp [Equiv.funUnique]

theorem ip_smul_right {n : ℕ} (c : ℂ) (ψ φ : Ψ n) : ip ψ (c • φ) = c * ip ψ φ := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem exists_rot_cj_two (ψ : Ψ 2) (hψ : nsq ψ = 1) :
    ∃ u : Fin 2 → Op1, (∀ i, SU2 (u i)) ∧ ∃ lam : ℂ, conj lam * lam = 1 ∧
      rot u (cj ψ) = lam • ψ := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => ψ ![i, j] with hM
  have hψM : ψ = vec2 M := by
    funext x
    have : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
    simp [vec2, hM, this]
  have hMne : M ≠ 0 := by
    intro h
    have : ψ = 0 := by rw [hψM, h]; funext x; simp [vec2]
    rw [this] at hψ
    simp [nsq] at hψ
  obtain ⟨U0, U1, h0, h1, μ, hμ, hrel⟩ := svd_lite M hMne
  refine ⟨![U0, U1], ?_, μ, hμ, ?_⟩
  · intro i; fin_cases i
    · exact h0
    · exact h1
  · have hc : cj ψ = vec2 (M.map conj) := by rw [hψM]; rfl
    rw [hc, rot_vec2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hrel, hψM]
    funext x; simp [vec2]

theorem exists_rot_cj_one (ψ : Ψ 1) :
    ∃ u : Fin 1 → Op1, (∀ i, SU2 (u i)) ∧ ∃ lam : ℂ, conj lam * lam = 1 ∧
      rot u (cj ψ) = lam • ψ := by
  set a : Fin 2 → ℂ := fun i => ψ (fun _ => i) with ha
  have hψa : ψ = vec1 a := by
    funext x
    have : (fun _ : Fin 1 => x 0) = x := by funext i; fin_cases i; rfl
    simp [vec1, ha, this]
  obtain ⟨u, hu, hua⟩ := exists_SU2_map (fun j => conj (a j)) a (by simp)
  refine ⟨fun _ => u, fun _ => hu, 1, by simp, ?_⟩
  have hc : cj ψ = vec1 (fun j => conj (a j)) := by rw [hψa]; rfl
  rw [hc, rot_vec1, hua, hψa]
  funext x; simp [vec1]

/-- A rotation taking `ψ̄` to a phase times `ψ` gives `F_K(ψ) = 1`. -/
theorem FKΘ_eq_one_of_rot {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (u : Fin n → Op1)
    (hu : ∀ i, SU2 (u i)) (lam : ℂ) (hl : conj lam * lam = 1) (h : rot u (cj ψ) = lam • ψ) :
    FKΘ ψ = 1 := by
  rw [FKΘ_eq_FK_cj]
  apply le_antisymm
  · have := FK_le ψ (cj ψ)
    rwa [hψ, nsq_cj, hψ, one_mul] at this
  · have := le_FK ψ (cj ψ) u hu
    rw [h, ip_smul_right, ip_self, hψ, map_mul] at this
    have hn : Complex.normSq lam = 1 := by
      have := Complex.normSq_eq_conj_mul_self (z := lam)
      rw [hl] at this; exact_mod_cast this
    simpa [hn] using this

/-- **Schmidt:** a pure state of one or two qubits has `F_K = 1` (`C_K = 0`). -/
theorem FKΘ_eq_one_of_le_two {b : ℕ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (ψ : Ψ b) (hψ : nsq ψ = 1) :
    FKΘ ψ = 1 := by
  interval_cases b
  · obtain ⟨u, hu, lam, hl, h⟩ := exists_rot_cj_one ψ
    exact FKΘ_eq_one_of_rot ψ hψ u hu lam hl h
  · obtain ⟨u, hu, lam, hl, h⟩ := exists_rot_cj_two ψ hψ
    exact FKΘ_eq_one_of_rot ψ hψ u hu lam hl h


/-! ### `thm:chiraldepth` (a), `thm:chiralEG` chain, `prop:exponentdepth` (b) -/

theorem CK_nonneg {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : 0 ≤ CK ψ := by
  unfold CK
  have h1 : FKΘ ψ ≤ 1 := by
    have := FK_le ψ (Θ ψ)
    rwa [nsq_Θ, hψ, one_mul] at this
  have := Real.log_nonpos (FKΘ_pos ψ hψ).le h1
  linarith

/-- Blocks of at most two qubits: a `2`-producible pure state has `F_K = 1`. -/
theorem Producible.FKΘ_eq_one {n : ℕ} {ψ : Ψ n} (h : Producible 2 ψ) : FKΘ ψ = 1 := by
  induction h with
  | single hb1 hbm φ hφ => exact FKΘ_eq_one_of_le_two hb1 hbm φ hφ
  | cons hb1 hbm φ hφ χ _ ih => rw [FKΘ_tens, FKΘ_eq_one_of_le_two hb1 hbm φ hφ, ih, one_mul]

/-- **`thm:chiraldepth` (a).**  `F_K(ψ,ψ̄) < 1` implies that `ψ` is not `2`-producible. -/
theorem not_producible_two_of_FKΘ_lt_one {n : ℕ} {ψ : Ψ n} (h : FKΘ ψ < 1) :
    ¬ Producible 2 ψ := fun hp => by rw [hp.FKΘ_eq_one] at h; exact lt_irrefl _ h

/-- **`thm:chiraldepth` (a).**  A nonzero value `a(ψ)` of an odd `k`-copy observable (`k ≥ 1`)
certifies that the unit state `ψ` is not `2`-producible. -/
theorem OddObs.not_producible_two {n k : ℕ} (O : OddObs n k) (hk : 1 ≤ k) (ψ : Ψ n)
    (hψ : nsq ψ = 1) (ha : O.a ψ ≠ 0) : ¬ Producible 2 ψ :=
  not_producible_two_of_FKΘ_lt_one (O.FKΘ_lt_one hk ψ hψ ha)

/-- **`thm:chiralEG`, the chain** (qubits, the part not using `ξ_inv`):
`-(1/2k) log(1 - a²) ≤ C_K/2 ≤ E_G`. -/
theorem OddObs.chiralEG_chain {n k : ℕ} (O : OddObs n k) (hk : 1 ≤ k) (ψ : Ψ n) (hψ : nsq ψ = 1) :
    -(1 / (2 * (k : ℝ))) * Real.log (1 - (O.a ψ).re ^ 2) ≤ CK ψ / 2 ∧ CK ψ / 2 ≤ EG ψ := by
  refine ⟨?_, by linarith [CK_le_two_EG ψ hψ]⟩
  have h := O.neg_log_le_CK hk ψ hψ
  have e : -(1 / (2 * (k : ℝ))) * Real.log (1 - (O.a ψ).re ^ 2) =
      (-(1 / (k : ℝ)) * Real.log (1 - (O.a ψ).re ^ 2)) / 2 := by ring
  rw [e]; linarith

/-- The supremum `c₃` of `C_K` over unit three-qubit states. -/
noncomputable def c3 : ℝ := sSup {r | ∃ β : Ψ 3, nsq β = 1 ∧ r = CK β}

theorem c3_bddAbove : BddAbove {r | ∃ β : Ψ 3, nsq β = 1 ∧ r = CK β} :=
  ⟨3 * Real.log 2, by rintro r ⟨β, hβ, rfl⟩; exact CK_le β hβ⟩

theorem CK_le_c3 (β : Ψ 3) (hβ : nsq β = 1) : CK β ≤ c3 :=
  le_csSup c3_bddAbove ⟨β, hβ, rfl⟩

theorem c3_nonneg : 0 ≤ c3 :=
  le_trans (CK_nonneg (zeroVec 3) (nsq_zeroVec 3)) (CK_le_c3 _ (nsq_zeroVec 3))

/-- **`prop:exponentdepth` (b).**  A pure `3`-producible state of `n` qubits has
`C_K ≤ ⌊n/3⌋ c₃`. -/
theorem CK_le_producible_three {n : ℕ} {ψ : Ψ n} (h : Producible 3 ψ) :
    CK ψ ≤ ((n / 3 : ℕ) : ℝ) * c3 := by
  induction h with
  | @single b hb1 hbm φ hφ =>
    by_cases hb : b ≤ 2
    · have : CK φ = 0 := by
        unfold CK; rw [FKΘ_eq_one_of_le_two hb1 hb φ hφ]; simp
      rw [this, Nat.div_eq_of_lt (by omega)]; simp
    · have hb3 : b = 3 := by omega
      subst hb3
      simpa using CK_le_c3 φ hφ
  | @cons b N hb1 hbm φ hφ χ hχ ih =>
    have hχ1 := hχ.nsq_eq_one
    rw [CK_tens φ χ hφ hχ1]
    have hφ' : CK φ ≤ ((b / 3 : ℕ) : ℝ) * c3 := by
      by_cases hb : b ≤ 2
      · have : CK φ = 0 := by
          unfold CK; rw [FKΘ_eq_one_of_le_two hb1 hb φ hφ]; simp
        rw [this, Nat.div_eq_of_lt (by omega)]; simp
      · have hb3 : b = 3 := by omega
        subst hb3
        simpa using CK_le_c3 φ hφ
    have hsum : (b / 3 + N / 3 : ℕ) ≤ (b + N) / 3 := Nat.div_add_div_le_add_div
    have hsum' : ((b / 3 : ℕ) : ℝ) + ((N / 3 : ℕ) : ℝ) ≤ (((b + N) / 3 : ℕ) : ℝ) := by
      exact_mod_cast hsum
    nlinarith [c3_nonneg]

/-- **`prop:exponentdepth` (b), sharpness** (given a minimiser: `Theorem threequbitminimiser` of the
paper is computer-assisted, so attainment of `c₃` is a hypothesis here): products of `m` copies of a
three-qubit state `β` with `C_K(β) = c₃` are `3`-producible with `C_K = m c₃ = ⌊n/3⌋ c₃`. -/
theorem exists_producible_three_attaining (β : Ψ 3) (hβ : nsq β = 1) (hc : CK β = c3) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ (N : ℕ) (ψ : Ψ N), N = 3 * m ∧ Producible 3 ψ ∧ CK ψ = ((N / 3 : ℕ) : ℝ) * c3 := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨3, β, rfl, Producible.single (by norm_num) le_rfl β hβ, by simp [hc]⟩
  | succ m hm ih =>
    obtain ⟨N, ψ, hN, hp, hCK⟩ := ih
    subst hN
    refine ⟨3 + 3 * m, tens β ψ, by ring, Producible.cons (by norm_num) le_rfl β hβ ψ hp, ?_⟩
    rw [CK_tens β ψ hβ hp.nsq_eq_one, hCK, hc]
    have : (3 + 3 * m) / 3 = m + 1 := by omega
    rw [this, show 3 * m / 3 = m by omega]
    push_cast; ring


/-! ### The state `M₄` (`thm:ceiling` applied; `thm:m4support`, `thm:m4exponent`) -/

/-- Four-qubit vectors of `FourQubitEntropy` as `Ψ 4`. -/
def toN (ψ : FormalResearch.FourQubitEntropy.Psi) : Ψ 4 := fun x => ψ (x 0) (x 1) (x 2) (x 3)

theorem nsq_toN (ψ : FormalResearch.FourQubitEntropy.Psi) :
    nsq (toN ψ) = FormalResearch.FourQubitEntropy.normSqPsi ψ := by
  let e : (Fin 4 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2 :=
    { toFun := fun x => (x 0, x 1, x 2, x 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := fun x => by funext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }
  unfold nsq FormalResearch.FourQubitEntropy.normSqPsi
  calc ∑ x, Complex.normSq (toN ψ x)
      = ∑ p : Fin 2 × Fin 2 × Fin 2 × Fin 2, Complex.normSq (ψ p.1 p.2.1 p.2.2.1 p.2.2.2) :=
        Fintype.sum_equiv e _ _ (fun x => rfl)
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- `M₄` as an `n = 4` vector. -/
noncomputable def M4v : Ψ 4 := toN FormalResearch.FourQubitEntropy.M4

theorem nsq_M4v : nsq M4v = 1 := by
  unfold M4v; rw [nsq_toN]; exact FormalResearch.FourQubitEntropy.M4_unit

/-- **`thm:m4support`, lower half** (from `thm:ceiling`): `F_C(M₄) ≥ 1/2`. -/
theorem half_le_FCΘ_M4 (hR : RealRep3) : 1 / 2 ≤ FCΘ M4v := ceiling_half hR M4v nsq_M4v

/-- `M₄` is uncalibrated: if `F_K(M₄) = 4/9` (its lower bound is proved in
`FrameFree/PhysicalBridge.lean`, `four_ninths_le_rotOverlap_M4`; the upper bound is the
recalled input R7), then `F_K(M₄) < 1/2 ≤ F_C(M₄)`. -/
theorem M4_uncalibrated (hR : RealRep3) (h49 : FKΘ M4v = 4 / 9) : FKΘ M4v < FCΘ M4v := by
  have := half_le_FCΘ_M4 hR
  rw [h49]; linarith

/-- `m + 1` copies of `M₄`. -/
noncomputable def M4pow : (m : ℕ) → Ψ (4 * (m + 1))
  | 0 => M4v
  | m + 1 => tens (M4pow m) M4v

theorem nsq_M4pow (m : ℕ) : nsq (M4pow m) = 1 := by
  induction m with
  | zero => exact nsq_M4v
  | succ m ih => show nsq (tens (M4pow m) M4v) = 1; rw [nsq_tens, ih, nsq_M4v, one_mul]

/-- **`thm:m4exponent`, chirality side** (given `F_K(M₄) = 4/9`): `F_K(M₄^{⊗(m+1)}) = (4/9)^{m+1}`
and `C_K = (m+1) log(9/4)`. -/
theorem CK_M4pow (h49 : FKΘ M4v = 4 / 9) (m : ℕ) :
    FKΘ (M4pow m) = (4 / 9) ^ (m + 1) ∧ CK (M4pow m) = (m + 1) * Real.log (9 / 4) := by
  have hF : FKΘ (M4pow m) = (4 / 9) ^ (m + 1) := by
    induction m with
    | zero => show FKΘ M4v = (4 / 9) ^ (0 + 1); rw [h49]; norm_num
    | succ m ih => show FKΘ (tens (M4pow m) M4v) = _; rw [FKΘ_tens, ih, h49]; ring
  refine ⟨hF, ?_⟩
  unfold CK
  rw [hF, Real.log_pow]
  have : Real.log (4 / 9 : ℝ) = - Real.log (9 / 4) := by
    rw [← Real.log_inv]; norm_num
  rw [this]; push_cast; ring

/-- **`thm:m4support`/`thm:m4exponent`, detectability side:** `F_C(M₄^{⊗(m+1)}) ≥ 2^{-(m+1)}`,
so `-log F_C ≤ (m+1) log 2`. -/
theorem FCΘ_M4pow_ge (hR : RealRep3) (m : ℕ) : (1 / 2 : ℝ) ^ (m + 1) ≤ FCΘ (M4pow m) := by
  induction m with
  | zero => show (1 / 2 : ℝ) ^ (0 + 1) ≤ FCΘ M4v; simpa using half_le_FCΘ_M4 hR
  | succ m ih =>
    show (1 / 2 : ℝ) ^ (m + 1 + 1) ≤ FCΘ (tens (M4pow m) M4v)
    rw [FCΘ_tens _ _ (by rw [nsq_M4pow]; norm_num) (by rw [nsq_M4v]; norm_num), pow_succ]
    exact mul_le_mul ih (half_le_FCΘ_M4 hR) (by norm_num) (FC_nonneg _ _)

/-- Under `F_C(M₄) ≤ 1/2` (the heavy half of `thm:m4support`, not formalised) the powers have
`F_C(M₄^{⊗(m+1)}) = 2^{-(m+1)}` exactly, hence `-log F_C = (m+1) log 2 < C_K` when `F_K(M₄) = 4/9`. -/
theorem FCΘ_M4pow_eq (hR : RealRep3) (hle : FCΘ M4v ≤ 1 / 2) (m : ℕ) :
    FCΘ (M4pow m) = (1 / 2 : ℝ) ^ (m + 1) := by
  have h1 : FCΘ M4v = 1 / 2 := le_antisymm hle (half_le_FCΘ_M4 hR)
  induction m with
  | zero => show FCΘ M4v = (1 / 2 : ℝ) ^ (0 + 1); rw [h1]; norm_num
  | succ m ih =>
    show FCΘ (tens (M4pow m) M4v) = _
    rw [FCΘ_tens _ _ (by rw [nsq_M4pow]; norm_num) (by rw [nsq_M4v]; norm_num), ih, h1]
    ring

/-- The exponent window for `M₄`-powers: `-log F_C = (m+1) log 2 < (m+1) log (9/4) = C_K`. -/
theorem M4pow_window (hR : RealRep3) (hle : FCΘ M4v ≤ 1 / 2) (h49 : FKΘ M4v = 4 / 9) (m : ℕ) :
    -Real.log (FCΘ (M4pow m)) = (m + 1) * Real.log 2 ∧
      (m + 1) * Real.log 2 < CK (M4pow m) := by
  have e := FCΘ_M4pow_eq hR hle m
  have hc := (CK_M4pow h49 m).2
  refine ⟨?_, ?_⟩
  · rw [e, Real.log_pow, one_div, Real.log_inv]; push_cast; ring
  · rw [hc]
    have : Real.log 2 < Real.log (9 / 4) := Real.log_lt_log (by norm_num) (by norm_num)
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    exact mul_lt_mul_of_pos_left this hm


/-! ### `prop:nozfpchirality` -/

theorem kform_eq_dot {k n : ℕ} (E : Matrix (Copies k n) (Copies k n) ℂ) (v : Copies k n → ℂ) :
    kform E v v = star v ⬝ᵥ E.mulVec v := by
  simp [kform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem kpow_smul (k : ℕ) {n : ℕ} (c : ℂ) (φ : Ψ n) : kpow k (c • φ) = c ^ k • kpow k φ := by
  funext x
  simp [kpow, Finset.prod_mul_distrib, Finset.prod_const]

theorem kpow_eq_zero {k n : ℕ} (hk : 1 ≤ k) : kpow k (0 : Ψ n) = 0 := by
  funext x
  simp only [kpow, Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩) rfl

open scoped ComplexOrder in
/-- **`prop:nozfpchirality`.**  Let `E ≥ 0` be a `k`-copy effect (`k ≥ 1`) with
`⟨φ^{⊗k}|E|φ^{⊗k}⟩ = 0` for every real unit vector `φ`.  Then `E` annihilates every `φ^{⊗k}`, for
complex `φ` as well: it fires on no pure state. -/
theorem nozfp_chirality {n k : ℕ} (E : Matrix (Copies k n) (Copies k n) ℂ) (hE : E.PosSemidef)
    (hk : 1 ≤ k)
    (h : ∀ φ : Ψ n, cj φ = φ → nsq φ = 1 → kform E (kpow k φ) (kpow k φ) = 0) (φ : Ψ n) :
    kform E (kpow k φ) (kpow k φ) = 0 := by
  -- Step 1: `E φ^{⊗k} = 0` for every real vector.
  have hreal : ∀ φ : Ψ n, cj φ = φ → E.mulVec (kpow k φ) = 0 := by
    intro φ hφ
    by_cases h0 : nsq φ = 0
    · have : φ = 0 := by
        funext x
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (φ x))).1 h0 x
          (Finset.mem_univ x)
        simpa using this
      rw [this, kpow_eq_zero hk, Matrix.mulVec_zero]
    · have hpos : 0 < nsq φ := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        (Ne.symm h0)
      set r := Real.sqrt (nsq φ) with hr
      have hr0 : 0 < r := Real.sqrt_pos.2 hpos
      have hrc : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      set ψ' : Ψ n := ((r : ℂ)⁻¹) • φ with hψ'
      have hcj : cj ψ' = ψ' := by
        funext x
        simp only [hψ', cj, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal]
        have := congrFun hφ x
        simp only [cj] at this
        rw [this]
      have hn : nsq ψ' = 1 := by
        have : nsq ψ' = (r⁻¹) ^ 2 * nsq φ := by
          unfold nsq
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [hψ', Complex.normSq_mul]
          left; rw [sq, mul_inv]
        rw [this, inv_pow, hr, Real.sq_sqrt hpos.le]
        field_simp
      have h1 := h ψ' hcj hn
      rw [kform_eq_dot] at h1
      have h2 := (hE.dotProduct_mulVec_zero_iff).1 h1
      rw [hψ', kpow_smul, Matrix.mulVec_smul] at h2
      have hne : ((r : ℂ)⁻¹) ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero hrc)
      exact (smul_eq_zero.1 h2).resolve_left hne
  -- Step 2: polynomial interpolation in the real parameter `t`.
  set x : Ψ n := fun i => ((φ i).re : ℂ) with hx
  set y : Ψ n := fun i => ((φ i).im : ℂ) with hy
  have hφxy : φ = x + Complex.I • y := by
    funext i
    apply Complex.ext <;> simp [hx, hy]
  have hz : E.mulVec (kpow k φ) = 0 := by
    funext z
    set P : Polynomial ℂ := ∑ w : Copies k n, Polynomial.C (E z w) *
      ∏ c : Fin k, (Polynomial.C (x (w c)) + Polynomial.X * Polynomial.C (y (w c))) with hP
    have hev : ∀ s : ℂ, P.eval s = (E.mulVec (kpow k (x + s • y))) z := by
      intro s
      simp [hP, Polynomial.eval_finsetSum, Polynomial.eval_prod, Matrix.mulVec, dotProduct, kpow]
      refine Finset.sum_congr rfl fun w _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      ring
    have hP0 : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
      rintro _ ⟨t, rfl⟩
      show P.eval (t : ℂ) = 0
      rw [hev]
      have hr : cj (x + (t : ℂ) • y) = x + (t : ℂ) • y := by
        funext i
        simp [cj, hx, hy, Complex.conj_ofReal]
      have := hreal _ hr
      exact congrFun this z
    have := hev Complex.I
    rw [hP0, Polynomial.eval_zero, ← hφxy] at this
    exact this.symm
  rw [kform_eq_dot, hz]
  simp

/-- `prop:phaseaverage` in every product basis: `F_K(ψ) ≥ ∑_x |(gψ)_x|⁴` for every `g ∈ SU(2)^n`. -/
theorem ipr_rot_le_FKΘ {n : ℕ} (ψ : Ψ n) (g : Fin n → Op1) (hg : ∀ i, SU2 (g i)) :
    ∑ x, (Complex.normSq (rot g ψ x)) ^ 2 ≤ FKΘ ψ := by
  rw [FKΘ_eq_FK_cj, ← FK_cj_rot ψ g hg]
  exact ipr_le_FK_cj _

end FormalResearch.FrameFree.Ceilings
