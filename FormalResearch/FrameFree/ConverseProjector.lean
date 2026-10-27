import FormalResearch.FrameFree.Helstrom
import FormalResearch.FrameFree.HelstromSupport
import FormalResearch.FrameFree.HelstromWindow
import FormalResearch.FrameFree.TwirlsSchurWeyl

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate Matrix BigOperators ComplexOrder MatrixOrder
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

namespace FormalResearch.FrameFree.Converse

open FormalResearch.FrameFree.Twirls (OpS tensOp blockPermSpan commutant_eq_blockPermSpan
  tensOp_commute_of_mem)

/-! ### Invariant tests commute with every `k`-fold local operator -/

/-- The slot pattern: slot `(c, i)` (copy `c`, qubit `i`) carries the frame of qubit `i`. -/
def slotPat (n k : ℕ) : Fin k × Fin n → Fin n := Prod.snd

/-- `(Fin k × Fin n → Fin 2) ≃ (Fin k → Fin n → Fin 2) = Copies n k`. -/
def slotEquiv (n k : ℕ) : (Fin k × Fin n → Fin 2) ≃ Copies n k := Equiv.curry _ _ _

theorem rotK_eq_reindex {n : ℕ} (k : ℕ) (w : Fin n → Op1) :
    rotK k w = Matrix.reindex (slotEquiv n k) (slotEquiv n k) (tensOp (slotPat n k) w) := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, rotK, kron, tensOp, slotPat,
    Matrix.of_apply]
  rw [Fintype.prod_prod_type]
  rfl

/-- **Every invariant operator commutes with `rotK k w` for *all* local matrices `w`**
(Schur--Weyl, `Twirls.commutant_eq_blockPermSpan`): `E` commuting with `rotK k u`, `u ∈ SU(2)^n`,
lies in the span of the copy permutations, which commute with every `⊗ w_{π i}`. -/
theorem commute_rotK_of_inv {n k : ℕ} {E : Matrix (Copies n k) (Copies n k) ℂ}
    (hE : ∀ u : Fin n → Op1, (∀ i, SU2 (u i)) → rotK k u * E = E * rotK k u)
    (w : Fin n → Op1) : rotK k w * E = E * rotK k w := by
  set R := Matrix.reindexAlgEquiv ℂ ℂ (slotEquiv n k).symm with hR
  have hRap : ∀ M : Matrix (Copies n k) (Copies n k) ℂ,
      R M = Matrix.reindex (slotEquiv n k).symm (slotEquiv n k).symm M := fun M => rfl
  have hrk : ∀ v : Fin n → Op1, R (rotK k v) = tensOp (slotPat n k) v := by
    intro v
    rw [hRap, rotK_eq_reindex]
    ext x y
    simp [Matrix.reindex_apply]
  have h1 : R E ∈ blockPermSpan (slotPat n k) := by
    rw [← commutant_eq_blockPermSpan]
    intro u hu
    rw [← hrk u, ← map_mul, ← map_mul, hE u hu]
  have h2 := tensOp_commute_of_mem (slotPat n k) w h1
  rw [← hrk w, ← map_mul, ← map_mul] at h2
  exact R.injective h2.symm.symm

/-! ### A commuting projector can only lower the error -/

section Proj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qf_mulVec_mulVec (M U : Matrix ι ι ℂ) (v w : ι → ℂ) :
    qf M (U *ᵥ v) (U *ᵥ w) = qf (Uᴴ * M * U) v w := by
  unfold qf
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]

/-- `⟨Qa|F|Qa⟩ ≤ ⟨a|F|a⟩` for a positive `F` commuting with an orthogonal projector `Q`. -/
theorem qf_re_proj_le {F Q : Matrix ι ι ℂ} (hF : F.PosSemidef) (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q)
    (hc : Q * F = F * Q) (a : ι → ℂ) :
    (qf F (Q *ᵥ a) (Q *ᵥ a)).re ≤ (qf F a a).re := by
  have key : F - Qᴴ * F * Q = (1 - Q)ᴴ * F * (1 - Q) := by
    have h1 : Q * F * Q = F * Q := by rw [hc, Matrix.mul_assoc, hQ2]
    rw [hQ, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ]
    have h2 : F * Q * Q = F * Q := by rw [Matrix.mul_assoc, hQ2]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h1, hc, h2]
    abel
  have h0 := qf_re_nonneg (hF.conjTranspose_mul_mul_same (1 - Q)) a
  rw [← key, qf_sub_matrix, Complex.sub_re] at h0
  rw [qf_mulVec_mulVec]
  linarith

end Proj

/-! ### An unnormalised Helstrom-type bound -/

section Pure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cauchy--Schwarz for `dotProduct`. -/
theorem normSq_dot_le (x y : ι → ℂ) :
    Complex.normSq (star x ⬝ᵥ y) ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  have hx : (star x ⬝ᵥ x).re = ‖WithLp.toLp 2 x‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 x)
    rw [inner_toLp] at this
    rw [this]; norm_cast
  have hy : (star y ⬝ᵥ y).re = ‖WithLp.toLp 2 y‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 y)
    rw [inner_toLp] at this
    rw [this]; norm_cast
  rw [hx, hy, Complex.normSq_eq_norm_sq, ← mul_pow, ← inner_toLp]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem isEffect_one_sub {E : Matrix ι ι ℂ} (hE : IsEffect E) : IsEffect (1 - E) :=
  ⟨hE.2, by simpa using hE.1⟩

/-- `‖Fa‖² ≤ ⟨a|F|a⟩` for an effect `F` (`F² ≤ F`). -/
theorem sq_le_qf {F : Matrix ι ι ℂ} (hF : IsEffect F) (a : ι → ℂ) :
    (star (F *ᵥ a) ⬝ᵥ (F *ᵥ a)).re ≤ (qf F a a).re := by
  have h0 : (0 : Matrix ι ι ℂ) ≤ F := Matrix.nonneg_iff_posSemidef.2 hF.1
  have h1 : (0 : Matrix ι ι ℂ) ≤ 1 - F := Matrix.nonneg_iff_posSemidef.2 hF.2
  have hc : Commute F (1 - F) := (Commute.one_right F).sub_right (Commute.refl F)
  have hp : (F * (1 - F)).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (hc.mul_nonneg h0 h1)
  have hh : Fᴴ = F := hF.1.1
  have e : star (F *ᵥ a) ⬝ᵥ (F *ᵥ a) = qf (F * F) a a := by
    rw [← qf_one, qf_mulVec_mulVec, hh, Matrix.mul_one]
  have h2 := qf_re_nonneg hp a
  rw [Matrix.mul_sub, Matrix.mul_one, qf_sub_matrix, Complex.sub_re, ← e] at h2
  linarith

/-- **An unnormalised Helstrom-type bound**: for every effect `E`,
`|⟨a|b⟩|² ≤ 2 (‖a‖² + ‖b‖²) · err E a b`.  (Proof: `E² ≤ E`, `(1-E)² ≤ 1-E`, and Cauchy--Schwarz
on `⟨a|b⟩ = ⟨Ea|b⟩ + ⟨a|(1-E)b⟩`.) -/
theorem normSq_dot_le_err {E : Matrix ι ι ℂ} (hE : IsEffect E) (a b : ι → ℂ) :
    Complex.normSq (star a ⬝ᵥ b) ≤
      2 * ((star a ⬝ᵥ a).re + (star b ⬝ᵥ b).re) * err E a b := by
  have hF := isEffect_one_sub hE
  have hh : Eᴴ = E := hE.1.1
  set p := (star a ⬝ᵥ a).re with hp
  set q := (star b ⬝ᵥ b).re with hq
  set s1 := (star (E *ᵥ a) ⬝ᵥ (E *ᵥ a)).re with hs1
  set s2 := (star ((1 - E) *ᵥ b) ⬝ᵥ ((1 - E) *ᵥ b)).re with hs2
  have hs1n : 0 ≤ s1 := by
    have := qf_re_nonneg (Matrix.PosSemidef.one (n := ι) (R := ℂ)) (E *ᵥ a)
    rwa [qf_one] at this
  have hs2n : 0 ≤ s2 := by
    have := qf_re_nonneg (Matrix.PosSemidef.one (n := ι) (R := ℂ)) ((1 - E) *ᵥ b)
    rwa [qf_one] at this
  have hpn : 0 ≤ p := by
    have := qf_re_nonneg (Matrix.PosSemidef.one (n := ι) (R := ℂ)) a
    rwa [qf_one] at this
  have hqn : 0 ≤ q := by
    have := qf_re_nonneg (Matrix.PosSemidef.one (n := ι) (R := ℂ)) b
    rwa [qf_one] at this
  have c1 := normSq_dot_le (E *ᵥ a) b
  have c2 := normSq_dot_le a ((1 - E) *ᵥ b)
  have hsplit : star a ⬝ᵥ b = star (E *ᵥ a) ⬝ᵥ b + star a ⬝ᵥ ((1 - E) *ᵥ b) := by
    have h1 : star (E *ᵥ a) ⬝ᵥ b = star a ⬝ᵥ (E *ᵥ b) := by
      rw [Matrix.star_mulVec, hh, Matrix.dotProduct_mulVec]
    have h2 : E *ᵥ b + (1 - E) *ᵥ b = b := by rw [← Matrix.add_mulVec]; simp
    rw [h1, ← dotProduct_add, h2]
  set z1 := star (E *ᵥ a) ⬝ᵥ b with hz1
  set z2 := star a ⬝ᵥ ((1 - E) *ᵥ b) with hz2
  have hA := norm_add_le z1 z2
  have hsq : Complex.normSq (z1 + z2) ≤ (‖z1‖ + ‖z2‖) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hA2 : ‖z1‖ ^ 2 ≤ s1 * q := by rw [← Complex.normSq_eq_norm_sq]; exact c1
  have hB2 : ‖z2‖ ^ 2 ≤ p * s2 := by rw [← Complex.normSq_eq_norm_sq]; exact c2
  have hAB : 2 * (‖z1‖ * ‖z2‖) ≤ s1 * p + s2 * q := by
    by_contra hcon
    rw [not_le] at hcon
    have h0 : 0 ≤ s1 * p + s2 * q := by positivity
    have h3 : (s1 * p + s2 * q) ^ 2 < (2 * (‖z1‖ * ‖z2‖)) ^ 2 :=
      pow_lt_pow_left₀ hcon h0 (by norm_num)
    have h4 : (‖z1‖ * ‖z2‖) ^ 2 ≤ (s1 * q) * (p * s2) := by
      rw [mul_pow]
      exact mul_le_mul hA2 hB2 (by positivity) (by positivity)
    nlinarith [sq_nonneg (s1 * p - s2 * q)]
  have herr : (s1 + s2) / 2 ≤ err E a b := by
    have e1 := sq_le_qf hE a
    have e2 := sq_le_qf hF b
    unfold err
    linarith
  rw [hsplit]
  have : (‖z1‖ + ‖z2‖) ^ 2 ≤ (s1 + s2) * (p + q) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left herr (by positivity : (0 : ℝ) ≤ 2 * (p + q))]

end Pure

/-! ### The converse: a lower bound on `P_e(k)` from local rank-one projections -/

/-- `w` is a family of local orthogonal projectors (matrices `w i = (w i)ᴴ = (w i)²`). -/
def IsLocalProj {n : ℕ} (w : Fin n → Op1) : Prop := ∀ i, (w i)ᴴ = w i ∧ w i * w i = w i

theorem nsq_nonneg' {n : ℕ} (x : Ψ n) : 0 ≤ nsq x :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem copies_star_dot_re {n : ℕ} (k : ℕ) (x : Ψ n) :
    (star (copies k x) ⬝ᵥ copies k x).re = nsq x ^ k := by
  rw [star_copies_dot, ← ip_eq_dot, NQubit.ip_self]
  norm_cast

theorem copies_normSq_dot {n : ℕ} (k : ℕ) (x y : Ψ n) :
    Complex.normSq (star (copies k x) ⬝ᵥ copies k y) = Complex.normSq (NQubit.ip x y) ^ k := by
  rw [star_copies_dot, ← ip_eq_dot, map_pow]

/-- **The projector converse** (`thm:expceiling`, `lem:branchconverse`, Haar-free).  Let `w` be local
orthogonal projectors on the `n` qubits (e.g. a rank-one projector `|u⟩⟨u|` on one qubit and `1` elsewhere) and
`v ∈ SU(2)^n`.  With `x = w ψ` and `y = w v Θψ`, for every `k`
`|⟨x|y⟩|^{2k} ≤ 2 (‖x‖^{2k} + ‖y‖^{2k}) P_e(k)`.

Proof: an invariant test commutes with `(⊗ w_i)^{⊗k}` (`commute_rotK_of_inv`, Schur--Weyl), so
projecting onto its range can only lower the error; the frame `v` may be applied to one hypothesis
(`err_rot_right`); then `normSq_dot_le_err`. -/
theorem pe_lower_proj {n : ℕ} (ψ : Ψ n) (k : ℕ) {w : Fin n → Op1} (hw : IsLocalProj w)
    {v : Fin n → Op1} (hv : ∀ i, SU2 (v i)) :
    Complex.normSq (NQubit.ip (rot w ψ) (rot (fun i => w i * v i) (Θ ψ))) ^ k ≤
      2 * (nsq (rot w ψ) ^ k + nsq (rot (fun i => w i * v i) (Θ ψ)) ^ k) * Pe k ψ := by
  set x := rot w ψ with hx
  set y := rot (fun i => w i * v i) (Θ ψ) with hy
  set C : ℝ := 2 * (nsq x ^ k + nsq y ^ k) with hC
  have hC0 : 0 ≤ C := by
    have := nsq_nonneg' x; have := nsq_nonneg' y; positivity
  have hQ : (rotK k w)ᴴ = rotK k w := by
    rw [rotK_conjTranspose]; congr 1; funext i; exact (hw i).1
  have hQ2 : rotK k w * rotK k w = rotK k w := by
    rw [rotK_mul]; congr 1; funext i; exact (hw i).2
  have key : ∀ E, IsInvEffect (n := n) k E →
      Complex.normSq (NQubit.ip x y) ^ k ≤ C * err E (copies k ψ) (copies k (Θ ψ)) := by
    intro E hE
    have hcomm : rotK k w * E = E * rotK k w := commute_rotK_of_inv hE.2 w
    have hcomm1 : rotK k w * (1 - E) = (1 - E) * rotK k w := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hcomm]
    set a := copies k ψ with ha
    set b' := rotK k v *ᵥ copies k (Θ ψ) with hb'
    have h1 : err E a (copies k (Θ ψ)) = err E a b' := (err_rot_right hE v hv _ _).symm
    have h2 : err E (rotK k w *ᵥ a) (rotK k w *ᵥ b') ≤ err E a b' := by
      unfold err
      have e1 := qf_re_proj_le hE.1.1 hQ hQ2 hcomm a
      have e2 := qf_re_proj_le hE.1.2 hQ hQ2 hcomm1 b'
      linarith
    have h3 := normSq_dot_le_err hE.1 (rotK k w *ᵥ a) (rotK k w *ᵥ b')
    have ea : rotK k w *ᵥ a = copies k x := (copies_rot k w ψ).symm
    have eb : rotK k w *ᵥ b' = copies k y := by
      rw [hb', Matrix.mulVec_mulVec, rotK_mul, hy, copies_rot]
    rw [ea, eb] at h2
    rw [ea, eb, copies_normSq_dot, copies_star_dot_re, copies_star_dot_re] at h3
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left h2 hC0]
  by_cases hC' : C = 0
  · have := key 0 (isInvEffect_zero k)
    rw [hC'] at this ⊢
    simpa using this
  · have hCp : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hC')
    rw [← div_le_iff₀' hCp]
    unfold Pe
    refine le_csInf ⟨_, 0, isInvEffect_zero k, rfl⟩ ?_
    rintro r ⟨E, hE, rfl⟩
    rw [div_le_iff₀' hCp]
    exact key E hE

/-! ### Linearity of `rot`, `Θ` -/

theorem rot_add' {n : ℕ} (u : Fin n → Op1) (a b : Ψ n) : rot u (a + b) = rot u a + rot u b := by
  funext x; simp [rot, mul_add, Finset.sum_add_distrib]

theorem rot_smul' {n : ℕ} (u : Fin n → Op1) (c : ℂ) (a : Ψ n) : rot u (c • a) = c • rot u a := by
  funext x
  simp only [rot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem rot_sub' {n : ℕ} (u : Fin n → Op1) (a b : Ψ n) : rot u (a - b) = rot u a - rot u b := by
  funext x; simp [rot, mul_sub, Finset.sum_sub_distrib]

theorem cj_add' {n : ℕ} (a b : Ψ n) : cj (a + b) = cj a + cj b := by
  funext x; simp [cj]

theorem cj_smul' {n : ℕ} (c : ℂ) (a : Ψ n) : cj (c • a) = conj c • cj a := by
  funext x; simp [cj]

theorem Θ_add' {n : ℕ} (a b : Ψ n) : Θ (a + b) = Θ a + Θ b := by
  simp only [Θ_eq_rot, cj_add', rot_add']

theorem Θ_smul' {n : ℕ} (c : ℂ) (a : Ψ n) : Θ (c • a) = conj c • Θ a := by
  simp only [Θ_eq_rot, cj_smul', rot_smul']

theorem nsq_smul' {n : ℕ} (c : ℂ) (a : Ψ n) : nsq (c • a) = Complex.normSq c * nsq a := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem ip_smul_right' {n : ℕ} (c : ℂ) (a b : Ψ n) : NQubit.ip a (c • b) = c * NQubit.ip a b := by
  simp only [NQubit.ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-! ### Achiral projected branches -/

/-- `ψ` has an **achiral projected branch of weight `N`**: there are local orthogonal projectors `w`
and a frame `v ∈ SU(2)^n` such that the `w`-branch `x = wψ` (of squared norm `N > 0`) satisfies
`w v Θψ = c · x` with `|c| = 1`. (For `w = |u⟩⟨u| ⊗ 1` this says the three-qubit branch vector is
locally-unitarily real: `Converse` branch criterion.) -/
def AchiralBranch {n : ℕ} (ψ : Ψ n) (N : ℝ) : Prop :=
  0 < N ∧ ∃ (w v : Fin n → Op1) (c : ℂ), IsLocalProj w ∧ (∀ i, SU2 (v i)) ∧ ‖c‖ = 1 ∧
    nsq (rot w ψ) = N ∧ rot (fun i => w i * v i) (Θ ψ) = c • rot w ψ

/-- **`P_e(k) ≥ N^k / 4`** for a state with an achiral projected branch of weight `N`. -/
theorem pe_ge_of_achiral {n : ℕ} {ψ : Ψ n} {N : ℝ} (h : AchiralBranch ψ N) (k : ℕ) :
    N ^ k / 4 ≤ Pe k ψ := by
  obtain ⟨hN, w, v, c, hw, hv, hc, hx, hy⟩ := h
  have key := pe_lower_proj ψ k hw hv
  have hcn : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc]; norm_num
  rw [hy, ip_smul_right', NQubit.ip_self, nsq_smul', hx, map_mul, Complex.normSq_ofReal, hcn,
    one_mul] at key
  have hNk : 0 < N ^ k := pow_pos hN k
  have : N ^ k * N ^ k ≤ N ^ k * (4 * Pe k ψ) := by
    calc N ^ k * N ^ k = (N * N) ^ k := by rw [mul_pow]
      _ ≤ _ := by
        convert key using 1
        ring
  have := le_of_mul_le_mul_left this hNk
  linarith

/-! ### Tensor products: the converse tensorises (no Helstrom product inequality needed) -/

theorem tens_smul' {m n : ℕ} (c d : ℂ) (a : Ψ m) (b : Ψ n) :
    tens (c • a) (d • b) = (c * d) • tens a b := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem IsLocalProj.append {m n : ℕ} {w₁ : Fin m → Op1} {w₂ : Fin n → Op1} (h₁ : IsLocalProj w₁)
    (h₂ : IsLocalProj w₂) : IsLocalProj (Fin.append w₁ w₂) := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [Fin.append_left] using h₁ i
  · simpa only [Fin.append_right] using h₂ i

theorem su2_append {m n : ℕ} {v₁ : Fin m → Op1} {v₂ : Fin n → Op1} (h₁ : ∀ i, SU2 (v₁ i))
    (h₂ : ∀ i, SU2 (v₂ i)) : ∀ i, SU2 (Fin.append v₁ v₂ i) := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [Fin.append_left] using h₁ i
  · simpa only [Fin.append_right] using h₂ i

/-- Achiral projected branches multiply under tensor products: `N = N₁ N₂`. -/
theorem AchiralBranch.tens {m n : ℕ} {ψ₁ : Ψ m} {ψ₂ : Ψ n} {N₁ N₂ : ℝ} (h₁ : AchiralBranch ψ₁ N₁)
    (h₂ : AchiralBranch ψ₂ N₂) : AchiralBranch (tens ψ₁ ψ₂) (N₁ * N₂) := by
  obtain ⟨hN₁, w₁, v₁, c₁, hw₁, hv₁, hc₁, hx₁, hy₁⟩ := h₁
  obtain ⟨hN₂, w₂, v₂, c₂, hw₂, hv₂, hc₂, hx₂, hy₂⟩ := h₂
  refine ⟨mul_pos hN₁ hN₂, Fin.append w₁ w₂, Fin.append v₁ v₂, c₁ * c₂, hw₁.append hw₂,
    su2_append hv₁ hv₂, by rw [norm_mul, hc₁, hc₂, one_mul], ?_, ?_⟩
  · rw [rot_tens, nsq_tens]
    simp only [Fin.append_left, Fin.append_right]
    rw [hx₁, hx₂]
  · have e : (fun i => Fin.append w₁ w₂ i * Fin.append v₁ v₂ i) =
        Fin.append (fun i => w₁ i * v₁ i) (fun i => w₂ i * v₂ i) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    rw [e, Θ_tens, rot_tens, rot_tens]
    simp only [Fin.append_left, Fin.append_right]
    rw [hy₁, hy₂, tens_smul']

end FormalResearch.FrameFree.Converse
