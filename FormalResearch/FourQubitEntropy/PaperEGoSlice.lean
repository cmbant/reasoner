import FormalResearch.FourQubitEntropy.PaperEFidelityFloor

/-!
# `thm:fqe-global-overlap`: the normal-slice interface and the reduction to it

Paper E, `global_overlap_certificate.tex` (`thm:fqe-global-overlap`, `Q ≥ 1 - Φ`).

The paper proves `Q ≥ 1 - Φ` by (i) moving a closest point of the HS orbit union `𝓜` to
`Z_* = diag(√3, i, i, i)/√6` and reading off a 19-real-coordinate *normal slice*
`Z = √3 X + i Y` (`eq:fqe-slice-stationary`), (ii) the positivity constraints at a closest point
(`K₀, K₁` Procrustes, the height Hessian `H`, the lower-frame matrices `L`, the fidelity-floor matrix
`B₀`, the rays `g_η ≥ 0`), and (iii) a rational polynomial certificate that `(Q - n² e)/36 ≥ 0` on the
slice subject to these constraints.

This file fixes, as Lean definitions, **exactly** the objects of the slice
(`sX`, `sY` in the 19 coordinates `t u₁u₂u₃ a₁a₂a₃ e₁₂e₁₃e₂₃ b₁₂b₁₃b₂₃ p₁p₂p₃ q₁q₂q₃`, the same order as
`NAMES` in `code/orbit_certificate_polynomials.py`), the target polynomial `sliceTarget`, the
constraint matrices, and the Prop

* `GOSliceCertificate : ∀ v, SliceConstraints v → 0 ≤ sliceTarget v`

that the polynomial certificate has to discharge (**not proved here**).  The theorem
`globalOverlap_of_slice` shows that `GOSliceCertificate`, together with the two reduction
hypotheses `SliceQIdentity` and `SliceNormalForm` (statements below; each is proved or reduced in
the later `PaperEGoSlice*` modules, see the `THEOREM_MAP.md` rows), gives `GlobalOverlap ψ` for every
unit `ψ`.

**Conventions (all polynomial, rational coefficients in the 19 reals).**
`sliceTarget v = (sliceQ v - n(v)² e(v))/36` with `n = 3‖X‖² + ‖Y‖²`, `h₀ = 6t + a₁+a₂+a₃`,
`e = n - h₀²/6`; `sliceQ` is the `Q` of `defects` in the Python checker (`27 n p₂ - 18 p₃ - 18 ‖N‖² - 4 n³`
in real form).  Matrix constraints are stated as nonnegativity of the quadratic form
(`QF K := ∀ w, 0 ≤ ∑ᵢⱼ wᵢ Kᵢⱼ wⱼ`), which is what the module `∑ G_ab v_aᵀ B v_b` needs.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-- A point of the 19-coordinate normal slice, in the order
`t u₁ u₂ u₃ a₁ a₂ a₃ e₁₂ e₁₃ e₂₃ b₁₂ b₁₃ b₂₃ p₁ p₂ p₃ q₁ q₂ q₃` (indices `0,…,18`). -/
abbrev SV := Fin 19 → ℝ

/-- Real part `X` of the slice matrix `Z = √3 X + i Y` (`eq:fqe-slice-stationary` parametrisation). -/
def sX (v : SV) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![v 0, v 13, v 14, v 15;
     v 16 / 3, v 1, v 7 + v 10, v 8 + v 11;
     v 17 / 3, v 7 - v 10, v 2, v 9 + v 12;
     v 18 / 3, v 8 - v 11, v 9 - v 12, v 3]

/-- Imaginary part `Y` of the slice matrix. -/
def sY (v : SV) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![v 1 + v 2 + v 3, v 16, v 17, v 18;
     3 * v 13, v 0 + v 4, -v 7 / 2, -v 8 / 2;
     3 * v 14, -v 7 / 2, v 0 + v 5, -v 9 / 2;
     3 * v 15, -v 8 / 2, -v 9 / 2, v 0 + v 6]

/-- Squared Frobenius norm of a real `4×4` matrix. -/
def fn4 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- `n = 3‖X‖² + ‖Y‖²`, the squared norm of `Z`. -/
def sN (v : SV) : ℝ := 3 * fn4 (sX v) + fn4 (sY v)

/-- `h₀ = 6t + a₁ + a₂ + a₃ = √6 ⟨Z_*, Z⟩`. -/
def sH0 (v : SV) : ℝ := 6 * v 0 + v 4 + v 5 + v 6

/-- `e = n - h₀²/6` (`= 1 - Φ` at a unit closest point). -/
def sE (v : SV) : ℝ := sN v - sH0 v ^ 2 / 6

/-- The slice matrix `Z = √3 X + i Y` (magic coordinates). -/
noncomputable def sZ (v : SV) : Mat4 := Matrix.of fun p q =>
  (((Real.sqrt 3 * sX v (pairIdx p) (pairIdx q) : ℝ) : ℂ) +
    Complex.I * ((sY v (pairIdx p) (pairIdx q) : ℝ) : ℂ))

/-- The four-qubit vector whose magic coordinates are the slice matrix. -/
noncomputable def sState (v : SV) : Psi := ofZmat (magicB * sZ v * magicBᵀ)

/-! ### The sextic `Q` on the slice (the `defects` of the Python checker) -/

def sA (v : SV) : Matrix (Fin 4) (Fin 4) ℝ := (3 : ℝ) • (sX v * (sX v)ᵀ) + sY v * (sY v)ᵀ
def sB (v : SV) : Matrix (Fin 4) (Fin 4) ℝ := sY v * (sX v)ᵀ - sX v * (sY v)ᵀ
def sC (v : SV) : Matrix (Fin 4) (Fin 4) ℝ := (3 : ℝ) • ((sX v)ᵀ * sX v) - (sY v)ᵀ * sY v
def sD (v : SV) : Matrix (Fin 4) (Fin 4) ℝ := (sX v)ᵀ * sY v + (sY v)ᵀ * sX v
/-- `s = tr Zᵀ Z = sR + i √3 sI`. -/
def sR (v : SV) : ℝ := Matrix.trace (sC v)
def sI (v : SV) : ℝ := 2 * ∑ i, ∑ j, sX v i j * sY v i j
/-- `N = Z Zᵀ Z - s Z / 2 = √3 Nr + i Ni`. -/
def sNr (v : SV) : Matrix (Fin 4) (Fin 4) ℝ :=
  sX v * sC v - sY v * sD v - (sR v / 2) • sX v + (sI v / 2) • sY v
def sNi (v : SV) : Matrix (Fin 4) (Fin 4) ℝ :=
  (3 : ℝ) • (sX v * sD v) + sY v * sC v - (sR v / 2) • sY v - (3 * sI v / 2) • sX v

/-- `Q = 27 n tr[(ZZ†)²] - 18 tr[(ZZ†)³] - 18 ‖Z Zᵀ Z - sZ/2‖² - 4 n³` (`eq:fqe-global-intrinsic`),
in real form (`p₂ = tr A² - 3 tr B²`, `p₃ = tr A³ - 9 tr A B²`, `‖N‖² = 3‖Nr‖² + ‖Ni‖²`). -/
def sliceQ (v : SV) : ℝ :=
  27 * sN v * (Matrix.trace (sA v * sA v) - 3 * Matrix.trace (sB v * sB v))
    - 18 * (Matrix.trace (sA v * sA v * sA v) - 9 * Matrix.trace (sA v * sB v * sB v))
    - 18 * (3 * fn4 (sNr v) + fn4 (sNi v)) - 4 * sN v ^ 3

/-- The homogeneous sextic target `(Q - n² e)/36` of the certificate
(`eq:fqe-global-overlap-sos`, left side). -/
def sliceTarget (v : SV) : ℝ := (sliceQ v - sN v ^ 2 * sE v) / 36

/-! ### The constraint matrices -/

/-- Nonnegativity of a quadratic form. -/
def QF {m : ℕ} (K : Fin m → Fin m → ℝ) : Prop := ∀ w : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, w i * K i j * w j

/-- Procrustes matrix `K₀ = √6 Re (Z Z_*†)`. -/
def sK0 (v : SV) : Fin 4 → Fin 4 → ℝ := fun i j => if j = 0 then 3 * sX v i j else sY v i j

/-- Procrustes matrix `K₁ = √6 Re (Z_*† Z)`. -/
def sK1 (v : SV) : Fin 4 → Fin 4 → ℝ := fun i j => if i = 0 then 3 * sX v i j else sY v i j

/-- The lower block `Y₃ = (Y_{jk})_{j,k=1}^3`. -/
def sY3 (v : SV) : Fin 3 → Fin 3 → ℝ := fun j k => sY v j.succ k.succ

/-- `S = Sym (X_{jk})_{j,k=1}^3`. -/
def sS (v : SV) : Fin 3 → Fin 3 → ℝ := fun j k => (sX v j.succ k.succ + sX v k.succ j.succ) / 2

/-- The lower-frame matrix `L_{σ₀,σ,c,s}` (`c = cos φ`, `s = sin φ/√3`). -/
def sL (v : SV) (σ₀ σ c s : ℝ) : Fin 3 → Fin 3 → ℝ := fun j k =>
  (if j = k then sH0 v - c * (σ₀ * sY v 0 0 + σ * ∑ i, sY3 v i i)
      - 3 * s * (-σ₀ * sX v 0 0 - σ * ∑ i, sS v i i) else 0)
    - c * (3 * sS v j k - σ * sY3 v j k) - 3 * s * (sY3 v j k + σ * sS v j k)

/-- The fidelity-floor matrix `B₀`. -/
def sB0 (v : SV) : Fin 2 → Fin 2 → ℝ :=
  !![sH0 v ^ 2 - sN v + sR v, sI v; sI v, (sH0 v ^ 2 - sN v - sR v) / 3]

/-! ### The height Hessian `H` (`eq:fqe-height-matrix`) -/

/-- An infinitesimal action `(X,Y) ↦ (L X - X R - p Y, L Y - Y R + 3 p X)` on `Z = √3 X + i Y`. -/
structure Gen where
  L : Matrix (Fin 4) (Fin 4) ℝ
  R : Matrix (Fin 4) (Fin 4) ℝ
  p : ℝ

/-- The real skew matrix `G_{ij}`: entry `(i,j) = 1`, `(j,i) = -1`. -/
def skewG (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => if a = i ∧ b = j then 1 else if a = j ∧ b = i then -1 else 0

def Gen.act (g : Gen) (xy : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ :=
  (g.L * xy.1 - xy.1 * g.R - g.p • xy.2, g.L * xy.2 - xy.2 * g.R + (3 * g.p) • xy.1)

/-- The ten generators, in the order of `height_hessian()`: for `j = 1,2,3` the left and right
`G_{0j}`, then the left `G_{jk}` for `(j,k) = (1,2),(1,3),(2,3)`, then the phase `i√3`. -/
def gens : Fin 10 → Gen := ![
  ⟨skewG 0 1, 0, 0⟩, ⟨0, skewG 0 1, 0⟩, ⟨skewG 0 2, 0, 0⟩, ⟨0, skewG 0 2, 0⟩,
  ⟨skewG 0 3, 0, 0⟩, ⟨0, skewG 0 3, 0⟩,
  ⟨skewG 1 2, 0, 0⟩, ⟨skewG 1 3, 0, 0⟩, ⟨skewG 2 3, 0, 0⟩, ⟨0, 0, 1⟩]

/-- `√6 Z_*` as the pair `(X, Y) = (E₀₀, E₁₁ + E₂₂ + E₃₃)`. -/
def cStar : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ :=
  (Matrix.of fun a b => if a = 0 ∧ b = 0 then 1 else 0,
   Matrix.of fun a b => if a = b ∧ a ≠ 0 then 1 else 0)

/-- `H_{ℓm} = -√6 Re ⟨Z, (T_ℓ T_m + T_m T_ℓ)/2 Z_*⟩`, as the polynomial
`-3 ⟨X, tx⟩ - ⟨Y, ty⟩` of `height_hessian()`. -/
def sHess (v : SV) : Fin 10 → Fin 10 → ℝ := fun l m =>
  (-3 : ℝ) * (∑ i, ∑ j, sX v i j * (((gens l).act ((gens m).act cStar)).1 i j / 2
      + ((gens m).act ((gens l).act cStar)).1 i j / 2))
    - (∑ i, ∑ j, sY v i j * (((gens l).act ((gens m).act cStar)).2 i j / 2
      + ((gens m).act ((gens l).act cStar)).2 i j / 2))

/-! ### The interface -/

/-- The positive constraints at a closest point, on a slice point `v`: `h₀ ≥ 0` (phase),
`e ≥ 0`, the Procrustes matrices `K₀, K₁`, the Hessian `H`, all lower-frame matrices
`L_{σ₀,σ,c,s}` (`σ₀,σ ∈ {±1}`, `c² + 3 s² = 1`; the certificate uses four of them), the fidelity-floor
matrix `B₀`, and `g_η ≥ 0` for every HS state `η` (the certificate uses 50 explicit rays). -/
structure SliceConstraints (v : SV) : Prop where
  h0_nonneg : 0 ≤ sH0 v
  e_nonneg : 0 ≤ sE v
  K0 : QF (sK0 v)
  K1 : QF (sK1 v)
  Hess : QF (sHess v)
  lower : ∀ σ₀ σ c s : ℝ, (σ₀ = 1 ∨ σ₀ = -1) → (σ = 1 ∨ σ = -1) → c ^ 2 + 3 * s ^ 2 = 1 →
    QF (sL v σ₀ σ c s)
  B0 : QF (sB0 v)
  rays : ∀ χ : Psi, InOrbit χ → Complex.normSq (ip χ (sState v)) ≤ sH0 v ^ 2 / 6

/-- **The interface the polynomial certificate must discharge**
(`eq:fqe-global-overlap-sos`, GO-2): the homogeneous sextic `(Q - n² e)/36` is nonnegative on the
19-coordinate normal slice subject to the positive constraints. -/
def GOSliceCertificate : Prop := ∀ v : SV, SliceConstraints v → 0 ≤ sliceTarget v

/-! ### Closest-point frames and the reduction -/

/-- `φ` is a unit state with `Z_* = G(η₀)` a closest point of `𝓜` at real height `h ≥ 0`:
`⟨Z_*, φ⟩ = h` and `|⟨χ, φ⟩|² ≤ h²` for every `χ ∈ 𝓜`. -/
def IsFrame (φ : Psi) (h : ℝ) : Prop :=
  normSqPsi φ = 1 ∧ 0 ≤ h ∧ ip (Gv (etaV 0)) φ = (h : ℂ) ∧
    ∀ χ : Psi, InOrbit χ → Complex.normSq (ip χ φ) ≤ h ^ 2

theorem IsFrame.Phi_eq {φ : Psi} {h : ℝ} (hf : IsFrame φ h) : Phi φ = h ^ 2 := by
  obtain ⟨hn, h0, hip, hle⟩ := hf
  unfold Phi
  refine le_antisymm (csSup_le ⟨_, Gv (etaV 0), orbit_etaV 0, rfl⟩ ?_) ?_
  · rintro _ ⟨χ, hχ, rfl⟩
    rw [ip_comm, Complex.normSq_conj]
    exact hle χ hχ
  · refine le_csSup ⟨1, ?_⟩ ⟨Gv (etaV 0), orbit_etaV 0, ?_⟩
    · rintro _ ⟨χ', hχ', rfl⟩
      exact normSq_ip_le hn (normSqPsi_InOrbit hχ')
    · rw [ip_comm, hip, Complex.normSq_conj, Complex.normSq_ofReal]; ring

theorem magicCoord_sState (v : SV) : magicCoord (zmat (sState v)) = sZ v := by
  unfold sState
  rw [zmat_ofZmat]
  exact coord_of_eq rfl

theorem sum_pair (f : Fin 4 → ℝ) : ∑ k : Fin 2 × Fin 2, f (pairIdx k) = ∑ j, f j := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, pairIdx]; ring

theorem sum_pair2 (g : Fin 4 → Fin 4 → ℝ) :
    ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2, g (pairIdx p) (pairIdx q) = ∑ i, ∑ j, g i j := by
  rw [sum_pair (fun i => ∑ q : Fin 2 × Fin 2, g i (pairIdx q))]
  exact Finset.sum_congr rfl fun i _ => sum_pair (g i)

theorem normSqPsi_sState (v : SV) : normSqPsi (sState v) = sN v := by
  rw [← frob_coord, magicCoord_sState]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : ∀ p q : Fin 2 × Fin 2, Complex.normSq (sZ v p q) =
      3 * sX v (pairIdx p) (pairIdx q) ^ 2 + sY v (pairIdx p) (pairIdx q) ^ 2 := by
    intro p q
    simp only [sZ, Matrix.of_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    nlinarith [h3]
  simp only [key]
  rw [sum_pair2 (fun i j => 3 * sX v i j ^ 2 + sY v i j ^ 2)]
  simp [sN, fn4, Finset.sum_add_distrib, Finset.mul_sum]

end

end FormalResearch.FourQubitEntropy.GO
