module

public import FormalResearch.Racah.P2AnalyticL2Wigner
public import FormalResearch.Racah.P2AnalyticL2ThreeJ
public import FormalResearch.Racah.P2RacahSystemWigner

/-!
# The finite-to-continuum maps `S_N`, `S_R` realised in `L²(-1,1)` (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:SN` (`eq:SNspectral`-`eq:SNintertwine`) and
`prop:6jRacahTransmutation` (`eq:6jRacahSpectralMap`-`eq:6jRacahIntertwine`).

The abstract orthonormal-family statements `SNmap_*` (`P2AnalyticL2ThreeJ`) and `SRmap_*`
(`P2RacahSystemWigner`) are instantiated in the genuine Hilbert space `L²(-1,1)`
(`L2m11 = Lp ℝ 2 (volume.restrict (Icc (-1) 1))`) with the Wigner modes
`u_L = √((2L+1)/2) d^L_{Mσ}(arccos x)` (resp. `u_f = √((2f+1)/2) d^f_{nm}(arccos x)`), whose orthonormality
is `integral_uWig_mul` (`eq:continuummass`).

## Contents

3j (`prop:SN`), `K = N - L₀`, ranks `L = L₀ + i`, `i : Fin K`, under `SpecAdm M σ N`:
* `uN_orthonormal`: `{u_L}` is orthonormal in `L²(-1,1)`;
* `prop_SN`: the unitarity statement of `prop:SN` for `𝒱_N = span{u_L}`: `S_N u_L = v_L`, isometry on `𝒱_N`,
  `S_N : 𝒱_N → ℓ²(𝒳_N, 2h)` bijective with inverse `S_N⁻¹`;
* `SN_kernel`: `eq:SNkernel`, `(S_N g)(x_n) = ∫_{-1}^1 K_N(x_n, y) g(y) dy` for continuous `g`, with
  `K_N(x_n, y) = ∑_L (2L+1)/2 Φ_L(x_n) d^L_{Mσ}(arccos y)`;
* `H0diff_uWigComb` and `SN_intertwine_diff`: `eq:SNintertwine`, `𝖧_h S_N g = S_N (𝖧₀ g)` for
  `g = ∑ c_L u_L` where `𝖧₀` is the differential operator of `eq:H0` (`H0diff`) acting on `(-1,1)`.

6j (`prop:6jRacahTransmutation`), under `RacahSystem a b m n D`:
* `uR_orthonormal`, `prop_6jRacahTransmutation`, `SR_kernel` (`eq:6jRacahKernel`) and
  `SR_intertwine_diff` (`eq:6jRacahIntertwine`), exactly parallel.

Not formalised: `L²` completeness of `{u_L}` (so `𝒱_N` is only the finite span, as in the paper's
definition of `𝒱_N`; `S_N` on all of `L²` is `S_N P_{𝒱_N}`, which the kernel formula realises), and the
self-adjoint-operator realisation of `𝖧₀` with a domain.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Special MeasureTheory

/-! ### Shared lemmas on combinations of modes -/

lemma uWig_differentiableAt (L M σ : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (uWig L M σ) x :=
  (wignerSmallDx_differentiableAt L M σ hx).const_mul _

lemma deriv_uWig (L M σ : ℚ) :
    deriv (uWig L M σ) = fun y => Real.sqrt ((2 * (L : ℝ) + 1) / 2) *
      deriv (wignerSmallDx L M σ) y := by
  funext y; unfold uWig; exact deriv_cmul _ _ _

lemma uWig_deriv_differentiableAt (L M σ : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (deriv (uWig L M σ)) x := by
  rw [deriv_uWig]
  exact (wignerSmallDx_deriv_differentiableAt L M σ hx).const_mul _

variable {ι : Type*} [Fintype ι]

/-- A finite combination `∑ c_k u_{L_k}` of Wigner modes. -/
noncomputable def combWig (L : ι → ℚ) (M σ : ℚ) (c : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ k, c k * uWig (L k) M σ x

lemma combWig_continuous (L : ι → ℚ) (M σ : ℚ) (c : ι → ℝ) : Continuous (combWig L M σ c) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (uWig_continuous _ M σ)

/-- **`𝖧₀` on a finite combination of modes**: `𝖧₀ ∑ c_k u_{L_k} = ∑ c_k L_k(L_k+1) u_{L_k}` on
`(-1,1)`. -/
theorem H0diff_combWig (L : ι → ℚ) (M σ : ℚ) (c : ι → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    H0diff M σ (combWig L M σ c) x =
      combWig L M σ (fun k => c k * ((L k : ℝ) * (L k + 1))) x := by
  unfold combWig
  rw [H0diff_sum Finset.univ c (fun k => uWig (L k) M σ) M σ
    (fun i _ y hy => uWig_differentiableAt _ M σ hy)
    (fun i _ y hy => uWig_deriv_differentiableAt _ M σ hy) hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [H0diff_uWig _ _ _ hx]; ring

/-- Pairing of a mode with a finite combination: `⟨[u_{L_j}], [∑ c_k u_{L_k}]⟩ = c_j`
(orthonormality `integral_uWig_mul`, `L` injective and admissible). -/
theorem inner_L2uWig_comb [DecidableEq ι] (L : ι → ℚ) (hinj : Function.Injective L) (M σ : ℚ)
    (hadm : ∀ i, DAdm (L i) M σ) (c : ι → ℝ) (j : ι) :
    inner ℝ (L2uWig (L j) M σ) (L2cont (combWig L M σ c) (combWig_continuous L M σ c)) = c j := by
  unfold L2uWig
  rw [inner_L2cont]
  have e : ∀ x, uWig (L j) M σ x * combWig L M σ c x =
      ∑ k, c k * (uWig (L j) M σ x * uWig (L k) M σ x) := by
    intro x
    unfold combWig
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e]
  have hsum : ∫ x in (-1 : ℝ)..1, ∑ k, c k * (uWig (L j) M σ x * uWig (L k) M σ x) =
      ∑ k, ∫ x in (-1 : ℝ)..1, c k * (uWig (L j) M σ x * uWig (L k) M σ x) :=
    intervalIntegral.integral_finsetSum (fun k _ => (((uWig_continuous (L j) M σ).mul
      (uWig_continuous (L k) M σ)).const_mul (c k)).intervalIntegrable _ _)
  rw [hsum]
  have : ∀ k ∈ Finset.univ, ∫ x in (-1 : ℝ)..1, c k * (uWig (L j) M σ x * uWig (L k) M σ x) =
      c k * (if j = k then 1 else 0) := by
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_uWig_mul (hadm j) (hadm k)]
    by_cases hjk : j = k
    · simp [hjk]
    · have : L j ≠ L k := fun e => hjk (hinj e)
      simp [hjk, this]
  rw [Finset.sum_congr rfl this]
  simp

/-- The kernel representation: for a finite family of continuous modes `φ_i` and coefficients
`w i`, `∑_i ⟨φ_i, g⟩ w_i = ∫ (∑_i w_i φ_i) g`. -/
lemma sum_inner_eq_integral {κ : Type*} (s : Finset κ) (φ : κ → ℝ → ℝ) (hφ : ∀ i, Continuous (φ i))
    (g : ℝ → ℝ) (hg : Continuous g) (w : κ → ℝ) :
    ∑ i ∈ s, (∫ x in (-1 : ℝ)..1, φ i x * g x) * w i =
      ∫ y in (-1 : ℝ)..1, (∑ i ∈ s, w i * φ i y) * g y := by
  have e : ∀ y, (∑ i ∈ s, w i * φ i y) * g y = ∑ i ∈ s, w i * (φ i y * g y) := by
    intro y
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [e]
  have hsum : ∫ y in (-1 : ℝ)..1, ∑ i ∈ s, w i * (φ i y * g y) =
      ∑ i ∈ s, ∫ y in (-1 : ℝ)..1, w i * (φ i y * g y) :=
    intervalIntegral.integral_finsetSum (fun i _ =>
      (((hφ i).mul hg).const_mul (w i)).intervalIntegrable _ _)
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul]; ring

/-! ### The `3j` map `S_N` in `L²(-1,1)` (`prop:SN`) -/

section ThreeJ

variable {M σ N : ℚ} {K : ℕ}

lemma dadm_of_ladm {N M σ L : ℚ} (h : LAdm (jMinus N σ) (jPlus N σ) M L) : DAdm L M σ := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := h
  refine ⟨h4, h5, ?_, ?_⟩
  · convert h2 using 1; unfold jMinus jPlus; ring
  · convert h1 using 1; unfold jMinus jPlus; ring

lemma dadm_rkN (hA : SpecAdm M σ N) (hK : (K : ℚ) = N - max |M| |σ|) (i : Fin K) :
    DAdm (rkN M σ i) M σ := dadm_of_ladm (rank_adm hA hK i.2)

/-- The continuum modes `u_L ∈ L²(-1,1)`, `L = L₀ + i` (`prop:SN`). -/
noncomputable def uN (M σ : ℚ) {K : ℕ} (i : Fin K) : L2m11 := L2uWig (rkN M σ i) M σ

/-- The `u_L`, `L₀ ≤ L ≤ N-1`, are orthonormal in `L²(-1,1)` (`eq:continuummass`). -/
theorem uN_orthonormal (hA : SpecAdm M σ N) (hK : (K : ℚ) = N - max |M| |σ|) :
    Orthonormal ℝ (uN M σ : Fin K → L2m11) := by
  have hinj : Function.Injective (fun i : Fin K => rkN M σ i) := fun i j h =>
    Fin.ext (by exact_mod_cast rkN_injective M σ h)
  exact L2uWig_orthonormal (fun i : Fin K => rkN M σ i) hinj M σ (dadm_rkN hA hK)

/-- The kernel `K_N(x_n, y) = ∑_L (2L+1)/2 Φ_L^{M,σ}(x_n; h) d^L_{Mσ}(arccos y)` of `eq:SNkernel`. -/
noncomputable def KN (M σ N : ℚ) {K : ℕ} (n : Fin K) (y : ℝ) : ℝ :=
  ∑ i : Fin K, (2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2 * PhiX (rkN M σ i) M σ N (xLat M σ N n) *
    wignerSmallDx (rkN M σ i) M σ y

/-- **`eq:SNkernel`**: `(S_N g)(x_n) = ∫_{-1}^{1} K_N(x_n, y) g(y) dy` for continuous `g`
(`S_N = SNmap` with the modes `u_L` of `L²(-1,1)`). -/
theorem SN_kernel (M σ N : ℚ) {K : ℕ} (g : ℝ → ℝ) (hg : Continuous g) (n : Fin K) :
    SNmap M σ N (uN M σ : Fin K → L2m11) (L2cont g hg) n =
      ∫ y in (-1 : ℝ)..1, KN M σ N n y * g y := by
  unfold SNmap
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ i : Fin K, inner ℝ (uN M σ i) (L2cont g hg) =
      ∫ x in (-1 : ℝ)..1, uWig (rkN M σ i) M σ x * g x := fun i => by
    unfold uN L2uWig; rw [inner_L2cont]
  simp only [e1]
  rw [sum_inner_eq_integral Finset.univ (fun i : Fin K => uWig (rkN M σ i) M σ)
    (fun i => uWig_continuous _ M σ) g hg (fun i => vN M σ N i n)]
  congr 1
  funext y
  unfold KN
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : (0 : ℝ) ≤ (2 * ((rkN M σ i : ℚ) : ℝ) + 1) / 2 := by
    have : (0 : ℝ) ≤ ((rkN M σ i : ℚ) : ℝ) := by exact_mod_cast rkN_nonneg M σ i
    linarith
  have hs := Real.mul_self_sqrt hpos
  unfold vN uWig
  linear_combination (PhiX (rkN M σ i) M σ N (xLat M σ N n) *
    wignerSmallDx (rkN M σ i) M σ y) * hs

/-- Pairing of `[g]`, `g = ∑ c_L u_L`, with `u_L` (the coefficient `c_L`), `3j` version. -/
lemma inner_uN_comb (hA : SpecAdm M σ N) (hK : (K : ℚ) = N - max |M| |σ|) (c : Fin K → ℝ)
    (j : Fin K) :
    inner ℝ (uN M σ j)
      (L2cont (combWig (fun i : Fin K => rkN M σ i) M σ c)
        (combWig_continuous _ M σ c)) = c j := by
  have hinj : Function.Injective (fun i : Fin K => rkN M σ i) := fun i j h =>
    Fin.ext (by exact_mod_cast rkN_injective M σ h)
  exact inner_L2uWig_comb (fun i : Fin K => rkN M σ i) hinj M σ (dadm_rkN hA hK) c j

/-- `S_N (∑ c_L u_L) = ∑ c_L v_L`, for `g = ∑ c_L u_L` as a continuous function. -/
lemma SN_comb (hA : SpecAdm M σ N) (hK : (K : ℚ) = N - max |M| |σ|) (c : Fin K → ℝ) :
    SNmap M σ N (uN M σ : Fin K → L2m11)
      (L2cont (combWig (fun i : Fin K => rkN M σ i) M σ c) (combWig_continuous _ M σ c)) =
      ∑ k, c k • vN M σ N k := by
  unfold SNmap
  exact Finset.sum_congr rfl fun j _ => by rw [inner_uN_comb hA hK]

/-- **`eq:SNintertwine`** with the differential operator `𝖧₀` of `eq:H0`: for
`g = ∑_L c_L u_L` (a continuous function on `[-1,1]`), the function
`𝖧₀ g = ∑_L c_L L(L+1) u_L` agrees with the differential expression `H0diff M σ g` on `(-1,1)`
(`H0diff_combWig`), and `𝖧_h S_N g = S_N (𝖧₀ g)`. -/
theorem SN_intertwine_diff (hA : SpecAdm M σ N) (hN : 0 < N)
    (hK : (K : ℚ) = N - max |M| |σ|) (c : Fin K → ℝ) :
    (∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      H0diff M σ (combWig (fun i : Fin K => rkN M σ i) M σ c) x =
        combWig (fun i : Fin K => rkN M σ i) M σ (fun k => c k * lamN M σ k) x) ∧
    HhLat M σ N (SNmap M σ N (uN M σ : Fin K → L2m11)
        (L2cont (combWig (fun i : Fin K => rkN M σ i) M σ c) (combWig_continuous _ M σ c))) =
      SNmap M σ N (uN M σ : Fin K → L2m11)
        (L2cont (combWig (fun i : Fin K => rkN M σ i) M σ (fun k => c k * lamN M σ k))
          (combWig_continuous _ M σ _)) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [H0diff_combWig _ M σ c hx]
    unfold combWig
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [lamN, rankEig, rkN]
  · rw [SN_comb hA hK, SN_comb hA hK, HhLat_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HhLat_vN hA hN hK, smul_smul]

/-- **`prop:SN`** (unitarity form).  For `SpecAdm M σ N`, `K = N - L₀`, and `u_L = √((2L+1)/2)
d^L_{Mσ}(arccos ·)`, `v_L = √((2L+1)/2) Φ_L(x_n; h)`, `L = L₀,…,N-1`:
the `u_L` are orthonormal in `L²(-1,1)` and the `v_L` are an orthonormal basis of `ℓ²(𝒳_N, 2h)`;
`S_N u_L = v_L`; `S_N` is isometric on `𝒱_N = span{u_L}` and `S_N : 𝒱_N → ℓ²(𝒳_N, 2h)` is
bijective with inverse `S_N⁻¹ q = ∑ ⟨v_L, q⟩ u_L`. -/
theorem prop_SN (hA : SpecAdm M σ N) (hN : 0 < N) (hK : (K : ℚ) = N - max |M| |σ|) :
    Orthonormal ℝ (uN M σ : Fin K → L2m11) ∧
    (∀ i j : Fin K, ipN N (vN M σ N i) (vN M σ N j) = if i = j then 1 else 0) ∧
    (∀ q : Fin K → ℝ, q = ∑ i, ipN N (vN M σ N i) q • vN M σ N i) ∧
    (∀ l : Fin K, SNmap M σ N (uN M σ : Fin K → L2m11) (uN M σ l) = vN M σ N l) ∧
    (∀ x y : L2m11, x ∈ Submodule.span ℝ (Set.range (uN M σ : Fin K → L2m11)) →
      y ∈ Submodule.span ℝ (Set.range (uN M σ : Fin K → L2m11)) →
      ipN N (SNmap M σ N (uN M σ : Fin K → L2m11) x) (SNmap M σ N (uN M σ : Fin K → L2m11) y) =
        inner ℝ x y) ∧
    (∀ q : Fin K → ℝ, SNmap M σ N (uN M σ : Fin K → L2m11)
      (SNinv M σ N (uN M σ : Fin K → L2m11) q) = q) ∧
    (∀ x : L2m11, x ∈ Submodule.span ℝ (Set.range (uN M σ : Fin K → L2m11)) →
      SNinv M σ N (uN M σ : Fin K → L2m11) (SNmap M σ N (uN M σ : Fin K → L2m11) x) = x) := by
  have hu := uN_orthonormal hA hK
  exact ⟨hu, vN_orthonormal hA hN hK, vN_expansion hA hN hK, SNmap_u hu,
    fun x y hx hy => SNmap_isometry hA hN hK hu hx hy, SNmap_SNinv hA hN hK hu,
    fun x hx => SNinv_SNmap hA hN hK hu hx⟩

end ThreeJ

/-! ### The `6j` map `S_R` in `L²(-1,1)` (`prop:6jRacahTransmutation`) -/

section SixJ

open FormalResearch.Racah.SixJ

variable {a b m n : ℚ} {D : ℕ}

lemma dadm_fPt (h : RacahSystem a b m n D) (j : Fin (D + 1)) : DAdm (fPt m n j) n m := by
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := fPt_mem h j
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert h5 using 1; ring
  · convert h4 using 1; ring
  · convert h1 using 1; ring
  · convert h2 using 1; ring

/-- The continuum modes `u_f = √((2f+1)/2) d^f_{nm}(arccos x) ∈ L²(-1,1)`, `f = f_0 + j`. -/
noncomputable def uR (m n : ℚ) {D : ℕ} (j : Fin (D + 1)) : L2m11 := L2uWig (fPt m n j) n m

/-- The `u_f` are orthonormal in `L²(-1,1)` (`eq:continuummass`). -/
theorem uR_orthonormal (h : RacahSystem a b m n D) :
    Orthonormal ℝ (uR m n : Fin (D + 1) → L2m11) :=
  L2uWig_orthonormal (fun j : Fin (D + 1) => fPt m n j) (fPt_injective m n) n m (dadm_fPt h)

/-- The kernel `K_R(c_i, x) = ∑_f (2f+1)/2 Φ_f(c_i) d^f_{nm}(arccos x)` of `eq:6jRacahKernel`. -/
noncomputable def KR (a b m n : ℚ) {D : ℕ} (i : Fin (D + 1)) (y : ℝ) : ℝ :=
  ∑ j : Fin (D + 1), (2 * (fPt m n j : ℝ) + 1) / 2 *
    Phi6 a b (cPt a b m n i) (fPt m n j) m n * wignerSmallDx (fPt m n j) n m y

/-- **`eq:6jRacahKernel`**: `(S_R g)(c_i) = ∫_{-1}^{1} K_R(c_i, x) g(x) dx` for continuous `g`. -/
theorem SR_kernel (g : ℝ → ℝ) (hg : Continuous g) (i : Fin (D + 1)) :
    SRmap a b m n (uR m n : Fin (D + 1) → L2m11) (L2cont g hg) i =
      ∫ y in (-1 : ℝ)..1, KR a b m n i y * g y := by
  unfold SRmap
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ j : Fin (D + 1), inner ℝ (uR m n j) (L2cont g hg) =
      ∫ x in (-1 : ℝ)..1, uWig (fPt m n j) n m x * g x := fun j => by
    unfold uR L2uWig; rw [inner_L2cont]
  simp only [e1]
  rw [sum_inner_eq_integral Finset.univ (fun j : Fin (D + 1) => uWig (fPt m n j) n m)
    (fun j => uWig_continuous _ n m) g hg (fun j => vR a b m n j i)]
  congr 1
  funext y
  unfold KR
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpos : (0 : ℝ) ≤ (2 * (fPt m n j : ℝ) + 1) / 2 := by
    have := fPt_nonneg m n j
    linarith
  have hs := Real.mul_self_sqrt hpos
  unfold vR uWig
  linear_combination (Phi6 a b (cPt a b m n i) (fPt m n j) m n *
    wignerSmallDx (fPt m n j) n m y) * hs

lemma SR_comb (h : RacahSystem a b m n D) (c : Fin (D + 1) → ℝ) :
    SRmap a b m n (uR m n : Fin (D + 1) → L2m11)
      (L2cont (combWig (fun j : Fin (D + 1) => fPt m n j) n m c) (combWig_continuous _ n m c)) =
      ∑ k, c k • vR a b m n k := by
  unfold SRmap
  refine Finset.sum_congr rfl fun j _ => ?_
  change inner ℝ (L2uWig (fPt m n j) n m) _ • _ = _
  rw [inner_L2uWig_comb (fun j : Fin (D + 1) => fPt m n j) (fPt_injective m n) n m (dadm_fPt h)]

/-- **`eq:6jRacahIntertwine`** with the differential operator `𝖧₀^{(m,n)}` of `eq:6jcontinuumH0`:
for `g = ∑_f c_f u_f`, `𝖧₀ g = ∑ c_f f(f+1) u_f` agrees with `H0diff n m g` on `(-1,1)`, and
`H_R S_R g = S_R (𝖧₀ g)`. -/
theorem SR_intertwine_diff (h : RacahSystem a b m n D) (c : Fin (D + 1) → ℝ) :
    (∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      H0diff n m (combWig (fun j : Fin (D + 1) => fPt m n j) n m c) x =
        combWig (fun j : Fin (D + 1) => fPt m n j) n m (fun k => c k * lamR m n k) x) ∧
    (HR a b m n D).mulVec (SRmap a b m n (uR m n : Fin (D + 1) → L2m11)
        (L2cont (combWig (fun j : Fin (D + 1) => fPt m n j) n m c) (combWig_continuous _ n m c))) =
      SRmap a b m n (uR m n : Fin (D + 1) → L2m11)
        (L2cont (combWig (fun j : Fin (D + 1) => fPt m n j) n m (fun k => c k * lamR m n k))
          (combWig_continuous _ n m _)) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [H0diff_combWig _ n m c hx]
    unfold combWig
    exact Finset.sum_congr rfl fun k _ => by simp only [lamR]
  · rw [SR_comb h, SR_comb h, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul, vR_eigen h, smul_smul]
    simp only [lamR]

/-- **`prop:6jRacahTransmutation`** (unitarity form) in `L²(-1,1)`: for `RacahSystem a b m n D`,
the `u_f = √((2f+1)/2) d^f_{nm}(arccos ·)` are orthonormal in `L²(-1,1)`, `S_R u_f = v_f`, `S_R` is
isometric on `𝒱 = span{u_f}` into `ℓ²(𝒞, ω)` and `S_R : 𝒱 → ℓ²(𝒞, ω)` is bijective with inverse
`S_R⁻¹ q = ∑ ⟨v_f, q⟩_ω u_f`. -/
theorem prop_6jRacahTransmutation (h : RacahSystem a b m n D) :
    Orthonormal ℝ (uR m n : Fin (D + 1) → L2m11) ∧
    (∀ l : Fin (D + 1), SRmap a b m n (uR m n : Fin (D + 1) → L2m11) (uR m n l) =
      vR a b m n l) ∧
    (∀ x y : L2m11, x ∈ Submodule.span ℝ (Set.range (uR m n : Fin (D + 1) → L2m11)) →
      y ∈ Submodule.span ℝ (Set.range (uR m n : Fin (D + 1) → L2m11)) →
      ipR a b m n (SRmap a b m n (uR m n : Fin (D + 1) → L2m11) x)
        (SRmap a b m n (uR m n : Fin (D + 1) → L2m11) y) = inner ℝ x y) ∧
    (∀ q : Fin (D + 1) → ℝ, SRmap a b m n (uR m n : Fin (D + 1) → L2m11)
      (SRinv a b m n (uR m n : Fin (D + 1) → L2m11) q) = q) ∧
    (∀ x : L2m11, x ∈ Submodule.span ℝ (Set.range (uR m n : Fin (D + 1) → L2m11)) →
      SRinv a b m n (uR m n : Fin (D + 1) → L2m11)
        (SRmap a b m n (uR m n : Fin (D + 1) → L2m11) x) = x) := by
  have hu := uR_orthonormal h
  exact ⟨hu, SRmap_u a b m n hu, fun x y hx hy => SRmap_isometry h hu hx hy,
    SRmap_SRinv h hu, fun x hx => SRinv_SRmap h hu hx⟩

end SixJ

/-- info: 'FormalResearch.Racah.uN_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uN_orthonormal

/-- info: 'FormalResearch.Racah.prop_SN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prop_SN

/-- info: 'FormalResearch.Racah.SN_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SN_kernel

/-- info: 'FormalResearch.Racah.SN_intertwine_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SN_intertwine_diff

/-- info: 'FormalResearch.Racah.uR_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uR_orthonormal

/-- info: 'FormalResearch.Racah.prop_6jRacahTransmutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prop_6jRacahTransmutation

/-- info: 'FormalResearch.Racah.SR_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SR_kernel

/-- info: 'FormalResearch.Racah.SR_intertwine_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SR_intertwine_diff

end FormalResearch.Racah
