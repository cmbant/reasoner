import FormalResearch.FrameFree.Sharing
import FormalResearch.FrameFree.OneCopy

open scoped ComplexConjugate Matrix BigOperators

/-!
# Zariski density of `SU(2)^b` in `SL(2,ℂ)^b` (Paper P, `thm:onecopy` (a), `prop:invariantstates`)

Namespace `FormalResearch.FrameFree.Zariski`.  This closes the two gaps recorded in `OneCopy.lean`
and `Sharing.lean`: the converse `F_K^π = 0 ⟹ F_C^π = 0` of `thm:onecopy` (a), and the passage from
`K_π`-invariance to invariance under the complexification in `prop:invariantstates` (filter part).

## Proved here (no hypothesis, no `sorry`)

* **One factor** (`vanish_SL2`).  If `f : Op1 → ℂ` is entire along holomorphic matrix curves
  (`CurveEntire`; any polynomial in the four entries is, `slotEntire_mvPolynomial`) and vanishes on
  `SU(2)`, it vanishes on `SL(2,ℂ)`.  The proof avoids polynomial algebra:
  1. polar decomposition `g = k p` of `g ∈ SL(2,ℂ)` with `k ∈ SU(2)`, `p` positive Hermitian of
     determinant one (`polar`, explicit, `p = (gᴴg + 1)/√(tr gᴴg + 2)`);
  2. `p = cosh τ + i sinh τ · Y` with `Y ∈ su(2)`, `Y² = -1`, i.e. `p = Mc α β (cos iτ) (sin iτ)`
     (`herm_eq_Mc`), where `t ↦ k · (cos t + sin t · Y)` lies in `SU(2)` for real `t` (`SU2_Mc`);
  3. the identity theorem for the entire function `t ↦ f (k (cos t + sin t · Y))`, which vanishes on `ℝ`
     (`entire_eq_zero_of_real`), evaluated at `t = iτ`.
* **Several factors** (`vanish_slots`, `vanish_SL2_pi`, `vanish_SL2_of_support`): induction on the
  number of slots, applying the one-factor result in each slot with the others fixed (first at
  `SU(2)` points, then at `SL(2,ℂ)` points).  The polynomial form is `mvPolynomial_vanish_SL2`: a
  polynomial in the `4|ι|` matrix entries vanishing on `SU(2)^ι` vanishes on `SL(2,ℂ)^ι`.
* **Application** (`slotEntire_rot`, `slotEntire_ip`: the overlap `⟨ψ|(⊗ v_{g i}) φ⟩` and every
  coordinate of `(⊗ v_{g i}) φ` are polynomial in the entries of the frames; the frame type `β` is
  arbitrary, only the finitely many blocks `g i` are read):
  - `ip_eq_zero_of_SU2`: vanishing of the overlap on `SU(2)` frames gives vanishing on `SL(2,ℂ)` frames;
  - `FCs_eq_zero_of_FKs_eq_zero`, `FKs_eq_zero_iff_FCs_eq_zero`, `FKΘs_eq_zero_iff_FCΘs_eq_zero`:
    **`thm:onecopy` (a)**, `F_K^π = 0 ⟺ F_C^π = 0` for every `ψ`, `φ` and sharing pattern (no
    normalisation hypothesis; `OneCopy.FKΘs_eq_zero_of_FCΘs_eq_zero` is the elementary direction);
  - `FCΘs_of_SU2_invariant(_unit)`: **`prop:invariantstates`** (filter part) with only
    `K_π`-invariance (`SU(2)` frames) as hypothesis, replacing the `SL(2,ℂ)`-invariance hypothesis of
    `Sharing.FCΘs_of_invariant`.

The other parts of `thm:onecopy` (a), (b) (orthogonal supports of the one-copy twirls, `F_K^π > 0` for
blocks of at most two spins) use Schur--Weyl duality and the Haar-free twirl and are in `TwirlsOneCopy`.
-/

namespace FormalResearch.FrameFree.Zariski

open FormalResearch.FrameFree.NQubit (Op1)

/-- An entire function vanishing on `ℝ` vanishes. -/
theorem entire_eq_zero_of_real {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (h : ∀ t : ℝ, φ t = 0) (z : ℂ) : φ z = 0 := by
  have hA : AnalyticOnNhd ℂ φ Set.univ := fun w _ => hφ.analyticAt w
  have hfreq : ∃ᶠ w in nhdsWithin (0 : ℂ) {0}ᶜ, φ w = 0 := by
    have ht : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) Filter.atTop
        (nhdsWithin (0 : ℂ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        exact this
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    exact ht.frequently (Filter.Frequently.of_forall fun n => h _)
  exact hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq (Set.mem_univ z)


/-- The one-parameter family `cos t + sin t · Y`, `Y = [[iα, β], [-β̄, -iα]]`, `Y² = -1` when
`α² + |β|² = 1`. -/
def Mc (α : ℝ) (β c s : ℂ) : Op1 :=
  !![c + Complex.I * α * s, β * s; -(conj β) * s, c - Complex.I * α * s]

theorem det_Mc (α : ℝ) (β c s : ℂ) (h : (α : ℂ) ^ 2 + β * conj β = 1) :
    (Mc α β c s).det = c ^ 2 + s ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Mc, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination s ^ 2 * h + (-(α : ℂ) ^ 2 * s ^ 2) * Complex.I_sq

theorem SU2_Mc (α : ℝ) (β : ℂ) (x y : ℝ) (h : (α : ℂ) ^ 2 + β * conj β = 1)
    (hxy : x ^ 2 + y ^ 2 = 1) : FormalResearch.FrameFree.NQubit.SU2 (Mc α β x y) := by
  have hxy' : (x : ℂ) ^ 2 + (y : ℂ) ^ 2 = 1 := by exact_mod_cast hxy
  refine ⟨?_, by rw [det_Mc α β _ _ h]; exact hxy'⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mc, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · linear_combination (y : ℂ) ^ 2 * h + hxy' + (-(α : ℂ) ^ 2 * (y : ℂ) ^ 2) * Complex.I_sq
  · ring
  · ring
  · linear_combination (y : ℂ) ^ 2 * h + hxy' + (-(α : ℂ) ^ 2 * (y : ℂ) ^ 2) * Complex.I_sq


/-- A positive Hermitian `2×2` matrix of determinant one is `Mc α β (cos iτ) (sin iτ)`. -/
theorem herm_eq_Mc (x y : ℝ) (w : ℂ) (hx : 0 < x) (hy : 0 < y)
    (hdet : (x : ℂ) * y - w * conj w = 1) :
    ∃ (α : ℝ) (β : ℂ) (τ : ℝ), (α : ℂ) ^ 2 + β * conj β = 1 ∧
      (!![(x : ℂ), w; conj w, (y : ℂ)] : Op1) =
        Mc α β (Complex.cos (τ * Complex.I)) (Complex.sin (τ * Complex.I)) := by
  have hw : w * conj w = (Complex.normSq w : ℂ) := Complex.mul_conj w
  have hreal : x * y - Complex.normSq w = 1 := by
    rw [hw] at hdet; exact_mod_cast hdet
  set h : ℝ := (x - y) / 2 with hh
  set c : ℝ := (x + y) / 2 with hc
  have hsig : c ^ 2 = 1 + (h ^ 2 + Complex.normSq w) := by
    rw [hh, hc]; nlinarith [hreal]
  set σ : ℝ := Real.sqrt (h ^ 2 + Complex.normSq w) with hσ
  have hσ2 : σ ^ 2 = h ^ 2 + Complex.normSq w :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcσ : c = Real.sqrt (1 + σ ^ 2) := by
    rw [hσ2, ← hsig]; exact (Real.sqrt_sq hcpos.le).symm
  have hcos : Complex.cos ((Real.arsinh σ : ℝ) * Complex.I) = (c : ℂ) := by
    rw [Complex.cos_mul_I, ← Complex.ofReal_cosh, Real.cosh_arsinh, ← hcσ]
  have hsin : Complex.sin ((Real.arsinh σ : ℝ) * Complex.I) = (σ : ℂ) * Complex.I := by
    rw [Complex.sin_mul_I, ← Complex.ofReal_sinh, Real.sinh_arsinh]
  rcases hσ0.eq_or_lt with hs | hs
  · -- `σ = 0`: the matrix is the identity
    have h0 : h ^ 2 + Complex.normSq w = 0 := by rw [← hσ2, ← hs]; ring
    have hh0 : h = 0 := by nlinarith [Complex.normSq_nonneg w, sq_nonneg h]
    have hw0 : Complex.normSq w = 0 := by nlinarith [Complex.normSq_nonneg w, sq_nonneg h]
    have hw' : w = 0 := Complex.normSq_eq_zero.1 hw0
    have hxy : x = y := by rw [hh] at hh0; linarith
    have hx1 : x = 1 := by
      rw [hw0] at hreal
      rw [← hxy] at hreal
      nlinarith
    have hy1 : y = 1 := by rw [← hxy]; exact hx1
    have hc1 : c = 1 := by rw [hc, hx1, hy1]; norm_num
    refine ⟨1, 0, Real.arsinh σ, by simp, ?_⟩
    rw [hcos, hsin, ← hs, hc1, hw', hx1, hy1]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Mc]
  · refine ⟨-h / σ, -Complex.I * w / σ, Real.arsinh σ, ?_, ?_⟩
    · have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have e1 : ((-h / σ : ℝ) : ℂ) ^ 2 = (h : ℂ) ^ 2 / (σ : ℂ) ^ 2 := by push_cast; ring
      have e2 : (-Complex.I * w / σ) * conj (-Complex.I * w / σ) =
          (Complex.normSq w : ℂ) / (σ : ℂ) ^ 2 := by
        rw [← hw]
        simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
        field_simp
        linear_combination (-(w * conj w)) * Complex.I_sq
      rw [e1, e2, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hσc)]
      exact_mod_cast hσ2.symm
    · have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      rw [hcos, hsin]
      have hxc : (x : ℂ) = c + h := by rw [hc, hh]; push_cast; ring
      have hyc : (y : ℂ) = c - h := by rw [hc, hh]; push_cast; ring
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Mc, hxc, hyc] <;> field_simp <;> (rw [Complex.I_sq]; ring)


/-- Polar decomposition `g = k p` of an `SL(2,ℂ)` element: `k ∈ SU(2)`, `p` positive Hermitian. -/
theorem polar (g : Op1) (hg : g.det = 1) :
    ∃ (k : Op1) (x y : ℝ) (w : ℂ), FormalResearch.FrameFree.NQubit.SU2 k ∧ 0 < x ∧ 0 < y ∧
      (x : ℂ) * y - w * conj w = 1 ∧ g = k * !![(x : ℂ), w; conj w, (y : ℂ)] := by
  have hg' : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hg
  set a := g 0 0 with ha
  set b := g 0 1 with hb
  set c := g 1 0 with hc
  set d := g 1 1 with hd
  have hgc : conj a * conj d - conj b * conj c = 1 := by
    have := congrArg conj hg'; simpa using this
  set A : ℝ := Complex.normSq a + Complex.normSq c with hA
  set D : ℝ := Complex.normSq b + Complex.normSq d with hD
  set B : ℂ := conj a * b + conj c * d with hB
  have hAc : (A : ℂ) = a * conj a + c * conj c := by
    rw [hA]; push_cast; rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; ring
  have hDc : (D : ℂ) = b * conj b + d * conj d := by
    rw [hD]; push_cast; rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; ring
  have hAD : (A : ℂ) * D - B * conj B = 1 := by
    rw [hAc, hDc, hB]
    simp only [map_add, map_mul, Complex.conj_conj]
    linear_combination (a * d - b * c) * hgc + hg'
  have hBB : B * conj B = (A : ℂ) * D - 1 := by linear_combination -hAD
  have hAnn : 0 ≤ A := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hDnn : 0 ≤ D := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hrpos : 0 < A + D + 2 := by linarith
  set r : ℝ := Real.sqrt (A + D + 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hrpos
  have hr2 : r ^ 2 = A + D + 2 := Real.sq_sqrt hrpos.le
  set ρ : ℂ := ((r : ℝ) : ℂ)⁻¹ with hρdef
  have hρ : ρ ^ 2 * ((A : ℂ) + D + 2) = 1 := by
    have : ((r : ℂ)) ^ 2 = (A : ℂ) + D + 2 := by exact_mod_cast hr2
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    rw [← this, hρdef]; field_simp
  have hρc : conj ρ = ρ := by rw [hρdef]; simp
  set w : ℂ := B * ρ with hw
  have hwc : conj w = conj B * ρ := by rw [hw]; simp [hρc]
  set x : ℝ := (A + 1) / r with hx
  set y : ℝ := (D + 1) / r with hy
  have hxc : (x : ℂ) = (A + 1) * ρ := by rw [hx, hρdef]; push_cast; ring
  have hyc : (y : ℂ) = (D + 1) * ρ := by rw [hy, hρdef]; push_cast; ring
  have hxpos : 0 < x := by rw [hx]; positivity
  have hypos : 0 < y := by rw [hy]; positivity
  have hxy : (x : ℂ) * y - w * conj w = 1 := by
    rw [hxc, hyc, hw, hwc]
    linear_combination (ρ ^ 2) * hAD + hρ
  have hBc : conj B = a * conj b + c * conj d := by
    rw [hB]; simp only [map_add, map_mul, Complex.conj_conj]
  set p : Op1 := !![(x : ℂ), w; conj w, (y : ℂ)] with hp
  set q : Op1 := !![(y : ℂ), -w; -conj w, (x : ℂ)] with hq
  have hpq : p * q = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, hq, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hxy
    · ring
    · ring
    · linear_combination hxy
  have hqp : q * p = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, hq, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hxy
    · ring
    · ring
    · linear_combination hxy
  have hqH : qᴴ = q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq, Matrix.conjTranspose_apply]
  have hgg : gᴴ * g = p * p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · rw [hxc, hw, hwc]
      linear_combination (-1 : ℂ) * hAc + (-(A : ℂ)) * hρ + (-(ρ ^ 2)) * hBB
    · rw [hxc, hyc, hw]
      linear_combination (-1 : ℂ) * hB + (-B) * hρ
    · rw [hxc, hyc, hwc]
      linear_combination (-1 : ℂ) * hBc + (-conj B) * hρ
    · rw [hyc, hw, hwc]
      linear_combination (-1 : ℂ) * hDc + (-(D : ℂ)) * hρ + (-(ρ ^ 2)) * hBB
  refine ⟨g * q, x, y, w, ⟨?_, ?_⟩, hxpos, hypos, hxy, ?_⟩
  · rw [Matrix.conjTranspose_mul, hqH]
    calc q * gᴴ * (g * q) = q * (gᴴ * g) * q := by simp only [Matrix.mul_assoc]
      _ = q * (p * p) * q := by rw [hgg]
      _ = (q * p) * (p * q) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hqp, hpq, Matrix.one_mul]
  · rw [Matrix.det_mul, hg, one_mul, Matrix.det_fin_two]
    simp only [hq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination hxy
  · rw [Matrix.mul_assoc, hqp, Matrix.mul_one]


/-- `f` is *entire along holomorphic matrix curves*: composed with any curve `ℂ → Op1` with entire
entries it is entire.  Polynomials in the four matrix entries are of this kind
(`curveEntire_mvPolynomial`). -/
def CurveEntire (f : Op1 → ℂ) : Prop :=
  ∀ γ : ℂ → Op1, (∀ i j, Differentiable ℂ fun t => γ t i j) →
    Differentiable ℂ fun t => f (γ t)

/-- **Zariski density of `SU(2)` in `SL(2,ℂ)`, one factor.**  A function which is entire along
holomorphic matrix curves (e.g. a polynomial in the entries) and vanishes on `SU(2)` vanishes on
`SL(2,ℂ)`.  Proof: polar decomposition `g = k·exp(iτ Y)` with `k ∈ SU(2)`, `Y ∈ su(2)`, and the
identity theorem on `t ↦ f (k·exp(tY))`, which vanishes for real `t`. -/
theorem vanish_SL2 {f : Op1 → ℂ} (hf : CurveEntire f)
    (h0 : ∀ u, FormalResearch.FrameFree.NQubit.SU2 u → f u = 0) (g : Op1) (hg : g.det = 1) :
    f g = 0 := by
  obtain ⟨k, x, y, w, hk, hx, hy, hxy, hgk⟩ := polar g hg
  obtain ⟨α, β, τ, hαβ, hM⟩ := herm_eq_Mc x y w hx hy hxy
  set γ : ℂ → Op1 := fun t => k * Mc α β (Complex.cos t) (Complex.sin t) with hγ
  have hdiff : ∀ i j, Differentiable ℂ fun t => γ t i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hγ, Mc, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have hφ : Differentiable ℂ fun t => f (γ t) := hf γ hdiff
  have hreal : ∀ t : ℝ, f (γ t) = 0 := by
    intro t
    apply h0
    have : γ t = k * Mc α β (Real.cos t : ℝ) (Real.sin t : ℝ) := by
      simp only [hγ, Complex.ofReal_cos, Complex.ofReal_sin]
    rw [this]
    exact FormalResearch.FrameFree.NQubit.SU2_mul hk
      (SU2_Mc α β _ _ hαβ (by rw [add_comm]; exact Real.sin_sq_add_cos_sq t))
  have := entire_eq_zero_of_real hφ hreal (τ * Complex.I)
  have hgγ : g = γ (τ * Complex.I) := by
    rw [hgk, hM]
  rw [hgγ]
  exact this


/-! ## Several factors -/

section Slots

variable {ι : Type*} [DecidableEq ι]

/-- `F` is entire along holomorphic curves in each slot separately (the other slots held fixed). -/
def SlotEntire (F : (ι → Op1) → ℂ) : Prop :=
  ∀ (v : ι → Op1) (a : ι) (γ : ℂ → Op1), (∀ i j, Differentiable ℂ fun t => γ t i j) →
    Differentiable ℂ fun t => F (Function.update v a (γ t))

/-- Slot by slot: if `F` is slot-entire and vanishes on `SU(2)^ι`, it vanishes at every `v` which is
`SL(2,ℂ)` on a finite set `s` of slots and `SU(2)` elsewhere. -/
theorem vanish_slots {F : (ι → Op1) → ℂ} (hF : SlotEntire F)
    (h0 : ∀ v : ι → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) → F v = 0)
    (s : Finset ι) :
    ∀ v : ι → Op1, (∀ b ∈ s, (v b).det = 1) →
      (∀ b ∉ s, FormalResearch.FrameFree.NQubit.SU2 (v b)) → F v = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro v _ hn
    exact h0 v fun b => hn b (Finset.notMem_empty b)
  | insert a s ha ih =>
    intro v hs hn
    have key : ∀ u : Op1, FormalResearch.FrameFree.NQubit.SU2 u →
        F (Function.update v a u) = 0 := by
      intro u hu
      apply ih
      · intro b hb
        have hba : b ≠ a := fun h => ha (h ▸ hb)
        rw [Function.update_of_ne hba]
        exact hs b (Finset.mem_insert_of_mem hb)
      · intro b hb
        by_cases hba : b = a
        · subst hba; rw [Function.update_self]; exact hu
        · rw [Function.update_of_ne hba]
          exact hn b (by simp [hba, hb])
    have hfa : CurveEntire (fun u => F (Function.update v a u)) := fun γ hγ => hF v a γ hγ
    have := vanish_SL2 hfa key (v a) (hs a (Finset.mem_insert_self a s))
    simpa using this

/-- Finitely many slots: a slot-entire function vanishing on `SU(2)^ι` vanishes on `SL(2,ℂ)^ι`. -/
theorem vanish_SL2_pi [Fintype ι] {F : (ι → Op1) → ℂ} (hF : SlotEntire F)
    (h0 : ∀ v : ι → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) → F v = 0)
    (v : ι → Op1) (hv : ∀ b, (v b).det = 1) : F v = 0 :=
  vanish_slots hF h0 Finset.univ v (fun b _ => hv b) (fun b hb => absurd (Finset.mem_univ b) hb)

/-- A function of `v` which only reads the slots in `s`: vanishing on `SU(2)^ι` suffices. -/
theorem vanish_SL2_of_support {F : (ι → Op1) → ℂ} (hF : SlotEntire F) (s : Finset ι)
    (hdep : ∀ v v' : ι → Op1, (∀ b ∈ s, v b = v' b) → F v = F v')
    (h0 : ∀ v : ι → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) → F v = 0)
    (v : ι → Op1) (hv : ∀ b ∈ s, (v b).det = 1) : F v = 0 := by
  classical
  set v' : ι → Op1 := fun b => if b ∈ s then v b else 1 with hv'
  have h1 : F v' = 0 := by
    refine vanish_slots hF h0 s v' (fun b hb => ?_) (fun b hb => ?_)
    · simp [hv', hb, hv b hb]
    · simp only [hv', hb, ite_false]; exact FormalResearch.FrameFree.NQubit.SU2_one
  rw [hdep v v' (fun b hb => by simp [hv', hb])]
  exact h1


theorem update_entry_differentiable (v : ι → Op1) (a : ι) {γ : ℂ → Op1}
    (hγ : ∀ i j, Differentiable ℂ fun t => γ t i j) (b : ι) (i j : Fin 2) :
    Differentiable ℂ fun t => (Function.update v a (γ t) b) i j := by
  by_cases h : b = a
  · subst h; simp only [Function.update_self]; exact hγ i j
  · simp only [Function.update_of_ne h]; exact differentiable_const _

/-- **Polynomials in the matrix entries** are slot-entire. -/
theorem slotEntire_mvPolynomial (p : MvPolynomial (ι × Fin 2 × Fin 2) ℂ) :
    SlotEntire (fun v : ι → Op1 => MvPolynomial.eval (fun q => v q.1 q.2.1 q.2.2) p) := by
  intro v a γ hγ
  induction p using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C]; exact differentiable_const c
  | add p q hp hq => simp only [map_add]; exact Differentiable.add hp hq
  | mul_X p q hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (update_entry_differentiable v a hγ q.1 q.2.1 q.2.2)

/-- **Zariski density of `SU(2)^ι` in `SL(2,ℂ)^ι`** (polynomial form): a polynomial in the `4|ι|`
matrix entries which vanishes on `SU(2)^ι` vanishes on `SL(2,ℂ)^ι`. -/
theorem mvPolynomial_vanish_SL2 [Fintype ι] (p : MvPolynomial (ι × Fin 2 × Fin 2) ℂ)
    (h0 : ∀ v : ι → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) →
      MvPolynomial.eval (fun q => v q.1 q.2.1 q.2.2) p = 0)
    (v : ι → Op1) (hv : ∀ b, (v b).det = 1) :
    MvPolynomial.eval (fun q => v q.1 q.2.1 q.2.2) p = 0 :=
  vanish_SL2_pi (slotEntire_mvPolynomial p) h0 v hv

end Slots


/-! ## Application to frame sharing -/

section Application

open FormalResearch.FrameFree.NQubit (Ψ rot Θ nsq)
open FormalResearch.FrameFree.Sharing (FKs FCs FKΘs FCΘs)

variable {n : ℕ} {β : Type*} [DecidableEq β]

/-- Each coordinate of `⊗_i v_{g i} φ` is a polynomial in the entries, hence slot-entire. -/
theorem slotEntire_rot (g : Fin n → β) (φ : Ψ n) (x : Fin n → Fin 2) :
    SlotEntire (fun v : β → Op1 => rot (fun i => v (g i)) φ x) := by
  intro v a γ hγ
  simp only [rot]
  refine Differentiable.fun_sum fun y _ => ?_
  refine Differentiable.mul ?_ (differentiable_const _)
  exact Differentiable.fun_finsetProd fun i _ =>
    update_entry_differentiable v a hγ (g i) (x i) (y i)

theorem slotEntire_ip (g : Fin n → β) (ψ φ : Ψ n) :
    SlotEntire (fun v : β → Op1 => FormalResearch.FrameFree.NQubit.ip ψ (rot (fun i => v (g i)) φ)) := by
  intro v a γ hγ
  simp only [FormalResearch.FrameFree.NQubit.ip]
  exact Differentiable.fun_sum fun x _ =>
    Differentiable.mul (differentiable_const _) (slotEntire_rot g φ x v a γ hγ)

/-- The overlap `⟨ψ|(⊗ v_{g i}) φ⟩` vanishes on all `SL(2,ℂ)` frames once it vanishes on all
`SU(2)` frames. -/
theorem ip_eq_zero_of_SU2 (g : Fin n → β) (ψ φ : Ψ n)
    (h : ∀ v : β → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) →
      FormalResearch.FrameFree.NQubit.ip ψ (rot (fun i => v (g i)) φ) = 0)
    (v : β → Op1) (hv : ∀ b, (v b).det = 1) :
    FormalResearch.FrameFree.NQubit.ip ψ (rot (fun i => v (g i)) φ) = 0 := by
  classical
  refine vanish_SL2_of_support (slotEntire_ip g ψ φ) (Finset.univ.image g) ?_ h v
    (fun b _ => hv b)
  intro v v' hvv
  have : (fun i => v (g i)) = fun i => v' (g i) :=
    funext fun i => hvv _ (Finset.mem_image_of_mem g (Finset.mem_univ i))
  rw [this]

/-- **`thm:onecopy` (a), the converse direction** `F_K^π = 0 ⟹ F_C^π = 0`. -/
theorem FCs_eq_zero_of_FKs_eq_zero (g : Fin n → β) (ψ φ : Ψ n) (h : FKs g ψ φ = 0) :
    FCs g ψ φ = 0 :=
  (OneCopy.FCs_eq_zero_iff g ψ φ).2
    (ip_eq_zero_of_SU2 g ψ φ ((OneCopy.FKs_eq_zero_iff g ψ φ).1 h))

/-- `F_K^π(ψ,φ) = 0 ⟺ F_C^π(ψ,φ) = 0` (no normalisation hypothesis). -/
theorem FKs_eq_zero_iff_FCs_eq_zero (g : Fin n → β) (ψ φ : Ψ n) :
    FKs g ψ φ = 0 ↔ FCs g ψ φ = 0 := by
  refine ⟨FCs_eq_zero_of_FKs_eq_zero g ψ φ, fun h => ?_⟩
  refine (OneCopy.FKs_eq_zero_iff g ψ φ).2 fun v hv => ?_
  exact (OneCopy.FCs_eq_zero_iff g ψ φ).1 h v fun b => (hv b).2

/-- **`thm:onecopy` (a)**: `F_K^π(ψ) = 0 ⟺ F_C^π(ψ) = 0`, for every `ψ` and every sharing
pattern. -/
theorem FKΘs_eq_zero_iff_FCΘs_eq_zero (g : Fin n → β) (ψ : Ψ n) :
    FKΘs g ψ = 0 ↔ FCΘs g ψ = 0 :=
  FKs_eq_zero_iff_FCs_eq_zero g ψ (Θ ψ)

/-- **`prop:invariantstates`, filter part, from `SU(2)`-invariance only.**  If `ψ` is invariant under
`K_π` (all `SU(2)` frames), then `F_C^π(ψ) = |⟨ψ|Θψ⟩|²/‖Θψ‖²`. -/
theorem FCΘs_of_SU2_invariant (g : Fin n → β) (ψ : Ψ n)
    (hψ : ∀ v : β → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) →
      rot (fun i => v (g i)) ψ = ψ) :
    FCΘs g ψ = Complex.normSq (FormalResearch.FrameFree.NQubit.ip ψ (Θ ψ)) / nsq (Θ ψ) := by
  refine FormalResearch.FrameFree.Sharing.FCΘs_of_invariant g ψ fun v hv => ?_
  funext x
  have hF : SlotEntire (fun v : β → Op1 => rot (fun i => v (g i)) ψ x - ψ x) :=
    fun v a γ hγ => (slotEntire_rot g ψ x v a γ hγ).sub_const _
  classical
  have := vanish_SL2_of_support hF (Finset.univ.image g) (by
      intro v v' hvv
      have : (fun i => v (g i)) = fun i => v' (g i) :=
        funext fun i => hvv _ (Finset.mem_image_of_mem g (Finset.mem_univ i))
      simp only [this])
    (fun v hv => by simp only [hψ v hv, sub_self]) v (fun b _ => hv b)
  exact sub_eq_zero.1 this

theorem FCΘs_of_SU2_invariant_unit (g : Fin n → β) (ψ : Ψ n) (hψ1 : nsq ψ = 1)
    (hψ : ∀ v : β → Op1, (∀ b, FormalResearch.FrameFree.NQubit.SU2 (v b)) →
      rot (fun i => v (g i)) ψ = ψ) :
    FCΘs g ψ = Complex.normSq (FormalResearch.FrameFree.NQubit.ip ψ (Θ ψ)) := by
  rw [FCΘs_of_SU2_invariant g ψ hψ, FormalResearch.FrameFree.NQubit.nsq_Θ, hψ1, div_one]

end Application

end FormalResearch.FrameFree.Zariski
