module

public import FormalResearch.Special.LangerCoordinate
public import FormalResearch.Special.AiryParametrixTaylor

/-!
# Uniform discrete-to-Airy, step 4: a `C²` jet calculus and jets of Hadamard integrals

To bound the Langer chart `ζ = (q-c)(3M/2)^{2/3}` in terms of the data (not just prove it smooth) we need explicit bounds of
`ζ', ζ'', ζ'''`.  `J2 f S b₀ b₁ b₂` says `f ∈ C²(S)` and `|f| ≤ b₀`, `|f'| ≤ b₁`, `|f''| ≤ b₂` on `S` (`S` open).  Closed under
products (`J2.mul`), sums, composition with a smooth function (`J2.comp`), powers of positive functions (`J2.rpow`), and the
Hadamard integrals `q ↦ ∫₀¹ w(t) K(c + t(q-c)) dt` with `0 ≤ w ≤ 1` (`J2.hadamard`: the jets of `hadInt w K c` are bounded by those of `K`).

**Claim class: proved** (calculus; constants explicit).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric

namespace FormalResearch.Special

/-- `C²` jet bounds: `f ∈ C²(S)`, `|f| ≤ b₀`, `|f'| ≤ b₁`, `|f''| ≤ b₂` on `S`. -/
def J2 (f : ℝ → ℝ) (S : Set ℝ) (b0 b1 b2 : ℝ) : Prop :=
  ContDiffOn ℝ 2 f S ∧ ∀ x ∈ S, |f x| ≤ b0 ∧ |deriv f x| ≤ b1 ∧ |deriv (deriv f) x| ≤ b2

lemma j2_d1 {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S) (hf : ContDiffOn ℝ 2 f S) {x : ℝ} (hx : x ∈ S) :
    HasDerivAt f (deriv f x) x := by
  have := apx_hasDerivAt_iterate hS hf 0 (by norm_num) x hx
  simpa using this

lemma j2_d2 {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S) (hf : ContDiffOn ℝ 2 f S) {x : ℝ} (hx : x ∈ S) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x := by
  have := apx_hasDerivAt_iterate hS hf 1 (by norm_num) x hx
  simpa [Function.iterate_succ_apply'] using this

lemma abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma deriv_deriv_of_hasDerivAt {h h1 : ℝ → ℝ} {h2 : ℝ} {S : Set ℝ} (hS : IsOpen S) {x : ℝ} (hx : x ∈ S)
    (hd : ∀ y ∈ S, HasDerivAt h (h1 y) y) (hd2 : HasDerivAt h1 h2 x) : deriv (deriv h) x = h2 := by
  have : deriv h =ᶠ[𝓝 x] h1 :=
    Filter.eventuallyEq_of_mem (hS.mem_nhds hx) (fun y hy => (hd y hy).deriv)
  rw [this.deriv_eq]; exact hd2.deriv

theorem J2.mono {f : ℝ → ℝ} {S S' : Set ℝ} {b0 b1 b2 : ℝ} (hf : J2 f S b0 b1 b2) (h : S' ⊆ S) :
    J2 f S' b0 b1 b2 := ⟨hf.1.mono h, fun x hx => hf.2 x (h hx)⟩

theorem J2.weaken {f : ℝ → ℝ} {S : Set ℝ} {b0 b1 b2 c0 c1 c2 : ℝ} (hf : J2 f S b0 b1 b2) (h0 : b0 ≤ c0)
    (h1 : b1 ≤ c1) (h2 : b2 ≤ c2) : J2 f S c0 c1 c2 :=
  ⟨hf.1, fun x hx => ⟨(hf.2 x hx).1.trans h0, (hf.2 x hx).2.1.trans h1, (hf.2 x hx).2.2.trans h2⟩⟩

theorem J2.mul {f g : ℝ → ℝ} {S : Set ℝ} {b0 b1 b2 c0 c1 c2 : ℝ} (hS : IsOpen S) (hf : J2 f S b0 b1 b2)
    (hg : J2 g S c0 c1 c2) :
    J2 (fun x => f x * g x) S (b0 * c0) (b1 * c0 + b0 * c1) (b2 * c0 + 2 * (b1 * c1) + b0 * c2) := by
  refine ⟨hf.1.mul hg.1, fun x hx => ?_⟩
  have hd : ∀ y ∈ S, HasDerivAt (fun x => f x * g x) (deriv f y * g y + f y * deriv g y) y :=
    fun y hy => (j2_d1 hS hf.1 hy).mul (j2_d1 hS hg.1 hy)
  have hd2 := ((j2_d2 hS hf.1 hx).mul (j2_d1 hS hg.1 hx)).add ((j2_d1 hS hf.1 hx).mul (j2_d2 hS hg.1 hx))
  obtain ⟨f0, f1, f2⟩ := hf.2 x hx
  obtain ⟨g0, g1, g2⟩ := hg.2 x hx
  refine ⟨abs_mul_le_of f0 g0, ?_, ?_⟩
  · rw [(hd x hx).deriv]
    exact (abs_add_le _ _).trans (add_le_add (abs_mul_le_of f1 g0) (abs_mul_le_of f0 g1))
  · rw [deriv_deriv_of_hasDerivAt hS hx hd hd2]
    have h1 := abs_mul_le_of f2 g0
    have h2 := abs_mul_le_of f1 g1
    have h3 := abs_mul_le_of f0 g2
    calc _ ≤ |deriv (deriv f) x * g x| + |deriv f x * deriv g x| + (|deriv f x * deriv g x| + |f x * deriv (deriv g) x|) :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
      _ ≤ _ := by linarith

theorem J2.add {f g : ℝ → ℝ} {S : Set ℝ} {b0 b1 b2 c0 c1 c2 : ℝ} (hS : IsOpen S) (hf : J2 f S b0 b1 b2)
    (hg : J2 g S c0 c1 c2) : J2 (fun x => f x + g x) S (b0 + c0) (b1 + c1) (b2 + c2) := by
  refine ⟨hf.1.add hg.1, fun x hx => ?_⟩
  have hd : ∀ y ∈ S, HasDerivAt (fun x => f x + g x) (deriv f y + deriv g y) y :=
    fun y hy => (j2_d1 hS hf.1 hy).add (j2_d1 hS hg.1 hy)
  have hd2 := (j2_d2 hS hf.1 hx).add (j2_d2 hS hg.1 hx)
  obtain ⟨f0, f1, f2⟩ := hf.2 x hx
  obtain ⟨g0, g1, g2⟩ := hg.2 x hx
  refine ⟨(abs_add_le _ _).trans (add_le_add f0 g0), ?_, ?_⟩
  · rw [(hd x hx).deriv]; exact (abs_add_le _ _).trans (add_le_add f1 g1)
  · rw [deriv_deriv_of_hasDerivAt hS hx hd hd2]; exact (abs_add_le _ _).trans (add_le_add f2 g2)

theorem J2.const {S : Set ℝ} (k : ℝ) : J2 (fun _ => k) S |k| 0 0 := by
  refine ⟨contDiffOn_const, fun x _ => ⟨le_rfl, ?_, ?_⟩⟩ <;> simp

theorem J2.const_mul {f : ℝ → ℝ} {S : Set ℝ} {b0 b1 b2 : ℝ} (hS : IsOpen S) (k : ℝ) (hf : J2 f S b0 b1 b2) :
    J2 (fun x => k * f x) S (|k| * b0) (|k| * b1) (|k| * b2) := by
  have := J2.mul hS (J2.const (S := S) k) hf
  refine ⟨this.1, fun x hx => ?_⟩
  obtain ⟨h0, h1, h2⟩ := this.2 x hx
  refine ⟨h0, ?_, ?_⟩
  · refine h1.trans (le_of_eq ?_); ring
  · refine h2.trans (le_of_eq ?_); ring

/-- Composition with a smooth function `φ` on an open set `T ⊇ f(S)`. -/
theorem J2.comp {φ f : ℝ → ℝ} {S T : Set ℝ} {b0 b1 b2 B0 B1 B2 : ℝ} (hS : IsOpen S) (hT : IsOpen T)
    (hf : J2 f S b0 b1 b2) (hφ : ContDiffOn ℝ 2 φ T) (hmap : ∀ x ∈ S, f x ∈ T)
    (hB : ∀ y ∈ T, |φ y| ≤ B0 ∧ |deriv φ y| ≤ B1 ∧ |deriv (deriv φ) y| ≤ B2) :
    J2 (fun x => φ (f x)) S B0 (B1 * b1) (B2 * (b1 * b1) + B1 * b2) := by
  refine ⟨hφ.comp hf.1 (fun x hx => hmap x hx), fun x hx => ?_⟩
  have hd : ∀ y ∈ S, HasDerivAt (fun x => φ (f x)) (deriv φ (f y) * deriv f y) y := fun y hy =>
    (j2_d1 hT hφ (hmap y hy)).comp y (j2_d1 hS hf.1 hy)
  have hc1 : HasDerivAt (fun y => deriv φ (f y)) (deriv (deriv φ) (f x) * deriv f x) x :=
    (j2_d2 hT hφ (hmap x hx)).comp x (j2_d1 hS hf.1 hx)
  have hd2 : HasDerivAt (fun y => deriv φ (f y) * deriv f y)
      (deriv (deriv φ) (f x) * deriv f x * deriv f x + deriv φ (f x) * deriv (deriv f) x) x :=
    hc1.mul (j2_d2 hS hf.1 hx)
  obtain ⟨f0, f1, f2⟩ := hf.2 x hx
  obtain ⟨p0, p1, p2⟩ := hB _ (hmap x hx)
  refine ⟨p0, ?_, ?_⟩
  · rw [(hd x hx).deriv]; exact abs_mul_le_of p1 f1
  · rw [deriv_deriv_of_hasDerivAt hS hx hd hd2]
    have h1 := abs_mul_le_of (abs_mul_le_of p2 f1) f1
    have h2 := abs_mul_le_of p1 f2
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring

theorem J2.congr {f g : ℝ → ℝ} {S : Set ℝ} {b0 b1 b2 : ℝ} (hS : IsOpen S) (hf : J2 f S b0 b1 b2)
    (heq : ∀ x ∈ S, g x = f x) : J2 g S b0 b1 b2 := by
  refine ⟨hf.1.congr heq, fun x hx => ?_⟩
  have hev : ∀ y ∈ S, deriv g y = deriv f y := fun y hy => by
    have : g =ᶠ[𝓝 y] f := Filter.eventuallyEq_of_mem (hS.mem_nhds hy) heq
    exact this.deriv_eq
  have hev2 : deriv (deriv g) x = deriv (deriv f) x := by
    have : deriv g =ᶠ[𝓝 x] deriv f := Filter.eventuallyEq_of_mem (hS.mem_nhds hx) hev
    exact this.deriv_eq
  obtain ⟨f0, f1, f2⟩ := hf.2 x hx
  exact ⟨by rw [heq x hx]; exact f0, by rw [hev x hx]; exact f1, by rw [hev2]; exact f2⟩

/-- For `x > 0` in `[ℓ, b]`: `x^e ≤ max (ℓ^e) (b^e)` (monotone or antitone). -/
lemma rpow_le_max_of_mem {x ℓ b : ℝ} (e : ℝ) (hℓ : 0 < ℓ) (h1 : ℓ ≤ x) (h2 : x ≤ b) :
    x ^ e ≤ max (ℓ ^ e) (b ^ e) := by
  have hx : 0 < x := lt_of_lt_of_le hℓ h1
  rcases le_total 0 e with he | he
  · exact (Real.rpow_le_rpow hx.le h2 he).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hℓ h1 he).trans (le_max_left _ _)

/-- Powers of a positive function with values in `[ℓ, b]`.  `R0, R1, R2` bound `f^p`, `f^(p-1)`, `f^(p-1-1)`. -/
theorem J2.rpow {f : ℝ → ℝ} {S : Set ℝ} {b0 b1 b2 ℓ : ℝ} (p : ℝ) {R0 R1 R2 : ℝ} (hS : IsOpen S)
    (hf : J2 f S b0 b1 b2) (hℓ : 0 < ℓ) (hrange : ∀ x ∈ S, ℓ ≤ f x)
    (h0 : ∀ x ∈ S, f x ^ p ≤ R0) (h1 : ∀ x ∈ S, f x ^ (p - 1) ≤ R1) (h2 : ∀ x ∈ S, f x ^ (p - 1 - 1) ≤ R2) :
    J2 (fun x => f x ^ p) S R0 (b1 * |p| * R1) (b2 * |p| * R1 + b1 * (|p| * |p - 1|) * R2 * b1) := by
  have hpos : ∀ x ∈ S, 0 < f x := fun x hx => lt_of_lt_of_le hℓ (hrange x hx)
  refine ⟨hf.1.rpow_const_of_ne (fun x hx => (hpos x hx).ne'), fun x hx => ?_⟩
  have hd : ∀ y ∈ S, HasDerivAt (fun x => f x ^ p) (deriv f y * p * f y ^ (p - 1)) y := fun y hy =>
    (j2_d1 hS hf.1 hy).rpow_const (Or.inl (hpos y hy).ne')
  have hd2 : HasDerivAt (fun y => deriv f y * p * f y ^ (p - 1))
      (deriv (deriv f) x * p * f x ^ (p - 1) + deriv f x * p * (deriv f x * (p - 1) * f x ^ (p - 1 - 1))) x :=
    (((j2_d2 hS hf.1 hx).mul_const p).mul
      ((j2_d1 hS hf.1 hx).rpow_const (p := p - 1) (Or.inl (hpos x hx).ne')))
  obtain ⟨f0, f1, f2⟩ := hf.2 x hx
  have hfx := hpos x hx
  have q0 : 0 ≤ f x ^ (p - 1) := (Real.rpow_pos_of_pos hfx _).le
  have q2 : 0 ≤ f x ^ (p - 1 - 1) := (Real.rpow_pos_of_pos hfx _).le
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (Real.rpow_pos_of_pos hfx _)]; exact h0 x hx
  · rw [(hd x hx).deriv]
    have := abs_mul_le_of (abs_mul_le_of f1 (le_refl |p|)) (show |f x ^ (p - 1)| ≤ R1 by
      rw [abs_of_nonneg q0]; exact h1 x hx)
    simpa [abs_mul] using this
  · rw [deriv_deriv_of_hasDerivAt hS hx hd hd2]
    have a1 := abs_mul_le_of (abs_mul_le_of f2 (le_refl |p|)) (show |f x ^ (p - 1)| ≤ R1 by
      rw [abs_of_nonneg q0]; exact h1 x hx)
    have a2 := abs_mul_le_of (abs_mul_le_of f1 (le_refl |p|))
      (abs_mul_le_of (abs_mul_le_of f1 (le_refl |p - 1|)) (show |f x ^ (p - 1 - 1)| ≤ R2 by
        rw [abs_of_nonneg q2]; exact h2 x hx))
    exact (abs_add_le _ _).trans ((add_le_add a1 a2).trans (le_of_eq (by ring)))

/-! ### Hadamard integrals -/

lemma abs_hadInt_le {w K : ℝ → ℝ} {c ρ q b : ℝ} (hw : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t ∧ w t ≤ 1)
    (hK : ∀ x ∈ ball c ρ, |K x| ≤ b) (hq : q ∈ ball c ρ) : |hadInt w K c q| ≤ b := by
  have hb : 0 ≤ b := (abs_nonneg _).trans (hK q hq)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => w t * K (c + t * (q - c))) (C := b) (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |w t| ≤ 1 := by rw [abs_of_nonneg (hw t ht').1]; exact (hw t ht').2
      exact (mul_le_mul h1 (hK _ (hadInt_mem_ball hq ht')) (abs_nonneg _) zero_le_one).trans (by linarith))
  simpa [hadInt, Real.norm_eq_abs] using this

lemma hadInt_ge {w K : ℝ → ℝ} {c ρ q ℓ : ℝ} (hw : Continuous w) (hw0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t)
    (hK : ContinuousOn K (ball c ρ)) (hℓ : ∀ x ∈ ball c ρ, ℓ ≤ K x) (hq : q ∈ ball c ρ) :
    ℓ * ∫ t in (0 : ℝ)..1, w t ≤ hadInt w K c q := by
  have hc := hadInt_cont_t hw hK hq
  have h1 : IntervalIntegrable (fun t => w t * ℓ) volume 0 1 :=
    (hw.mul continuous_const).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => w t * K (c + t * (q - c))) volume 0 1 :=
    hc.intervalIntegrable_of_Icc zero_le_one
  have := intervalIntegral.integral_mono_on zero_le_one h1 h2 (fun t ht => by
    exact mul_le_mul_of_nonneg_left (hℓ _ (hadInt_mem_ball hq ht)) (hw0 t ht))
  rw [intervalIntegral.integral_mul_const] at this
  simp only [hadInt]
  linarith

theorem J2.hadamard {w K : ℝ → ℝ} {c ρ b0 b1 b2 : ℝ} (hw : Continuous w)
    (hw01 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t ∧ w t ≤ 1) (hK : J2 K (ball c ρ) b0 b1 b2) :
    J2 (hadInt w K c) (ball c ρ) b0 b1 b2 := by
  have hK1 : ContDiffOn ℝ 1 K (ball c ρ) := hK.1.of_le (by norm_num)
  have hKd : ContDiffOn ℝ 1 (deriv K) (ball c ρ) := hK.1.deriv_of_isOpen isOpen_ball (by norm_num)
  have hwt : Continuous (fun t => t * w t) := continuous_id.mul hw
  have hw1 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ t * w t ∧ t * w t ≤ 1 := fun t ht => by
    obtain ⟨a, b⟩ := hw01 t ht
    exact ⟨mul_nonneg ht.1 a, by nlinarith [ht.1, ht.2]⟩
  have hw2 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ t * (t * w t) ∧ t * (t * w t) ≤ 1 := fun t ht => by
    obtain ⟨a, b⟩ := hw1 t ht
    exact ⟨mul_nonneg ht.1 a, by nlinarith [ht.1, ht.2]⟩
  have hd : ∀ y ∈ ball c ρ, HasDerivAt (hadInt w K c) (hadInt (fun t => t * w t) (deriv K) c y) y :=
    fun y hy => hasDerivAt_hadInt hw hK1 hy
  have hdd : ∀ y ∈ ball c ρ, HasDerivAt (hadInt (fun t => t * w t) (deriv K) c)
      (hadInt (fun t => t * (t * w t)) (deriv (deriv K)) c y) y :=
    fun y hy => hasDerivAt_hadInt hwt hKd hy
  refine ⟨by simpa using contDiffOn_hadInt 2 w K hw (by simpa using hK.1), fun x hx => ⟨?_, ?_, ?_⟩⟩
  · exact abs_hadInt_le hw01 (fun y hy => (hK.2 y hy).1) hx
  · rw [(hd x hx).deriv]; exact abs_hadInt_le hw1 (fun y hy => (hK.2 y hy).2.1) hx
  · rw [deriv_deriv_of_hasDerivAt isOpen_ball hx hd (hdd x hx)]
    exact abs_hadInt_le hw2 (fun y hy => (hK.2 y hy).2.2) hx

/-- A function with `|f'| ≤ L` on a ball is `L`-Lipschitz there. -/
lemma lip_of_j2 {f : ℝ → ℝ} {c ρ b0 b1 b2 : ℝ} (hf : J2 f (ball c ρ) b0 b1 b2) {x y : ℝ}
    (hx : x ∈ ball c ρ) (hy : y ∈ ball c ρ) : |f x - f y| ≤ b1 * |x - y| := by
  have hdiff : ∀ z ∈ ball c ρ, DifferentiableAt ℝ f z := fun z hz =>
    (j2_d1 isOpen_ball hf.1 hz).differentiableAt
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := ball c ρ) (C := b1) hdiff
    (fun z hz => by simpa [Real.norm_eq_abs] using (hf.2 z hz).2.1) (convex_ball c ρ) hy hx
  simpa [Real.norm_eq_abs] using this

end FormalResearch.Special
