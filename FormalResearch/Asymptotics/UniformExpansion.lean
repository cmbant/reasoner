module

public import Mathlib

/-!
# Uniform asymptotic expansions in a parameter

A function `f : E → ι → F` has a *uniform asymptotic expansion* `∑ r, ε(i)^r • a r z` along a
filter `l` on `ι`, uniformly for `z` in a set `K ⊆ E`, if for every `R` the remainder
`f z i - ∑_{r<R} ε i ^ r • a r z` is `O(ε i ^ R)` as a function of `(z, i)` along the product filter
`𝓟 K ×ˢ l`.  (An `IsBigO` along `𝓟 K ×ˢ l` is exactly a bound `‖·‖ ≤ C * ‖·‖` valid for all
`z ∈ K` and all `i` in a set of `l`, with `C` independent of `z`: this is the uniformity.)
`hasUniformExpansion_iff` records this unfolded form.

The base notion `HasExpansionAlong L f a ε` allows an arbitrary filter `L` on `E × ι`.  Two
instances are named:

* `HasUniformExpansion f a ε l K`: `L = 𝓟 K ×ˢ l`;
* `HasUniformExpansionOn S f a ε l K`: `L = 𝓟 S ⊓ (𝓟 K ×ˢ l)`, for expansions that are only
  claimed at the points of a set `S ⊆ E × ι` (for example a lattice, where `z` is tied to the index).

## Main results

* `HasExpansionAlong.mono`, `.add`, `.neg`, `.sub`, `.smul`, `.mul` (Cauchy product `cauchyCoeff`),
  `.of_sq` (an expansion in `ε²` is an expansion in `ε` with `evenCoeff`);
* `HasUniformExpansion.mono_set`, `.comp_left` (composition with a fixed function of `z`),
  `.comp_index`;
* `HasUniformExpansion.isBigO_remainder`, `.isBigO_at`: truncation gives an `IsBigO` remainder;
* `HasUniformExpansion.eq_of_tendsto`: uniqueness of the coefficients;
* `HasUniformExpansion.isEquivalent_leading`, `.isEquivalent_zero`: leading term gives
  `IsEquivalent`.

The coefficients live in a real normed space `F`, `ε : ι → ℝ` acts by scalar multiplication
(so `F = ℝ` or `F = 𝕜` for an `RCLike` field `𝕜` are the typical cases); products need a normed
algebra over `ℝ`.
-/

@[expose] public section

open Asymptotics Filter Topology Finset

namespace FormalResearch.Asymptotics

variable {E ι F : Type*}

/-! ### The base notion -/

section Basic

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `f` has the asymptotic expansion `∑ r, ε i ^ r • a r z` along the filter `L` on `E × ι`:
for every `R` the remainder after `R` terms is `O(ε ^ R)` along `L`. -/
def HasExpansionAlong (L : Filter (E × ι)) (f : E → ι → F) (a : ℕ → E → F) (ε : ι → ℝ) : Prop :=
  ∀ R : ℕ, (fun p : E × ι => f p.1 p.2 - ∑ r ∈ range R, ε p.2 ^ r • a r p.1) =O[L]
    fun p => ε p.2 ^ R

/-- `f z i` has the uniform asymptotic expansion `∑ r, ε i ^ r • a r z` along `l`, uniformly for
`z ∈ K`: the remainder after `R` terms is `O(ε i ^ R)` along `𝓟 K ×ˢ l`. -/
def HasUniformExpansion (f : E → ι → F) (a : ℕ → E → F) (ε : ι → ℝ) (l : Filter ι)
    (K : Set E) : Prop :=
  HasExpansionAlong (𝓟 K ×ˢ l) f a ε

/-- The uniform expansion claimed only at the points of `S ⊆ E × ι`. -/
def HasUniformExpansionOn (S : Set (E × ι)) (f : E → ι → F) (a : ℕ → E → F) (ε : ι → ℝ)
    (l : Filter ι) (K : Set E) : Prop :=
  HasExpansionAlong (𝓟 S ⊓ (𝓟 K ×ˢ l)) f a ε

variable {L L' : Filter (E × ι)} {f g : E → ι → F} {a b : ℕ → E → F} {ε : ι → ℝ}

theorem HasExpansionAlong.mono (h : HasExpansionAlong L f a ε) (hL : L' ≤ L) :
    HasExpansionAlong L' f a ε := fun R => (h R).mono hL

theorem HasExpansionAlong.congr_left (h : HasExpansionAlong L f a ε)
    (hfg : ∀ᶠ p in L, f p.1 p.2 = g p.1 p.2) : HasExpansionAlong L g a ε := fun R =>
  (h R).congr' (by filter_upwards [hfg] with p hp using by rw [hp]) EventuallyEq.rfl

theorem HasExpansionAlong.add (hf : HasExpansionAlong L f a ε) (hg : HasExpansionAlong L g b ε) :
    HasExpansionAlong L (fun z i => f z i + g z i) (fun r z => a r z + b r z) ε := fun R =>
  ((hf R).add (hg R)).congr_left fun p => by
    simp only [smul_add, Finset.sum_add_distrib]; abel

theorem HasExpansionAlong.neg (hf : HasExpansionAlong L f a ε) :
    HasExpansionAlong L (fun z i => -f z i) (fun r z => -a r z) ε := fun R =>
  (hf R).neg_left.congr_left fun p => by
    simp only [smul_neg, Finset.sum_neg_distrib]; abel

theorem HasExpansionAlong.sub (hf : HasExpansionAlong L f a ε) (hg : HasExpansionAlong L g b ε) :
    HasExpansionAlong L (fun z i => f z i - g z i) (fun r z => a r z - b r z) ε := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasExpansionAlong.smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (hf : HasExpansionAlong L f a ε) :
    HasExpansionAlong L (fun z i => c • f z i) (fun r z => c • a r z) ε := fun R =>
  ((hf R).const_smul_left c).congr_left fun p => by
    simp only [Pi.smul_apply, smul_sub, Finset.smul_sum]
    congr 1
    exact sum_congr rfl fun x _ => (smul_comm _ _ _).symm

/-- The remainder of order `R` of the expansion, as an `IsBigO`. -/
theorem HasExpansionAlong.isBigO_remainder (h : HasExpansionAlong L f a ε) (R : ℕ) :
    (fun p : E × ι => f p.1 p.2 - ∑ r ∈ range R, ε p.2 ^ r • a r p.1) =O[L]
      fun p => ε p.2 ^ R := h R

/-- The function itself is bounded (order `R = 0`). -/
theorem HasExpansionAlong.isBigO_one (h : HasExpansionAlong L f a ε) :
    (fun p : E × ι => f p.1 p.2) =O[L] fun _ => (1 : ℝ) := by
  simpa using h 0

/-- If `ε` is bounded then each term `ε ^ r • a r z` of the expansion is `O(ε ^ r)`. -/
theorem HasExpansionAlong.isBigO_term (h : HasExpansionAlong L f a ε)
    (hε : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ)) (r : ℕ) :
    (fun p : E × ι => ε p.2 ^ r • a r p.1) =O[L] fun p => ε p.2 ^ r := by
  have h1 : (fun p : E × ι => ε p.2 ^ (r + 1)) =O[L] fun p => ε p.2 ^ r := by
    simpa [pow_succ] using (isBigO_refl (fun p : E × ι => ε p.2 ^ r) L).mul hε
  refine ((h r).sub ((h (r + 1)).trans h1)).congr_left fun p => ?_
  simp [Finset.sum_range_succ]

/-- If `ε` is bounded, a higher power of `ε` is smaller. -/
theorem isBigO_pow_of_le {L : Filter (E × ι)} {ε : ι → ℝ}
    (hε : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ)) {m n : ℕ} (hmn : m ≤ n) :
    (fun p : E × ι => ε p.2 ^ n) =O[L] fun p => ε p.2 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h1 : (fun p : E × ι => ε p.2 ^ k) =O[L] fun _ => (1 : ℝ) := by
    simpa using hε.pow k
  simpa [pow_add] using (isBigO_refl (fun p : E × ι => ε p.2 ^ m) L).mul h1

/-- `ε` tending to `0` along `l` makes it bounded along any filter on `E × ι` projecting to `l`. -/
theorem isBigO_one_of_tendsto {L : Filter (E × ι)} {l : Filter ι} (hL : Tendsto Prod.snd L l)
    (hε : Tendsto ε l (𝓝 0)) : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ) :=
  (hε.isBigO_one ℝ).comp_tendsto hL

/-! #### Even expansions -/

/-- Coefficients of an expansion in `ε` that has `b s` in front of `ε ^ (2 * s)` and no odd
powers. -/
def evenCoeff (b : ℕ → E → F) : ℕ → E → F := fun r z => if Even r then b (r / 2) z else 0

theorem sum_range_evenCoeff (b : ℕ → E → F) (ε : ι → ℝ) (z : E) (i : ι) (R : ℕ) :
    ∑ r ∈ range R, ε i ^ r • evenCoeff b r z = ∑ s ∈ range ((R + 1) / 2), (ε i ^ 2) ^ s • b s z := by
  have key : ∀ S : ℕ, ∑ r ∈ range (2 * S), ε i ^ r • evenCoeff b r z =
      ∑ s ∈ range S, (ε i ^ 2) ^ s • b s z := by
    intro S
    induction S with
    | zero => simp
    | succ S ih =>
      rw [show 2 * (S + 1) = 2 * S + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
        sum_range_succ]
      have h1 : Even (2 * S) := even_two_mul S
      have h2 : ¬ Even (2 * S + 1) := by simp
      simp [evenCoeff, h1, h2, ← pow_mul]
  obtain ⟨S, rfl | rfl⟩ := Nat.even_or_odd' R
  · rw [key, show (2 * S + 1) / 2 = S by omega]
  · rw [show 2 * S + 1 = 2 * S + 1 from rfl, sum_range_succ, key]
    have h1 : Even (2 * S) := even_two_mul S
    rw [show (2 * S + 1 + 1) / 2 = S + 1 by omega, sum_range_succ]
    simp [evenCoeff, h1, ← pow_mul]

/-- An expansion in `ε ^ 2` (with coefficients `b`) is an expansion in `ε` with the even
coefficients `evenCoeff b`, provided `ε` is bounded. -/
theorem HasExpansionAlong.of_sq (h : HasExpansionAlong L f b (fun i => ε i ^ 2))
    (hε : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ)) :
    HasExpansionAlong L f (evenCoeff b) ε := fun R => by
  have h1 : (fun p : E × ι => ((ε p.2) ^ 2) ^ ((R + 1) / 2)) =O[L] fun p => ε p.2 ^ R := by
    simpa [← pow_mul] using isBigO_pow_of_le hε (m := R) (n := 2 * ((R + 1) / 2)) (by omega)
  refine (( h ((R + 1) / 2)).trans h1).congr_left fun p => ?_
  rw [sum_range_evenCoeff]

end Basic

/-! ### Products -/

section Mul

variable [NormedRing F] [NormedAlgebra ℝ F]
variable {L : Filter (E × ι)} {f g : E → ι → F} {a b : ℕ → E → F} {ε : ι → ℝ}

/-- The Cauchy product of two coefficient sequences. -/
def cauchyCoeff (a b : ℕ → E → F) (r : ℕ) (z : E) : F :=
  ∑ p ∈ antidiagonal r, a p.1 z * b p.2 z

omit [NormedAlgebra ℝ F] in
theorem sum_mul_sum_sub_cauchy (X Y : ℕ → F) (R : ℕ) :
    (∑ i ∈ range R, X i) * (∑ j ∈ range R, Y j) - ∑ r ∈ range R, ∑ p ∈ antidiagonal r, X p.1 * Y p.2 =
      ∑ p ∈ (range R ×ˢ range R).filter (fun p => R ≤ p.1 + p.2), X p.1 * Y p.2 := by
  rw [sum_mul_sum, ← sum_product']
  have h := sum_filter_add_sum_filter_not (range R ×ˢ range R) (fun p => R ≤ p.1 + p.2)
    (fun p => X p.1 * Y p.2)
  have h2 : ∑ p ∈ (range R ×ˢ range R).filter (fun p => ¬ R ≤ p.1 + p.2), X p.1 * Y p.2 =
      ∑ r ∈ range R, ∑ p ∈ antidiagonal r, X p.1 * Y p.2 := by
    rw [← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2) (t := range R)
      (fun p hp => by simp at hp ⊢; omega)]
    refine sum_congr rfl fun r hr => ?_
    refine sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [mem_filter, mem_product, mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hr ⊢
    omega
  rw [← h, h2]; abel

/-- **Product of expansions.**  If `ε` is bounded along `L`, the product of two expansions is
an expansion with the Cauchy product coefficients. -/
theorem HasExpansionAlong.mul (hf : HasExpansionAlong L f a ε) (hg : HasExpansionAlong L g b ε)
    (hε : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ)) :
    HasExpansionAlong L (fun z i => f z i * g z i) (cauchyCoeff a b) ε := fun R => by
  set A : E × ι → F := fun p => ∑ r ∈ range R, ε p.2 ^ r • a r p.1 with hA
  set B : E × ι → F := fun p => ∑ r ∈ range R, ε p.2 ^ r • b r p.1 with hB
  have hεR : (fun p : E × ι => ε p.2 ^ R) =O[L] fun _ => (1 : ℝ) := by simpa using hε.pow R
  have hrf := hf R
  have hrg := hg R
  have hAO : A =O[L] fun _ => (1 : ℝ) := by
    refine (hf.isBigO_one.sub (hrf.trans hεR)).congr_left fun p => ?_
    simp [hA]
  have hBO : B =O[L] fun _ => (1 : ℝ) := by
    refine (hg.isBigO_one.sub (hrg.trans hεR)).congr_left fun p => ?_
    simp [hB]
  -- the three error terms
  have e2 : (fun p : E × ι => A p * (g p.1 p.2 - B p)) =O[L] fun p => ε p.2 ^ R := by
    simpa using hAO.mul hrg
  have e3 : (fun p : E × ι => (f p.1 p.2 - A p) * B p) =O[L] fun p => ε p.2 ^ R := by
    simpa using hrf.mul hBO
  have e4 : (fun p : E × ι => (f p.1 p.2 - A p) * (g p.1 p.2 - B p)) =O[L]
      fun p => ε p.2 ^ R := by
    simpa using hrf.mul (hrg.trans hεR)
  -- the truncation error
  have e1 : (fun p : E × ι => A p * B p - ∑ r ∈ range R, ε p.2 ^ r • cauchyCoeff a b r p.1) =O[L]
      fun p => ε p.2 ^ R := by
    have hT : ∀ p : E × ι, ∑ r ∈ range R, ε p.2 ^ r • cauchyCoeff a b r p.1 =
        ∑ r ∈ range R, ∑ q ∈ antidiagonal r,
          (ε p.2 ^ q.1 • a q.1 p.1) * (ε p.2 ^ q.2 • b q.2 p.1) := by
      intro p
      refine sum_congr rfl fun r _ => ?_
      rw [cauchyCoeff, Finset.smul_sum]
      refine sum_congr rfl fun q hq => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
      rw [smul_mul_smul_comm, ← pow_add, hq]
    have hmain : (fun p : E × ι => A p * B p -
        ∑ r ∈ range R, ε p.2 ^ r • cauchyCoeff a b r p.1) = fun p =>
        ∑ q ∈ (range R ×ˢ range R).filter (fun q => R ≤ q.1 + q.2),
          (ε p.2 ^ q.1 • a q.1 p.1) * (ε p.2 ^ q.2 • b q.2 p.1) := by
      funext p
      rw [hT p, ← sum_mul_sum_sub_cauchy (fun i => ε p.2 ^ i • a i p.1)
        (fun j => ε p.2 ^ j • b j p.1) R]
    rw [hmain]
    refine IsBigO.fun_sum fun q hq => ?_
    have hq' : R ≤ q.1 + q.2 := (mem_filter.1 hq).2
    have := ((hf.isBigO_term hε q.1).mul (hg.isBigO_term hε q.2)).trans
      (by simpa [pow_add] using isBigO_pow_of_le hε hq')
    exact this
  refine (((e1.add e2).add e3).add e4).congr_left fun p => ?_
  simp only [cauchyCoeff]
  noncomm_ring

theorem HasUniformExpansion.mul {l : Filter ι} {K : Set E} (hf : HasUniformExpansion f a ε l K)
    (hg : HasUniformExpansion g b ε l K) (hε : Tendsto ε l (𝓝 0)) :
    HasUniformExpansion (fun z i => f z i * g z i) (cauchyCoeff a b) ε l K :=
  HasExpansionAlong.mul hf hg (isBigO_one_of_tendsto tendsto_snd hε)

end Mul

/-! ### Uniform expansions -/

section Uniform

variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f g : E → ι → F} {a b : ℕ → E → F} {ε : ι → ℝ} {l : Filter ι} {K K' : Set E}

theorem eventually_principal_prod_iff {p : E × ι → Prop} :
    (∀ᶠ x in 𝓟 K ×ˢ l, p x) ↔ ∀ᶠ i in l, ∀ z ∈ K, p (z, i) := by
  rw [Filter.prod_comm, eventually_map, eventually_prod_principal_iff]
  rfl

/-- Unfolded form: the constants are uniform in `z ∈ K`. -/
theorem hasUniformExpansion_iff :
    HasUniformExpansion f a ε l K ↔ ∀ R : ℕ, ∃ C : ℝ, ∀ᶠ i in l, ∀ z ∈ K,
      ‖f z i - ∑ r ∈ range R, ε i ^ r • a r z‖ ≤ C * |ε i| ^ R := by
  unfold HasUniformExpansion HasExpansionAlong
  refine forall_congr' fun R => ?_
  rw [isBigO_iff]
  refine exists_congr fun C => ?_
  rw [eventually_principal_prod_iff]
  simp only [norm_pow, Real.norm_eq_abs]

theorem eventually_inf_principal_prod_iff {S : Set (E × ι)} {p : E × ι → Prop} :
    (∀ᶠ x in 𝓟 S ⊓ (𝓟 K ×ˢ l), p x) ↔ ∀ᶠ i in l, ∀ z ∈ K, (z, i) ∈ S → p (z, i) := by
  rw [inf_comm, eventually_inf_principal, eventually_principal_prod_iff]

/-- Unfolded form of `HasUniformExpansionOn`: the bound is only required at points of `S`. -/
theorem hasUniformExpansionOn_iff {S : Set (E × ι)} :
    HasUniformExpansionOn S f a ε l K ↔ ∀ R : ℕ, ∃ C : ℝ, ∀ᶠ i in l, ∀ z ∈ K, (z, i) ∈ S →
      ‖f z i - ∑ r ∈ range R, ε i ^ r • a r z‖ ≤ C * |ε i| ^ R := by
  unfold HasUniformExpansionOn HasExpansionAlong
  refine forall_congr' fun R => ?_
  rw [isBigO_iff]
  refine exists_congr fun C => ?_
  rw [eventually_inf_principal_prod_iff]
  simp only [norm_pow, Real.norm_eq_abs]

theorem HasUniformExpansion.mono_set (h : HasUniformExpansion f a ε l K) (hK : K' ⊆ K) :
    HasUniformExpansion f a ε l K' :=
  HasExpansionAlong.mono h (prod_mono (principal_mono.2 hK) le_rfl)

theorem HasUniformExpansion.mono_filter {l' : Filter ι} (h : HasUniformExpansion f a ε l K)
    (hl : l' ≤ l) : HasUniformExpansion f a ε l' K :=
  HasExpansionAlong.mono h (prod_mono le_rfl hl)

theorem HasUniformExpansion.on (S : Set (E × ι)) (h : HasUniformExpansion f a ε l K) :
    HasUniformExpansionOn S f a ε l K := HasExpansionAlong.mono h inf_le_right

theorem hasUniformExpansionOn_univ :
    HasUniformExpansionOn Set.univ f a ε l K ↔ HasUniformExpansion f a ε l K := by
  simp [HasUniformExpansionOn, HasUniformExpansion]

theorem HasUniformExpansionOn.mono_set {S S' : Set (E × ι)}
    (h : HasUniformExpansionOn S f a ε l K) (hS : S' ⊆ S) (hK : K' ⊆ K) :
    HasUniformExpansionOn S' f a ε l K' :=
  HasExpansionAlong.mono h (inf_le_inf (principal_mono.2 hS)
    (prod_mono (principal_mono.2 hK) le_rfl))

/-- Truncation: the remainder of order `R` is `O(ε ^ R)` uniformly on `K`. -/
theorem HasUniformExpansion.isBigO_remainder (h : HasUniformExpansion f a ε l K) (R : ℕ) :
    (fun p : E × ι => f p.1 p.2 - ∑ r ∈ range R, ε p.2 ^ r • a r p.1) =O[𝓟 K ×ˢ l]
      fun p => ε p.2 ^ R := h R

/-- Pointwise in `z ∈ K`, the remainder of order `R` is `O(ε ^ R)` along `l`. -/
theorem HasUniformExpansion.isBigO_at (h : HasUniformExpansion f a ε l K) {z : E} (hz : z ∈ K)
    (R : ℕ) : (fun i => f z i - ∑ r ∈ range R, ε i ^ r • a r z) =O[l] fun i => ε i ^ R :=
  (h R).comp_tendsto (k := fun i => (z, i))
    (Tendsto.prodMk (tendsto_principal.2 (Eventually.of_forall fun _ => hz)) tendsto_id)

/-- **Composition with a fixed function of `z`.** -/
theorem HasUniformExpansion.comp_left {E' : Type*} (h : HasUniformExpansion f a ε l K)
    {g : E' → E} {K' : Set E'} (hg : Set.MapsTo g K' K) :
    HasUniformExpansion (fun z i => f (g z) i) (fun r z => a r (g z)) ε l K' := fun R =>
  (h R).comp_tendsto (k := Prod.map g id)
    (Tendsto.prodMap (tendsto_principal_principal.2 hg) tendsto_id)

/-- **Reindexing**: along a map `φ : ι' → ι` tending from `l'` to `l`. -/
theorem HasUniformExpansion.comp_index {ι' : Type*} {l' : Filter ι'} (h : HasUniformExpansion f a ε l K)
    {φ : ι' → ι} (hφ : Tendsto φ l' l) :
    HasUniformExpansion (fun z j => f z (φ j)) a (fun j => ε (φ j)) l' K := fun R =>
  (h R).comp_tendsto (k := Prod.map id φ) (Tendsto.prodMap tendsto_id hφ)

theorem HasUniformExpansion.add (hf : HasUniformExpansion f a ε l K)
    (hg : HasUniformExpansion g b ε l K) :
    HasUniformExpansion (fun z i => f z i + g z i) (fun r z => a r z + b r z) ε l K :=
  HasExpansionAlong.add hf hg

theorem HasUniformExpansion.sub (hf : HasUniformExpansion f a ε l K)
    (hg : HasUniformExpansion g b ε l K) :
    HasUniformExpansion (fun z i => f z i - g z i) (fun r z => a r z - b r z) ε l K :=
  HasExpansionAlong.sub hf hg

theorem HasUniformExpansion.smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (hf : HasUniformExpansion f a ε l K) :
    HasUniformExpansion (fun z i => c • f z i) (fun r z => c • a r z) ε l K :=
  HasExpansionAlong.smul c hf

/-- **Uniqueness of the coefficients.**  If `ε → 0` along `l` and `ε ≠ 0` eventually, two
uniform expansions of the same function agree pointwise on `K` (this needs `l ≠ ⊥`). -/
theorem HasUniformExpansion.eq_of_tendsto [l.NeBot] (h₁ : HasUniformExpansion f a ε l K)
    (h₂ : HasUniformExpansion f b ε l K) (hε : Tendsto ε l (𝓝 0)) (hε0 : ∀ᶠ i in l, ε i ≠ 0)
    {z : E} (hz : z ∈ K) (r : ℕ) : a r z = b r z := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    set c : F := a r z - b r z with hc
    have hdiff : (fun i => ε i ^ r • c) =O[l] fun i => ε i ^ (r + 1) := by
      refine ((h₂.isBigO_at hz (r + 1)).sub (h₁.isBigO_at hz (r + 1))).congr_left fun i => ?_
      have : ∑ s ∈ range r, ε i ^ s • a s z = ∑ s ∈ range r, ε i ^ s • b s z :=
        sum_congr rfl fun s hs => by rw [ih s (mem_range.1 hs)]
      simp only [sum_range_succ, this, hc, smul_sub]
      abel
    obtain ⟨C, hC⟩ := hdiff.bound
    have hle : ∀ᶠ i in l, ‖c‖ ≤ C * |ε i| := by
      filter_upwards [hC, hε0] with i hi h0
      simp only [norm_smul, norm_pow, Real.norm_eq_abs] at hi
      rw [pow_succ] at hi
      have hpos : 0 < |ε i| ^ r := pow_pos (abs_pos.2 h0) r
      have : |ε i| ^ r * ‖c‖ ≤ |ε i| ^ r * (C * |ε i|) := by linarith [hi, mul_comm (|ε i| ^ r) (C * |ε i|)]
      exact le_of_mul_le_mul_left this hpos
    have hlim : Tendsto (fun i => C * |ε i|) l (𝓝 0) := by
      simpa using (hε.abs).const_mul C
    have : ‖c‖ ≤ 0 := ge_of_tendsto hlim hle
    have : c = 0 := norm_le_zero_iff.1 this
    exact sub_eq_zero.1 this

/-- **Leading term.**  If the coefficients below `m` vanish at `z ∈ K` and `a m z ≠ 0`, then
`f z i ∼ ε i ^ m • a m z` along `l` (when `ε → 0`). -/
theorem HasUniformExpansion.isEquivalent_leading (h : HasUniformExpansion f a ε l K)
    (hε : Tendsto ε l (𝓝 0)) {z : E} (hz : z ∈ K) (m : ℕ) (hlow : ∀ r < m, a r z = 0)
    (hm : a m z ≠ 0) : (fun i => f z i) ~[l] fun i => ε i ^ m • a m z := by
  have h1 : (fun i => f z i - ε i ^ m • a m z) =O[l] fun i => ε i ^ (m + 1) := by
    refine (h.isBigO_at hz (m + 1)).congr_left fun i => ?_
    rw [sum_range_succ, sum_eq_zero fun r hr => by rw [hlow r (mem_range.1 hr), smul_zero]]
    simp
  have h2 : (fun i => ε i ^ (m + 1)) =o[l] fun i => ε i ^ m • a m z := by
    rw [isLittleO_iff]
    intro c hc
    have hpos : 0 < c * ‖a m z‖ := mul_pos hc (norm_pos_iff.2 hm)
    have : ∀ᶠ i in l, |ε i| < c * ‖a m z‖ := by
      have h0 : Tendsto (fun i => |ε i|) l (𝓝 0) := by simpa using hε.abs
      exact (tendsto_order.1 h0).2 _ hpos
    filter_upwards [this] with i hi
    simp only [norm_pow, norm_smul, Real.norm_eq_abs]
    rw [pow_succ]
    have : 0 ≤ |ε i| ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hi.le this]
  exact h1.trans_isLittleO h2

theorem HasUniformExpansion.isEquivalent_zero (h : HasUniformExpansion f a ε l K)
    (hε : Tendsto ε l (𝓝 0)) {z : E} (hz : z ∈ K) (h0 : a 0 z ≠ 0) :
    (fun i => f z i) ~[l] fun _ => a 0 z := by
  simpa using h.isEquivalent_leading hε hz 0 (fun r hr => absurd hr (Nat.not_lt_zero r)) h0

/-- **Even expansions.**  An expansion in `ε ^ 2` is an expansion in `ε` whose odd coefficients
vanish. -/
theorem HasUniformExpansion.of_sq (h : HasUniformExpansion f b (fun i => ε i ^ 2) l K)
    (hε : Tendsto ε l (𝓝 0)) : HasUniformExpansion f (evenCoeff b) ε l K :=
  HasExpansionAlong.of_sq h (isBigO_one_of_tendsto tendsto_snd hε)

end Uniform

/-- info: 'FormalResearch.Asymptotics.HasExpansionAlong.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasExpansionAlong.mul

/-- info: 'FormalResearch.Asymptotics.HasUniformExpansion.eq_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasUniformExpansion.eq_of_tendsto

/-- info: 'FormalResearch.Asymptotics.HasUniformExpansion.isEquivalent_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasUniformExpansion.isEquivalent_leading

/-- info: 'FormalResearch.Asymptotics.HasUniformExpansion.of_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasUniformExpansion.of_sq

/-- info: 'FormalResearch.Asymptotics.HasUniformExpansion.comp_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasUniformExpansion.comp_left

/-- info: 'FormalResearch.Asymptotics.hasUniformExpansion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniformExpansion_iff

/-- info: 'FormalResearch.Asymptotics.hasUniformExpansionOn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniformExpansionOn_iff

end FormalResearch.Asymptotics
