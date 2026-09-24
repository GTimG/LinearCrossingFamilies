import Mathlib

/-!
# Linear crossing families

The main declaration is `LinearCrossingFamilies.linear_crossing_families`.
It asserts that there is an absolute constant `c > 0` such that every finite
planar set of at least two points in general position spans at least `c * n`
pairwise interior-crossing segments with pairwise distinct endpoints, where
`n` is the number of points.

All project definitions and proofs are included here. This includes the
near-avoidance extraction argument of Pach, Rubin, and Tardos at the fixed
error `ε = 1/4` needed for the main theorem, and the required finite ε-net
construction. The full parameter-dependent extraction theorem and the paper's
later applications to plane trees and spoke sets are outside the scope of this
formalization.

This file combines the original modular development in dependency order.
The section boundaries preserve the scopes of local instances and open commands.
Only Mathlib is imported. The required versions are Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`, pinned in the accompanying
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

Fetch the Mathlib build cache: `lake exe cache get`
Build: `lake build LinearCrossingFamiliesAll`
Check directly: `lake env lean LinearCrossingFamiliesAll.lean`
The main theorem and its axiom audit appear at the end of the file.
-/

set_option autoImplicit false

section OriginalModule_LinearCrossingFamilies_Basic

/-!
## Basic definitions for crossing families

The real plane is represented by `ℝ × ℝ`.  An element of `Sym2 Point` is an
unordered pair of endpoints, hence represents an unoriented segment.  The predicate
`Crosses` says exactly that the relative interiors of two segments meet.
-/

open Set

namespace LinearCrossingFamilies

abbrev Point := ℝ × ℝ

/-- The signed twice-area determinant of the ordered triple `p, q, r`. -/
def orientation (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- No three distinct members of `P` are collinear. -/
def GeneralPosition (P : Finset Point) : Prop :=
  ∀ ⦃p⦄, p ∈ P → ∀ ⦃q⦄, q ∈ P → ∀ ⦃r⦄, r ∈ P →
    p ≠ q → p ≠ r → q ≠ r → orientation p q r ≠ 0

/-- The relative interior of the segment represented by an unordered endpoint pair. -/
def segmentInterior : Sym2 Point → Set Point :=
  Sym2.lift ⟨fun p q ↦ openSegment ℝ p q, openSegment_symm ℝ⟩

@[simp]
theorem segmentInterior_mk (p q : Point) :
    segmentInterior s(p, q) = openSegment ℝ p q :=
  rfl

/-- Two segments cross when their relative interiors have a common point. -/
def Crosses (e f : Sym2 Point) : Prop :=
  (segmentInterior e ∩ segmentInterior f).Nonempty

/-- The two endpoints of a segment are distinct. -/
def Nondegenerate (e : Sym2 Point) : Prop :=
  ¬ e.IsDiag

/-- Every endpoint of `e` belongs to the finite point set `P`. -/
def SpannedBy (P : Finset Point) (e : Sym2 Point) : Prop :=
  ∀ p ∈ e, p ∈ P

/-- Two segments have no endpoint in common. -/
def EndpointDisjoint (e f : Sym2 Point) : Prop :=
  Disjoint (e : Set Point) (f : Set Point)

/--
`F` is a finite family of nondegenerate segments spanned by `P`, all of whose
endpoints are distinct, and whose members cross pairwise in their relative interiors.
-/
def IsCrossingFamily (P : Finset Point) (F : Set (Sym2 Point)) : Prop :=
  F.Finite ∧
    (∀ e ∈ F, SpannedBy P e ∧ Nondegenerate e) ∧
    F.Pairwise fun e f ↦ EndpointDisjoint e f ∧ Crosses e f

/-- Convex-hull separation, as used in the paper and in PRT. -/
def Separated (A B : Finset Point) : Prop :=
  Disjoint (convexHull ℝ (A : Set Point)) (convexHull ℝ (B : Set Point))

/--
The exact public statement of the paper's main theorem.  The constant is absolute:
it is quantified before the finite point set.
-/
def LinearCrossingFamiliesStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ P : Finset Point, 2 ≤ P.card → GeneralPosition P →
      ∃ F : Set (Sym2 Point),
        IsCrossingFamily P F ∧ c * (P.card : ℝ) ≤ F.ncard

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_Basic

section OriginalModule_LinearCrossingFamilies_Avoidance

/-!
## Separation and the avoidance defect

The avoidance defect counts unordered pairs of distinct points whose supporting
line meets the opposite convex hull. Each pair is counted once.
-/

open Set

namespace LinearCrossingFamilies

theorem orientation_swap (p q r : Point) :
    orientation q p r = -orientation p q r := by
  simp only [orientation]
  ring

/-- For distinct endpoints, the entire affine line through them. For coincident
endpoints, this determinant-based definition gives the whole plane; such pairs
are excluded from `DefectivePair` by its nondegeneracy condition. -/
def supportingLine : Sym2 Point → Set Point :=
  Sym2.lift ⟨fun p q ↦ {r | orientation p q r = 0}, fun p q ↦ by
    ext r
    simp only [Set.mem_ofPred_eq]
    rw [orientation_swap]
    simp⟩

@[simp]
theorem supportingLine_mk (p q : Point) :
    supportingLine s(p, q) = {r | orientation p q r = 0} :=
  rfl

/-- The supporting line of `e` meets the convex hull of `B`. -/
def LineMeetsConvexHull (e : Sym2 Point) (B : Finset Point) : Prop :=
  (supportingLine e ∩ convexHull ℝ (B : Set Point)).Nonempty

/-- An unordered pair in `A` counted by the `A`-part of the avoidance defect. -/
def DefectivePair (A B : Finset Point) (e : Sym2 Point) : Prop :=
  SpannedBy A e ∧ Nondegenerate e ∧ LineMeetsConvexHull e B

/-- The finite set of unordered pairs in `A` whose line meets `conv(B)`. -/
def defectivePairs (A B : Finset Point) : Set (Sym2 Point) :=
  {e | DefectivePair A B e}

theorem spannedBy_iff_mem_sym2 {P : Finset Point} {e : Sym2 Point} :
    SpannedBy P e ↔ e ∈ (P : Set Point).sym2 := by
  rw [Set.mem_sym2_iff_subset]
  rfl

theorem defectivePairs_finite (A B : Finset Point) :
    (defectivePairs A B).Finite := by
  have hsym2 : ((A : Set Point).sym2).Finite := by
    rw [Set.sym2_eq_mk_image]
    exact (A.finite_toSet.prod A.finite_toSet).image _
  apply hsym2.subset
  intro e he
  exact spannedBy_iff_mem_sym2.mp he.1

/-- The avoidance defect `t(A,B)`: the sum of the two counts of defective unordered pairs. -/
noncomputable def avoidanceDefect (A B : Finset Point) : ℕ :=
  (defectivePairs A B).ncard + (defectivePairs B A).ncard

theorem avoidanceDefect_comm (A B : Finset Point) :
    avoidanceDefect A B = avoidanceDefect B A := by
  simp only [avoidanceDefect, Nat.add_comm]

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_Avoidance

section OriginalModule_LinearCrossingFamilies_CrossingCriterion

/-!
## The strict side test for crossing segments

The construction in `crosses_of_orientation_mul_neg` supplies the actual
intersection point as a strict convex combination of either pair of endpoints.
-/

namespace LinearCrossingFamilies

private theorem ratio_mem_Ioo_of_mul_neg {x y : ℝ} (h : x * y < 0) :
    x / (x - y) ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases mul_neg_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hd : 0 < x - y := by linarith
    exact ⟨div_pos hx hd, (div_lt_one hd).mpr (by linarith)⟩
  · have hd : x - y < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg hx hd, (div_lt_one_of_neg hd).mpr (by linarith)⟩

theorem orientation_difference (a b c d : Point) :
    orientation c d a - orientation c d b =
      -(orientation a b c - orientation a b d) := by
  simp only [orientation]
  ring

theorem orientation_interpolate (a b c d : Point) (t : ℝ) :
    orientation a b ((1 - t) • c + t • d) =
      (1 - t) * orientation a b c + t * orientation a b d := by
  simp only [orientation, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

@[simp] theorem orientation_self_left (a b : Point) : orientation a b a = 0 := by
  simp [orientation]

@[simp] theorem orientation_self_right (a b : Point) : orientation a b b = 0 := by
  simp [orientation, mul_comm]

/-- Reciprocal strict side tests imply an intersection in both open segments. -/
theorem crosses_of_orientation_mul_neg {a b c d : Point}
    (hab : orientation a b c * orientation a b d < 0)
    (hcd : orientation c d a * orientation c d b < 0) :
    Crosses s(a, b) s(c, d) := by
  have ht := ratio_mem_Ioo_of_mul_neg hcd
  have hu := ratio_mem_Ioo_of_mul_neg hab
  have hden : orientation a b c - orientation a b d ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [heq] at hab
    exact (mul_self_nonneg _).not_gt hab
  let t := orientation c d a / (orientation c d a - orientation c d b)
  let u := orientation a b c / (orientation a b c - orientation a b d)
  have heq : (1 - t) • a + t • b = (1 - u) • c + u • d := by
    dsimp [t, u]
    rw [orientation_difference]
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
    all_goals
      field_simp
      simp only [orientation]
      ring
  refine ⟨(1 - t) • a + t • b, ?_, ?_⟩
  · rw [segmentInterior_mk, openSegment_eq_image]
    exact ⟨t, ht, rfl⟩
  · rw [segmentInterior_mk, openSegment_eq_image]
    exact ⟨u, hu, heq.symm⟩

private theorem mul_neg_of_strict_combination_eq_zero {x y t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hx : x ≠ 0)
    (h : (1 - t) * x + t * y = 0) : x * y < 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hprod : 0 < (1 - t) * (-x) := mul_pos (sub_pos.mpr ht.2) (neg_pos.mpr hx)
    have hy : 0 < y := by
      by_contra! hy
      have := mul_nonpos_of_nonneg_of_nonpos ht.1.le hy
      nlinarith
    exact mul_neg_of_neg_of_pos hx hy
  · have hprod : 0 < (1 - t) * x := mul_pos (sub_pos.mpr ht.2) hx
    have hy : y < 0 := by
      by_contra! hy
      have := mul_nonneg ht.1.le hy
      nlinarith
    exact mul_neg_of_pos_of_neg hx hy

/-- A crossing gives reciprocal strict side tests if no tested triple is collinear. -/
theorem orientation_mul_neg_of_crosses {a b c d : Point}
    (h : Crosses s(a, b) s(c, d))
    (habc : orientation a b c ≠ 0) (hcda : orientation c d a ≠ 0) :
    orientation a b c * orientation a b d < 0 ∧
      orientation c d a * orientation c d b < 0 := by
  rcases h with ⟨p, hpab, hpcd⟩
  rw [segmentInterior_mk, openSegment_eq_image] at hpab hpcd
  rcases hpab with ⟨t, ht, htEq⟩
  rcases hpcd with ⟨u, hu, huEq⟩
  dsimp only at htEq huEq
  have hab : orientation a b p = 0 := by
    rw [← htEq, orientation_interpolate]
    simp
  have hcd : orientation c d p = 0 := by
    rw [← huEq, orientation_interpolate]
    simp
  constructor
  · apply mul_neg_of_strict_combination_eq_zero hu habc
    rw [← orientation_interpolate, huEq]
    exact hab
  · apply mul_neg_of_strict_combination_eq_zero ht hcda
    rw [← orientation_interpolate, htEq]
    exact hcd

/-- The familiar reciprocal side test, stated with actual open-segment crossings. -/
theorem crosses_iff_orientation_mul_neg {a b c d : Point}
    (habc : orientation a b c ≠ 0) (hcda : orientation c d a ≠ 0) :
    Crosses s(a, b) s(c, d) ↔
      orientation a b c * orientation a b d < 0 ∧
        orientation c d a * orientation c d b < 0 :=
  ⟨fun h => orientation_mul_neg_of_crosses h habc hcda,
    fun h => crosses_of_orientation_mul_neg h.1 h.2⟩

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_CrossingCriterion

section OriginalModule_LinearCrossingFamilies_HullSideTest

/-!
## Supporting lines and convex hulls

When no point of a set lies on a supporting line, the line meets its convex hull
exactly when that set has points on both strict sides of the line.
-/

namespace LinearCrossingFamilies

theorem orientation_combo (a b x y : Point) {u v : ℝ} (huv : u + v = 1) :
    orientation a b (u • x + v • y) =
      u * orientation a b x + v * orientation a b y := by
  have hu : u = 1 - v := by linarith
  rw [hu, orientation_interpolate]

theorem convex_orientation_pos (a b : Point) :
    Convex ℝ {p : Point | 0 < orientation a b p} := by
  apply convex_iff_add_mem.mpr
  intro x hx y hy u v hu hv huv
  change 0 < orientation a b (u • x + v • y)
  rw [orientation_combo a b x y huv]
  rcases eq_or_lt_of_le hv with hv | hv
  · have hv : v = 0 := hv.symm
    have hu : u = 1 := by linarith
    simpa [hv, hu] using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hu hx.le) (mul_pos hv hy)

theorem convex_orientation_neg (a b : Point) :
    Convex ℝ {p : Point | orientation a b p < 0} := by
  simpa only [orientation_swap a b, neg_pos] using convex_orientation_pos b a

/-- A line through `a,b` meets `conv(B)` iff `B` has points on both strict sides,
provided none of its points is on the line. -/
theorem lineMeetsConvexHull_iff_opposite_sides {a b : Point} {B : Finset Point}
    (hB : ∀ p ∈ B, orientation a b p ≠ 0) :
    LineMeetsConvexHull s(a, b) B ↔
      (∃ p ∈ B, orientation a b p < 0) ∧ (∃ p ∈ B, 0 < orientation a b p) := by
  constructor
  · rintro ⟨z, hzLine, hzHull⟩
    change orientation a b z = 0 at hzLine
    constructor
    · by_contra! h
      have hpos : (B : Set Point) ⊆ {p | 0 < orientation a b p} := by
        intro p hp
        exact lt_of_le_of_ne (h p hp) (hB p hp).symm
      have := convexHull_min hpos (convex_orientation_pos a b) hzHull
      change 0 < orientation a b z at this
      rw [hzLine] at this
      exact (lt_irrefl 0) this
    · by_contra! h
      have hneg : (B : Set Point) ⊆ {p | orientation a b p < 0} := by
        intro p hp
        exact lt_of_le_of_ne (h p hp) (hB p hp)
      have := convexHull_min hneg (convex_orientation_neg a b) hzHull
      change orientation a b z < 0 at this
      rw [hzLine] at this
      exact (lt_irrefl 0) this
  · rintro ⟨⟨x, hxB, hx⟩, ⟨y, hyB, hy⟩⟩
    let t := orientation a b x / (orientation a b x - orientation a b y)
    have hden : orientation a b x - orientation a b y < 0 := by linarith
    have ht0 : 0 < t := div_pos_of_neg_of_neg hx hden
    have ht1 : t < 1 := (div_lt_one_of_neg hden).mpr (by linarith)
    refine ⟨(1 - t) • x + t • y, ?_, ?_⟩
    · change orientation a b ((1 - t) • x + t • y) = 0
      rw [orientation_interpolate]
      dsimp [t]
      field_simp [ne_of_lt hden]
      ring
    · exact convex_convexHull ℝ (B : Set Point)
        (subset_convexHull ℝ _ hxB) (subset_convexHull ℝ _ hyB)
        (sub_nonneg.mpr ht1.le) ht0.le (sub_add_cancel 1 t)

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_HullSideTest

section OriginalModule_LinearCrossingFamilies_Duality

/-!
## Point-line duality and the crossing brackets

These identities implement the geometric translation at the end of the paper's
clean-intersection lemma. The sweep argument establishing the brackets is separate.
-/

namespace LinearCrossingFamilies

/-- The height at horizontal coordinate `x` of the dual line of `p`. -/
def dualValue (p : Point) (x : ℝ) : ℝ := p.1 * x - p.2

/-- The horizontal coordinate of the intersection of two dual lines with unequal slopes. -/
noncomputable def dualAbscissa (a b : Point) : ℝ := (b.2 - a.2) / (b.1 - a.1)

theorem dualValue_dualAbscissa {a b : Point} (h : a.1 ≠ b.1) :
    dualValue a (dualAbscissa a b) = dualValue b (dualAbscissa a b) := by
  dsimp [dualValue, dualAbscissa]
  field_simp [sub_ne_zero.mpr h.symm]
  ring

/-- The determinant/height identity used to transfer the dual brackets. -/
theorem orientation_eq_dual (a b p : Point) {s h : ℝ}
    (ha : dualValue a s = h) (hb : dualValue b s = h) :
    orientation a b p = -(b.1 - a.1) * (dualValue p s - h) := by
  have ha' : a.2 = a.1 * s - h := by dsimp [dualValue] at ha; linarith
  have hb' : b.2 = b.1 * s - h := by dsimp [dualValue] at hb; linarith
  dsimp [orientation, dualValue]
  rw [ha', hb']
  ring

/-- Two reciprocal strict dual height brackets imply a primal interior crossing. -/
theorem crosses_of_dual_brackets {a b c d : Point} {s h s' h' : ℝ}
    (hab : a.1 < b.1) (hcd : c.1 < d.1)
    (ha : dualValue a s = h) (hb : dualValue b s = h)
    (hc : dualValue c s' = h') (hd : dualValue d s' = h')
    (hc_above : h < dualValue c s) (hd_below : dualValue d s < h)
    (hb_above : h' < dualValue b s') (ha_below : dualValue a s' < h') :
    Crosses s(a, b) s(c, d) := by
  have hnab : -(b.1 - a.1) < 0 := neg_neg_of_pos (sub_pos.mpr hab)
  have hncd : -(d.1 - c.1) < 0 := neg_neg_of_pos (sub_pos.mpr hcd)
  have hac : orientation a b c < 0 := by
    rw [orientation_eq_dual a b c ha hb]
    exact mul_neg_of_neg_of_pos hnab (sub_pos.mpr hc_above)
  have had : 0 < orientation a b d := by
    rw [orientation_eq_dual a b d ha hb]
    exact mul_pos_of_neg_of_neg hnab (sub_neg.mpr hd_below)
  have hca : 0 < orientation c d a := by
    rw [orientation_eq_dual c d a hc hd]
    exact mul_pos_of_neg_of_neg hncd (sub_neg.mpr ha_below)
  have hcb : orientation c d b < 0 := by
    rw [orientation_eq_dual c d b hc hd]
    exact mul_neg_of_neg_of_pos hncd (sub_pos.mpr hb_above)
  exact crosses_of_orientation_mul_neg
    (mul_neg_of_neg_of_pos hac had) (mul_neg_of_pos_of_neg hca hcb)

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_Duality

section OriginalModule_LinearCrossingFamilies_Collinearity

/-! ## Agreement of determinant definitions with affine geometry -/

namespace LinearCrossingFamilies

/-- For distinct endpoints, determinant zero describes exactly their affine line. -/
theorem orientation_eq_zero_iff_mem_affineSpan {a b p : Point} (hab : a ≠ b) :
    orientation a b p = 0 ↔ p ∈ affineSpan ℝ ({a, b} : Set Point) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · intro hp
    by_cases hx : a.1 = b.1
    · have hy : a.2 ≠ b.2 := by
        intro hy
        exact hab (Prod.ext hx hy)
      refine ⟨(p.2 - a.2) / (b.2 - a.2), ?_⟩
      rw [AffineMap.lineMap_apply_module]
      apply Prod.ext <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
      all_goals
        field_simp [sub_ne_zero.mpr hy.symm]
        dsimp [orientation] at hp
        nlinarith [hp]
    · refine ⟨(p.1 - a.1) / (b.1 - a.1), ?_⟩
      rw [AffineMap.lineMap_apply_module]
      apply Prod.ext <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
      all_goals
        field_simp [sub_ne_zero.mpr (Ne.symm hx)]
        dsimp [orientation] at hp
        nlinarith [hp]
  · rintro ⟨t, rfl⟩
    rw [AffineMap.lineMap_apply_module, orientation_interpolate]
    simp

theorem supportingLine_eq_affineSpan {a b : Point} (hab : a ≠ b) :
    supportingLine s(a, b) = (affineSpan ℝ ({a, b} : Set Point) : Set Point) := by
  ext p
  exact orientation_eq_zero_iff_mem_affineSpan hab

theorem orientation_eq_zero_iff_collinear {a b c : Point} (hab : a ≠ b) :
    orientation a b c = 0 ↔ Collinear ℝ ({a, b, c} : Set Point) := by
  rw [orientation_eq_zero_iff_mem_affineSpan hab]
  constructor
  · intro hc
    have h := collinear_insert_of_mem_affineSpan_pair hc
    convert h using 1
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · intro h
    exact h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab

/-- The project's general-position predicate is precisely the no-three-collinear condition. -/
theorem generalPosition_iff_no_three_collinear (P : Finset Point) :
    GeneralPosition P ↔
      ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → ∀ ⦃c⦄, c ∈ P →
        a ≠ b → a ≠ c → b ≠ c → ¬ Collinear ℝ ({a, b, c} : Set Point) := by
  constructor
  · intro h a ha b hb c hc hab hac hbc hcol
    exact h ha hb hc hab hac hbc ((orientation_eq_zero_iff_collinear hab).mpr hcol)
  · intro h a ha b hb c hc hab hac hbc hzero
    exact h ha hb hc hab hac hbc ((orientation_eq_zero_iff_collinear hab).mp hzero)

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_Collinearity

section OriginalModule_LinearCrossingFamilies_OrientationTransfer

/-!
## Transfer by orientation signs

The transfer lemmas concern maps preserving the signs of triples on a specified
finite set. The existence of a generic perturbation with these properties is
proved in `GeneralPosition.exists_generic_perturbation` below.
-/

namespace LinearCrossingFamilies

noncomputable local instance : DecidableEq Point := Classical.decEq _

/-- Both strict signs of every labelled triple are preserved by `f`. -/
def PreservesOrientationOn (P : Finset Point) (f : Point → Point) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P,
    (orientation (f a) (f b) (f c) < 0 ↔ orientation a b c < 0) ∧
    (0 < orientation (f a) (f b) (f c) ↔ 0 < orientation a b c)

theorem PreservesOrientationOn.orientation_ne_zero {P : Finset Point} {f : Point → Point}
    (h : PreservesOrientationOn P f) {a b c : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) :
    orientation (f a) (f b) (f c) ≠ 0 ↔ orientation a b c ≠ 0 := by
  rw [ne_iff_lt_or_gt, ne_iff_lt_or_gt]
  exact or_congr (h a ha b hb c hc).1 (h a ha b hb c hc).2

theorem PreservesOrientationOn.orientation_mul_neg {P : Finset Point} {f : Point → Point}
    (h : PreservesOrientationOn P f) {a b c d : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P) :
    orientation (f a) (f b) (f c) * orientation (f a) (f b) (f d) < 0 ↔
      orientation a b c * orientation a b d < 0 := by
  simp only [mul_neg_iff]
  exact or_congr
    (and_congr (h a ha b hb c hc).2 (h a ha b hb d hd).1)
    (and_congr (h a ha b hb c hc).1 (h a ha b hb d hd).2)

/-- Under noncollinearity, preservation of triple signs preserves actual crossings. -/
theorem PreservesOrientationOn.crosses_iff {P : Finset Point} {f : Point → Point}
    (h : PreservesOrientationOn P f) {a b c d : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (habc : orientation a b c ≠ 0) (hcda : orientation c d a ≠ 0) :
    Crosses s(f a, f b) s(f c, f d) ↔ Crosses s(a, b) s(c, d) := by
  rw [crosses_iff_orientation_mul_neg ((h.orientation_ne_zero ha hb hc).mpr habc)
      ((h.orientation_ne_zero hc hd ha).mpr hcda),
    crosses_iff_orientation_mul_neg habc hcda]
  exact and_congr (h.orientation_mul_neg ha hb hc hd) (h.orientation_mul_neg hc hd ha hb)

/-- General position is retained under a sign-preserving map. -/
theorem PreservesOrientationOn.generalPosition {P : Finset Point} {f : Point → Point}
    (h : PreservesOrientationOn P f) (hP : GeneralPosition P) :
    GeneralPosition (P.image f) := by
  intro a ha b hb c hc hab hac hbc
  rcases Finset.mem_image.mp ha with ⟨a, haP, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨b, hbP, rfl⟩
  rcases Finset.mem_image.mp hc with ⟨c, hcP, rfl⟩
  exact (h.orientation_ne_zero haP hbP hcP).mpr
    (hP haP hbP hcP (fun heq => hab (congrArg f heq))
      (fun heq => hac (congrArg f heq)) (fun heq => hbc (congrArg f heq)))

/-- The line-hull incidence of a labelled pair is preserved by its triple signs. -/
theorem PreservesOrientationOn.lineMeetsConvexHull_iff
    {P B : Finset Point} {f : Point → Point} (h : PreservesOrientationOn P f)
    {a b : Point} (ha : a ∈ P) (hb : b ∈ P) (hBP : B ⊆ P)
    (hB : ∀ c ∈ B, orientation a b c ≠ 0) :
    LineMeetsConvexHull s(f a, f b) (B.image f) ↔ LineMeetsConvexHull s(a, b) B := by
  have hB' : ∀ c ∈ B.image f, orientation (f a) (f b) c ≠ 0 := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨c, hcB, rfl⟩
    exact (h.orientation_ne_zero ha hb (hBP hcB)).mpr (hB c hcB)
  rw [lineMeetsConvexHull_iff_opposite_sides hB', lineMeetsConvexHull_iff_opposite_sides hB]
  constructor
  · rintro ⟨⟨c, hc, hcneg⟩, ⟨d, hd, hdpos⟩⟩
    rcases Finset.mem_image.mp hc with ⟨c, hcB, rfl⟩
    rcases Finset.mem_image.mp hd with ⟨d, hdB, rfl⟩
    exact ⟨⟨c, hcB, (h a ha b hb c (hBP hcB)).1.mp hcneg⟩,
      ⟨d, hdB, (h a ha b hb d (hBP hdB)).2.mp hdpos⟩⟩
  · rintro ⟨⟨c, hc, hcneg⟩, ⟨d, hd, hdpos⟩⟩
    exact ⟨⟨f c, Finset.mem_image.mpr ⟨c, hc, rfl⟩,
        (h a ha b hb c (hBP hc)).1.mpr hcneg⟩,
      ⟨f d, Finset.mem_image.mpr ⟨d, hd, rfl⟩,
        (h a ha b hb d (hBP hd)).2.mpr hdpos⟩⟩

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_OrientationTransfer

section OriginalModule_LinearCrossingFamilies_FamilyTransfer

/-! ## Transfer of complete crossing families, including their cardinalities -/

namespace LinearCrossingFamilies

noncomputable local instance : DecidableEq Point := Classical.decEq _

@[simp] theorem spannedBy_mk_iff (P : Finset Point) (a b : Point) :
    SpannedBy P s(a, b) ↔ a ∈ P ∧ b ∈ P := Sym2.forall_mem_pair

@[simp] theorem nondegenerate_mk_iff (a b : Point) :
    Nondegenerate s(a, b) ↔ a ≠ b := by
  simp only [Nondegenerate, Sym2.mk_isDiag_iff]

@[simp] theorem endpointDisjoint_mk_iff (a b c d : Point) :
    EndpointDisjoint s(a, b) s(c, d) ↔ (a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d) := by
  simp [EndpointDisjoint, ne_comm, and_left_comm, and_assoc]

theorem sym2_map_injOn_spanned {P : Finset Point} {f : Point → Point}
    (hf : Set.InjOn f (P : Set Point)) :
    Set.InjOn (Sym2.map f) {e | SpannedBy P e} := by
  intro e he g hg h
  induction e using Sym2.inductionOn with | _ a b =>
  induction g using Sym2.inductionOn with | _ c d =>
  have hab := (spannedBy_mk_iff P a b).mp he
  have hcd := (spannedBy_mk_iff P c d).mp hg
  change s(f a, f b) = s(f c, f d) at h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Sym2.eq_iff.mpr (Or.inl ⟨hf hab.1 hcd.1 h.1, hf hab.2 hcd.2 h.2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨hf hab.1 hcd.2 h.1, hf hab.2 hcd.1 h.2⟩)

theorem SpannedBy.map {P : Finset Point} {e : Sym2 Point} (he : SpannedBy P e)
    (f : Point → Point) : SpannedBy (P.image f) (e.map f) := by
  intro p hp
  rcases Sym2.mem_map.mp hp with ⟨a, ha, rfl⟩
  exact Finset.mem_image.mpr ⟨a, he a ha, rfl⟩

theorem Nondegenerate.map {P : Finset Point} {e : Sym2 Point} {f : Point → Point}
    (he : Nondegenerate e) (hP : SpannedBy P e) (hf : Set.InjOn f (P : Set Point)) :
    Nondegenerate (e.map f) := by
  induction e using Sym2.inductionOn with | _ a b =>
  have hab := (spannedBy_mk_iff P a b).mp hP
  simpa only [Sym2.map_mk, nondegenerate_mk_iff] using
    fun h => (nondegenerate_mk_iff a b).mp he (hf hab.1 hab.2 h)

theorem EndpointDisjoint.map {P : Finset Point} {e g : Sym2 Point} {f : Point → Point}
    (heg : EndpointDisjoint e g) (he : SpannedBy P e) (hg : SpannedBy P g)
    (hf : Set.InjOn f (P : Set Point)) : EndpointDisjoint (e.map f) (g.map f) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  rcases Sym2.mem_map.mp hp with ⟨a, ha, hap⟩
  rcases Sym2.mem_map.mp hq with ⟨b, hb, hbp⟩
  have hab : a = b := hf (he a ha) (hg b hb) (hap.trans hbp.symm)
  exact Set.disjoint_left.mp heg ha (hab ▸ hb)

theorem PreservesOrientationOn.crosses_map_iff {P : Finset Point} {f : Point → Point}
    (hf : PreservesOrientationOn P f) (hP : GeneralPosition P) {e g : Sym2 Point}
    (he : SpannedBy P e) (hg : SpannedBy P g)
    (he' : Nondegenerate e) (hg' : Nondegenerate g) (heg : EndpointDisjoint e g) :
    Crosses (e.map f) (g.map f) ↔ Crosses e g := by
  induction e using Sym2.inductionOn with | _ a b =>
  induction g using Sym2.inductionOn with | _ c d =>
  have ha := (spannedBy_mk_iff P a b).mp he
  have hc := (spannedBy_mk_iff P c d).mp hg
  have hab := (nondegenerate_mk_iff a b).mp he'
  have hcd := (nondegenerate_mk_iff c d).mp hg'
  have hdis := (endpointDisjoint_mk_iff a b c d).mp heg
  exact hf.crosses_iff ha.1 ha.2 hc.1 hc.2
    (hP ha.1 ha.2 hc.1 hab hdis.1.1 hdis.2.1)
    (hP hc.1 hc.2 ha.1 hcd hdis.1.1.symm hdis.1.2.symm)

/-- A sign-preserving injection on `P` transfers a crossing family with exactly
the same number of segments. -/
theorem PreservesOrientationOn.crossingFamily_image {P : Finset Point} {f : Point → Point}
    (hf : PreservesOrientationOn P f) (hinj : Set.InjOn f (P : Set Point))
    (hP : GeneralPosition P) {F : Set (Sym2 Point)} (hF : IsCrossingFamily P F) :
    IsCrossingFamily (P.image f) (Sym2.map f '' F) ∧
      (Sym2.map f '' F).ncard = F.ncard := by
  constructor
  · refine ⟨hF.1.image _, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨(hF.2.1 e he).1.map f,
        (hF.2.1 e he).2.map (hF.2.1 e he).1 hinj⟩
    · rintro _ ⟨e, he, rfl⟩ _ ⟨g, hg, rfl⟩ hne
      have heg := hF.2.2 he hg (fun h => hne (congrArg (Sym2.map f) h))
      have heP := hF.2.1 e he
      have hgP := hF.2.1 g hg
      exact ⟨heg.1.map heP.1 hgP.1 hinj,
        (hf.crosses_map_iff hP heP.1 hgP.1 heP.2 hgP.2 heg.1).mpr heg.2⟩
  · exact (sym2_map_injOn_spanned hinj |>.mono (fun e he => (hF.2.1 e he).1)).ncard_image

/-- A crossing family in a sign-preserving perturbation transfers back to the
original point set without losing any segments. -/
theorem PreservesOrientationOn.crossingFamily_pullback
    {P : Finset Point} {f : Point → Point} (hf : PreservesOrientationOn P f)
    (hinj : Set.InjOn f (P : Set Point)) (hP : GeneralPosition P)
    {F : Set (Sym2 Point)} (hF : IsCrossingFamily (P.image f) F) :
    ∃ G : Set (Sym2 Point), IsCrossingFamily P G ∧ G.ncard = F.ncard := by
  let g := Function.invFunOn f (P : Set Point)
  have hg : ∀ a ∈ P, g (f a) = a := hinj.leftInvOn_invFunOn
  have hgOrient : PreservesOrientationOn (P.image f) g := by
    intro a ha b hb c hc
    rcases Finset.mem_image.mp ha with ⟨a, haP, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b, hbP, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨c, hcP, rfl⟩
    rw [hg a haP, hg b hbP, hg c hcP]
    exact ⟨(hf a haP b hbP c hcP).1.symm, (hf a haP b hbP c hcP).2.symm⟩
  have hgInj : Set.InjOn g (P.image f : Set Point) := by
    simpa only [Finset.coe_image] using f.invFunOn_injOn_image (P : Set Point)
  have hgImage : (P.image f).image g = P := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image] using hinj.invFunOn_image (Set.Subset.rfl)
  obtain ⟨hG, hcard⟩ := hgOrient.crossingFamily_image hgInj (hf.generalPosition hP) hF
  exact ⟨Sym2.map g '' F, hgImage ▸ hG, hcard⟩

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_FamilyTransfer

section OriginalModule_LinearCrossingFamilies_DefectTransfer

/-! ## Preservation of the unordered avoidance-defect count -/

namespace LinearCrossingFamilies

noncomputable local instance : DecidableEq Point := Classical.decEq _

theorem GeneralPosition.orientation_ne_zero_of_disjoint
    {P A B : Finset Point} (hP : GeneralPosition P) (hAP : A ⊆ P) (hBP : B ⊆ P)
    (hAB : Disjoint A B) {a b c : Point} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ B) (hab : a ≠ b) : orientation a b c ≠ 0 := by
  apply hP (hAP ha) (hAP hb) (hBP hc) hab
  · intro hac
    exact Finset.disjoint_left.mp hAB ha (hac ▸ hc)
  · intro hbc
    exact Finset.disjoint_left.mp hAB hb (hbc ▸ hc)

theorem PreservesOrientationOn.defectivePair_map_iff
    {P A B : Finset Point} {f : Point → Point} (hf : PreservesOrientationOn P f)
    (hinj : Set.InjOn f (P : Set Point)) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B)
    {e : Sym2 Point} (he : SpannedBy A e) :
    DefectivePair (A.image f) (B.image f) (e.map f) ↔ DefectivePair A B e := by
  induction e using Sym2.inductionOn with | _ a b =>
  have habA := (spannedBy_mk_iff A a b).mp he
  by_cases hab : a = b
  · subst b
    simp [DefectivePair]
  · have hfab : f a ≠ f b := fun h => hab (hinj (hAP habA.1) (hAP habA.2) h)
    have hline := hf.lineMeetsConvexHull_iff (hAP habA.1) (hAP habA.2) hBP
      (fun c hc => hP.orientation_ne_zero_of_disjoint hAP hBP hAB habA.1 habA.2 hc hab)
    constructor
    · intro h
      exact ⟨he, (nondegenerate_mk_iff a b).mpr hab, hline.mp h.2.2⟩
    · intro h
      exact ⟨he.map f, (nondegenerate_mk_iff (f a) (f b)).mpr hfab, hline.mpr h.2.2⟩

/-- Each defective unordered pair transfers exactly once by endpoint labels. -/
theorem PreservesOrientationOn.defectivePairs_image
    {P A B : Finset Point} {f : Point → Point} (hf : PreservesOrientationOn P f)
    (hinj : Set.InjOn f (P : Set Point)) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B) :
    Sym2.map f '' defectivePairs A B = defectivePairs (A.image f) (B.image f) := by
  ext e
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hf.defectivePair_map_iff hinj hP hAP hBP hAB hg.1).mpr hg
  · intro he
    induction e using Sym2.inductionOn with | _ c d =>
    have hcd := (spannedBy_mk_iff (A.image f) c d).mp he.1
    rcases Finset.mem_image.mp hcd.1 with ⟨a, haA, rfl⟩
    rcases Finset.mem_image.mp hcd.2 with ⟨b, hbA, rfl⟩
    have habA : SpannedBy A s(a, b) := (spannedBy_mk_iff A a b).mpr ⟨haA, hbA⟩
    exact ⟨s(a, b), (hf.defectivePair_map_iff hinj hP hAP hBP hAB habA).mp he, rfl⟩

theorem PreservesOrientationOn.defectivePairs_ncard
    {P A B : Finset Point} {f : Point → Point} (hf : PreservesOrientationOn P f)
    (hinj : Set.InjOn f (P : Set Point)) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B) :
    (defectivePairs (A.image f) (B.image f)).ncard = (defectivePairs A B).ncard := by
  rw [← hf.defectivePairs_image hinj hP hAP hBP hAB]
  apply Set.InjOn.ncard_image
  apply (sym2_map_injOn_spanned hinj).mono
  intro e he p hp
  exact hAP (he.1 p hp)

/-- The complete avoidance defect is unchanged by a sign-preserving injection. -/
theorem PreservesOrientationOn.avoidanceDefect_image
    {P A B : Finset Point} {f : Point → Point} (hf : PreservesOrientationOn P f)
    (hinj : Set.InjOn f (P : Set Point)) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B) :
    avoidanceDefect (A.image f) (B.image f) = avoidanceDefect A B := by
  simp only [avoidanceDefect,
    hf.defectivePairs_ncard hinj hP hAP hBP hAB,
    hf.defectivePairs_ncard hinj hP hBP hAP hAB.symm]

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DefectTransfer

section OriginalModule_LinearCrossingFamilies_Perturbation

/-!
## Stability under small perturbations

For a finite general-position point set, preserving all orientation signs and
injectivity are neighborhood conditions at the identity map. A map in this
neighborhood with distinct first coordinates and distinct slopes for all spanned
lines is constructed in `GeneralPosition.exists_generic_perturbation` below.
-/

open Filter Topology

namespace LinearCrossingFamilies

theorem continuous_orientation_eval (a b c : Point) :
    Continuous (fun f : Point → Point => orientation (f a) (f b) (f c)) := by
  unfold orientation
  fun_prop

/-- All signs of the finitely many triple orientations persist near the identity. -/
theorem GeneralPosition.eventually_preservesOrientationOn {P : Finset Point}
    (hP : GeneralPosition P) :
    ∀ᶠ f : Point → Point in 𝓝 id, PreservesOrientationOn P f := by
  unfold PreservesOrientationOn
  simp only [Filter.eventually_all_finset]
  intro a ha b hb c hc
  by_cases hab : a = b
  · subst b
    exact Filter.Eventually.of_forall (fun f => by simp [orientation])
  by_cases hac : a = c
  · subst c
    exact Filter.Eventually.of_forall (fun f => by simp)
  by_cases hbc : b = c
  · subst c
    exact Filter.Eventually.of_forall (fun f => by simp)
  rcases lt_or_gt_of_ne (hP ha hb hc hab hac hbc) with hneg | hpos
  · have hnear : ∀ᶠ f : Point → Point in 𝓝 id,
        orientation (f a) (f b) (f c) < 0 :=
      (isOpen_lt (continuous_orientation_eval a b c) continuous_const).mem_nhds hneg
    filter_upwards [hnear] with f hf
    exact ⟨iff_of_true hf hneg, iff_of_false (not_lt_of_ge hf.le) (not_lt_of_ge hneg.le)⟩
  · have hnear : ∀ᶠ f : Point → Point in 𝓝 id,
        0 < orientation (f a) (f b) (f c) :=
      (isOpen_lt continuous_const (continuous_orientation_eval a b c)).mem_nhds hpos
    filter_upwards [hnear] with f hf
    exact ⟨iff_of_false (not_lt_of_ge hf.le) (not_lt_of_ge hpos.le), iff_of_true hf hpos⟩

/-- Distinct labels of a finite point set remain distinct near the identity. -/
theorem eventually_injOn_finset (P : Finset Point) :
    ∀ᶠ f : Point → Point in 𝓝 id, Set.InjOn f (P : Set Point) := by
  change ∀ᶠ f : Point → Point in 𝓝 id,
    ∀ a ∈ P, ∀ b ∈ P, f a = f b → a = b
  simp only [Filter.eventually_all_finset]
  intro a _ b _
  by_cases hab : a = b
  · exact Filter.Eventually.of_forall (fun _ _ => hab)
  · have hnear : ∀ᶠ f : Point → Point in 𝓝 id, f a ≠ f b :=
      (isOpen_ne_fun (continuous_apply a) (continuous_apply b)).mem_nhds hab
    exact hnear.mono (fun _ hf heq => (hf heq).elim)

/-- The conditions needed for labelwise geometric transfer hold throughout some
neighborhood of the identity, within which the generic perturbation is constructed. -/
theorem GeneralPosition.eventually_transfer_conditions {P : Finset Point}
    (hP : GeneralPosition P) :
    ∀ᶠ f : Point → Point in 𝓝 id,
      PreservesOrientationOn P f ∧ Set.InjOn f (P : Set Point) :=
  hP.eventually_preservesOrientationOn.and (eventually_injOn_finset P)

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_Perturbation

section OriginalModule_LinearCrossingFamilies_PolynomialGenericity

/-!
## Avoiding polynomial coincidences

A nonzero real multivariate polynomial cannot vanish on a nonempty open set.
This follows directly from Mathlib's polynomial extensionality on boxes with
infinite sides, and also applies to an infinite ambient variable type.
-/

open Set Filter Topology

namespace LinearCrossingFamilies

theorem dense_mvPolynomial_eval_ne_zero {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : p ≠ 0) : Dense {w : σ → ℝ | MvPolynomial.eval w p ≠ 0} := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  rcases hUne with ⟨x, hx⟩
  rcases isOpen_pi_iff.mp hU x hx with ⟨I, u, hu, hsub⟩
  by_contra hn
  apply hp
  let v : σ → Set ℝ := fun i => if i ∈ I then u i else univ
  have hv : ∀ i, (v i).Infinite := by
    intro i
    by_cases hi : i ∈ I
    · simpa only [v, ite_eq_left hi] using
        infinite_of_mem_nhds (x i) ((hu i hi).1.mem_nhds (hu i hi).2)
    · simpa only [v, ite_eq_right hi] using (Set.infinite_univ : (univ : Set ℝ).Infinite)
  apply MvPolynomial.funext_set v hv
  intro y hy
  have hyU : y ∈ U := hsub (fun i hi => by
    have := hy i (mem_univ i)
    simpa only [v, ite_eq_left (show i ∈ I from hi)] using this)
  have hyzero : MvPolynomial.eval y p = 0 := by
    by_contra hne
    exact hn ⟨y, hyU, hne⟩
  simpa only [map_zero] using hyzero

/-- A finite family of nonzero polynomial conditions can be met in any neighborhood. -/
theorem exists_mvPolynomial_eval_ne_zero_mem_nhds {σ ι : Type*}
    (I : Finset ι) (p : ι → MvPolynomial σ ℝ) (hp : ∀ i ∈ I, p i ≠ 0)
    {x : σ → ℝ} {U : Set (σ → ℝ)} (hU : U ∈ 𝓝 x) :
    ∃ w ∈ U, ∀ i ∈ I, MvPolynomial.eval w (p i) ≠ 0 := by
  have hprod : (∏ i ∈ I, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  obtain ⟨w, hwprod, hwU⟩ := (dense_mvPolynomial_eval_ne_zero hprod).inter_nhds_nonempty hU
  refine ⟨w, hwU, ?_⟩
  have heval : (∏ i ∈ I, MvPolynomial.eval w (p i)) ≠ 0 := by
    simpa only [Set.mem_ofPred_eq, map_prod] using hwprod
  exact Finset.prod_ne_zero_iff.mp heval

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_PolynomialGenericity

section OriginalModule_LinearCrossingFamilies_GenericCoordinates

/-!
## Generic finite configurations

The unwanted equalities of first coordinates and slopes are nonzero polynomial
conditions on labelled point coordinates. Their product can be avoided in any
neighborhood, including the orientation-preserving neighborhood.
-/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

/-- Two scalar variables for each point label: `false` for x, `true` for y. -/
abbrev CoordinateVariables := Point × Bool

def pointCoordinates (f : Point → Point) (v : CoordinateVariables) : ℝ :=
  if v.2 then (f v.1).2 else (f v.1).1

def coordinatePoints (w : CoordinateVariables → ℝ) (p : Point) : Point :=
  (w (p, false), w (p, true))

@[simp] theorem coordinatePoints_pointCoordinates (f : Point → Point) :
    coordinatePoints (pointCoordinates f) = f := by
  funext p
  simp [coordinatePoints, pointCoordinates]

theorem continuous_coordinatePoints : Continuous coordinatePoints := by
  unfold coordinatePoints
  fun_prop

def firstCoordinatePolynomial (a b : Point) : MvPolynomial CoordinateVariables ℝ :=
  MvPolynomial.X (a, false) - MvPolynomial.X (b, false)

/-- Cross-multiplication polynomial for equality of the slopes of `ab` and `cd`. -/
def slopePolynomial (a b c d : Point) : MvPolynomial CoordinateVariables ℝ :=
  (MvPolynomial.X (b, true) - MvPolynomial.X (a, true)) *
      (MvPolynomial.X (d, false) - MvPolynomial.X (c, false)) -
    (MvPolynomial.X (d, true) - MvPolynomial.X (c, true)) *
      (MvPolynomial.X (b, false) - MvPolynomial.X (a, false))

theorem firstCoordinatePolynomial_ne_zero {a b : Point} (hab : a ≠ b) :
    firstCoordinatePolynomial a b ≠ 0 := by
  classical
  intro h
  have heval := congrArg
    (MvPolynomial.eval (pointCoordinates (fun p => (if p = a then 1 else 0, 0)))) h
  norm_num [firstCoordinatePolynomial, pointCoordinates, Ne.symm hab] at heval

/-- Different nondegenerate unordered pairs impose a genuine polynomial condition,
including when the pairs share one endpoint. -/
theorem slopePolynomial_ne_zero {a b c d : Point}
    (hab : a ≠ b) (hcd : c ≠ d) (hpairs : s(a, b) ≠ s(c, d)) :
    slopePolynomial a b c d ≠ 0 := by
  classical
  have hunique : (a ≠ c ∧ a ≠ d) ∨ (b ≠ c ∧ b ≠ d) := by
    by_cases hac : a = c
    · right
      exact ⟨fun hbc => hab (hac.trans hbc.symm),
        fun hbd => hpairs (Sym2.eq_iff.mpr (Or.inl ⟨hac, hbd⟩))⟩
    · by_cases had : a = d
      · right
        exact ⟨fun hbc => hpairs (Sym2.eq_iff.mpr (Or.inr ⟨had, hbc⟩)),
          fun hbd => hab (had.trans hbd.symm)⟩
      · exact Or.inl ⟨hac, had⟩
  intro h
  rcases hunique with ⟨hac, had⟩ | ⟨hbc, hbd⟩
  · have heval := congrArg (MvPolynomial.eval (pointCoordinates
        (fun p => (if p = d then 1 else 0, if p = a then 1 else 0)))) h
    norm_num [slopePolynomial, pointCoordinates, hab, Ne.symm hab, hcd,
      hac, Ne.symm hac, had, Ne.symm had] at heval
  · have heval := congrArg (MvPolynomial.eval (pointCoordinates
        (fun p => (if p = d then 1 else 0, if p = b then 1 else 0)))) h
    norm_num [slopePolynomial, pointCoordinates, hab, hcd,
      hbc, Ne.symm hbc, hbd, Ne.symm hbd] at heval

/-- The finite product of all forbidden coordinate and slope coincidences. -/
def genericPolynomial (P : Finset Point) : MvPolynomial CoordinateVariables ℝ := by
  classical
  exact (∏ e ∈ P.offDiag, firstCoordinatePolynomial e.1 e.2) *
    ∏ z ∈ (P.offDiag ×ˢ P.offDiag).filter
      (fun z => s(z.1.1, z.1.2) ≠ s(z.2.1, z.2.2)),
      slopePolynomial z.1.1 z.1.2 z.2.1 z.2.2

theorem genericPolynomial_ne_zero (P : Finset Point) : genericPolynomial P ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro e he
    exact firstCoordinatePolynomial_ne_zero (Finset.mem_offDiag.mp he).2.2
  · apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hz, hpairs⟩
    rcases Finset.mem_product.mp hz with ⟨he, hf⟩
    exact slopePolynomial_ne_zero (Finset.mem_offDiag.mp he).2.2
      (Finset.mem_offDiag.mp hf).2.2 hpairs

/-- First coordinates are distinct, and each different spanned segment has a
different slope. This implies unique horizontal coordinates for all dual intersections. -/
def GenericCoordinatesOn (P : Finset Point) (f : Point → Point) : Prop :=
  (∀ a ∈ P, ∀ b ∈ P, a ≠ b → (f a).1 ≠ (f b).1) ∧
    (∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ d ∈ P,
      a ≠ b → c ≠ d → s(a, b) ≠ s(c, d) →
        dualAbscissa (f a) (f b) ≠ dualAbscissa (f c) (f d))

/-- Genericity on endpoint labels gives genericity of the actual image point set. -/
theorem GenericCoordinatesOn.image {P : Finset Point} {f : Point → Point}
    (h : GenericCoordinatesOn P f) : GenericCoordinatesOn (P.image f) id := by
  classical
  constructor
  · intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨a, haP, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b, hbP, rfl⟩
    exact h.1 a haP b hbP (fun heq => hab (congrArg f heq))
  · intro a ha b hb c hc d hd hab hcd hpairs
    rcases Finset.mem_image.mp ha with ⟨a, haP, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b, hbP, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨c, hcP, rfl⟩
    rcases Finset.mem_image.mp hd with ⟨d, hdP, rfl⟩
    exact h.2 a haP b hbP c hcP d hdP
      (fun heq => hab (congrArg f heq)) (fun heq => hcd (congrArg f heq))
      (fun heq => hpairs (congrArg (Sym2.map f) heq))

theorem genericCoordinatesOn_of_eval_ne_zero {P : Finset Point}
    {w : CoordinateVariables → ℝ} (hw : MvPolynomial.eval w (genericPolynomial P) ≠ 0) :
    GenericCoordinatesOn P (coordinatePoints w) := by
  classical
  simp only [genericPolynomial, map_mul, map_prod, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff] at hw
  have hfirst : ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      (coordinatePoints w a).1 ≠ (coordinatePoints w b).1 := by
    intro a ha b hb hab
    have h := hw.1 (a, b) (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩)
    simpa only [firstCoordinatePolynomial, map_sub, MvPolynomial.eval_X,
      coordinatePoints, sub_ne_zero] using h
  refine ⟨hfirst, ?_⟩
  intro a ha b hb c hc d hd hab hcd hpairs heq
  have h := hw.2 ((a, b), (c, d)) (Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩,
      Finset.mem_offDiag.mpr ⟨hc, hd, hcd⟩⟩, hpairs⟩)
  apply h
  simp only [slopePolynomial, map_sub, map_mul, MvPolynomial.eval_X]
  have hxab := sub_ne_zero.mpr (Ne.symm (hfirst a ha b hb hab))
  have hxcd := sub_ne_zero.mpr (Ne.symm (hfirst c hc d hd hcd))
  dsimp [dualAbscissa, coordinatePoints] at heq hxab hxcd
  exact sub_eq_zero.mpr ((div_eq_div_iff hxab hxcd).mp heq)

/-- Generic configurations exist in every neighborhood of any labelled configuration. -/
theorem exists_genericCoordinatesOn_mem_nhds (P : Finset Point) {f : Point → Point}
    {U : Set (Point → Point)} (hU : U ∈ 𝓝 f) :
    ∃ g ∈ U, GenericCoordinatesOn P g := by
  have hpre : coordinatePoints ⁻¹' U ∈ 𝓝 (pointCoordinates f) := by
    apply continuous_coordinatePoints.continuousAt.preimage_mem_nhds
    simpa only [coordinatePoints_pointCoordinates] using hU
  obtain ⟨w, hw, hwU⟩ :=
    (dense_mvPolynomial_eval_ne_zero (genericPolynomial_ne_zero P)).inter_nhds_nonempty hpre
  exact ⟨coordinatePoints w, hwU, genericCoordinatesOn_of_eval_ne_zero hw⟩

/-- Every finite general-position set admits an arbitrarily small generic
perturbation preserving all orientation signs and endpoint labels. -/
theorem GeneralPosition.exists_generic_perturbation {P : Finset Point}
    (hP : GeneralPosition P) {U : Set (Point → Point)} (hU : U ∈ 𝓝 id) :
    ∃ f ∈ U, PreservesOrientationOn P f ∧ Set.InjOn f (P : Set Point) ∧
      GenericCoordinatesOn P f := by
  obtain ⟨f, ⟨hfU, hfSigns, hfInj⟩, hfGeneric⟩ :=
    exists_genericCoordinatesOn_mem_nhds P (Filter.inter_mem hU hP.eventually_transfer_conditions)
  exact ⟨f, hfU, hfSigns, hfInj, hfGeneric⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_GenericCoordinates

section OriginalModule_LinearCrossingFamilies_SeparationCoordinates

/-! ## Orienting a strict separating line as the vertical axis -/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- A translated rotation followed by a positive uniform scaling. -/
def orientedCoordinates (α β t : ℝ) (p : Point) : Point :=
  (α * p.1 + β * p.2 - t, -β * p.1 + α * p.2)

theorem orientation_orientedCoordinates (α β t : ℝ) (a b c : Point) :
    orientation (orientedCoordinates α β t a) (orientedCoordinates α β t b)
      (orientedCoordinates α β t c) = (α ^ 2 + β ^ 2) * orientation a b c := by
  simp only [orientation, orientedCoordinates]
  ring

theorem orientedCoordinates_preservesOrientationOn (P : Finset Point) {α β : ℝ}
    (h : 0 < α ^ 2 + β ^ 2) (t : ℝ) :
    PreservesOrientationOn P (orientedCoordinates α β t) := by
  intro a _ b _ c _
  rw [orientation_orientedCoordinates]
  constructor
  · simp [mul_neg_iff, h, not_lt_of_ge h.le]
  · exact mul_pos_iff_of_pos_left h

theorem orientedCoordinates_injective {α β : ℝ} (h : 0 < α ^ 2 + β ^ 2) (t : ℝ) :
    Function.Injective (orientedCoordinates α β t) := by
  have hinverse : Function.LeftInverse
      (fun q : Point => ((α * (q.1 + t) - β * q.2) / (α ^ 2 + β ^ 2),
        (β * (q.1 + t) + α * q.2) / (α ^ 2 + β ^ 2)))
      (orientedCoordinates α β t) := by
    intro p
    apply Prod.ext <;> dsimp [orientedCoordinates] <;> field_simp [ne_of_gt h] <;> ring
  exact hinverse.injective

theorem linearMap_point_coordinates (L : Point →ₗ[ℝ] ℝ) (p : Point) :
    L p = L (1, 0) * p.1 + L (0, 1) * p.2 := by
  have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- Strict separation by the y-axis, expressed on the original endpoint labels. -/
def VerticallySeparatedOn (A B : Finset Point) (f : Point → Point) : Prop :=
  (∀ a ∈ A, (f a).1 < 0) ∧ (∀ b ∈ B, 0 < (f b).1)

/-- Disjoint finite convex hulls admit an injective, orientation-preserving
coordinate change that strictly separates the two sets by the y-axis. -/
theorem Separated.exists_vertical_coordinates {A B : Finset Point}
    (hsep : Separated A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ f : Point → Point, Function.Injective f ∧
      PreservesOrientationOn (A ∪ B) f ∧ VerticallySeparatedOn A B f := by
  obtain ⟨L, u, v, hLA, huv, hLB⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ (A : Set Point)) (A.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (B : Set Point)) (B.finite_toSet.isClosed_convexHull ℝ) hsep
  let α := L (1, 0)
  let β := L (0, 1)
  have hL : ∀ p : Point, L p = α * p.1 + β * p.2 :=
    linearMap_point_coordinates L.toLinearMap
  have hnonzero : α ≠ 0 ∨ β ≠ 0 := by
    by_contra! h
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    have haL := hLA a (subset_convexHull ℝ _ ha)
    have hbL := hLB b (subset_convexHull ℝ _ hb)
    rw [hL a] at haL
    rw [hL b] at hbL
    simp only [h.1, h.2, zero_mul, add_zero] at haL hbL
    linarith
  have hnorm : 0 < α ^ 2 + β ^ 2 := by
    rcases hnonzero with hα | hβ
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hα) (sq_nonneg β)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg α) (sq_pos_of_ne_zero hβ)
  refine ⟨orientedCoordinates α β u, orientedCoordinates_injective hnorm u,
    orientedCoordinates_preservesOrientationOn _ hnorm u, ?_, ?_⟩
  · intro a ha
    have haL := hLA a (subset_convexHull ℝ _ ha)
    change α * a.1 + β * a.2 - u < 0
    rw [← hL a]
    linarith
  · intro b hb
    have hbL := hLB b (subset_convexHull ℝ _ hb)
    change 0 < α * b.1 + β * b.2 - u
    rw [← hL b]
    linarith

/-- Strict vertical separation persists throughout a neighborhood of a configuration. -/
theorem VerticallySeparatedOn.eventually {A B : Finset Point} {f : Point → Point}
    (h : VerticallySeparatedOn A B f) :
    ∀ᶠ g : Point → Point in 𝓝 f, VerticallySeparatedOn A B g := by
  apply Filter.Eventually.and
  · simp only [Filter.eventually_all_finset]
    intro a ha
    exact (isOpen_lt (continuous_apply a |>.fst) continuous_const).mem_nhds (h.1 a ha)
  · simp only [Filter.eventually_all_finset]
    intro b hb
    exact (isOpen_lt continuous_const (continuous_apply b |>.fst)).mem_nhds (h.2 b hb)

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_SeparationCoordinates

section OriginalModule_LinearCrossingFamilies_CoordinatePreparation

/-!
## Coordinate preparation for the dual arrangement

This completes the coordinate-preparation step from the paper: strict separation
is first made vertical by an orientation-preserving affine change, and a generic
perturbation is then chosen inside the sign- and separation-preserving neighborhood.
-/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

theorem PreservesOrientationOn.comp {P : Finset Point} {f g : Point → Point}
    (hf : PreservesOrientationOn P f) (hg : PreservesOrientationOn (P.image f) g) :
    PreservesOrientationOn P (g ∘ f) := by
  intro a ha b hb c hc
  have ha' : f a ∈ P.image f := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hb' : f b ∈ P.image f := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hc' : f c ∈ P.image f := Finset.mem_image.mpr ⟨c, hc, rfl⟩
  exact ⟨(hg _ ha' _ hb' _ hc').1.trans (hf a ha b hb c hc).1,
    (hg _ ha' _ hb' _ hc').2.trans (hf a ha b hb c hc).2⟩

theorem GenericCoordinatesOn.comp {P : Finset Point} {f g : Point → Point}
    (hf : Set.InjOn f (P : Set Point)) (hg : GenericCoordinatesOn (P.image f) g) :
    GenericCoordinatesOn P (g ∘ f) := by
  have himage : ∀ p ∈ P, f p ∈ P.image f :=
    fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩
  constructor
  · intro a ha b hb hab
    exact hg.1 _ (himage a ha) _ (himage b hb) (fun h => hab (hf ha hb h))
  · intro a ha b hb c hc d hd hab hcd hpairs
    apply hg.2 _ (himage a ha) _ (himage b hb) _ (himage c hc) _ (himage d hd)
      (fun h => hab (hf ha hb h)) (fun h => hcd (hf hc hd h))
    intro h
    exact hpairs (sym2_map_injOn_spanned hf
      ((spannedBy_mk_iff P a b).mpr ⟨ha, hb⟩)
      ((spannedBy_mk_iff P c d).mpr ⟨hc, hd⟩) h)

theorem Separated.disjoint {A B : Finset Point} (h : Separated A B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro p ha hb
  exact Set.disjoint_left.mp h (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ hb)

/-- Vertical separation of endpoints gives disjoint convex hulls in the prepared plane. -/
theorem VerticallySeparatedOn.separated_images {A B : Finset Point} {f : Point → Point}
    (h : VerticallySeparatedOn A B f) : Separated (A.image f) (B.image f) := by
  have hA : (A.image f : Set Point) ⊆ {p | p.1 < 0} := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    exact h.1 a ha
  have hB : (B.image f : Set Point) ⊆ {p | 0 < p.1} := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨b, hb, rfl⟩
    exact h.2 b hb
  have hfst : IsLinearMap ℝ (fun p : Point => p.1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hA' := convexHull_min hA (convex_halfSpace_lt hfst 0)
  have hB' := convexHull_min hB (convex_halfSpace_gt hfst 0)
  apply Set.disjoint_left.mpr
  intro p hpA hpB
  have hlt : p.1 < 0 := hA' hpA
  have hgt : 0 < p.1 := hB' hpB
  exact hlt.not_gt hgt

/-- Every pair covered by the deletion proposition has coordinates satisfying all
genericity and sign requirements of the dual sweep. There are no extra geometric
hypotheses beyond nonemptiness, convex-hull separation, and general position. -/
theorem Separated.exists_prepared_coordinates {A B : Finset Point}
    (hsep : Separated A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hP : GeneralPosition (A ∪ B)) :
    ∃ f : Point → Point, PreservesOrientationOn (A ∪ B) f ∧
      Set.InjOn f (A ∪ B : Finset Point) ∧ VerticallySeparatedOn A B f ∧
      GenericCoordinatesOn (A ∪ B) f := by
  obtain ⟨f, hfInj, hfSigns, hfVert⟩ := hsep.exists_vertical_coordinates hA hB
  have hGP := hfSigns.generalPosition hP
  have hvertical : VerticallySeparatedOn (A.image f) (B.image f) id := by
    constructor
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
      exact hfVert.1 p hp
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
      exact hfVert.2 p hp
  obtain ⟨g, hgVert, hgSigns, hgInj, hgGeneric⟩ :=
    hGP.exists_generic_perturbation hvertical.eventually
  refine ⟨g ∘ f, hfSigns.comp hgSigns, ?_, ?_,
    GenericCoordinatesOn.comp hfInj.injOn hgGeneric⟩
  · intro a ha b hb hab
    apply hfInj
    exact hgInj (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (Finset.mem_image.mpr ⟨b, hb, rfl⟩) hab
  · constructor
    · intro a ha
      exact hgVert.1 (f a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    · intro b hb
      exact hgVert.2 (f b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)

/-- Prepared coordinates preserve precisely the defect that controls deletion. -/
theorem Separated.exists_prepared_coordinates_defect {A B : Finset Point}
    (hsep : Separated A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hP : GeneralPosition (A ∪ B)) :
    ∃ f : Point → Point, PreservesOrientationOn (A ∪ B) f ∧
      Set.InjOn f (A ∪ B : Finset Point) ∧ VerticallySeparatedOn A B f ∧
      GenericCoordinatesOn (A ∪ B) f ∧
      avoidanceDefect (A.image f) (B.image f) = avoidanceDefect A B := by
  obtain ⟨f, hfSigns, hfInj, hfVert, hfGeneric⟩ :=
    hsep.exists_prepared_coordinates hA hB hP
  exact ⟨f, hfSigns, hfInj, hfVert, hfGeneric,
    hfSigns.avoidanceDefect_image hfInj hP Finset.subset_union_left Finset.subset_union_right
      hsep.disjoint⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_CoordinatePreparation

section OriginalModule_LinearCrossingFamilies_DualEvents

/-!
## The finite dual event set

Events are nondegenerate unordered endpoint pairs. In generic coordinates, their
horizontal coordinates are distinct. An event has level `k` when exactly `k - 1`
lines lie strictly below its height at its horizontal coordinate. Its level lies
between 1 and `P.card - 1`.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

theorem dualAbscissa_comm (a b : Point) : dualAbscissa a b = dualAbscissa b a := by
  unfold dualAbscissa
  rw [← neg_sub a.2 b.2, ← neg_sub a.1 b.1, neg_div_neg_eq]

def eventAbscissa : Sym2 Point → ℝ :=
  Sym2.lift ⟨dualAbscissa, dualAbscissa_comm⟩

@[simp] theorem eventAbscissa_mk (a b : Point) :
    eventAbscissa s(a, b) = dualAbscissa a b := rfl

/-- The symmetric average agrees with both incident heights for genuine events. -/
def eventHeight : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun a b =>
    (dualValue a (dualAbscissa a b) + dualValue b (dualAbscissa a b)) / 2,
    fun a b => by dsimp only; rw [dualAbscissa_comm a b, add_comm]⟩

theorem eventHeight_mk {a b : Point} (hab : a.1 ≠ b.1) :
    eventHeight s(a, b) = dualValue a (dualAbscissa a b) := by
  change (dualValue a (dualAbscissa a b) + dualValue b (dualAbscissa a b)) / 2 = _
  rw [← dualValue_dualAbscissa hab]
  ring

def spannedPairs (P : Finset Point) : Finset (Sym2 Point) := by
  classical
  exact P.sym2.filter Nondegenerate

@[simp] theorem mem_spannedPairs {P : Finset Point} {e : Sym2 Point} :
    e ∈ spannedPairs P ↔ SpannedBy P e ∧ Nondegenerate e := by
  simp only [spannedPairs, Finset.mem_filter, Finset.mem_sym2_iff, SpannedBy]

/-- In a generic configuration, distinct unordered events have distinct horizontal coordinates. -/
theorem GenericCoordinatesOn.eventAbscissa_injOn {P : Finset Point}
    (h : GenericCoordinatesOn P id) :
    Set.InjOn eventAbscissa (spannedPairs P : Set (Sym2 Point)) := by
  intro e he g hg heq
  induction e using Sym2.inductionOn with | _ a b =>
  induction g using Sym2.inductionOn with | _ c d =>
  obtain ⟨heP, heNon⟩ := mem_spannedPairs.mp he
  obtain ⟨hgP, hgNon⟩ := mem_spannedPairs.mp hg
  obtain ⟨ha, hb⟩ := (spannedBy_mk_iff P a b).mp heP
  obtain ⟨hc, hd⟩ := (spannedBy_mk_iff P c d).mp hgP
  by_contra hne
  exact h.2 a ha b hb c hc d hd ((nondegenerate_mk_iff a b).mp heNon)
    ((nondegenerate_mk_iff c d).mp hgNon) hne heq

/-- Each endpoint's dual line passes through its event. -/
theorem dualValue_event_of_mem {P : Finset Point} (h : GenericCoordinatesOn P id)
    {e : Sym2 Point} (he : e ∈ spannedPairs P) {p : Point} (hp : p ∈ e) :
    dualValue p (eventAbscissa e) = eventHeight e := by
  induction e using Sym2.inductionOn with | _ a b =>
  obtain ⟨heP, heNon⟩ := mem_spannedPairs.mp he
  obtain ⟨ha, hb⟩ := (spannedBy_mk_iff P a b).mp heP
  have hab : a.1 ≠ b.1 := h.1 a ha b hb ((nondegenerate_mk_iff a b).mp heNon)
  rw [eventAbscissa_mk, eventHeight_mk hab]
  rcases Sym2.mem_iff.mp hp with rfl | rfl
  · rfl
  · exact (dualValue_dualAbscissa hab).symm

/-- General position excludes a third line through a dual event. -/
theorem dualValue_event_ne_of_not_mem {P : Finset Point}
    (h : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {e : Sym2 Point} (he : e ∈ spannedPairs P) {p : Point} (hp : p ∈ P) (hpe : p ∉ e) :
    dualValue p (eventAbscissa e) ≠ eventHeight e := by
  induction e using Sym2.inductionOn with | _ a b =>
  obtain ⟨heP, heNon⟩ := mem_spannedPairs.mp he
  obtain ⟨ha, hb⟩ := (spannedBy_mk_iff P a b).mp heP
  have hab := (nondegenerate_mk_iff a b).mp heNon
  have hap : a ≠ p := by rintro rfl; exact hpe (Sym2.mem_mk_left _ _)
  have hbp : b ≠ p := by rintro rfl; exact hpe (Sym2.mem_mk_right _ _)
  intro heq
  have ho := orientation_eq_dual a b p
    (dualValue_event_of_mem h he (Sym2.mem_mk_left a b))
    (dualValue_event_of_mem h he (Sym2.mem_mk_right a b))
  rw [heq, sub_self, mul_zero] at ho
  exact hP ha hb hp hab hap hbp ho

/-- The height difference has exactly one zero and changes sign there. -/
theorem dualValue_sub_eq {a b : Point} (hab : a.1 ≠ b.1) (x : ℝ) :
    dualValue a x - dualValue b x = (a.1 - b.1) * (x - dualAbscissa a b) := by
  calc
    _ = (a.1 - b.1) * (x - dualAbscissa a b) +
        (dualValue a (dualAbscissa a b) - dualValue b (dualAbscissa a b)) := by
      dsimp [dualValue]
      ring
    _ = _ := by rw [dualValue_dualAbscissa hab, sub_self, add_zero]

/-- In increasing x, the lower-slope line passes from above to below its partner. -/
theorem dualValue_lt_iff_abscissa_lt {a b : Point} (hab : a.1 < b.1) (x : ℝ) :
    dualValue a x < dualValue b x ↔ dualAbscissa a b < x := by
  rw [← sub_neg, dualValue_sub_eq hab.ne]
  have hneg : a.1 - b.1 < 0 := sub_neg.mpr hab
  simp [mul_neg_iff, hneg, not_lt_of_ge hneg.le, sub_pos]

def linesBelow (P : Finset Point) (e : Sym2 Point) : Finset Point :=
  P.filter (fun p => dualValue p (eventAbscissa e) < eventHeight e)

def eventLevel (P : Finset Point) (e : Sym2 Point) : ℕ := (linesBelow P e).card + 1

theorem one_le_eventLevel (P : Finset Point) (e : Sym2 Point) : 1 ≤ eventLevel P e := by
  unfold eventLevel
  omega

/-- The two incident lines do not count as lines strictly below an event. -/
theorem eventLevel_le_card_sub_one {P : Finset Point} (h : GenericCoordinatesOn P id)
    {e : Sym2 Point} (he : e ∈ spannedPairs P) : eventLevel P e ≤ P.card - 1 := by
  induction e using Sym2.inductionOn with | _ a b =>
  obtain ⟨heP, heNon⟩ := mem_spannedPairs.mp he
  obtain ⟨ha, hb⟩ := (spannedBy_mk_iff P a b).mp heP
  have hab := (nondegenerate_mk_iff a b).mp heNon
  have hbelow : linesBelow P s(a, b) ⊆ (P.erase a).erase b := by
    intro p hp
    obtain ⟨hpP, hpBelow⟩ := Finset.mem_filter.mp hp
    have hpa : p ≠ a := by
      intro hpa
      subst p
      rw [dualValue_event_of_mem h he (Sym2.mem_mk_left a b)] at hpBelow
      exact (lt_irrefl _) hpBelow
    have hpb : p ≠ b := by
      intro hpb
      subst p
      rw [dualValue_event_of_mem h he (Sym2.mem_mk_right a b)] at hpBelow
      exact (lt_irrefl _) hpBelow
    exact Finset.mem_erase.mpr ⟨hpb, Finset.mem_erase.mpr ⟨hpa, hpP⟩⟩
  have hcard := Finset.card_le_card hbelow
  have hba : b ∈ P.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hca := Finset.card_erase_add_one ha
  have hcb := Finset.card_erase_add_one hba
  unfold eventLevel
  omega

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualEvents

section OriginalModule_LinearCrossingFamilies_DualDefects

/-!
## Avoidance defects as dual events

The geometric dual bracket predicate agrees exactly with the paper's supporting
line/convex-hull defect. Grouping these finite events by their levels therefore
counts each avoidance defect once.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- Lines from `B` pass strictly below and strictly above the event. -/
def DualDefective (B : Finset Point) (e : Sym2 Point) : Prop :=
  (∃ p ∈ B, dualValue p (eventAbscissa e) < eventHeight e) ∧
    (∃ p ∈ B, eventHeight e < dualValue p (eventAbscissa e))

private theorem both_sides_mul_iff (B : Finset Point) (g : Point → ℝ)
    {c : ℝ} (hc : c ≠ 0) :
    ((∃ p ∈ B, c * g p < 0) ∧ (∃ p ∈ B, 0 < c * g p)) ↔
      ((∃ p ∈ B, g p < 0) ∧ (∃ p ∈ B, 0 < g p)) := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · simp [mul_neg_iff, mul_pos_iff, hc, not_lt_of_ge hc.le, and_comm]
  · simp [mul_neg_iff, hc, not_lt_of_ge hc.le]

/-- The supporting-line defect and the dual bracket condition are equivalent. -/
theorem lineMeetsConvexHull_iff_dualDefective {P A B : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B)
    {e : Sym2 Point} (he : e ∈ spannedPairs A) :
    LineMeetsConvexHull e B ↔ DualDefective B e := by
  induction e using Sym2.inductionOn with | _ a b =>
  obtain ⟨heA, heNon⟩ := mem_spannedPairs.mp he
  obtain ⟨ha, hb⟩ := (spannedBy_mk_iff A a b).mp heA
  have hab := (nondegenerate_mk_iff a b).mp heNon
  have habx : a.1 ≠ b.1 := hgen.1 a (hAP ha) b (hAP hb) hab
  have heP : s(a, b) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P a b).mpr ⟨hAP ha, hAP hb⟩, heNon⟩
  have haeq := dualValue_event_of_mem hgen heP (Sym2.mem_mk_left a b)
  have hbeq := dualValue_event_of_mem hgen heP (Sym2.mem_mk_right a b)
  have hB : ∀ p ∈ B, orientation a b p ≠ 0 :=
    fun p hp => hP.orientation_ne_zero_of_disjoint hAP hBP hAB ha hb hp hab
  rw [lineMeetsConvexHull_iff_opposite_sides hB]
  simp_rw [orientation_eq_dual a b _ haeq hbeq]
  rw [both_sides_mul_iff B _ (neg_ne_zero.mpr (sub_ne_zero.mpr habx.symm))]
  simp only [DualDefective, sub_neg, sub_pos]

def defectiveEvents (A B : Finset Point) : Finset (Sym2 Point) := by
  classical
  exact (spannedPairs A).filter (DualDefective B)

/-- The finite dual events represent exactly the unordered pairs in the defect. -/
theorem coe_defectiveEvents {P A B : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B) :
    (defectiveEvents A B : Set (Sym2 Point)) = defectivePairs A B := by
  ext e
  simp only [defectiveEvents, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨he, hdual⟩
    obtain ⟨heA, heNon⟩ := mem_spannedPairs.mp he
    exact ⟨heA, heNon,
      (lineMeetsConvexHull_iff_dualDefective hgen hP hAP hBP hAB he).mpr hdual⟩
  · intro he
    have heA : e ∈ spannedPairs A := mem_spannedPairs.mpr ⟨he.1, he.2.1⟩
    exact ⟨heA, (lineMeetsConvexHull_iff_dualDefective hgen hP hAP hBP hAB heA).mp he.2.2⟩

theorem card_defectiveEvents {P A B : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B) :
    (defectiveEvents A B).card = (defectivePairs A B).ncard := by
  rw [← coe_defectiveEvents hgen hP hAP hBP hAB, Set.ncard_coe_finset]

/-- Defective events of one color at level `k` in the full arrangement `P`. -/
def defectiveEventsAtLevel (P A B : Finset Point) (k : ℕ) : Finset (Sym2 Point) :=
  (defectiveEvents A B).filter (fun e => eventLevel P e = k)

/-- Partitioning one color's defects by level counts every defect exactly once. -/
theorem sum_card_defectiveEventsAtLevel {P A B : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hAP : A ⊆ P) :
    ∑ k ∈ Finset.Icc 1 (P.card - 1), (defectiveEventsAtLevel P A B k).card =
      (defectiveEvents A B).card := by
  classical
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro e he
  have heA : e ∈ spannedPairs A := (Finset.mem_filter.mp he).1
  obtain ⟨heSpan, heNon⟩ := mem_spannedPairs.mp heA
  have heP : e ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨fun p hp => hAP (heSpan p hp), heNon⟩
  exact Finset.mem_Icc.mpr ⟨one_le_eventLevel P e, eventLevel_le_card_sub_one hgen heP⟩

/-- The sum of the red and blue defect counts at a single level. -/
def levelDefect (P A B : Finset Point) (k : ℕ) : ℕ :=
  (defectiveEventsAtLevel P A B k).card + (defectiveEventsAtLevel P B A k).card

/-- The paper's identity `∑ₖ Tₖ = t(A,B)`, with no extra multiplicity factor. -/
theorem sum_levelDefect {P A B : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAB : Disjoint A B) :
    ∑ k ∈ Finset.Icc 1 (P.card - 1), levelDefect P A B k = avoidanceDefect A B := by
  simp only [levelDefect, Finset.sum_add_distrib,
    sum_card_defectiveEventsAtLevel hgen hAP, sum_card_defectiveEventsAtLevel hgen hBP,
    card_defectiveEvents hgen hP hAP hBP hAB,
    card_defectiveEvents hgen hP hBP hAP hAB.symm, avoidanceDefect]

/-- The exact level range `1,...,2m-1` for the equal-sized separated sets in the paper. -/
theorem sum_levelDefect_eq_size {A B : Finset Point} {m : ℕ}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hsep : Separated A B) (hA : A.card = m) (hB : B.card = m) :
    ∑ k ∈ Finset.Icc 1 (2 * m - 1), levelDefect (A ∪ B) A B k = avoidanceDefect A B := by
  have hcard : (A ∪ B).card = 2 * m := by
    rw [Finset.card_union_of_disjoint hsep.disjoint, hA, hB]
    omega
  simpa only [hcard] using sum_levelDefect hgen hP
    Finset.subset_union_left Finset.subset_union_right hsep.disjoint

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualDefects

section OriginalModule_LinearCrossingFamilies_DualSweep

/-!
## Local changes in the dual sweep

`rankBelow P p x` counts lines strictly below the line labelled by `p` at `x`.
Away from ties it is the zero-based vertical rank. At a simple event the incident
lines exchange two adjacent ranks, while other comparisons persist locally.
-/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

def belowAt (P : Finset Point) (p : Point) (x : ℝ) : Finset Point :=
  P.filter (fun q => dualValue q x < dualValue p x)

def rankBelow (P : Finset Point) (p : Point) (x : ℝ) : ℕ := (belowAt P p x).card

/-- Membership in the bottom `k` lines, defined using strict ranks. -/
def InLowest (P : Finset Point) (k : ℕ) (p : Point) (x : ℝ) : Prop :=
  p ∈ P ∧ rankBelow P p x < k

theorem continuous_dualValue (p : Point) : Continuous (dualValue p) := by
  unfold dualValue
  fun_prop

/-- A strict height comparison is unchanged in a neighborhood where the lines do not meet. -/
theorem eventually_dualValue_lt_iff {p q : Point} {s : ℝ}
    (h : dualValue p s ≠ dualValue q s) :
    ∀ᶠ x in 𝓝 s, (dualValue p x < dualValue q x ↔ dualValue p s < dualValue q s) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hevent := (isOpen_lt (continuous_dualValue p) (continuous_dualValue q)).mem_nhds hlt
    filter_upwards [hevent] with x hx
    exact iff_of_true hx hlt
  · have hevent := (isOpen_lt (continuous_dualValue q) (continuous_dualValue p)).mem_nhds hgt
    filter_upwards [hevent] with x hx
    exact iff_of_false hx.not_gt hgt.not_gt

/-- Before their intersection, the higher-slope line is below the lower-slope line. -/
theorem dualValue_rev_lt_iff_lt_abscissa {a b : Point} (hab : a.1 < b.1) (x : ℝ) :
    dualValue b x < dualValue a x ↔ x < dualAbscissa a b := by
  rw [← sub_neg, dualValue_sub_eq hab.ne.symm, dualAbscissa_comm b a]
  have hpos : 0 < b.1 - a.1 := sub_pos.mpr hab
  simp [mul_neg_iff, hpos, not_lt_of_ge hpos.le, sub_neg]

/-- Every nonincident line has the same comparison with either incident line near
the event as it has with the event height itself. -/
theorem eventually_nonincident_comparisons {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {a b : Point} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    ∀ᶠ x in 𝓝 (eventAbscissa s(a, b)), ∀ p ∈ P, p ≠ a → p ≠ b →
      (dualValue p x < dualValue a x ↔ dualValue p (eventAbscissa s(a, b)) < eventHeight s(a, b)) ∧
      (dualValue p x < dualValue b x ↔ dualValue p (eventAbscissa s(a, b)) < eventHeight s(a, b)) := by
  have he : s(a, b) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P a b).mpr ⟨ha, hb⟩, (nondegenerate_mk_iff a b).mpr hab⟩
  have hae := dualValue_event_of_mem hgen he (Sym2.mem_mk_left a b)
  have hbe := dualValue_event_of_mem hgen he (Sym2.mem_mk_right a b)
  rw [Filter.eventually_all_finset]
  intro p hp
  by_cases hpa : p = a
  · exact Filter.Eventually.of_forall (fun _ hn => (hn hpa).elim)
  by_cases hpb : p = b
  · exact Filter.Eventually.of_forall (fun _ _ hn => (hn hpb).elim)
  have hpe : p ∉ s(a, b) := by simpa only [Sym2.mem_iff, not_or] using And.intro hpa hpb
  have hne := dualValue_event_ne_of_not_mem hgen hP he hp hpe
  have hnea : dualValue p (eventAbscissa s(a, b)) ≠ dualValue a (eventAbscissa s(a, b)) := by
    rwa [hae]
  have hneb : dualValue p (eventAbscissa s(a, b)) ≠ dualValue b (eventAbscissa s(a, b)) := by
    rwa [hbe]
  filter_upwards [eventually_dualValue_lt_iff hnea, eventually_dualValue_lt_iff hneb] with x hxa hxb
  intro _ _
  simpa only [hae, hbe] using And.intro hxa hxb

private theorem belowAt_eq_if_partner {P : Finset Point} {a b : Point}
    {e : Sym2 Point} {x : ℝ} (hb : b ∈ P) (hab : a ≠ b)
    (hae : dualValue a (eventAbscissa e) = eventHeight e)
    (hbe : dualValue b (eventAbscissa e) = eventHeight e)
    (hother : ∀ p ∈ P, p ≠ a → p ≠ b →
      (dualValue p x < dualValue a x ↔ dualValue p (eventAbscissa e) < eventHeight e)) :
    belowAt P a x = if dualValue b x < dualValue a x then insert b (linesBelow P e)
      else linesBelow P e := by
  ext p
  by_cases hpa : p = a
  · subst p
    by_cases hba : dualValue b x < dualValue a x <;>
      simp [belowAt, linesBelow, hae, hab, hba]
  by_cases hpb : p = b
  · subst p
    by_cases hba : dualValue b x < dualValue a x <;>
      simp [belowAt, linesBelow, hbe, hb, hba]
  by_cases hp : p ∈ P
  · by_cases hba : dualValue b x < dualValue a x <;>
      simp [belowAt, linesBelow, hp, hpb, hba, hother p hp hpa hpb]
  · by_cases hba : dualValue b x < dualValue a x <;>
      simp [belowAt, linesBelow, hp, hpb, hba]

/-- Near an event, the lower-slope line loses exactly its partner from the set
of lines below it, and the higher-slope line gains exactly its partner. -/
theorem eventually_belowAt_event {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {a b : Point} (ha : a ∈ P) (hb : b ∈ P) (hab : a.1 < b.1) :
    ∀ᶠ x in 𝓝 (eventAbscissa s(a, b)),
      (x < eventAbscissa s(a, b) →
        belowAt P a x = insert b (linesBelow P s(a, b)) ∧
        belowAt P b x = linesBelow P s(a, b)) ∧
      (eventAbscissa s(a, b) < x →
        belowAt P a x = linesBelow P s(a, b) ∧
        belowAt P b x = insert a (linesBelow P s(a, b))) := by
  have hne : a ≠ b := fun heq => hab.ne (congrArg Prod.fst heq)
  have he : s(a, b) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P a b).mpr ⟨ha, hb⟩, (nondegenerate_mk_iff a b).mpr hne⟩
  have hae := dualValue_event_of_mem hgen he (Sym2.mem_mk_left a b)
  have hbe := dualValue_event_of_mem hgen he (Sym2.mem_mk_right a b)
  filter_upwards [eventually_nonincident_comparisons hgen hP ha hb hne] with x hx
  have hxa := belowAt_eq_if_partner hb hne hae hbe (fun p hp hpa hpb => (hx p hp hpa hpb).1)
  have hxb := belowAt_eq_if_partner ha hne.symm hbe hae
    (fun p hp hpb hpa => (hx p hp hpa hpb).2)
  constructor
  · intro hxs
    have hba := (dualValue_rev_lt_iff_lt_abscissa hab x).mpr hxs
    exact ⟨by simpa only [ite_eq_left hba] using hxa,
      by simpa only [ite_eq_right hba.not_gt] using hxb⟩
  · intro hsx
    have hab' := (dualValue_lt_iff_abscissa_lt hab x).mpr hsx
    exact ⟨by simpa only [ite_eq_right hab'.not_gt] using hxa,
      by simpa only [ite_eq_left hab'] using hxb⟩

/-- The exact two adjacent ranks on either side of an event. -/
theorem eventually_rankBelow_event {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {a b : Point} (ha : a ∈ P) (hb : b ∈ P) (hab : a.1 < b.1) :
    ∀ᶠ x in 𝓝 (eventAbscissa s(a, b)),
      (x < eventAbscissa s(a, b) →
        rankBelow P a x = eventLevel P s(a, b) ∧
        rankBelow P b x + 1 = eventLevel P s(a, b)) ∧
      (eventAbscissa s(a, b) < x →
        rankBelow P a x + 1 = eventLevel P s(a, b) ∧
        rankBelow P b x = eventLevel P s(a, b)) := by
  have hne : a ≠ b := fun heq => hab.ne (congrArg Prod.fst heq)
  have he : s(a, b) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P a b).mpr ⟨ha, hb⟩, (nondegenerate_mk_iff a b).mpr hne⟩
  have hae := dualValue_event_of_mem hgen he (Sym2.mem_mk_left a b)
  have hbe := dualValue_event_of_mem hgen he (Sym2.mem_mk_right a b)
  have hna : a ∉ linesBelow P s(a, b) := by
    simp only [linesBelow, Finset.mem_filter, hae, lt_self_iff_false, and_false, not_false_eq_true]
  have hnb : b ∉ linesBelow P s(a, b) := by
    simp only [linesBelow, Finset.mem_filter, hbe, lt_self_iff_false, and_false, not_false_eq_true]
  filter_upwards [eventually_belowAt_event hgen hP ha hb hab] with x hx
  constructor
  · intro hxs
    obtain ⟨hxa, hxb⟩ := hx.1 hxs
    simp only [rankBelow, eventLevel, hxa, hxb, Finset.card_insert_of_notMem hnb,
      and_self]
  · intro hsx
    obtain ⟨hxa, hxb⟩ := hx.2 hsx
    simp only [rankBelow, eventLevel, hxa, hxb, Finset.card_insert_of_notMem hna,
      and_self]

/-- For any cut `k`, the two incident lines exchange membership precisely when
`k` is the event level. Before the event the higher-slope line is the lower one. -/
theorem eventually_inLowest_event {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {a b : Point} (ha : a ∈ P) (hb : b ∈ P) (hab : a.1 < b.1) (k : ℕ) :
    ∀ᶠ x in 𝓝 (eventAbscissa s(a, b)),
      (x < eventAbscissa s(a, b) →
        (InLowest P k a x ↔ eventLevel P s(a, b) < k) ∧
        (InLowest P k b x ↔ eventLevel P s(a, b) ≤ k)) ∧
      (eventAbscissa s(a, b) < x →
        (InLowest P k a x ↔ eventLevel P s(a, b) ≤ k) ∧
        (InLowest P k b x ↔ eventLevel P s(a, b) < k)) := by
  filter_upwards [eventually_rankBelow_event hgen hP ha hb hab] with x hx
  constructor
  · intro hxs
    obtain ⟨hxa, hxb⟩ := hx.1 hxs
    simp only [InLowest, ha, hb, true_and]
    omega
  · intro hsx
    obtain ⟨hxa, hxb⟩ := hx.2 hsx
    simp only [InLowest, ha, hb, true_and]
    omega

/-- At a bichromatic level-`k` event, red enters and blue leaves the bottom `k`. -/
theorem eventually_red_enters_blue_leaves {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {a b : Point} (ha : a ∈ A) (hb : b ∈ B) :
    ∀ᶠ x in 𝓝 (eventAbscissa s(a, b)),
      (x < eventAbscissa s(a, b) →
        ¬InLowest (A ∪ B) (eventLevel (A ∪ B) s(a, b)) a x ∧
        InLowest (A ∪ B) (eventLevel (A ∪ B) s(a, b)) b x) ∧
      (eventAbscissa s(a, b) < x →
        InLowest (A ∪ B) (eventLevel (A ∪ B) s(a, b)) a x ∧
        ¬InLowest (A ∪ B) (eventLevel (A ∪ B) s(a, b)) b x) := by
  have hab : a.1 < b.1 := (hvert.1 a ha).trans (hvert.2 b hb)
  filter_upwards [eventually_inLowest_event hgen hP
    (Finset.mem_union_left _ ha) (Finset.mem_union_right _ hb) hab
    (eventLevel (A ∪ B) s(a, b))] with x hx
  constructor
  · intro hxs
    have h := hx.1 hxs
    exact ⟨fun hh => (lt_irrefl _) (h.1.mp hh), h.2.mpr le_rfl⟩
  · intro hsx
    have h := hx.2 hsx
    exact ⟨h.1.mpr le_rfl, fun hh => (lt_irrefl _) (h.2.mp hh)⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualSweep

section OriginalModule_LinearCrossingFamilies_DualSweepConstancy

/-! ## Constancy of ranks away from incident events -/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

theorem dualValue_eq_iff_abscissa_eq {a b : Point} (hab : a.1 ≠ b.1) (x : ℝ) :
    dualValue a x = dualValue b x ↔ x = dualAbscissa a b := by
  rw [← sub_eq_zero, dualValue_sub_eq hab, mul_eq_zero]
  simp only [sub_ne_zero.mpr hab, false_or, sub_eq_zero]

/-- A horizontal coordinate is regular when no two spanned dual lines intersect there. -/
def RegularAbscissa (P : Finset Point) (x : ℝ) : Prop :=
  ∀ e ∈ spannedPairs P, eventAbscissa e ≠ x

/-- A line's rank is locally constant near a horizontal coordinate at which it has no event. -/
theorem eventually_rankBelow_eq_of_no_incident_event {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {p : Point} (hp : p ∈ P) {s : ℝ}
    (hs : ∀ q ∈ P, q ≠ p → eventAbscissa s(q, p) ≠ s) :
    ∀ᶠ x in 𝓝 s, rankBelow P p x = rankBelow P p s := by
  have hcomp : ∀ᶠ x in 𝓝 s, ∀ q ∈ P,
      (dualValue q x < dualValue p x ↔ dualValue q s < dualValue p s) := by
    rw [Filter.eventually_all_finset]
    intro q hq
    by_cases hqp : q = p
    · subst q
      exact Filter.Eventually.of_forall (fun _ => by simp)
    have hslope : q.1 ≠ p.1 := hgen.1 q hq p hp hqp
    apply eventually_dualValue_lt_iff
    intro heq
    exact hs q hq hqp ((dualValue_eq_iff_abscissa_eq hslope s).mp heq).symm
  filter_upwards [hcomp] with x hx
  unfold rankBelow
  congr 1
  ext q
  by_cases hq : q ∈ P
  · simp only [belowAt, Finset.mem_filter, hq, true_and, hx q hq]
  · simp only [belowAt, Finset.mem_filter, hq, false_and]

theorem eventually_rankBelow_eq_of_regular {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {p : Point} (hp : p ∈ P) {s : ℝ}
    (hs : RegularAbscissa P s) :
    ∀ᶠ x in 𝓝 s, rankBelow P p x = rankBelow P p s := by
  apply eventually_rankBelow_eq_of_no_incident_event hgen hp
  intro q hq hqp
  exact hs s(q, p) (mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P q p).mpr ⟨hq, hp⟩, (nondegenerate_mk_iff q p).mpr hqp⟩)

/-- Only the two incident lines can change rank at an event. -/
theorem eventually_rankBelow_eq_of_nonincident {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {e : Sym2 Point} (he : e ∈ spannedPairs P)
    {p : Point} (hp : p ∈ P) (hpe : p ∉ e) :
    ∀ᶠ x in 𝓝 (eventAbscissa e), rankBelow P p x = rankBelow P p (eventAbscissa e) := by
  apply eventually_rankBelow_eq_of_no_incident_event hgen hp
  intro q hq hqp hsame
  have hqpEvent : s(q, p) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P q p).mpr ⟨hq, hp⟩, (nondegenerate_mk_iff q p).mpr hqp⟩
  have heq : s(q, p) = e := hgen.eventAbscissa_injOn hqpEvent he hsame
  exact hpe (heq ▸ Sym2.mem_mk_right q p)

theorem eventually_inLowest_iff_of_nonincident {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {e : Sym2 Point} (he : e ∈ spannedPairs P)
    {p : Point} (hp : p ∈ P) (hpe : p ∉ e) (k : ℕ) :
    ∀ᶠ x in 𝓝 (eventAbscissa e),
      InLowest P k p x ↔ InLowest P k p (eventAbscissa e) := by
  filter_upwards [eventually_rankBelow_eq_of_nonincident hgen he hp hpe] with x hx
  simp only [InLowest, hx]

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualSweepConstancy

section OriginalModule_LinearCrossingFamilies_DualSweepIntermediate

/-!
## Intermediate exit events

Bottom-`k` membership is closed when ties are counted by strict rank. Continuous
induction then shows that losing membership requires an incident level-`k`
event with a lower-slope partner. This avoids choosing an enumeration of all
events while proving the same finite-sweep intermediate-event assertion.
-/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- Strictly lower lines at a horizontal coordinate remain lower in a neighborhood. -/
theorem eventually_rankBelow_le (P : Finset Point) (p : Point) (s : ℝ) :
    ∀ᶠ x in 𝓝 s, rankBelow P p s ≤ rankBelow P p x := by
  have hcomp : ∀ᶠ x in 𝓝 s, ∀ q ∈ belowAt P p s, dualValue q x < dualValue p x := by
    rw [Filter.eventually_all_finset]
    intro q hq
    exact (isOpen_lt (continuous_dualValue q) (continuous_dualValue p)).mem_nhds
      (Finset.mem_filter.mp hq).2
  filter_upwards [hcomp] with x hx
  apply Finset.card_le_card
  intro q hq
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1, hx q hq⟩

theorem isClosed_inLowest (P : Finset Point) (k : ℕ) (p : Point) :
    IsClosed {x | InLowest P k p x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro s hs
  filter_upwards [eventually_rankBelow_le P p s] with x hx
  intro hin
  exact hs ⟨hin.1, lt_of_le_of_lt hx hin.2⟩

/-- At an event, either incident line has rank one less than the event level. -/
theorem rankBelow_event_add_one {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {e : Sym2 Point} (he : e ∈ spannedPairs P)
    {p : Point} (hp : p ∈ e) :
    rankBelow P p (eventAbscissa e) + 1 = eventLevel P e := by
  have hheight := dualValue_event_of_mem hgen he hp
  simp only [rankBelow, belowAt, hheight, eventLevel, linesBelow]

theorem inLowest_event_iff {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {e : Sym2 Point} (he : e ∈ spannedPairs P)
    {p : Point} (hp : p ∈ e) (k : ℕ) :
    InLowest P k p (eventAbscissa e) ↔ eventLevel P e ≤ k := by
  have hpP : p ∈ P := (mem_spannedPairs.mp he).1 p hp
  have hrank := rankBelow_event_add_one hgen he hp
  simp only [InLowest, hpP, true_and]
  omega

/-- A level-`k` event at which `p` exits has a lower-slope partner. -/
def ExitEvent (P : Finset Point) (k : ℕ) (p : Point) (x : ℝ) : Prop :=
  ∃ q ∈ P, q.1 < p.1 ∧ eventAbscissa s(q, p) = x ∧ eventLevel P s(q, p) = k

/-- Membership persists immediately to the right unless this is an exit event. -/
theorem eventually_inLowest_right_of_not_exit {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {s : ℝ} (hin : InLowest P k p s)
    (hno : ¬ExitEvent P k p s) :
    ∀ᶠ x in 𝓝[>] s, InLowest P k p x := by
  classical
  by_cases hinc : ∃ q ∈ P, q ≠ p ∧ eventAbscissa s(q, p) = s
  · obtain ⟨q, hq, hqp, hqs⟩ := hinc
    have hslope : q.1 ≠ p.1 := hgen.1 q hq p hin.1 hqp
    have he : s(q, p) ∈ spannedPairs P := mem_spannedPairs.mpr
      ⟨(spannedBy_mk_iff P q p).mpr ⟨hq, hin.1⟩, (nondegenerate_mk_iff q p).mpr hqp⟩
    have hlevel : eventLevel P s(q, p) ≤ k :=
      (inLowest_event_iff hgen he (Sym2.mem_mk_right q p) k).mp (hqs.symm ▸ hin)
    rcases lt_or_gt_of_ne hslope with hlt | hgt
    · have hne : eventLevel P s(q, p) ≠ k := fun hk => hno ⟨q, hq, hlt, hqs, hk⟩
      have hstrict : eventLevel P s(q, p) < k := lt_of_le_of_ne hlevel hne
      have hevent := eventually_inLowest_event hgen hP hq hin.1 hlt k
      rw [hqs] at hevent
      filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxs
      exact (hx.2 hxs).2.mpr hstrict
    · have hswap : s(p, q) = s(q, p) := Sym2.eq_swap
      have hevent := eventually_inLowest_event hgen hP hin.1 hq hgt k
      rw [hswap, hqs] at hevent
      filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxs
      exact (hx.2 hxs).1.mpr hlevel
  · have hnone : ∀ q ∈ P, q ≠ p → eventAbscissa s(q, p) ≠ s := by
      intro q hq hqp heq
      exact hinc ⟨q, hq, hqp, heq⟩
    filter_upwards [(eventually_rankBelow_eq_of_no_incident_event hgen hin.1 hnone).filter_mono
      nhdsWithin_le_nhds] with x hx
    exact ⟨hin.1, hx ▸ hin.2⟩

/-- Losing bottom-`k` membership forces a level-`k` exit in the intervening sweep. -/
theorem exists_exitEvent_between {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {a b : ℝ} (hab : a ≤ b)
    (ha : InLowest P k p a) (hb : ¬InLowest P k p b) :
    ∃ s ∈ Ico a b, ExitEvent P k p s := by
  by_contra hno
  have hpersist : Icc a b ⊆ {x | InLowest P k p x} :=
    ((isClosed_inLowest P k p).inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin ha
      (by
        intro s hs
        exact eventually_inLowest_right_of_not_exit hgen hP hs.1
          (fun he => hno ⟨s, hs.2, he⟩))
  exact hb (hpersist ⟨hab, le_rfl⟩)

theorem exists_exitEvent_strictly_between {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {a b : ℝ} (hab : a ≤ b) (hareg : RegularAbscissa P a)
    (ha : InLowest P k p a) (hb : ¬InLowest P k p b) :
    ∃ s ∈ Ioo a b, ExitEvent P k p s := by
  obtain ⟨s, hs, q, hq, hqp, heq, hk⟩ := exists_exitEvent_between hgen hP hab ha hb
  have hne : q ≠ p := fun he => hqp.ne (congrArg Prod.fst he)
  have he : s(q, p) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P q p).mpr ⟨hq, ha.1⟩, (nondegenerate_mk_iff q p).mpr hne⟩
  have hsa : s ≠ a := by simpa only [heq] using hareg _ he
  exact ⟨s, ⟨lt_of_le_of_ne hs.1 hsa.symm, hs.2⟩, q, hq, hqp, heq, hk⟩

/-- An entrance event has a higher-slope partner. -/
def EntranceEvent (P : Finset Point) (k : ℕ) (p : Point) (x : ℝ) : Prop :=
  ∃ q ∈ P, p.1 < q.1 ∧ eventAbscissa s(p, q) = x ∧ eventLevel P s(p, q) = k

/-- Membership persists immediately to the left unless this is an entrance event. -/
theorem eventually_inLowest_left_of_not_entrance {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {s : ℝ} (hin : InLowest P k p s)
    (hno : ¬EntranceEvent P k p s) :
    ∀ᶠ x in 𝓝[<] s, InLowest P k p x := by
  classical
  by_cases hinc : ∃ q ∈ P, q ≠ p ∧ eventAbscissa s(q, p) = s
  · obtain ⟨q, hq, hqp, hqs⟩ := hinc
    have hslope : q.1 ≠ p.1 := hgen.1 q hq p hin.1 hqp
    have he : s(q, p) ∈ spannedPairs P := mem_spannedPairs.mpr
      ⟨(spannedBy_mk_iff P q p).mpr ⟨hq, hin.1⟩, (nondegenerate_mk_iff q p).mpr hqp⟩
    have hlevel : eventLevel P s(q, p) ≤ k :=
      (inLowest_event_iff hgen he (Sym2.mem_mk_right q p) k).mp (hqs.symm ▸ hin)
    rcases lt_or_gt_of_ne hslope with hlt | hgt
    · have hevent := eventually_inLowest_event hgen hP hq hin.1 hlt k
      rw [hqs] at hevent
      filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxs
      exact (hx.1 hxs).2.mpr hlevel
    · have hswap : s(p, q) = s(q, p) := Sym2.eq_swap
      have hne : eventLevel P s(q, p) ≠ k := by
        intro hk
        exact hno ⟨q, hq, hgt, hswap ▸ hqs, hswap ▸ hk⟩
      have hstrict : eventLevel P s(q, p) < k := lt_of_le_of_ne hlevel hne
      have hevent := eventually_inLowest_event hgen hP hin.1 hq hgt k
      rw [hswap, hqs] at hevent
      filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxs
      exact (hx.1 hxs).1.mpr hstrict
  · have hnone : ∀ q ∈ P, q ≠ p → eventAbscissa s(q, p) ≠ s := by
      intro q hq hqp heq
      exact hinc ⟨q, hq, hqp, heq⟩
    filter_upwards [(eventually_rankBelow_eq_of_no_incident_event hgen hin.1 hnone).filter_mono
      nhdsWithin_le_nhds] with x hx
    exact ⟨hin.1, hx ▸ hin.2⟩

/-- Gaining membership forces an entrance; the proof is continuous induction
in the reverse order, with no change to the geometric configuration. -/
theorem exists_entranceEvent_between {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {a b : ℝ} (hab : a ≤ b)
    (ha : ¬InLowest P k p a) (hb : InLowest P k p b) :
    ∃ s ∈ Ioc a b, EntranceEvent P k p s := by
  by_contra hno
  have hpersist : Icc a b ⊆ {x | InLowest P k p x} := by
    have hclosed : IsClosed ({x | InLowest P k p x} ∩
        Set.Icc (α := OrderDual ℝ) b a) := by
      have heq : Set.Icc (α := OrderDual ℝ) b a = Set.Icc a b := by
        ext x
        exact and_comm
      rw [heq]
      exact (isClosed_inLowest P k p).inter isClosed_Icc
    have h := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (α := OrderDual ℝ)
      (a := b) (b := a) (s := {x | InLowest P k p x}) hclosed hb (by
      intro s hs
      apply eventually_inLowest_left_of_not_entrance hgen hP hs.1
      intro he
      exact hno ⟨s, ⟨hs.2.2, hs.2.1⟩, he⟩)
    exact fun x hx => h ⟨hx.2, hx.1⟩
  exact ha (hpersist ⟨le_rfl, hab⟩)

theorem exists_entranceEvent_strictly_between {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {a b : ℝ} (hab : a ≤ b) (hbreg : RegularAbscissa P b)
    (ha : ¬InLowest P k p a) (hb : InLowest P k p b) :
    ∃ s ∈ Ioo a b, EntranceEvent P k p s := by
  obtain ⟨s, hs, q, hq, hpq, heq, hk⟩ := exists_entranceEvent_between hgen hP hab ha hb
  have hne : p ≠ q := fun he => hpq.ne (congrArg Prod.fst he)
  have he : s(p, q) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P p q).mpr ⟨hb.1, hq⟩, (nondegenerate_mk_iff p q).mpr hne⟩
  have hsb : s ≠ b := by simpa only [heq] using hbreg _ he
  exact ⟨s, ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩, q, hq, hpq, heq, hk⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualSweepIntermediate

section OriginalModule_LinearCrossingFamilies_DualRepeatedEvents

/-! ## Intermediate events between repeated entrances or exits -/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- Simplicity of the sweep forbids simultaneous entrance and exit of a line. -/
theorem not_exitEvent_of_entranceEvent {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {p : Point} (hp : p ∈ P)
    {k : ℕ} {x : ℝ} (hin : EntranceEvent P k p x) : ¬ExitEvent P k p x := by
  obtain ⟨r, hr, hpr, hrx, _⟩ := hin
  rintro ⟨q, hq, hqp, hqx, _⟩
  have hprne : p ≠ r := fun he => hpr.ne (congrArg Prod.fst he)
  have hqpne : q ≠ p := fun he => hqp.ne (congrArg Prod.fst he)
  have he₁ : s(p, r) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P p r).mpr ⟨hp, hr⟩, (nondegenerate_mk_iff p r).mpr hprne⟩
  have he₂ : s(q, p) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P q p).mpr ⟨hq, hp⟩, (nondegenerate_mk_iff q p).mpr hqpne⟩
  have heq := hgen.eventAbscissa_injOn he₂ he₁ (hqx.trans hrx.symm)
  have hmem : q ∈ s(p, r) := heq ▸ Sym2.mem_mk_left q p
  rcases Sym2.mem_iff.mp hmem with hqeq | hqeq
  · exact hqpne hqeq
  · subst q
    exact (hpr.trans hqp).false

/-- Any two same-level entrances of a line bracket a same-level exit. -/
theorem exists_exit_between_entrances {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} (hp : p ∈ P) {k : ℕ} {s t : ℝ} (hst : s < t)
    (hs : EntranceEvent P k p s) (ht : EntranceEvent P k p t) :
    ∃ x ∈ Ioo s t, ExitEvent P k p x := by
  have hno := not_exitEvent_of_entranceEvent hgen hp hs
  obtain ⟨q, hq, hpq, hqs, hqk⟩ := hs
  obtain ⟨r, hr, hpr, hrt, hrk⟩ := ht
  have hpqne : p ≠ q := fun he => hpq.ne (congrArg Prod.fst he)
  have he : s(p, q) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P p q).mpr ⟨hp, hq⟩, (nondegenerate_mk_iff p q).mpr hpqne⟩
  have hins : InLowest P k p s := by
    rw [← hqs, inLowest_event_iff hgen he (Sym2.mem_mk_left p q), hqk]
  have hevent := eventually_inLowest_event hgen hP hp hr hpr k
  rw [hrt, hrk] at hevent
  have hbefore : ∀ᶠ y in 𝓝[<] t, s < y ∧ y < t ∧ ¬InLowest P k p y := by
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (Ioi_mem_nhds hst), self_mem_nhdsWithin] with y hy hsy hyt
    exact ⟨hsy, hyt, fun h => (lt_irrefl k) ((hy.1 hyt).1.mp h)⟩
  obtain ⟨y, hsy, hyt, hy⟩ := hbefore.exists
  obtain ⟨x, hx, hexit⟩ := exists_exitEvent_between hgen hP hsy.le hins hy
  have hxs : x ≠ s := fun heq => hno (heq ▸ hexit)
  exact ⟨x, ⟨lt_of_le_of_ne hx.1 hxs.symm, hx.2.trans hyt⟩, hexit⟩

/-- Any two same-level exits of a line bracket a same-level entrance. -/
theorem exists_entrance_between_exits {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} (hp : p ∈ P) {k : ℕ} {s t : ℝ} (hst : s < t)
    (hs : ExitEvent P k p s) (ht : ExitEvent P k p t) :
    ∃ x ∈ Ioo s t, EntranceEvent P k p x := by
  have hno : ¬EntranceEvent P k p t := fun h => not_exitEvent_of_entranceEvent hgen hp h ht
  obtain ⟨q, hq, hqp, hqs, hqk⟩ := hs
  obtain ⟨r, hr, hrp, hrt, hrk⟩ := ht
  have hrpne : r ≠ p := fun he => hrp.ne (congrArg Prod.fst he)
  have he : s(r, p) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P r p).mpr ⟨hr, hp⟩, (nondegenerate_mk_iff r p).mpr hrpne⟩
  have hint : InLowest P k p t := by
    rw [← hrt, inLowest_event_iff hgen he (Sym2.mem_mk_right r p), hrk]
  have hevent := eventually_inLowest_event hgen hP hq hp hqp k
  rw [hqs, hqk] at hevent
  have hafter : ∀ᶠ y in 𝓝[>] s, s < y ∧ y < t ∧ ¬InLowest P k p y := by
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (Iio_mem_nhds hst), self_mem_nhdsWithin] with y hy hyt hsy
    exact ⟨hsy, hyt, fun h => (lt_irrefl k) ((hy.2 hsy).2.mp h)⟩
  obtain ⟨y, hsy, hyt, hy⟩ := hafter.exists
  obtain ⟨x, hx, hentry⟩ := exists_entranceEvent_between hgen hP hyt.le hy hint
  have hxt : x ≠ t := fun heq => hno (heq ▸ hentry)
  exact ⟨x, ⟨hsy.trans hx.1, lt_of_le_of_ne hx.2 hxt⟩, hentry⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualRepeatedEvents

section OriginalModule_LinearCrossingFamilies_DualRepeatedDefects

/-! ## Repeated bichromatic incidences force directional monochromatic defects -/

open Set

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- The two blue partners bracket a red exit between repeated bichromatic
entrances. No consecutiveness assumption is needed for the witness. -/
theorem exists_red_defective_exit_between {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {a b c : Point}
    (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ B) {k : ℕ}
    (hbk : eventLevel (A ∪ B) s(a, b) = k)
    (hck : eventLevel (A ∪ B) s(a, c) = k)
    (horder : eventAbscissa s(a, b) < eventAbscissa s(a, c)) :
    ∃ q ∈ A, q.1 < a.1 ∧ eventLevel (A ∪ B) s(q, a) = k ∧
      eventAbscissa s(q, a) ∈ Ioo (eventAbscissa s(a, b)) (eventAbscissa s(a, c)) ∧
      DualDefective B s(q, a) := by
  have hab : a.1 < b.1 := (hvert.1 a ha).trans (hvert.2 b hb)
  have hac : a.1 < c.1 := (hvert.1 a ha).trans (hvert.2 c hc)
  have haP := Finset.mem_union_left B ha
  have hbP := Finset.mem_union_right A hb
  have hcP := Finset.mem_union_right A hc
  obtain ⟨x, hx, q, hqP, hqa, hqx, hqk⟩ := exists_exit_between_entrances hgen hP haP horder
    ⟨b, hbP, hab, rfl, hbk⟩ ⟨c, hcP, hac, rfl, hck⟩
  have hq : q ∈ A := by
    rcases Finset.mem_union.mp hqP with hq | hq
    · exact hq
    · exact ((hvert.2 q hq).trans (hqa.trans (hvert.1 a ha))).false.elim
  have hne : q ≠ a := fun he => hqa.ne (congrArg Prod.fst he)
  have he : s(q, a) ∈ spannedPairs (A ∪ B) := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff _ q a).mpr ⟨hqP, haP⟩, (nondegenerate_mk_iff q a).mpr hne⟩
  have hheight := dualValue_event_of_mem hgen he (Sym2.mem_mk_right q a)
  have hbelow : dualValue c x < dualValue a x :=
    (dualValue_rev_lt_iff_lt_abscissa hac x).mpr hx.2
  have habove : dualValue a x < dualValue b x :=
    (dualValue_lt_iff_abscissa_lt hab x).mpr hx.1
  refine ⟨q, hq, hqa, hqk, hqx.symm ▸ hx, ?_⟩
  unfold DualDefective
  rw [← hheight]
  exact ⟨⟨c, hc, hqx.symm ▸ hbelow⟩, ⟨b, hb, hqx.symm ▸ habove⟩⟩

/-- The two red partners bracket a blue entrance between repeated bichromatic exits. -/
theorem exists_blue_defective_entrance_between {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {a c b : Point}
    (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) {k : ℕ}
    (hak : eventLevel (A ∪ B) s(a, b) = k)
    (hck : eventLevel (A ∪ B) s(c, b) = k)
    (horder : eventAbscissa s(a, b) < eventAbscissa s(c, b)) :
    ∃ q ∈ B, b.1 < q.1 ∧ eventLevel (A ∪ B) s(b, q) = k ∧
      eventAbscissa s(b, q) ∈ Ioo (eventAbscissa s(a, b)) (eventAbscissa s(c, b)) ∧
      DualDefective A s(b, q) := by
  have hab : a.1 < b.1 := (hvert.1 a ha).trans (hvert.2 b hb)
  have hcb : c.1 < b.1 := (hvert.1 c hc).trans (hvert.2 b hb)
  have haP := Finset.mem_union_left B ha
  have hcP := Finset.mem_union_left B hc
  have hbP := Finset.mem_union_right A hb
  obtain ⟨x, hx, q, hqP, hbq, hqx, hqk⟩ := exists_entrance_between_exits hgen hP hbP horder
    ⟨a, haP, hab, rfl, hak⟩ ⟨c, hcP, hcb, rfl, hck⟩
  have hq : q ∈ B := by
    rcases Finset.mem_union.mp hqP with hq | hq
    · exact ((hvert.2 b hb).trans (hbq.trans (hvert.1 q hq))).false.elim
    · exact hq
  have hne : b ≠ q := fun he => hbq.ne (congrArg Prod.fst he)
  have he : s(b, q) ∈ spannedPairs (A ∪ B) := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff _ b q).mpr ⟨hbP, hqP⟩, (nondegenerate_mk_iff b q).mpr hne⟩
  have hheight := dualValue_event_of_mem hgen he (Sym2.mem_mk_left b q)
  have hbelow : dualValue a x < dualValue b x :=
    (dualValue_lt_iff_abscissa_lt hab x).mpr hx.1
  have habove : dualValue b x < dualValue c x :=
    (dualValue_rev_lt_iff_lt_abscissa hcb x).mpr hx.2
  refine ⟨q, hq, hbq, hqk, hqx.symm ▸ hx, ?_⟩
  unfold DualDefective
  rw [← hheight]
  exact ⟨⟨a, ha, hqx.symm ▸ hbelow⟩, ⟨c, hc, hqx.symm ▸ habove⟩⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualRepeatedDefects

section OriginalModule_LinearCrossingFamilies_InterlacingCount

/-! ## Counting points separated by witnesses in a linear order -/

namespace LinearCrossingFamilies

/-- If every two distinct ordered points of `S` have a point of `T` strictly
between them, there are at most one more points in `S` than in `T`. -/
theorem card_le_card_add_one_of_between {α : Type*} [LinearOrder α]
    (S T : Finset α)
    (hbetween : ∀ a ∈ S, ∀ b ∈ S, a < b → ∃ t ∈ T, a < t ∧ t < b) :
    S.card ≤ T.card + 1 := by
  classical
  induction S using Finset.induction_on_max generalizing T with
  | empty => simp
  | insert a S hmax ih =>
    have ha : a ∉ S := fun h => (hmax a h).false
    rw [Finset.card_insert_of_notMem ha]
    rcases S.eq_empty_or_nonempty with hS | hS
    · simp [hS]
    obtain ⟨t, ht, hmt, hta⟩ := hbetween (S.max' hS)
      (Finset.mem_insert_of_mem (Finset.max'_mem S hS)) a (Finset.mem_insert_self a S)
      (hmax _ (Finset.max'_mem S hS))
    have hbound := ih (T.erase t) (by
      intro x hx y hy hxy
      obtain ⟨u, hu, hxu, huy⟩ := hbetween x (Finset.mem_insert_of_mem hx)
        y (Finset.mem_insert_of_mem hy) hxy
      have hut : u ≠ t := ne_of_lt (huy.trans_le (Finset.le_max' S y hy) |>.trans hmt)
      exact ⟨u, Finset.mem_erase.mpr ⟨hut, hu⟩, hxu, huy⟩)
    have hcard := Finset.card_erase_add_one ht
    omega

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_InterlacingCount

section OriginalModule_LinearCrossingFamilies_DualRepeatedCount

/-!
## The repeated-incidence bounds

For a fixed line, a partner uniquely specifies its incident event. The finite
sets below therefore count bichromatic incidences and directional defect marks
without choosing an orientation for arbitrary unordered events.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

def redPartnersAtLevel (A B : Finset Point) (k : ℕ) (a : Point) : Finset Point :=
  B.filter (fun b => eventLevel (A ∪ B) s(a, b) = k)

def bluePartnersAtLevel (A B : Finset Point) (k : ℕ) (b : Point) : Finset Point :=
  A.filter (fun a => eventLevel (A ∪ B) s(a, b) = k)

def redMarkPartners (A B : Finset Point) (k : ℕ) (a : Point) : Finset Point := by
  classical
  exact A.filter (fun q => q.1 < a.1 ∧ eventLevel (A ∪ B) s(q, a) = k ∧ DualDefective B s(q, a))

def blueMarkPartners (A B : Finset Point) (k : ℕ) (b : Point) : Finset Point := by
  classical
  exact B.filter (fun q => b.1 < q.1 ∧ eventLevel (A ∪ B) s(b, q) = k ∧ DualDefective A s(b, q))

theorem GenericCoordinatesOn.eventAbscissa_mk_left_injOn {P Q : Finset Point}
    (hgen : GenericCoordinatesOn P id) {p : Point} (hp : p ∈ P)
    (hQP : Q ⊆ P) (hne : ∀ q ∈ Q, p ≠ q) :
    Set.InjOn (fun q => eventAbscissa s(p, q)) (Q : Set Point) := by
  intro q hq r hr heq
  have hqE : s(p, q) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P p q).mpr ⟨hp, hQP hq⟩, (nondegenerate_mk_iff p q).mpr (hne q hq)⟩
  have hrE : s(p, r) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P p r).mpr ⟨hp, hQP hr⟩, (nondegenerate_mk_iff p r).mpr (hne r hr)⟩
  rcases Sym2.eq_iff.mp (hgen.eventAbscissa_injOn hqE hrE heq) with h | h
  · exact h.2
  · exact h.2.trans h.1

theorem GenericCoordinatesOn.eventAbscissa_mk_right_injOn {P Q : Finset Point}
    (hgen : GenericCoordinatesOn P id) {p : Point} (hp : p ∈ P)
    (hQP : Q ⊆ P) (hne : ∀ q ∈ Q, p ≠ q) :
    Set.InjOn (fun q => eventAbscissa s(q, p)) (Q : Set Point) := by
  intro q hq r hr heq
  apply hgen.eventAbscissa_mk_left_injOn hp hQP hne hq hr
  simpa only [eventAbscissa_mk, dualAbscissa_comm p] using heq

/-- The repeated-incidence bound for a red line: `d_k(a) ≤ 1 + u_k(a)`. -/
theorem red_repeated_incidence_bound {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {a : Point} (ha : a ∈ A) (k : ℕ) :
    (redPartnersAtLevel A B k a).card ≤ 1 + (redMarkPartners A B k a).card := by
  classical
  let S := redPartnersAtLevel A B k a
  let T := redMarkPartners A B k a
  let f := fun b => eventAbscissa s(a, b)
  let g := fun q => eventAbscissa s(q, a)
  have hf : Set.InjOn f (S : Set Point) := by
    apply hgen.eventAbscissa_mk_left_injOn (Finset.mem_union_left B ha)
    · exact fun q hq => Finset.mem_union_right A (Finset.mem_filter.mp hq).1
    · intro q hq heq
      have hqB : q ∈ B := (Finset.mem_filter.mp hq).1
      have hlt : a.1 < q.1 := (hvert.1 a ha).trans (hvert.2 q hqB)
      exact hlt.ne (congrArg Prod.fst heq)
  have hbound := card_le_card_add_one_of_between (S.image f) (T.image g) (by
    intro x hx y hy hxy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hbB, hbk⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcB, hck⟩ := Finset.mem_filter.mp hc
    obtain ⟨q, hq, hqa, hqk, hqx, hdef⟩ :=
      exists_red_defective_exit_between hgen hP hvert ha hbB hcB hbk hck hxy
    exact ⟨g q, Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hqa, hqk, hdef⟩, rfl⟩,
      hqx.1, hqx.2⟩)
  rw [Finset.card_image_of_injOn hf] at hbound
  have hT := Finset.card_image_le (s := T) (f := g)
  change S.card ≤ 1 + T.card
  omega

/-- The repeated-incidence bound for a blue line: `d_k(b) ≤ 1 + u_k(b)`. -/
theorem blue_repeated_incidence_bound {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {b : Point} (hb : b ∈ B) (k : ℕ) :
    (bluePartnersAtLevel A B k b).card ≤ 1 + (blueMarkPartners A B k b).card := by
  classical
  let S := bluePartnersAtLevel A B k b
  let T := blueMarkPartners A B k b
  let f := fun a => eventAbscissa s(a, b)
  let g := fun q => eventAbscissa s(b, q)
  have hf : Set.InjOn f (S : Set Point) := by
    apply hgen.eventAbscissa_mk_right_injOn (Finset.mem_union_right A hb)
    · exact fun q hq => Finset.mem_union_left B (Finset.mem_filter.mp hq).1
    · intro q hq heq
      have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
      have hlt : q.1 < b.1 := (hvert.1 q hqA).trans (hvert.2 b hb)
      exact hlt.ne (congrArg Prod.fst heq.symm)
  have hbound := card_le_card_add_one_of_between (S.image f) (T.image g) (by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨haA, hak⟩ := Finset.mem_filter.mp ha
    obtain ⟨hcA, hck⟩ := Finset.mem_filter.mp hc
    obtain ⟨q, hq, hbq, hqk, hqx, hdef⟩ :=
      exists_blue_defective_entrance_between hgen hP hvert haA hcA hb hak hck hxy
    exact ⟨g q, Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hbq, hqk, hdef⟩, rfl⟩,
      hqx.1, hqx.2⟩)
  rw [Finset.card_image_of_injOn hf] at hbound
  have hT := Finset.card_image_le (s := T) (f := g)
  change S.card ≤ 1 + T.card
  omega

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualRepeatedCount

section OriginalModule_LinearCrossingFamilies_DualDeletionCount

/-! ## The levelwise deletion count -/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- A red defect marks at most one red line: its higher-slope endpoint. -/
theorem sum_card_redMarkPartners_le (A B : Finset Point) (k : ℕ) :
    ∑ a ∈ A, (redMarkPartners A B k a).card ≤
      (defectiveEventsAtLevel (A ∪ B) A B k).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun z : Σ _ : Point, Point => s(z.2, z.1))
  · rintro ⟨a, q⟩ hz
    obtain ⟨ha, hq⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hqA, hqa, hk, hdef⟩ := Finset.mem_filter.mp hq
    have hne : q ≠ a := fun he => hqa.ne (congrArg Prod.fst he)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨mem_spannedPairs.mpr ⟨(spannedBy_mk_iff A q a).mpr ⟨hqA, ha⟩,
        (nondegenerate_mk_iff q a).mpr hne⟩, hdef⟩, hk⟩
  · rintro ⟨a, q⟩ hz ⟨b, r⟩ hw heq
    have hqa := (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).2.1
    have hrb := (Finset.mem_filter.mp (Finset.mem_sigma.mp hw).2).2.1
    rcases Sym2.eq_iff.mp heq with ⟨hqr, hab⟩ | ⟨hqb, har⟩
    · cases hqr
      cases hab
      rfl
    · cases hqb
      cases har
      exact (hqa.trans hrb).false.elim

/-- A blue defect marks at most one blue line: its lower-slope endpoint. -/
theorem sum_card_blueMarkPartners_le (A B : Finset Point) (k : ℕ) :
    ∑ b ∈ B, (blueMarkPartners A B k b).card ≤
      (defectiveEventsAtLevel (A ∪ B) B A k).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun z : Σ _ : Point, Point => s(z.1, z.2))
  · rintro ⟨b, q⟩ hz
    obtain ⟨hb, hq⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hqB, hbq, hk, hdef⟩ := Finset.mem_filter.mp hq
    have hne : b ≠ q := fun he => hbq.ne (congrArg Prod.fst he)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨mem_spannedPairs.mpr ⟨(spannedBy_mk_iff B b q).mpr ⟨hb, hqB⟩,
        (nondegenerate_mk_iff b q).mpr hne⟩, hdef⟩, hk⟩
  · rintro ⟨b, q⟩ hz ⟨c, r⟩ hw heq
    have hbq := (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).2.1
    have hcr := (Finset.mem_filter.mp (Finset.mem_sigma.mp hw).2).2.1
    rcases Sym2.eq_iff.mp heq with ⟨hbc, hqr⟩ | ⟨hbr, hqc⟩
    · cases hbc
      cases hqr
      rfl
    · cases hbr
      cases hqc
      exact (hbq.trans hcr).false.elim

private theorem sum_marked_bound {α : Type*} (S : Finset α) (d u : α → ℕ)
    (hdu : ∀ a ∈ S, d a ≤ 1 + u a) :
    ∑ a ∈ S.filter (fun a => 0 < u a), d a ≤ 2 * ∑ a ∈ S, u a := by
  classical
  calc
    _ ≤ ∑ a ∈ S.filter (fun a => 0 < u a), 2 * u a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨haS, hpos⟩ := Finset.mem_filter.mp ha
      have h := hdu a haS
      omega
    _ = 2 * ∑ a ∈ S.filter (fun a => 0 < u a), u a := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ a ∈ S, u a := Nat.mul_le_mul_left _
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))

def markedRedLines (A B : Finset Point) (k : ℕ) : Finset Point := by
  classical
  exact A.filter (fun a => (redMarkPartners A B k a).Nonempty)

def markedBlueLines (A B : Finset Point) (k : ℕ) : Finset Point := by
  classical
  exact B.filter (fun b => (blueMarkPartners A B k b).Nonempty)

theorem sum_marked_red_incidence_le {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) (k : ℕ) :
    ∑ a ∈ markedRedLines A B k, (redPartnersAtLevel A B k a).card ≤
      2 * (defectiveEventsAtLevel (A ∪ B) A B k).card := by
  have h := sum_marked_bound A (fun a => (redPartnersAtLevel A B k a).card)
    (fun a => (redMarkPartners A B k a).card)
    (fun a ha => red_repeated_incidence_bound hgen hP hvert ha k)
  simp only [Finset.card_pos] at h
  exact h.trans (Nat.mul_le_mul_left 2 (sum_card_redMarkPartners_le A B k))

theorem sum_marked_blue_incidence_le {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) (k : ℕ) :
    ∑ b ∈ markedBlueLines A B k, (bluePartnersAtLevel A B k b).card ≤
      2 * (defectiveEventsAtLevel (A ∪ B) B A k).card := by
  have h := sum_marked_bound B (fun b => (bluePartnersAtLevel A B k b).card)
    (fun b => (blueMarkPartners A B k b).card)
    (fun b hb => blue_repeated_incidence_bound hgen hP hvert hb k)
  simp only [Finset.card_pos] at h
  exact h.trans (Nat.mul_le_mul_left 2 (sum_card_blueMarkPartners_le A B k))

/-- Ordered red-blue pairs deleted because the red line is marked. -/
def redDeletedPairs (A B : Finset Point) (k : ℕ) : Finset (Point × Point) :=
  ((markedRedLines A B k).sigma (redPartnersAtLevel A B k)).image (fun z => (z.1, z.2))

/-- Ordered red-blue pairs deleted because the blue line is marked. -/
def blueDeletedPairs (A B : Finset Point) (k : ℕ) : Finset (Point × Point) :=
  ((markedBlueLines A B k).sigma (bluePartnersAtLevel A B k)).image (fun z => (z.2, z.1))

def deletedLevelPairs (A B : Finset Point) (k : ℕ) : Finset (Point × Point) :=
  redDeletedPairs A B k ∪ blueDeletedPairs A B k

/-- These are exactly the bichromatic level-`k` pairs with a marked incident line. -/
theorem mem_deletedLevelPairs {A B : Finset Point} {k : ℕ} {a b : Point} :
    (a, b) ∈ deletedLevelPairs A B k ↔
      a ∈ A ∧ b ∈ B ∧ eventLevel (A ∪ B) s(a, b) = k ∧
        ((redMarkPartners A B k a).Nonempty ∨ (blueMarkPartners A B k b).Nonempty) := by
  classical
  simp only [deletedLevelPairs, Finset.mem_union, redDeletedPairs, blueDeletedPairs,
    Finset.mem_image, Finset.mem_sigma, markedRedLines, markedBlueLines,
    redPartnersAtLevel, bluePartnersAtLevel, Finset.mem_filter, Sigma.exists,
    Prod.mk.injEq]
  aesop

/-- The levelwise deletion bound: at most `2 T_k` bichromatic level-`k` pairs
are not clean. Pairs marked at both endpoints are counted only once in the union. -/
theorem card_deletedLevelPairs_le {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) (k : ℕ) :
    (deletedLevelPairs A B k).card ≤ 2 * levelDefect (A ∪ B) A B k := by
  have hred : (redDeletedPairs A B k).card ≤
      2 * (defectiveEventsAtLevel (A ∪ B) A B k).card := by
    calc
      _ ≤ ((markedRedLines A B k).sigma (redPartnersAtLevel A B k)).card := Finset.card_image_le
      _ = ∑ a ∈ markedRedLines A B k, (redPartnersAtLevel A B k a).card := Finset.card_sigma _ _
      _ ≤ _ := sum_marked_red_incidence_le hgen hP hvert k
  have hblue : (blueDeletedPairs A B k).card ≤
      2 * (defectiveEventsAtLevel (A ∪ B) B A k).card := by
    calc
      _ ≤ ((markedBlueLines A B k).sigma (bluePartnersAtLevel A B k)).card := Finset.card_image_le
      _ = ∑ b ∈ markedBlueLines A B k, (bluePartnersAtLevel A B k b).card := Finset.card_sigma _ _
      _ ≤ _ := sum_marked_blue_incidence_le hgen hP hvert k
  have h := Finset.card_union_le (redDeletedPairs A B k) (blueDeletedPairs A B k)
  unfold deletedLevelPairs levelDefect
  omega

/-- Summing over levels charges each defect at its own level, and therefore
deletes at most twice the geometric avoidance defect in total. -/
theorem sum_card_deletedLevelPairs_le {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) :
    ∑ k ∈ Finset.Icc 1 ((A ∪ B).card - 1), (deletedLevelPairs A B k).card ≤
      2 * avoidanceDefect A B := by
  have hAB : Disjoint A B := Finset.disjoint_left.mpr (by
    intro p hpA hpB
    exact ((hvert.2 p hpB).trans (hvert.1 p hpA)).false)
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 ((A ∪ B).card - 1), 2 * levelDefect (A ∪ B) A B k :=
      Finset.sum_le_sum (fun k _ => card_deletedLevelPairs_le hgen hP hvert k)
    _ = 2 * ∑ k ∈ Finset.Icc 1 ((A ∪ B).card - 1), levelDefect (A ∪ B) A B k := by
      rw [Finset.mul_sum]
    _ = 2 * avoidanceDefect A B := by
      rw [sum_levelDefect hgen hP Finset.subset_union_left Finset.subset_union_right hAB]

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualDeletionCount

section OriginalModule_LinearCrossingFamilies_DualCleanSetup

/-! ## Rank comparisons and endpoint uniqueness for clean events -/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

def CleanPairAtLevel (A B : Finset Point) (k : ℕ) (a b : Point) : Prop :=
  a ∈ A ∧ b ∈ B ∧ eventLevel (A ∪ B) s(a, b) = k ∧
    ¬(redMarkPartners A B k a).Nonempty ∧ ¬(blueMarkPartners A B k b).Nonempty

theorem inLowest_of_lt_eventHeight {P : Finset Point} {e : Sym2 Point}
    {p : Point} (hp : p ∈ P) (h : dualValue p (eventAbscissa e) < eventHeight e) :
    InLowest P (eventLevel P e) p (eventAbscissa e) := by
  refine ⟨hp, ?_⟩
  have hsub : belowAt P p (eventAbscissa e) ⊆ linesBelow P e := by
    intro q hq
    obtain ⟨hqP, hqp⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hqP, hqp.trans h⟩
  exact Nat.lt_succ_of_le (Finset.card_le_card hsub)

theorem not_inLowest_of_eventHeight_lt {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {e : Sym2 Point} (he : e ∈ spannedPairs P)
    {p : Point} (h : eventHeight e < dualValue p (eventAbscissa e)) :
    ¬InLowest P (eventLevel P e) p (eventAbscissa e) := by
  let a := e.out.1
  have ha : a ∈ e := Sym2.out_fst_mem e
  have haP : a ∈ P := (mem_spannedPairs.mp he).1 a ha
  have hae := dualValue_event_of_mem hgen he ha
  have hna : a ∉ linesBelow P e := by
    simp only [linesBelow, Finset.mem_filter, hae, lt_self_iff_false, and_false, not_false_eq_true]
  have hsub : insert a (linesBelow P e) ⊆ belowAt P p (eventAbscissa e) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨haP, hae ▸ h⟩
    · obtain ⟨hqP, hqh⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hqP, hqh.trans h⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hna] at hcard
  exact fun hin => (not_lt_of_ge hcard) hin.2

theorem not_exitEvent_of_nonincident {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {e : Sym2 Point} (he : e ∈ spannedPairs P)
    {p : Point} (hp : p ∈ P) (hpe : p ∉ e) (k : ℕ) :
    ¬ExitEvent P k p (eventAbscissa e) := by
  rintro ⟨q, hq, hqp, heq, _⟩
  have hne : q ≠ p := fun h => hqp.ne (congrArg Prod.fst h)
  have he' : s(q, p) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P q p).mpr ⟨hq, hp⟩, (nondegenerate_mk_iff q p).mpr hne⟩
  exact hpe (hgen.eventAbscissa_injOn he' he heq ▸ Sym2.mem_mk_right q p)

theorem not_entranceEvent_of_nonincident {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) {e : Sym2 Point} (he : e ∈ spannedPairs P)
    {p : Point} (hp : p ∈ P) (hpe : p ∉ e) (k : ℕ) :
    ¬EntranceEvent P k p (eventAbscissa e) := by
  rintro ⟨q, hq, hpq, heq, _⟩
  have hne : p ≠ q := fun h => hpq.ne (congrArg Prod.fst h)
  have he' : s(p, q) ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff P p q).mpr ⟨hp, hq⟩, (nondegenerate_mk_iff p q).mpr hne⟩
  exact hpe (hgen.eventAbscissa_injOn he' he heq ▸ Sym2.mem_mk_left p q)

theorem dualValue_lt_forward {p q : Point} {s x : ℝ}
    (hslope : p.1 ≤ q.1) (h : dualValue p s < dualValue q s) (hsx : s ≤ x) :
    dualValue p x < dualValue q x := by
  have hm := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hsx)
  dsimp [dualValue] at *
  nlinarith

theorem dualValue_lt_backward {p q : Point} {t x : ℝ}
    (hslope : q.1 ≤ p.1) (h : dualValue p t < dualValue q t) (hxt : x ≤ t) :
    dualValue p x < dualValue q x := by
  have hm := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hxt)
  dsimp [dualValue] at *
  nlinarith

theorem cleanPair_red_partner_unique {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {k : ℕ} {a b c : Point}
    (hab : CleanPairAtLevel A B k a b) (hac : CleanPairAtLevel A B k a c) : b = c := by
  have h := red_repeated_incidence_bound hgen hP hvert hab.1 k
  have hempty : redMarkPartners A B k a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hab.2.2.2.1
  rw [hempty, Finset.card_empty, add_zero] at h
  exact Finset.card_le_one_iff.mp h (Finset.mem_filter.mpr ⟨hab.2.1, hab.2.2.1⟩)
    (Finset.mem_filter.mpr ⟨hac.2.1, hac.2.2.1⟩)

theorem cleanPair_blue_partner_unique {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {k : ℕ} {a b c : Point}
    (hab : CleanPairAtLevel A B k a b) (hcb : CleanPairAtLevel A B k c b) : a = c := by
  have h := blue_repeated_incidence_bound hgen hP hvert hab.2.1 k
  have hempty : blueMarkPartners A B k b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hab.2.2.2.2
  rw [hempty, Finset.card_empty, add_zero] at h
  exact Finset.card_le_one_iff.mp h (Finset.mem_filter.mpr ⟨hab.1, hab.2.2.1⟩)
    (Finset.mem_filter.mpr ⟨hcb.1, hcb.2.2.1⟩)

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualCleanSetup

section OriginalModule_LinearCrossingFamilies_DualCleanTransitions

/-! ## Intermediate transitions and their directional marks -/

open Set Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

theorem exists_exit_before_entrance {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {s t : ℝ} (hst : s < t)
    (hin : InLowest P k p s) (hno : ¬ExitEvent P k p s)
    (ht : EntranceEvent P k p t) : ∃ x ∈ Ioo s t, ExitEvent P k p x := by
  obtain ⟨q, hq, hpq, hqt, hqk⟩ := ht
  have hev := eventually_inLowest_event hgen hP hin.1 hq hpq k
  rw [hqt, hqk] at hev
  have hbefore : ∀ᶠ y in 𝓝[<] t, s < y ∧ y < t ∧ ¬InLowest P k p y := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (Ioi_mem_nhds hst), self_mem_nhdsWithin] with y hy hsy hyt
    exact ⟨hsy, hyt, fun h => (lt_irrefl k) ((hy.1 hyt).1.mp h)⟩
  obtain ⟨y, hsy, hyt, hy⟩ := hbefore.exists
  obtain ⟨x, hx, he⟩ := exists_exitEvent_between hgen hP hsy.le hin hy
  have hxs : x ≠ s := fun h => hno (h ▸ he)
  exact ⟨x, ⟨lt_of_le_of_ne hx.1 hxs.symm, hx.2.trans hyt⟩, he⟩

theorem exists_entrance_before_exit {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} (hp : p ∈ P) {k : ℕ} {s t : ℝ} (hst : s < t)
    (hout : ¬InLowest P k p s) (ht : ExitEvent P k p t) :
    ∃ x ∈ Ioo s t, EntranceEvent P k p x := by
  obtain ⟨q, hq, hqp, hqt, hqk⟩ := ht
  have hev := eventually_inLowest_event hgen hP hq hp hqp k
  rw [hqt, hqk] at hev
  have hbefore : ∀ᶠ y in 𝓝[<] t, s < y ∧ y < t ∧ InLowest P k p y := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (Ioi_mem_nhds hst), self_mem_nhdsWithin] with y hy hsy hyt
    exact ⟨hsy, hyt, (hy.1 hyt).2.mpr le_rfl⟩
  obtain ⟨y, hsy, hyt, hy⟩ := hbefore.exists
  obtain ⟨x, hx, he⟩ := exists_entranceEvent_between hgen hP hsy.le hout hy
  exact ⟨x, ⟨hx.1, hx.2.trans_lt hyt⟩, he⟩

theorem exists_exit_after_entrance {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} (hp : p ∈ P) {k : ℕ} {s t : ℝ} (hst : s < t)
    (hs : EntranceEvent P k p s) (hout : ¬InLowest P k p t) :
    ∃ x ∈ Ioo s t, ExitEvent P k p x := by
  obtain ⟨q, hq, hpq, hqs, hqk⟩ := hs
  have hev := eventually_inLowest_event hgen hP hp hq hpq k
  rw [hqs, hqk] at hev
  have hafter : ∀ᶠ y in 𝓝[>] s, s < y ∧ y < t ∧ InLowest P k p y := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (Iio_mem_nhds hst), self_mem_nhdsWithin] with y hy hyt hsy
    exact ⟨hsy, hyt, (hy.2 hsy).1.mpr le_rfl⟩
  obtain ⟨y, hsy, hyt, hy⟩ := hafter.exists
  obtain ⟨x, hx, he⟩ := exists_exitEvent_between hgen hP hyt.le hy hout
  exact ⟨x, ⟨hsy.trans_le hx.1, hx.2⟩, he⟩

theorem exists_entrance_after_exit {P : Finset Point}
    (hgen : GenericCoordinatesOn P id) (hP : GeneralPosition P)
    {p : Point} {k : ℕ} {s t : ℝ} (hst : s < t)
    (hs : ExitEvent P k p s) (hin : InLowest P k p t)
    (hno : ¬EntranceEvent P k p t) : ∃ x ∈ Ioo s t, EntranceEvent P k p x := by
  obtain ⟨q, hq, hqp, hqs, hqk⟩ := hs
  have hev := eventually_inLowest_event hgen hP hq hin.1 hqp k
  rw [hqs, hqk] at hev
  have hafter : ∀ᶠ y in 𝓝[>] s, s < y ∧ y < t ∧ ¬InLowest P k p y := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (Iio_mem_nhds hst), self_mem_nhdsWithin] with y hy hyt hsy
    exact ⟨hsy, hyt, fun h => (lt_irrefl k) ((hy.2 hsy).2.mp h)⟩
  obtain ⟨y, hsy, hyt, hy⟩ := hafter.exists
  obtain ⟨x, hx, he⟩ := exists_entranceEvent_between hgen hP hyt.le hy hin
  have hxt : x ≠ t := fun h => hno (h ▸ he)
  exact ⟨x, ⟨hsy.trans hx.1, lt_of_le_of_ne hx.2 hxt⟩, he⟩

theorem red_mark_of_exit_bracket {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hvert : VerticallySeparatedOn A B id)
    {a : Point} (ha : a ∈ A) {k : ℕ} {x : ℝ} (he : ExitEvent (A ∪ B) k a x)
    (hbelow : ∃ b ∈ B, dualValue b x < dualValue a x)
    (habove : ∃ b ∈ B, dualValue a x < dualValue b x) :
    (redMarkPartners A B k a).Nonempty := by
  classical
  obtain ⟨q, hqP, hqa, hqx, hk⟩ := he
  have hqA : q ∈ A := by
    rcases Finset.mem_union.mp hqP with hq | hq
    · exact hq
    · exact ((hvert.2 q hq).trans (hqa.trans (hvert.1 a ha))).false.elim
  have hne : q ≠ a := fun heq => hqa.ne (congrArg Prod.fst heq)
  have heP : s(q, a) ∈ spannedPairs (A ∪ B) := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff _ q a).mpr ⟨hqP, Finset.mem_union_left B ha⟩,
      (nondegenerate_mk_iff q a).mpr hne⟩
  have hheight := dualValue_event_of_mem hgen heP (Sym2.mem_mk_right q a)
  refine ⟨q, Finset.mem_filter.mpr ⟨hqA, hqa, hk, ?_⟩⟩
  unfold DualDefective
  rw [← hheight, hqx]
  exact ⟨hbelow, habove⟩

theorem blue_mark_of_entrance_bracket {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hvert : VerticallySeparatedOn A B id)
    {b : Point} (hb : b ∈ B) {k : ℕ} {x : ℝ} (he : EntranceEvent (A ∪ B) k b x)
    (hbelow : ∃ a ∈ A, dualValue a x < dualValue b x)
    (habove : ∃ a ∈ A, dualValue b x < dualValue a x) :
    (blueMarkPartners A B k b).Nonempty := by
  classical
  obtain ⟨q, hqP, hbq, hqx, hk⟩ := he
  have hqB : q ∈ B := by
    rcases Finset.mem_union.mp hqP with hq | hq
    · exact ((hvert.2 b hb).trans (hbq.trans (hvert.1 q hq))).false.elim
    · exact hq
  have hne : b ≠ q := fun heq => hbq.ne (congrArg Prod.fst heq)
  have heP : s(b, q) ∈ spannedPairs (A ∪ B) := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff _ b q).mpr ⟨Finset.mem_union_right A hb, hqP⟩,
      (nondegenerate_mk_iff b q).mpr hne⟩
  have hheight := dualValue_event_of_mem hgen heP (Sym2.mem_mk_left b q)
  refine ⟨q, Finset.mem_filter.mpr ⟨hqB, hbq, hk, ?_⟩⟩
  unfold DualDefective
  rw [← hheight, hqx]
  exact ⟨hbelow, habove⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualCleanTransitions

section OriginalModule_LinearCrossingFamilies_DualCleanBrackets

/-!
## Reciprocal brackets at clean intersections

The forward and backward interval arguments are proved directly in the original
coordinates. They implement the paper's sweep reversal without introducing a
second reflected configuration.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- Two clean same-level events, in left-to-right order, satisfy all four
strict dual height inequalities used by the primal crossing criterion. -/
theorem cleanPair_reciprocal_brackets {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {k : ℕ} {a b c d : Point}
    (hab : CleanPairAtLevel A B k a b) (hcd : CleanPairAtLevel A B k c d)
    (hst : eventAbscissa s(a, b) < eventAbscissa s(c, d)) :
    eventHeight s(a, b) < dualValue c (eventAbscissa s(a, b)) ∧
    dualValue d (eventAbscissa s(a, b)) < eventHeight s(a, b) ∧
    eventHeight s(c, d) < dualValue b (eventAbscissa s(c, d)) ∧
    dualValue a (eventAbscissa s(c, d)) < eventHeight s(c, d) := by
  have haP := Finset.mem_union_left B hab.1
  have hbP := Finset.mem_union_right A hab.2.1
  have hcP := Finset.mem_union_left B hcd.1
  have hdP := Finset.mem_union_right A hcd.2.1
  have habs : a.1 < b.1 := (hvert.1 a hab.1).trans (hvert.2 b hab.2.1)
  have hads : a.1 < d.1 := (hvert.1 a hab.1).trans (hvert.2 d hcd.2.1)
  have hcbs : c.1 < b.1 := (hvert.1 c hcd.1).trans (hvert.2 b hab.2.1)
  have hcds : c.1 < d.1 := (hvert.1 c hcd.1).trans (hvert.2 d hcd.2.1)
  have hac : a ≠ c := by
    intro heq
    subst c
    have hbd := cleanPair_red_partner_unique hgen hP hvert hab hcd
    subst d
    exact hst.false
  have hbd : b ≠ d := by
    intro heq
    subst d
    exact hac (cleanPair_blue_partner_unique hgen hP hvert hab hcd)
  have he : s(a, b) ∈ spannedPairs (A ∪ B) := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff _ a b).mpr ⟨haP, hbP⟩,
      (nondegenerate_mk_iff a b).mpr (fun heq => habs.ne (congrArg Prod.fst heq))⟩
  have he' : s(c, d) ∈ spannedPairs (A ∪ B) := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff _ c d).mpr ⟨hcP, hdP⟩,
      (nondegenerate_mk_iff c d).mpr (fun heq => hcds.ne (congrArg Prod.fst heq))⟩
  have hcn : c ∉ s(a, b) := by
    rw [Sym2.mem_iff, not_or]
    exact ⟨hac.symm, fun heq => hcbs.ne (congrArg Prod.fst heq)⟩
  have hdn : d ∉ s(a, b) := by
    rw [Sym2.mem_iff, not_or]
    exact ⟨fun heq => hads.ne (congrArg Prod.fst heq.symm), hbd.symm⟩
  have han : a ∉ s(c, d) := by
    rw [Sym2.mem_iff, not_or]
    exact ⟨hac, fun heq => hads.ne (congrArg Prod.fst heq)⟩
  have hbn : b ∉ s(c, d) := by
    rw [Sym2.mem_iff, not_or]
    exact ⟨fun heq => hcbs.ne (congrArg Prod.fst heq.symm), hbd⟩
  have hae := dualValue_event_of_mem hgen he (Sym2.mem_mk_left a b)
  have hbe := dualValue_event_of_mem hgen he (Sym2.mem_mk_right a b)
  have hce := dualValue_event_of_mem hgen he' (Sym2.mem_mk_left c d)
  have hde := dualValue_event_of_mem hgen he' (Sym2.mem_mk_right c d)
  have hcabove : eventHeight s(a, b) < dualValue c (eventAbscissa s(a, b)) := by
    by_contra hn
    have hbad := lt_of_le_of_ne (le_of_not_gt hn)
      (dualValue_event_ne_of_not_mem hgen hP he hcP hcn)
    have hin : InLowest (A ∪ B) k c (eventAbscissa s(a, b)) := by
      simpa only [hab.2.2.1] using inLowest_of_lt_eventHeight hcP hbad
    obtain ⟨x, hx, hexit⟩ := exists_exit_before_entrance hgen hP hst hin
      (not_exitEvent_of_nonincident hgen he hcP hcn k)
      ⟨d, hdP, hcds, rfl, hcd.2.2.1⟩
    apply hcd.2.2.2.1
    apply red_mark_of_exit_bracket hgen hvert hcd.1 hexit
    · exact ⟨d, hcd.2.1, (dualValue_rev_lt_iff_lt_abscissa hcds x).mpr hx.2⟩
    · exact ⟨b, hab.2.1, dualValue_lt_forward hcbs.le (hbe.symm ▸ hbad) hx.1.le⟩
  have hdbelow : dualValue d (eventAbscissa s(a, b)) < eventHeight s(a, b) := by
    by_contra hn
    have hbad := lt_of_le_of_ne (le_of_not_gt hn)
      (dualValue_event_ne_of_not_mem hgen hP he hdP hdn).symm
    have hout : ¬InLowest (A ∪ B) k d (eventAbscissa s(a, b)) := by
      simpa only [hab.2.2.1] using not_inLowest_of_eventHeight_lt hgen he hbad
    obtain ⟨x, hx, hentry⟩ := exists_entrance_before_exit hgen hP hdP hst hout
      ⟨c, hcP, hcds, rfl, hcd.2.2.1⟩
    apply hcd.2.2.2.2
    apply blue_mark_of_entrance_bracket hgen hvert hcd.2.1 hentry
    · exact ⟨a, hab.1, dualValue_lt_forward hads.le (hae.symm ▸ hbad) hx.1.le⟩
    · exact ⟨c, hcd.1, (dualValue_rev_lt_iff_lt_abscissa hcds x).mpr hx.2⟩
  have hbabove : eventHeight s(c, d) < dualValue b (eventAbscissa s(c, d)) := by
    by_contra hn
    have hbad := lt_of_le_of_ne (le_of_not_gt hn)
      (dualValue_event_ne_of_not_mem hgen hP he' hbP hbn)
    have hin : InLowest (A ∪ B) k b (eventAbscissa s(c, d)) := by
      simpa only [hcd.2.2.1] using inLowest_of_lt_eventHeight hbP hbad
    obtain ⟨x, hx, hentry⟩ := exists_entrance_after_exit hgen hP hst
      ⟨a, haP, habs, rfl, hab.2.2.1⟩ hin
      (not_entranceEvent_of_nonincident hgen he' hbP hbn k)
    apply hab.2.2.2.2
    apply blue_mark_of_entrance_bracket hgen hvert hab.2.1 hentry
    · exact ⟨a, hab.1, (dualValue_lt_iff_abscissa_lt habs x).mpr hx.1⟩
    · exact ⟨c, hcd.1, dualValue_lt_backward hcbs.le (hce.symm ▸ hbad) hx.2.le⟩
  have habelow : dualValue a (eventAbscissa s(c, d)) < eventHeight s(c, d) := by
    by_contra hn
    have hbad := lt_of_le_of_ne (le_of_not_gt hn)
      (dualValue_event_ne_of_not_mem hgen hP he' haP han).symm
    have hout : ¬InLowest (A ∪ B) k a (eventAbscissa s(c, d)) := by
      simpa only [hcd.2.2.1] using not_inLowest_of_eventHeight_lt hgen he' hbad
    obtain ⟨x, hx, hexit⟩ := exists_exit_after_entrance hgen hP haP hst
      ⟨b, hbP, habs, rfl, hab.2.2.1⟩ hout
    apply hab.2.2.2.1
    apply red_mark_of_exit_bracket hgen hvert hab.1 hexit
    · exact ⟨d, hcd.2.1, dualValue_lt_backward hads.le (hde.symm ▸ hbad) hx.2.le⟩
    · exact ⟨b, hab.2.1, (dualValue_lt_iff_abscissa_lt habs x).mpr hx.1⟩
  exact ⟨hcabove, hdbelow, hbabove, habelow⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualCleanBrackets

section OriginalModule_LinearCrossingFamilies_DualCleanFamily

/-! ## Clean intersections form a crossing family -/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

def bichromaticLevelPairs (A B : Finset Point) (k : ℕ) : Finset (Point × Point) :=
  (A ×ˢ B).filter (fun z => eventLevel (A ∪ B) s(z.1, z.2) = k)

def cleanLevelPairs (A B : Finset Point) (k : ℕ) : Finset (Point × Point) :=
  bichromaticLevelPairs A B k \ deletedLevelPairs A B k

def cleanLevelEvents (A B : Finset Point) (k : ℕ) : Finset (Sym2 Point) :=
  (cleanLevelPairs A B k).image (fun z => s(z.1, z.2))

@[simp] theorem mem_cleanLevelPairs {A B : Finset Point} {k : ℕ} {a b : Point} :
    (a, b) ∈ cleanLevelPairs A B k ↔ CleanPairAtLevel A B k a b := by
  classical
  simp only [cleanLevelPairs, Finset.mem_sdiff, bichromaticLevelPairs,
    Finset.mem_filter, Finset.mem_product, mem_deletedLevelPairs, CleanPairAtLevel]
  tauto

theorem cleanPair_mem_spannedPairs {A B : Finset Point}
    (hvert : VerticallySeparatedOn A B id) {k : ℕ} {a b : Point}
    (hab : CleanPairAtLevel A B k a b) : s(a, b) ∈ spannedPairs (A ∪ B) := by
  have hs : a.1 < b.1 := (hvert.1 a hab.1).trans (hvert.2 b hab.2.1)
  exact mem_spannedPairs.mpr ⟨(spannedBy_mk_iff _ a b).mpr
    ⟨Finset.mem_union_left B hab.1, Finset.mem_union_right A hab.2.1⟩,
    (nondegenerate_mk_iff a b).mpr (fun h => hs.ne (congrArg Prod.fst h))⟩

theorem cleanPair_crosses_of_abscissa_lt {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {k : ℕ} {a b c d : Point}
    (hab : CleanPairAtLevel A B k a b) (hcd : CleanPairAtLevel A B k c d)
    (hst : eventAbscissa s(a, b) < eventAbscissa s(c, d)) : Crosses s(a, b) s(c, d) := by
  obtain ⟨hc, hd, hb, ha⟩ := cleanPair_reciprocal_brackets hgen hP hvert hab hcd hst
  have he := cleanPair_mem_spannedPairs hvert hab
  have he' := cleanPair_mem_spannedPairs hvert hcd
  exact crosses_of_dual_brackets
    ((hvert.1 a hab.1).trans (hvert.2 b hab.2.1))
    ((hvert.1 c hcd.1).trans (hvert.2 d hcd.2.1))
    (dualValue_event_of_mem hgen he (Sym2.mem_mk_left a b))
    (dualValue_event_of_mem hgen he (Sym2.mem_mk_right a b))
    (dualValue_event_of_mem hgen he' (Sym2.mem_mk_left c d))
    (dualValue_event_of_mem hgen he' (Sym2.mem_mk_right c d)) hc hd hb ha

theorem cleanPair_crosses {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {k : ℕ} {a b c d : Point}
    (hab : CleanPairAtLevel A B k a b) (hcd : CleanPairAtLevel A B k c d)
    (hne : s(a, b) ≠ s(c, d)) : Crosses s(a, b) s(c, d) := by
  have hneX : eventAbscissa s(a, b) ≠ eventAbscissa s(c, d) := fun h =>
    hne (hgen.eventAbscissa_injOn (cleanPair_mem_spannedPairs hvert hab)
      (cleanPair_mem_spannedPairs hvert hcd) h)
  rcases lt_or_gt_of_ne hneX with hlt | hgt
  · exact cleanPair_crosses_of_abscissa_lt hgen hP hvert hab hcd hlt
  · have h := cleanPair_crosses_of_abscissa_lt hgen hP hvert hcd hab hgt
    simpa only [Crosses, Set.inter_comm] using h

theorem cleanPair_endpointDisjoint {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) {k : ℕ} {a b c d : Point}
    (hab : CleanPairAtLevel A B k a b) (hcd : CleanPairAtLevel A B k c d)
    (hne : s(a, b) ≠ s(c, d)) : EndpointDisjoint s(a, b) s(c, d) := by
  rw [endpointDisjoint_mk_iff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro heq
    subst c
    have hbd := cleanPair_red_partner_unique hgen hP hvert hab hcd
    exact hne (hbd ▸ rfl)
  · intro heq
    have hs : a.1 < d.1 := (hvert.1 a hab.1).trans (hvert.2 d hcd.2.1)
    exact hs.ne (congrArg Prod.fst heq)
  · intro heq
    have hs : c.1 < b.1 := (hvert.1 c hcd.1).trans (hvert.2 b hab.2.1)
    exact hs.ne (congrArg Prod.fst heq.symm)
  · intro heq
    subst d
    have hac := cleanPair_blue_partner_unique hgen hP hvert hab hcd
    exact hne (hac ▸ rfl)

/-- The clean-intersection crossing lemma, with a finite family of unordered segments. -/
theorem isCrossingFamily_cleanLevelEvents {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) (k : ℕ) :
    IsCrossingFamily (A ∪ B) (cleanLevelEvents A B k : Set (Sym2 Point)) := by
  refine ⟨Finset.finite_toSet _, ?_, ?_⟩
  · intro e he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    exact mem_spannedPairs.mp (cleanPair_mem_spannedPairs hvert (mem_cleanLevelPairs.mp hab))
  · intro e he f hf hne
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp hf
    have hab' := mem_cleanLevelPairs.mp hab
    have hcd' := mem_cleanLevelPairs.mp hcd
    exact ⟨cleanPair_endpointDisjoint hgen hP hvert hab' hcd' hne,
      cleanPair_crosses hgen hP hvert hab' hcd' hne⟩

/-- Orienting each bichromatic segment from red to blue loses no cardinality. -/
theorem card_cleanLevelEvents {A B : Finset Point}
    (hvert : VerticallySeparatedOn A B id) (k : ℕ) :
    (cleanLevelEvents A B k).card = (cleanLevelPairs A B k).card := by
  apply Finset.card_image_of_injOn
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  have hab' := mem_cleanLevelPairs.mp hab
  have hcd' := mem_cleanLevelPairs.mp hcd
  rcases Sym2.eq_iff.mp heq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact Prod.ext hac hbd
  · have hs : a.1 < d.1 := (hvert.1 a hab'.1).trans (hvert.2 d hcd'.2.1)
    exact (hs.ne (congrArg Prod.fst had)).elim

theorem eventLevel_of_mem_cleanLevelEvents {A B : Finset Point} {k : ℕ}
    {e : Sym2 Point} (he : e ∈ cleanLevelEvents A B k) : eventLevel (A ∪ B) e = k := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
  exact (mem_cleanLevelPairs.mp hab).2.2.1

/-- A retained segment belongs to at most one level family. -/
theorem cleanLevelEvents_disjoint {A B : Finset Point} {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (cleanLevelEvents A B k) (cleanLevelEvents A B l) := by
  apply Finset.disjoint_left.mpr
  intro e hek hel
  exact hkl ((eventLevel_of_mem_cleanLevelEvents hek).symm.trans
    (eventLevel_of_mem_cleanLevelEvents hel))

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualCleanFamily

section OriginalModule_LinearCrossingFamilies_DualAveraging

/-! ## Counting retained families and averaging over dual levels -/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

theorem deletedLevelPairs_subset (A B : Finset Point) (k : ℕ) :
    deletedLevelPairs A B k ⊆ bichromaticLevelPairs A B k := by
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb, hk, _⟩ := mem_deletedLevelPairs.mp hab
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hk⟩

theorem card_clean_add_card_deleted (A B : Finset Point) (k : ℕ) :
    (cleanLevelPairs A B k).card + (deletedLevelPairs A B k).card =
      (bichromaticLevelPairs A B k).card :=
  Finset.card_sdiff_add_card_eq_card (deletedLevelPairs_subset A B k)

theorem sum_card_bichromaticLevelPairs {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hvert : VerticallySeparatedOn A B id) :
    ∑ k ∈ Finset.Icc 1 ((A ∪ B).card - 1), (bichromaticLevelPairs A B k).card =
      A.card * B.card := by
  rw [← Finset.card_product]
  symm
  change (A ×ˢ B).card = ∑ k ∈ Finset.Icc 1 ((A ∪ B).card - 1),
    ((A ×ˢ B).filter (fun z => eventLevel (A ∪ B) s(z.1, z.2) = k)).card
  apply Finset.card_eq_sum_card_fiberwise
    (f := fun z : Point × Point => eventLevel (A ∪ B) s(z.1, z.2))
    (s := A ×ˢ B) (t := Finset.Icc 1 ((A ∪ B).card - 1))
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have hs : a.1 < b.1 := (hvert.1 a ha).trans (hvert.2 b hb)
  have he : s(a, b) ∈ spannedPairs (A ∪ B) := mem_spannedPairs.mpr
    ⟨(spannedBy_mk_iff _ a b).mpr ⟨Finset.mem_union_left B ha, Finset.mem_union_right A hb⟩,
      (nondegenerate_mk_iff a b).mpr (fun h => hs.ne (congrArg Prod.fst h))⟩
  exact Finset.mem_Icc.mpr ⟨one_le_eventLevel _ _, eventLevel_le_card_sub_one hgen he⟩

/-- The total size of retained crossing families, plus the permitted deletion
budget, is at least the number of all bichromatic segments. -/
theorem card_product_le_sum_clean_add_defect {A B : Finset Point}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) :
    A.card * B.card ≤
      (∑ k ∈ Finset.Icc 1 ((A ∪ B).card - 1), (cleanLevelEvents A B k).card) +
        2 * avoidanceDefect A B := by
  have hsum := Finset.sum_congr (s₁ := Finset.Icc 1 ((A ∪ B).card - 1))
    rfl (fun k _ => card_clean_add_card_deleted A B k)
  rw [Finset.sum_add_distrib, sum_card_bichromaticLevelPairs hgen hvert] at hsum
  have hdel := sum_card_deletedLevelPairs_le hgen hP hvert
  simp only [card_cleanLevelEvents hvert]
  omega

/-- At least one prepared level satisfies the averaging bound, expressed using
natural counts so that subtraction cannot truncate the numerator. -/
theorem exists_clean_level_large {A B : Finset Point} {m : ℕ}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) (hm : 1 ≤ m)
    (hA : A.card = m) (hB : B.card = m) :
    ∃ k ∈ Finset.Icc 1 (2 * m - 1),
      m * m ≤ (2 * m - 1) * (cleanLevelEvents A B k).card + 2 * avoidanceDefect A B := by
  have hAB : Disjoint A B := Finset.disjoint_left.mpr (by
    intro p hpA hpB
    exact ((hvert.2 p hpB).trans (hvert.1 p hpA)).false)
  have hcard : (A ∪ B).card = 2 * m := by
    rw [Finset.card_union_of_disjoint hAB, hA, hB]
    omega
  have hrange : (Finset.Icc 1 (2 * m - 1)).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨k, hk, hmax⟩ := (Finset.Icc 1 (2 * m - 1)).exists_max_image
    (fun j => (cleanLevelEvents A B j).card) hrange
  refine ⟨k, hk, ?_⟩
  have hsum : (∑ j ∈ Finset.Icc 1 (2 * m - 1), (cleanLevelEvents A B j).card) ≤
      (2 * m - 1) * (cleanLevelEvents A B k).card := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 (2 * m - 1), (cleanLevelEvents A B k).card :=
        Finset.sum_le_sum hmax
      _ = _ := by simp
  have h := card_product_le_sum_clean_add_defect hgen hP hvert
  rw [hcard, hA, hB] at h
  omega

/-- Quantitative conclusion of the dual-level proposition in prepared coordinates. -/
theorem exists_crossingFamily_bound_prepared {A B : Finset Point} {m : ℕ}
    (hgen : GenericCoordinatesOn (A ∪ B) id) (hP : GeneralPosition (A ∪ B))
    (hvert : VerticallySeparatedOn A B id) (hm : 1 ≤ m)
    (hA : A.card = m) (hB : B.card = m) :
    ∃ F : Set (Sym2 Point), IsCrossingFamily (A ∪ B) F ∧
      ((m : ℝ) ^ 2 - 2 * (avoidanceDefect A B : ℝ)) / (2 * (m : ℝ) - 1) ≤ F.ncard := by
  obtain ⟨k, _, hk⟩ := exists_clean_level_large hgen hP hvert hm hA hB
  refine ⟨cleanLevelEvents A B k, isCrossingFamily_cleanLevelEvents hgen hP hvert k, ?_⟩
  rw [Set.ncard_coe_finset]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < 2 * (m : ℝ) - 1 := by linarith
  apply (div_le_iff₀ hden).mpr
  have hR : (m : ℝ) * m ≤ ((2 * m - 1 : ℕ) : ℝ) *
      ((cleanLevelEvents A B k).card : ℝ) + 2 * (avoidanceDefect A B : ℝ) := by
    exact_mod_cast hk
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hR
  nlinarith

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DualAveraging

section OriginalModule_LinearCrossingFamilies_SeparatedCrossingBound

/-!
## The separated-set crossing bound in the original coordinates

The generic-coordinate and vertical-separation hypotheses are discharged by
the verified coordinate preparation. Families and their cardinalities are
transferred back, preserving the original geometric meaning.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

/-- The quantitative bound from the paper's dual-level deletion proposition,
with only its original geometric hypotheses. -/
theorem Separated.exists_crossingFamily_bound {A B : Finset Point} {m : ℕ}
    (hsep : Separated A B) (hP : GeneralPosition (A ∪ B)) (hm : 1 ≤ m)
    (hA : A.card = m) (hB : B.card = m) :
    ∃ F : Set (Sym2 Point), IsCrossingFamily (A ∪ B) F ∧
      ((m : ℝ) ^ 2 - 2 * (avoidanceDefect A B : ℝ)) / (2 * (m : ℝ) - 1) ≤ F.ncard := by
  classical
  have hAnon : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBnon : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨f, hsign, hinj, hvert, hgen, hdef⟩ :=
    hsep.exists_prepared_coordinates_defect hAnon hBnon hP
  have hgen' : GenericCoordinatesOn (A.image f ∪ B.image f) id := by
    convert hgen.image using 1
    ext p
    simp only [Finset.mem_union, Finset.mem_image]
    aesop
  have hP' : GeneralPosition (A.image f ∪ B.image f) := by
    simpa only [Finset.image_union] using hsign.generalPosition hP
  have hvert' : VerticallySeparatedOn (A.image f) (B.image f) id := by
    constructor
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact hvert.1 p hp
    · intro b hb
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
      exact hvert.2 p hp
  have hA' : (A.image f).card = m := by
    rw [Finset.card_image_of_injOn (hinj.mono Finset.subset_union_left), hA]
  have hB' : (B.image f).card = m := by
    rw [Finset.card_image_of_injOn (hinj.mono Finset.subset_union_right), hB]
  obtain ⟨F, hF, hlarge⟩ := exists_crossingFamily_bound_prepared hgen' hP' hvert' hm hA' hB'
  have hF' : IsCrossingFamily ((A ∪ B).image f) F := by
    simpa only [Finset.image_union] using hF
  obtain ⟨G, hG, hcard⟩ := hsign.crossingFamily_pullback hinj hP hF'
  refine ⟨G, hG, ?_⟩
  simpa only [hcard, hdef] using hlarge

/-- Near avoidance with error `1/4` gives a crossing family of size at least `m/4`. -/
theorem Separated.exists_crossingFamily_quarter {A B : Finset Point} {m : ℕ}
    (hsep : Separated A B) (hP : GeneralPosition (A ∪ B)) (hm : 1 ≤ m)
    (hA : A.card = m) (hB : B.card = m)
    (ht : (avoidanceDefect A B : ℝ) ≤ (m : ℝ) ^ 2 / 4) :
    ∃ F : Set (Sym2 Point), IsCrossingFamily (A ∪ B) F ∧ (m : ℝ) / 4 ≤ F.ncard := by
  obtain ⟨F, hF, hsize⟩ := hsep.exists_crossingFamily_bound hP hm hA hB
  refine ⟨F, hF, le_trans ?_ hsize⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < 2 * (m : ℝ) - 1 := by linarith
  apply (le_div_iff₀ hden).mpr
  nlinarith

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_SeparatedCrossingBound

section OriginalModule_LinearCrossingFamilies_FinalAssembly

/-!
## Final arithmetic, conditional on fixed-parameter near-avoidance extraction

The extraction hypothesis is explicit in this reusable implication. It is proved
in `fixed_parameter_near_avoidance_extraction` and applied in
`linear_crossing_families` to obtain the unconditional main theorem. Both the
large- and small-cardinality cases of the paper's final argument are handled here.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance : DecidableEq Point := Classical.decEq _

theorem GeneralPosition.mono {P Q : Finset Point} (hP : GeneralPosition P) (hQP : Q ⊆ P) :
    GeneralPosition Q := by
  intro a ha b hb c hc hab hac hbc
  exact hP (hQP ha) (hQP hb) (hQP hc) hab hac hbc

theorem IsCrossingFamily.mono {P Q : Finset Point} {F : Set (Sym2 Point)}
    (hF : IsCrossingFamily P F) (hPQ : P ⊆ Q) : IsCrossingFamily Q F := by
  refine ⟨hF.1, ?_, hF.2.2⟩
  intro e he
  have h := hF.2.1 e he
  exact ⟨fun p hp => hPQ (h.1 p hp), h.2⟩

/-- The small-set case needs only two distinct endpoints, not general position. -/
theorem exists_singleton_crossingFamily {P : Finset Point} (hP : 2 ≤ P.card) :
    ∃ F : Set (Sym2 Point), IsCrossingFamily P F ∧ F.ncard = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  refine ⟨{s(a, b)}, ⟨Set.finite_singleton _, ?_, ?_⟩, Set.ncard_singleton _⟩
  · intro e he
    have heq : e = s(a, b) := Set.mem_singleton_iff.mp he
    subst e
    exact ⟨(spannedBy_mk_iff P a b).mpr ⟨ha, hb⟩, (nondegenerate_mk_iff a b).mpr hab⟩
  · intro e he f hf hne
    exact (hne ((Set.mem_singleton_iff.mp he).trans (Set.mem_singleton_iff.mp hf).symm)).elim

/-- Final arithmetic from the `ε = 1/4` extraction specialization with an
absolute natural threshold `H`; the hypothesis is proved in
`fixed_parameter_near_avoidance_extraction`. -/
theorem linearCrossingFamilies_of_fixed_extraction
    (hextract : ∃ H : ℕ, 2 ≤ H ∧
      ∀ (P : Finset Point) (m : ℕ), GeneralPosition P → 1 ≤ m → H * m ≤ P.card →
        ∃ A B : Finset Point, A ⊆ P ∧ B ⊆ P ∧ Separated A B ∧
          A.card = m ∧ B.card = m ∧ (avoidanceDefect A B : ℝ) ≤ (m : ℝ) ^ 2 / 4) :
    LinearCrossingFamiliesStatement := by
  obtain ⟨H, hH, hextract⟩ := hextract
  have hHpos : 0 < H := by omega
  have hHR : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hden : (0 : ℝ) < 8 * H := by positivity
  refine ⟨1 / (8 * (H : ℝ)), by positivity, ?_⟩
  intro P hPcard hP
  by_cases hlarge : 2 * H ≤ P.card
  · let m := P.card / H
    have hm : 1 ≤ m := (Nat.le_div_iff_mul_le hHpos).mpr (by omega)
    have hsize : H * m ≤ P.card := by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self P.card H
    have hrem : P.card % H < H := Nat.mod_lt P.card hHpos
    have hdiv : P.card % H + H * m = P.card := Nat.mod_add_div P.card H
    have happrox : P.card ≤ 2 * H * m := by
      have hmul := Nat.mul_le_mul_left H hm
      nlinarith
    obtain ⟨A, B, hAP, hBP, hsep, hA, hB, ht⟩ := hextract P m hP hm hsize
    have hsub : A ∪ B ⊆ P := Finset.union_subset hAP hBP
    obtain ⟨F, hF, hFsize⟩ := hsep.exists_crossingFamily_quarter (hP.mono hsub) hm hA hB ht
    refine ⟨F, hF.mono hsub, le_trans ?_ hFsize⟩
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    have happroxR : (P.card : ℝ) ≤ 2 * (H : ℝ) * m := by exact_mod_cast happrox
    nlinarith
  · obtain ⟨F, hF, hcard⟩ := exists_singleton_crossingFamily hPcard
    refine ⟨F, hF, ?_⟩
    rw [hcard, Nat.cast_one, one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    have hn : P.card < 2 * H := by omega
    have hnR : (P.card : ℝ) < 2 * (H : ℝ) := by exact_mod_cast hn
    nlinarith

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_FinalAssembly

section OriginalModule_LinearCrossingFamilies_ExtractionCounting

/-!
## The cluster double count for near-avoidance extraction

This is the complete-geometric-graph specialization of the counting step in
PRT Lemma 3.3. Its geometric input is an explicitly stated bound on how many
cluster hulls each internal supporting line meets. The required clusters and
small-zone arrangement are constructed in later sections.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance extractionCountingDecEqPoint : DecidableEq Point := Classical.decEq _

/-- A finite version of the geometric defect, independent of dual coordinates. -/
def hullDefectPairs (A B : Finset Point) : Finset (Sym2 Point) := by
  classical
  exact (spannedPairs A).filter (fun e => LineMeetsConvexHull e B)

theorem coe_hullDefectPairs (A B : Finset Point) :
    (hullDefectPairs A B : Set (Sym2 Point)) = defectivePairs A B := by
  ext e
  simp only [hullDefectPairs, Finset.mem_coe, Finset.mem_filter, mem_spannedPairs,
    defectivePairs, Set.mem_ofPred_eq, DefectivePair]
  tauto

theorem card_hullDefectPairs (A B : Finset Point) :
    (hullDefectPairs A B).card = (defectivePairs A B).ncard := by
  rw [← coe_hullDefectPairs, Set.ncard_coe_finset]

/-- Clusters whose convex hull is met by the supporting line of `e`. -/
def hitClusters (C : Finset (Finset Point)) (e : Sym2 Point) : Finset (Finset Point) := by
  classical
  exact C.filter (fun B => LineMeetsConvexHull e B)

theorem sum_hullDefectPairs_eq_sum_hitClusters (A : Finset Point)
    (C : Finset (Finset Point)) :
    ∑ B ∈ C, (hullDefectPairs A B).card = ∑ e ∈ spannedPairs A, (hitClusters C e).card := by
  classical
  simp only [hullDefectPairs, hitClusters, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Ordered pairs of clusters count each directional defect twice in the sum
of the symmetric avoidance defect. Diagonal pairs are included here. -/
theorem sum_avoidanceDefect_eq_twice_incidence (C : Finset (Finset Point)) :
    ∑ A ∈ C, ∑ B ∈ C, avoidanceDefect A B =
      2 * ∑ A ∈ C, ∑ e ∈ spannedPairs A, (hitClusters C e).card := by
  simp only [avoidanceDefect, ← card_hullDefectPairs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun A B => (hullDefectPairs B A).card)]
  simp only [sum_hullDefectPairs_eq_sum_hitClusters]
  omega

/-- A deliberately coarse quadratic bound suffices when the extraction
parameters are fixed; it avoids needing the exact binomial coefficient. -/
theorem card_spannedPairs_le_square (A : Finset Point) :
    (spannedPairs A).card ≤ A.card * A.card := by
  classical
  calc
    _ ≤ A.sym2.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (A ×ˢ A).card := by
      rw [Finset.sym2_eq_image]
      exact Finset.card_image_le
    _ = _ := Finset.card_product A A

/-- Uniform cluster size and a uniform line-incidence bound control total defect. -/
theorem sum_avoidanceDefect_le {C : Finset (Finset Point)} {m q : ℕ}
    (hsize : ∀ A ∈ C, A.card = m)
    (hhit : ∀ A ∈ C, ∀ e ∈ spannedPairs A, (hitClusters C e).card ≤ q) :
    ∑ A ∈ C, ∑ B ∈ C, avoidanceDefect A B ≤ 2 * C.card * (m * m) * q := by
  rw [sum_avoidanceDefect_eq_twice_incidence]
  have hsum : (∑ A ∈ C, ∑ e ∈ spannedPairs A, (hitClusters C e).card) ≤
      C.card * (m * m * q) := by
    calc
      _ ≤ ∑ A ∈ C, m * m * q := by
        apply Finset.sum_le_sum
        intro A hA
        calc
          _ ≤ ∑ _e ∈ spannedPairs A, q := Finset.sum_le_sum (fun e he => hhit A hA e he)
          _ = (spannedPairs A).card * q := by simp
          _ ≤ m * m * q := Nat.mul_le_mul_right q (by
            simpa only [hsize A hA] using card_spannedPairs_le_square A)
      _ = _ := by simp
  nlinarith

/-- Sufficiently many clusters relative to the line-incidence bound force a
distinct pair with the fixed `1/4` avoidance error. -/
theorem exists_cluster_pair_small_defect {C : Finset (Finset Point)} {m q : ℕ}
    (hsize : ∀ A ∈ C, A.card = m)
    (hhit : ∀ A ∈ C, ∀ e ∈ spannedPairs A, (hitClusters C e).card ≤ q)
    (hcount : 8 * q + 2 ≤ C.card) :
    ∃ A ∈ C, ∃ B ∈ C, A ≠ B ∧ 4 * avoidanceDefect A B ≤ m * m := by
  classical
  have htwo : 1 < C.card := by omega
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp htwo
  have hnon : C.offDiag.Nonempty := ⟨(A, B), Finset.mem_offDiag.mpr ⟨hA, hB, hAB⟩⟩
  obtain ⟨⟨A, B⟩, hab, hmin⟩ := C.offDiag.exists_min_image
    (fun z => avoidanceDefect z.1 z.2) hnon
  obtain ⟨hA, hB, hAB⟩ := Finset.mem_offDiag.mp hab
  refine ⟨A, hA, B, hB, hAB, ?_⟩
  have hsub : C.offDiag ⊆ C ×ˢ C := by
    intro z hz
    have h := Finset.mem_offDiag.mp hz
    exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩
  have hbound : C.card * (C.card - 1) * avoidanceDefect A B ≤
      2 * C.card * (m * m) * q := by
    calc
      _ = ∑ _z ∈ C.offDiag, avoidanceDefect A B := by
        simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]
      _ ≤ ∑ z ∈ C.offDiag, avoidanceDefect z.1 z.2 := Finset.sum_le_sum hmin
      _ ≤ ∑ z ∈ C ×ˢ C, avoidanceDefect z.1 z.2 := Finset.sum_le_sum_of_subset hsub
      _ = ∑ U ∈ C, ∑ V ∈ C, avoidanceDefect U V := Finset.sum_product _ _ _
      _ ≤ _ := sum_avoidanceDefect_le hsize hhit
  have hcancel : (C.card - 1) * avoidanceDefect A B ≤ 2 * (m * m) * q := by
    apply Nat.le_of_mul_le_mul_left (c := C.card) _ (by omega)
    nlinarith
  have hq : 8 * q ≤ C.card - 1 := by omega
  have hmul := Nat.mul_le_mul_right (m * m) hq
  apply Nat.le_of_mul_le_mul_left (c := C.card - 1) _ (by omega)
  nlinarith

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ExtractionCounting

section OriginalModule_LinearCrossingFamilies_ExtractionClusters

/-!
## Sufficient geometric cluster data for fixed-parameter extraction

Pairwise separated equal-sized clusters that retain half the input points and
whose hit-cluster union has small mass provide the required near-avoiding pair.
The required arrangement and subdivision are constructed in the later sections
on separated clusters and small-zone arrangements.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance extractionClustersDecEqPoint : DecidableEq Point := Classical.decEq _

def hitClusterPoints (C : Finset (Finset Point)) (e : Sym2 Point) : Finset Point :=
  (hitClusters C e).biUnion id

theorem card_hitClusterPoints {C : Finset (Finset Point)} {m : ℕ}
    (hsize : ∀ A ∈ C, A.card = m)
    (hsep : (C : Set (Finset Point)).Pairwise Separated) (e : Sym2 Point) :
    (hitClusterPoints C e).card = (hitClusters C e).card * m := by
  classical
  have hdis : (hitClusters C e : Set (Finset Point)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    exact (hsep (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hAB).disjoint
  rw [hitClusterPoints, Finset.card_biUnion hdis]
  calc
    _ = ∑ _A ∈ hitClusters C e, m := Finset.sum_congr rfl (fun A hA =>
      hsize A (Finset.mem_filter.mp hA).1)
    _ = _ := by simp

/-- The counting half of fixed-parameter PRT extraction. The hypotheses are
concrete finite cluster data, not an assumed extraction theorem. -/
theorem exists_near_avoiding_pair_of_clusters {P : Finset Point}
    {C : Finset (Finset Point)} {m : ℕ} (hm : 1 ≤ m)
    (hsub : ∀ A ∈ C, A ⊆ P) (hsize : ∀ A ∈ C, A.card = m)
    (hsep : (C : Set (Finset Point)).Pairwise Separated)
    (hcount : 4 ≤ C.card) (hcover : P.card ≤ 2 * C.card * m)
    (hzone : ∀ A ∈ C, ∀ e ∈ spannedPairs A, 32 * (hitClusterPoints C e).card ≤ P.card) :
    ∃ A B : Finset Point, A ⊆ P ∧ B ⊆ P ∧ Separated A B ∧
      A.card = m ∧ B.card = m ∧ (avoidanceDefect A B : ℝ) ≤ (m : ℝ) ^ 2 / 4 := by
  have hhit : ∀ A ∈ C, ∀ e ∈ spannedPairs A, (hitClusters C e).card ≤ C.card / 16 := by
    intro A hA e he
    have hz := (hzone A hA e he).trans hcover
    rw [card_hitClusterPoints hsize hsep] at hz
    have hmass : 16 * (hitClusters C e).card ≤ C.card := by
      apply Nat.le_of_mul_le_mul_left (c := 2 * m) _ (by omega)
      nlinarith
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 16)).mpr (by omega)
  have hmany : 8 * (C.card / 16) + 2 ≤ C.card := by omega
  obtain ⟨A, hA, B, hB, hAB, hdef⟩ := exists_cluster_pair_small_defect hsize hhit hmany
  refine ⟨A, B, hsub A hA, hsub B hB, hsep hA hB hAB, hsize A hA, hsize B hB, ?_⟩
  have hR : 4 * (avoidanceDefect A B : ℝ) ≤ (m : ℝ) * m := by exact_mod_cast hdef
  nlinarith

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ExtractionClusters

section OriginalModule_LinearCrossingFamilies_ClusterProjection

/-! ## A separating projection and ordered enumeration for finite point sets -/

namespace LinearCrossingFamilies

noncomputable section

local instance clusterProjectionDecEqPoint : DecidableEq Point := Classical.decEq _

def shearProjection (t : ℝ) : Point →ₗ[ℝ] ℝ where
  toFun p := p.1 + t * p.2
  map_add' p q := by simp; ring
  map_smul' c p := by simp; ring

/-- A finite set has an injective linear projection. No general-position
assumption and no perturbation of the input points is needed. -/
theorem exists_injective_projection (P : Finset Point) :
    ∃ l : Point →ₗ[ℝ] ℝ, Set.InjOn l (P : Set Point) := by
  classical
  let forbidden := P.offDiag.image (fun z => (z.2.1 - z.1.1) / (z.1.2 - z.2.2))
  obtain ⟨t, ht⟩ := forbidden.exists_notMem
  refine ⟨shearProjection t, ?_⟩
  intro p hp q hq heq
  by_contra hpq
  have hval : p.1 + t * p.2 = q.1 + t * q.2 := heq
  by_cases hsecond : p.2 = q.2
  · have hfirst : p.1 = q.1 := by rw [hsecond] at hval; linarith
    exact hpq (Prod.ext hfirst hsecond)
  · apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, ?_⟩
    exact (div_eq_iff (sub_ne_zero.mpr hsecond)).mpr (by nlinarith)

/-- Enumerate a finite point set in strictly increasing projection order. -/
theorem exists_ordered_enumeration (P : Finset Point) {f : Point → ℝ}
    (hf : Set.InjOn f (P : Set Point)) :
    ∃ e : Fin P.card → Point, Function.Injective e ∧ (∀ i, e i ∈ P) ∧
      (∀ p ∈ P, ∃ i, e i = p) ∧ StrictMono (fun i => f (e i)) := by
  classical
  let S := P.image f
  have hcard : S.card = P.card := Finset.card_image_of_injOn hf
  let v := S.orderEmbOfFin hcard
  have hv : ∀ i : Fin P.card, ∃ p ∈ P, f p = v i := fun i =>
    Finset.mem_image.mp (S.orderEmbOfFin_mem hcard i)
  choose e heP hfe using hv
  refine ⟨e, ?_, heP, ?_, ?_⟩
  · intro i j hij
    apply v.injective
    rw [← hfe i, ← hfe j, hij]
  · intro p hp
    have hfp : f p ∈ S := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    change f p ∈ (S : Set ℝ) at hfp
    rw [← S.range_orderEmbOfFin hcard] at hfp
    obtain ⟨i, hi⟩ := hfp
    exact ⟨i, hf (heP i) hp ((hfe i).trans hi)⟩
  · intro i j hij
    dsimp only
    rw [hfe i, hfe j]
    exact v.strictMono hij

/-- Strictly ordered projection values on two finite sets imply disjoint
convex hulls. Convexity extends the inequality in each variable in turn. -/
theorem separated_of_projection_lt {A B : Finset Point} (l : Point →ₗ[ℝ] ℝ)
    (h : ∀ a ∈ A, ∀ b ∈ B, l a < l b) : Separated A B := by
  have hl : IsLinearMap ℝ l := l.isLinear
  have hleft : ∀ b ∈ B, ∀ x ∈ convexHull ℝ (A : Set Point), l x < l b := by
    intro b hb
    exact convexHull_min (fun a ha => h a ha b hb) (convex_halfSpace_lt hl (l b))
  have hboth : ∀ x ∈ convexHull ℝ (A : Set Point),
      ∀ y ∈ convexHull ℝ (B : Set Point), l x < l y := by
    intro x hx
    exact convexHull_min (fun b hb => hleft b hb x hx) (convex_halfSpace_gt hl (l x))
  exact Set.disjoint_left.mpr (fun x hx hy => (hboth x hx x hy).false)

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ClusterProjection

section OriginalModule_LinearCrossingFamilies_ClusterBlocks

/-! ## Splitting a finite point set into equal-sized separated clusters -/

namespace LinearCrossingFamilies

noncomputable section

local instance clusterBlocksDecEqPoint : DecidableEq Point := Classical.decEq _

/-- Index into the `j`th full block of length `m`. -/
def blockIndex {n m : ℕ} (j : Fin (n / m)) (r : Fin m) : Fin n := by
  refine ⟨j.val * m + r.val, ?_⟩
  have hmul := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr j.isLt)
  have hdiv := Nat.div_mul_le_self n m
  have hr := r.isLt
  nlinarith

theorem blockIndex_strict_order {n m : ℕ} {i j : Fin (n / m)} (hij : i < j)
    (r s : Fin m) : blockIndex i r < blockIndex j s := by
  change i.val * m + r.val < j.val * m + s.val
  have hmul := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hij)
  have hr := r.isLt
  nlinarith

def blockCluster {n : ℕ} (e : Fin n → Point) (m : ℕ) (j : Fin (n / m)) : Finset Point :=
  Finset.univ.image (fun r : Fin m => e (blockIndex j r))

theorem card_blockCluster {n m : ℕ} {e : Fin n → Point} (he : Function.Injective e)
    (j : Fin (n / m)) : (blockCluster e m j).card = m := by
  classical
  have hblock : Function.Injective (fun r : Fin m => e (blockIndex j r)) := by
    intro r s hrs
    have h := congrArg Fin.val (he hrs)
    apply Fin.ext
    change j.val * m + r.val = j.val * m + s.val at h
    omega
  rw [blockCluster, Finset.card_image_of_injective _ hblock, Finset.card_univ, Fintype.card_fin]

theorem blockCluster_subset {P : Finset Point} {e : Fin P.card → Point}
    (heP : ∀ i, e i ∈ P) {m : ℕ} (j : Fin (P.card / m)) : blockCluster e m j ⊆ P := by
  intro p hp
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
  exact heP _

theorem separated_blockClusters {n m : ℕ} {e : Fin n → Point}
    (l : Point →ₗ[ℝ] ℝ) (hmono : StrictMono (fun i => l (e i)))
    {i j : Fin (n / m)} (hij : i ≠ j) : Separated (blockCluster e m i) (blockCluster e m j) := by
  have hforward : ∀ i j : Fin (n / m), i < j →
      Separated (blockCluster e m i) (blockCluster e m j) := by
    intro i j hij
    apply separated_of_projection_lt l
    intro a ha b hb
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hb
    exact hmono (blockIndex_strict_order hij r s)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hforward i j hlt
  · exact (hforward j i hgt).symm

/-- Parallel cuts ordered by an injective projection produce full `m`-point
clusters, with fewer than `m` points left over. Their hulls are pairwise disjoint. -/
theorem exists_separated_equal_clusters (P : Finset Point) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : Finset (Finset Point), (∀ A ∈ C, A ⊆ P) ∧
      (∀ A ∈ C, A.card = m) ∧ (C : Set (Finset Point)).Pairwise Separated ∧
      C.card = P.card / m ∧ (P \ C.biUnion id).card < m := by
  classical
  obtain ⟨l, hl⟩ := exists_injective_projection P
  obtain ⟨e, he, heP, _, hmono⟩ := exists_ordered_enumeration P hl
  let C := Finset.univ.image (blockCluster e m)
  have hsub : ∀ A ∈ C, A ⊆ P := by
    intro A hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
    exact blockCluster_subset heP j
  have hsize : ∀ A ∈ C, A.card = m := by
    intro A hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
    exact card_blockCluster he j
  have hsep : (C : Set (Finset Point)).Pairwise Separated := by
    intro A hA B hB hAB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact separated_blockClusters l hmono (fun hij => hAB (hij ▸ rfl))
  have hinj : Function.Injective (blockCluster e m) := by
    intro i j hij
    by_contra hne
    have hdis := (separated_blockClusters l hmono hne).disjoint
    have hnon : (blockCluster e m i).Nonempty := Finset.card_pos.mp (by
      rw [card_blockCluster he]
      omega)
    obtain ⟨p, hp⟩ := hnon
    exact Finset.disjoint_left.mp hdis hp (hij ▸ hp)
  have hcard : C.card = P.card / m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hdis : (C : Set (Finset Point)).PairwiseDisjoint id := fun _ hA _ hB hAB =>
    (hsep hA hB hAB).disjoint
  have hunion : (C.biUnion id).card = C.card * m := by
    rw [Finset.card_biUnion hdis]
    calc
      _ = ∑ _A ∈ C, m := Finset.sum_congr rfl hsize
      _ = _ := by simp
  have hunionSub : C.biUnion id ⊆ P := by
    intro p hp
    obtain ⟨A, hA, hpA⟩ := Finset.mem_biUnion.mp hp
    exact hsub A hA hpA
  refine ⟨C, hsub, hsize, hsep, hcard, ?_⟩
  have htotal := Finset.card_sdiff_add_card_eq_card hunionSub
  rw [hunion, hcard] at htotal
  have hrem := Nat.mod_lt P.card (by omega : 0 < m)
  have hdiv := Nat.mod_add_div P.card m
  nlinarith

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ClusterBlocks

section OriginalModule_LinearCrossingFamilies_ClusterRefinement

/-! ## Refining separated cells into equal-sized clusters -/

namespace LinearCrossingFamilies

noncomputable section

local instance clusterRefinementDecEqPoint : DecidableEq Point := Classical.decEq _

theorem Separated.mono {A B C D : Finset Point} (h : Separated C D)
    (hAC : A ⊆ C) (hBD : B ⊆ D) : Separated A B := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact Set.disjoint_left.mp h (convexHull_mono hAC hp) (convexHull_mono hBD hq)

/-- Refine every cell independently. Each output cluster has a parent cell,
and fewer than `m` points per parent are omitted. -/
theorem exists_equal_cluster_refinement (D : Finset (Finset Point)) {m : ℕ} (hm : 1 ≤ m)
    (hDsep : (D : Set (Finset Point)).Pairwise Separated) :
    ∃ C : Finset (Finset Point),
      (∀ A ∈ C, ∃ Q ∈ D, A ⊆ Q) ∧ (∀ A ∈ C, A.card = m) ∧
      (C : Set (Finset Point)).Pairwise Separated ∧
      (D.biUnion id).card ≤ C.card * m + D.card * (m - 1) := by
  classical
  choose F hsub hsize hsep hcard _ using
    (fun Q : Finset Point => exists_separated_equal_clusters Q hm)
  let C := D.biUnion F
  have hparent : ∀ A ∈ C, ∃ Q ∈ D, A ⊆ Q := by
    intro A hA
    obtain ⟨Q, hQ, hAQ⟩ := Finset.mem_biUnion.mp hA
    exact ⟨Q, hQ, hsub Q A hAQ⟩
  have hCsize : ∀ A ∈ C, A.card = m := by
    intro A hA
    obtain ⟨Q, _, hAQ⟩ := Finset.mem_biUnion.mp hA
    exact hsize Q A hAQ
  have hCsep : (C : Set (Finset Point)).Pairwise Separated := by
    intro A hA B hB hAB
    obtain ⟨Q, hQ, hAQ⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨R, hR, hBR⟩ := Finset.mem_biUnion.mp hB
    by_cases hQR : Q = R
    · subst R
      exact hsep Q hAQ hBR hAB
    · exact (hDsep hQ hR hQR).mono (hsub Q A hAQ) (hsub R B hBR)
  have hFdis : (D : Set (Finset Point)).PairwiseDisjoint F := by
    intro Q hQ R hR hQR
    apply Finset.disjoint_left.mpr
    intro A hAQ hAR
    have hnon : A.Nonempty := Finset.card_pos.mp (by rw [hsize Q A hAQ]; omega)
    obtain ⟨p, hp⟩ := hnon
    exact Finset.disjoint_left.mp (hDsep hQ hR hQR).disjoint
      (hsub Q A hAQ hp) (hsub R A hAR hp)
  have hCcard : C.card = ∑ Q ∈ D, (F Q).card := Finset.card_biUnion hFdis
  have hDdis : (D : Set (Finset Point)).PairwiseDisjoint id :=
    fun _ hQ _ hR hQR => (hDsep hQ hR hQR).disjoint
  refine ⟨C, hparent, hCsize, hCsep, ?_⟩
  rw [Finset.card_biUnion hDdis, hCcard]
  calc
    _ ≤ ∑ Q ∈ D, ((F Q).card * m + (m - 1)) := by
      apply Finset.sum_le_sum
      intro Q _
      rw [hcard Q]
      have hrem := Nat.mod_lt Q.card (by omega : 0 < m)
      have hdiv := Nat.mod_add_div Q.card m
      dsimp only [id]
      rw [Nat.mul_comm m] at hdiv
      omega
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, smul_eq_mul]

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ClusterRefinement

section OriginalModule_LinearCrossingFamilies_ArrangementCells

/-!
## Finite line-arrangement cells and zones

Cells are intersections of strict sides of finitely many oriented lines. This
sign-vector representation gives convex cells directly; the coarse `2^r` cell
bound is sufficient for the fixed-parameter extraction needed here.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance arrangementCellsDecEqPoint : DecidableEq Point := Classical.decEq _

def cellRegion (L : Finset (Point × Point)) (σ : L → Bool) : Set Point :=
  {p | ∀ l : L, if σ l then 0 < orientation l.val.1 l.val.2 p
    else orientation l.val.1 l.val.2 p < 0}

def cellPoints (P : Finset Point) (L : Finset (Point × Point)) (σ : L → Bool) : Finset Point := by
  classical
  exact P.filter (fun p => p ∈ cellRegion L σ)

def arrangementCells (P : Finset Point) (L : Finset (Point × Point)) : Finset (Finset Point) :=
  Finset.univ.image (cellPoints P L)

def arrangementZone (P : Finset Point) (L : Finset (Point × Point)) (e : Sym2 Point) :
    Finset Point := by
  classical
  exact P.filter (fun p => ∃ σ : L → Bool, p ∈ cellRegion L σ ∧
    (supportingLine e ∩ cellRegion L σ).Nonempty)

theorem convex_cellRegion (L : Finset (Point × Point)) (σ : L → Bool) :
    Convex ℝ (cellRegion L σ) := by
  apply convex_iff_add_mem.mpr
  intro x hx y hy u v hu hv huv l
  have hi : Convex ℝ {p | if σ l then 0 < orientation l.val.1 l.val.2 p
      else orientation l.val.1 l.val.2 p < 0} := by
    cases hσ : σ l
    · simpa only [hσ, Bool.false_eq_true, ite_false] using convex_orientation_neg l.val.1 l.val.2
    · simpa only [hσ, ite_true] using convex_orientation_pos l.val.1 l.val.2
  exact hi (hx l) (hy l) hu hv huv

theorem cellPoints_subset (P : Finset Point) (L : Finset (Point × Point)) (σ : L → Bool) :
    cellPoints P L σ ⊆ P := by
  classical
  exact Finset.filter_subset _ _

theorem hull_cellPoints_subset (P : Finset Point) (L : Finset (Point × Point)) (σ : L → Bool) :
    convexHull ℝ (cellPoints P L σ : Set Point) ⊆ cellRegion L σ := by
  classical
  exact convexHull_min (fun _ hp => (Finset.mem_filter.mp hp).2) (convex_cellRegion L σ)

theorem cellRegion_disjoint {L : Finset (Point × Point)} {σ τ : L → Bool} (h : σ ≠ τ) :
    Disjoint (cellRegion L σ) (cellRegion L τ) := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp h
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hp' := hp l
  have hq' := hq l
  cases hσ : σ l <;> cases hτ : τ l <;> simp_all
  all_goals linarith

theorem cellPoints_separated {P : Finset Point} {L : Finset (Point × Point)}
    {σ τ : L → Bool} (h : σ ≠ τ) : Separated (cellPoints P L σ) (cellPoints P L τ) :=
  (cellRegion_disjoint h).mono (hull_cellPoints_subset P L σ) (hull_cellPoints_subset P L τ)

theorem arrangementCells_subset (P : Finset Point) (L : Finset (Point × Point)) :
    ∀ Q ∈ arrangementCells P L, Q ⊆ P := by
  intro Q hQ
  obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hQ
  exact cellPoints_subset P L σ

theorem arrangementCells_separated (P : Finset Point) (L : Finset (Point × Point)) :
    (arrangementCells P L : Set (Finset Point)).Pairwise Separated := by
  intro Q hQ R hR hQR
  obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hR
  exact cellPoints_separated (fun h => hQR (h ▸ rfl))

theorem card_arrangementCells_le (P : Finset Point) (L : Finset (Point × Point)) :
    (arrangementCells P L).card ≤ 2 ^ L.card := by
  calc
    _ ≤ (Finset.univ : Finset (L → Bool)).card := Finset.card_image_le
    _ = _ := by simp

/-- Every point off the arrangement lines belongs to a sign-vector cell. -/
theorem mem_cell_of_off_lines {P : Finset Point} {L : Finset (Point × Point)} {p : Point}
    (hp : p ∈ P) (hoff : ∀ l ∈ L, orientation l.1 l.2 p ≠ 0) :
    p ∈ (arrangementCells P L).biUnion id := by
  classical
  let σ : L → Bool := fun l => decide (0 < orientation l.val.1 l.val.2 p)
  have hregion : p ∈ cellRegion L σ := by
    intro l
    by_cases hpos : 0 < orientation l.val.1 l.val.2 p
    · simp [σ, hpos]
    · simpa [σ, hpos] using lt_of_le_of_ne (le_of_not_gt hpos) (hoff l.val l.property)
  exact Finset.mem_biUnion.mpr ⟨cellPoints P L σ,
    Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩, Finset.mem_filter.mpr ⟨hp, hregion⟩⟩

/-- A hit subcluster puts all points of its parent cell in the line's zone. -/
theorem cell_subset_zone_of_hull_hit {P A Q : Finset Point} {L : Finset (Point × Point)}
    (hQ : Q ∈ arrangementCells P L) (hAQ : A ⊆ Q) {e : Sym2 Point}
    (hhit : LineMeetsConvexHull e A) : Q ⊆ arrangementZone P L e := by
  classical
  obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨x, hline, hx⟩ := hhit
  have hxregion := hull_cellPoints_subset P L σ (convexHull_mono hAQ hx)
  intro p hp
  obtain ⟨hpP, hpregion⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpP, σ, hpregion, x, hline, hxregion⟩

theorem hitClusterPoints_subset_zone {P : Finset Point} {L : Finset (Point × Point)}
    {C : Finset (Finset Point)}
    (hparent : ∀ A ∈ C, ∃ Q ∈ arrangementCells P L, A ⊆ Q) (e : Sym2 Point) :
    hitClusterPoints C e ⊆ arrangementZone P L e := by
  classical
  intro p hp
  obtain ⟨A, hA, hpA⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hAC, hhit⟩ := Finset.mem_filter.mp hA
  obtain ⟨Q, hQ, hAQ⟩ := hparent A hAC
  exact cell_subset_zone_of_hull_hit hQ hAQ hhit (hAQ hpA)

def boundaryPoints (P : Finset Point) (L : Finset (Point × Point)) : Finset Point := by
  classical
  exact P.filter (fun p => ∃ l ∈ L, orientation l.1 l.2 p = 0)

theorem card_boundaryPoints_le {P : Finset Point} (hP : GeneralPosition P)
    {L : Finset (Point × Point)} (hL : L ⊆ P.offDiag) : (boundaryPoints P L).card ≤ 2 * L.card := by
  classical
  have hsub : boundaryPoints P L ⊆ L.biUnion (fun l => {l.1, l.2}) := by
    intro p hp
    obtain ⟨hpP, l, hl, hzero⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp (hL hl)
    have hmem : p ∈ ({l.1, l.2} : Finset Point) := by
      by_cases hpa : p = l.1
      · simp [hpa]
      by_cases hpb : p = l.2
      · simp [hpb]
      exact (hP ha hb hpP hab (Ne.symm hpa) (Ne.symm hpb) hzero).elim
    exact Finset.mem_biUnion.mpr ⟨l, hl, hmem⟩
  calc
    _ ≤ (L.biUnion (fun l => {l.1, l.2})).card := Finset.card_le_card hsub
    _ ≤ ∑ l ∈ L, ({l.1, l.2} : Finset Point).card := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ L, 2 := Finset.sum_le_sum (fun l _ => by
      simpa using Finset.card_insert_le l.1 ({l.2} : Finset Point))
    _ = _ := by simp [Nat.mul_comm]

theorem card_le_cells_add_boundary {P : Finset Point} (hP : GeneralPosition P)
    {L : Finset (Point × Point)} (hL : L ⊆ P.offDiag) :
    P.card ≤ ((arrangementCells P L).biUnion id).card + 2 * L.card := by
  classical
  have hsub : P ⊆ (arrangementCells P L).biUnion id ∪ boundaryPoints P L := by
    intro p hp
    by_cases hb : p ∈ boundaryPoints P L
    · exact Finset.mem_union_right _ hb
    · apply Finset.mem_union_left
      apply mem_cell_of_off_lines hp
      intro l hl hzero
      exact hb (Finset.mem_filter.mpr ⟨hp, l, hl, hzero⟩)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact h.trans (Nat.add_le_add_left (card_boundaryPoints_le hP hL) _)

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ArrangementCells

section OriginalModule_LinearCrossingFamilies_ExtractionFromZones

/-!
## Fixed-parameter extraction from a small-zone arrangement

Given a bounded-size small-zone arrangement, the cluster construction and
counting arguments establish fixed-parameter extraction. The required arrangement
is constructed in `exists_bounded_small_zone_arrangement` below.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance extractionFromZonesDecEqPoint : DecidableEq Point := Classical.decEq _

/-- For fixed extraction parameters, the exponential cell bound only changes
an absolute constant. Optimal polynomial dependence on the error is not needed. -/
def zoneExtractionThreshold (r : ℕ) : ℕ := 8 + 2 * (2 ^ r + 2 * r)

theorem zoneExtractionThreshold_mono : Monotone zoneExtractionThreshold := by
  intro r s hrs
  unfold zoneExtractionThreshold
  gcongr

theorem exists_near_avoiding_pair_of_arrangement {P : Finset Point}
    (hP : GeneralPosition P) {L : Finset (Point × Point)} (hL : L ⊆ P.offDiag)
    {m : ℕ} (hm : 1 ≤ m) (hlarge : zoneExtractionThreshold L.card * m ≤ P.card)
    (hzone : ∀ e ∈ spannedPairs P, 32 * (arrangementZone P L e).card ≤ P.card) :
    ∃ A B : Finset Point, A ⊆ P ∧ B ⊆ P ∧ Separated A B ∧
      A.card = m ∧ B.card = m ∧ (avoidanceDefect A B : ℝ) ≤ (m : ℝ) ^ 2 / 4 := by
  let D := arrangementCells P L
  obtain ⟨C, hparent, hsize, hsep, hretained⟩ :=
    exists_equal_cluster_refinement D hm (arrangementCells_separated P L)
  have hsub : ∀ A ∈ C, A ⊆ P := by
    intro A hA
    obtain ⟨Q, hQ, hAQ⟩ := hparent A hA
    exact hAQ.trans (arrangementCells_subset P L Q hQ)
  have hcells : D.card ≤ 2 ^ L.card := card_arrangementCells_le P L
  have hboundary := card_le_cells_add_boundary hP hL
  have hdiscard : D.card * (m - 1) + 2 * L.card ≤ (2 ^ L.card + 2 * L.card) * m := by
    have h₁ := Nat.mul_le_mul hcells (Nat.sub_le m 1)
    have h₂ := Nat.mul_le_mul_left (2 * L.card) hm
    nlinarith
  have hcover₁ : P.card ≤ C.card * m + (2 ^ L.card + 2 * L.card) * m := by
    change P.card ≤ (D.biUnion id).card + 2 * L.card at hboundary
    omega
  unfold zoneExtractionThreshold at hlarge
  have hcover : P.card ≤ 2 * C.card * m := by nlinarith
  have hcount : 4 ≤ C.card := by
    by_contra hn
    have hC : C.card ≤ 3 := by omega
    have hmul := Nat.mul_le_mul_right m hC
    nlinarith
  apply exists_near_avoiding_pair_of_clusters hm hsub hsize hsep hcount hcover
  intro A hA e he
  have heP : e ∈ spannedPairs P := mem_spannedPairs.mpr
    ⟨fun p hp => hsub A hA ((mem_spannedPairs.mp he).1 p hp), (mem_spannedPairs.mp he).2⟩
  exact (Nat.mul_le_mul_left 32 (Finset.card_le_card
    (hitClusterPoints_subset_zone hparent e))).trans (hzone e heP)

/-- An explicit reduction to the small-zone theorem. This reusable implication
is conditional; its existence hypothesis is proved in
`exists_bounded_small_zone_arrangement`. -/
theorem linearCrossingFamilies_of_small_zones
    (hzones : ∃ r : ℕ, ∀ P : Finset Point, GeneralPosition P →
      ∃ L : Finset (Point × Point), L ⊆ P.offDiag ∧ L.card ≤ r ∧
        ∀ e ∈ spannedPairs P, 32 * (arrangementZone P L e).card ≤ P.card) :
    LinearCrossingFamiliesStatement := by
  obtain ⟨r, hz⟩ := hzones
  apply linearCrossingFamilies_of_fixed_extraction
  refine ⟨zoneExtractionThreshold r, by unfold zoneExtractionThreshold; omega, ?_⟩
  intro P m hP hm hlarge
  obtain ⟨L, hL, hcard, hzone⟩ := hz P hP
  apply exists_near_avoiding_pair_of_arrangement hP hL hm _ hzone
  exact (Nat.mul_le_mul_right m (zoneExtractionThreshold_mono hcard)).trans hlarge

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ExtractionFromZones

section OriginalModule_LinearCrossingFamilies_HalfplaneTraces

/-!
## Finite half-plane and sector traces

Radon's theorem bounds the shattering dimension of planar half-planes by three.
This is the range-complexity ingredient for the finite ε-net construction
proved in `exists_sector_epsilon_net` below.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance halfplaneTracesDecEqPoint : DecidableEq Point := Classical.decEq _

def halfplaneTraces (P : Finset Point) : Finset (Finset Point) := by
  classical
  exact P.powerset.filter (fun S => ∃ (l : Point →ₗ[ℝ] ℝ) (c : ℝ),
    S = P.filter (fun p => l p < c))

def sectorTraces (P : Finset Point) : Finset (Finset Point) :=
  (halfplaneTraces P ×ˢ halfplaneTraces P).image (fun z => z.1 ∩ z.2)

theorem subset_of_mem_halfplaneTraces {P S : Finset Point} (hS : S ∈ halfplaneTraces P) :
    S ⊆ P := by
  classical
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1

theorem subset_of_shattered_halfplaneTraces {P S : Finset Point}
    (hs : (halfplaneTraces P).Shatters S) : S ⊆ P := by
  obtain ⟨U, hU, hSU⟩ := hs.exists_superset
  exact hSU.trans (subset_of_mem_halfplaneTraces hU)

/-- A set shattered by strict half-planes must be affinely independent. -/
theorem affineIndependent_of_shattered_halfplaneTraces {P S : Finset Point}
    (hs : (halfplaneTraces P).Shatters S) : AffineIndependent ℝ (fun p : S => (p : Point)) := by
  classical
  by_contra hdep
  obtain ⟨I, x, hxI, hxJ⟩ := Convex.radon_partition hdep
  let T := (S.attach.filter (fun p => p ∈ I)).image (fun p : S => (p : Point))
  have hTS : T ⊆ S := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  have hT : ∀ p : S, p.val ∈ T ↔ p ∈ I := by
    intro p
    simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨q, hq, heq⟩
      exact (Subtype.ext heq) ▸ hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  obtain ⟨U, hU, hUT⟩ := hs hTS
  obtain ⟨_, l, c, hUeq⟩ := Finset.mem_filter.mp hU
  have hSP := subset_of_shattered_halfplaneTraces hs
  have hleft : (fun p : S => (p : Point)) '' I ⊆ {p | l p < c} := by
    rintro _ ⟨p, hp, rfl⟩
    have hpT := (hT p).mpr hp
    rw [← hUT] at hpT
    have hpU := (Finset.mem_inter.mp hpT).2
    rw [hUeq] at hpU
    exact (Finset.mem_filter.mp hpU).2
  have hright : (fun p : S => (p : Point)) '' Iᶜ ⊆ {p | c ≤ l p} := by
    rintro _ ⟨p, hp, rfl⟩
    change c ≤ l (p : Point)
    apply le_of_not_gt
    intro hlt
    have hpU : p.val ∈ U := hUeq.symm ▸ Finset.mem_filter.mpr ⟨hSP p.property, hlt⟩
    have hpT : p.val ∈ T := hUT ▸ Finset.mem_inter.mpr ⟨p.property, hpU⟩
    exact hp ((hT p).mp hpT)
  have hxlt : l x < c := convexHull_min hleft (convex_halfSpace_lt l.isLinear c) hxI
  have hxge : c ≤ l x := convexHull_min hright (convex_halfSpace_ge l.isLinear c) hxJ
  exact (not_lt_of_ge hxge) hxlt

theorem card_shattered_halfplaneTraces_le_three {P S : Finset Point}
    (hs : (halfplaneTraces P).Shatters S) : S.card ≤ 3 := by
  have hi := affineIndependent_of_shattered_halfplaneTraces hs
  have hdim := hi.card_le_finrank_succ
  have hspan := Submodule.finrank_le (vectorSpan ℝ (Set.range (fun p : S => (p : Point))))
  have hplane : Module.finrank ℝ Point = 2 := by simp [Point, Module.finrank_prod]
  rw [hplane] at hspan
  simp only [Fintype.card_coe] at hdim
  omega

theorem vcDim_halfplaneTraces_le_three (P : Finset Point) : (halfplaneTraces P).vcDim ≤ 3 := by
  unfold Finset.vcDim
  apply Finset.sup_le
  intro S hS
  exact card_shattered_halfplaneTraces_le_three (Finset.mem_shatterer.mp hS)

/-- A finite Sauer bound without requiring the ambient real plane to be finite. -/
theorem card_halfplaneTraces_le (P : Finset Point) :
    (halfplaneTraces P).card ≤ ∑ k ∈ Finset.range 4, P.card.choose k := by
  classical
  have hsub : (halfplaneTraces P).shatterer ⊆
      (Finset.range 4).biUnion (fun k => P.powersetCard k) := by
    intro S hS
    have hs := Finset.mem_shatterer.mp hS
    exact Finset.mem_biUnion.mpr ⟨S.card,
      Finset.mem_range.mpr (by have := card_shattered_halfplaneTraces_le_three hs; omega),
      Finset.mem_powersetCard.mpr ⟨subset_of_shattered_halfplaneTraces hs, rfl⟩⟩
  calc
    _ ≤ (halfplaneTraces P).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ((Finset.range 4).biUnion (fun k => P.powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range 4, (P.powersetCard k).card := Finset.card_biUnion_le
    _ = _ := by simp only [Finset.card_powersetCard]

theorem card_sectorTraces_le (P : Finset Point) :
    (sectorTraces P).card ≤ (∑ k ∈ Finset.range 4, P.card.choose k) ^ 2 := by
  calc
    _ ≤ (halfplaneTraces P ×ˢ halfplaneTraces P).card := Finset.card_image_le
    _ = (halfplaneTraces P).card * (halfplaneTraces P).card := Finset.card_product _ _
    _ ≤ (∑ k ∈ Finset.range 4, P.card.choose k) * (∑ k ∈ Finset.range 4, P.card.choose k) :=
      Nat.mul_le_mul (card_halfplaneTraces_le P) (card_halfplaneTraces_le P)
    _ = _ := (pow_two _).symm

theorem inter_mem_halfplaneTraces {P S U : Finset Point} (hSP : S ⊆ P)
    (hU : U ∈ halfplaneTraces P) : S ∩ U ∈ halfplaneTraces S := by
  classical
  obtain ⟨_, l, c, hUeq⟩ := Finset.mem_filter.mp hU
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_left, l, c, ?_⟩
  ext p
  by_cases hp : p ∈ S
  · simp only [Finset.mem_inter, hp, true_and, hUeq, Finset.mem_filter, hSP hp]
  · simp only [Finset.mem_inter, hp, false_and, Finset.mem_filter]

theorem inter_mem_sectorTraces {P S U : Finset Point} (hSP : S ⊆ P)
    (hU : U ∈ sectorTraces P) : S ∩ U ∈ sectorTraces S := by
  obtain ⟨⟨V, W⟩, hVW, rfl⟩ := Finset.mem_image.mp hU
  obtain ⟨hV, hW⟩ := Finset.mem_product.mp hVW
  refine Finset.mem_image.mpr ⟨(S ∩ V, S ∩ W),
    Finset.mem_product.mpr ⟨inter_mem_halfplaneTraces hSP hV, inter_mem_halfplaneTraces hSP hW⟩, ?_⟩
  ext p
  simp only [Finset.mem_inter]
  tauto

/-- Uniform bound on the number of sector traces on any finite subsample. -/
theorem card_sector_restriction_le {P S : Finset Point} (hSP : S ⊆ P) :
    ((sectorTraces P).image (fun U => S ∩ U)).card ≤
      (∑ k ∈ Finset.range 4, S.card.choose k) ^ 2 := by
  apply le_trans (Finset.card_le_card (t := sectorTraces S) ?_) (card_sectorTraces_le S)
  intro V hV
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hV
  exact inter_mem_sectorTraces hSP hU

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_HalfplaneTraces

section OriginalModule_LinearCrossingFamilies_FiniteSampling

/-!
## Finite sampling counts

These counting lemmas are the lower-bound half of the fixed-density ε-net
argument. All samples are finite tuples with replacement; no randomness axiom
or probabilistic oracle is used.
-/

namespace LinearCrossingFamilies

open scoped BigOperators

theorem reverse_markov_card {α : Type*} (S : Finset α) (f : α → ℕ) {a b : ℕ}
    (ha : 0 < a) (hmean : 2 * a * S.card ≤ ∑ x ∈ S, f x)
    (hmax : ∀ x ∈ S, f x ≤ b * a) :
    S.card ≤ b * (S.filter (fun x => a ≤ f x)).card := by
  classical
  have hgood : (∑ x ∈ S.filter (fun x => a ≤ f x), f x) ≤
      (S.filter (fun x => a ≤ f x)).card * (b * a) := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => a ≤ f x), b * a :=
        Finset.sum_le_sum (fun x hx => hmax x (Finset.mem_filter.mp hx).1)
      _ = _ := by simp
  have hbad : (∑ x ∈ S.filter (fun x => ¬a ≤ f x), f x) ≤ S.card * a := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => ¬a ≤ f x), a := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ = (S.filter (fun x => ¬a ≤ f x)).card * a := by simp
      _ ≤ _ := Nat.mul_le_mul_right a (Finset.card_filter_le _ _)
  have hsum := Finset.sum_filter_add_sum_filter_not S (fun x => a ≤ f x) f
  apply Nat.le_of_mul_le_mul_left (c := a) _ ha
  nlinarith

def sampleHits {α : Type*} [DecidableEq α] (R : Finset α) {s : ℕ} (x : Fin s → α) : ℕ :=
  (Finset.univ.filter (fun i => x i ∈ R)).card

theorem sampleHits_le {α : Type*} [DecidableEq α] (R : Finset α) {s : ℕ} (x : Fin s → α) :
    sampleHits R x ≤ s := by
  simpa only [sampleHits, Finset.card_univ, Fintype.card_fin] using Finset.card_filter_le
    (s := (Finset.univ : Finset (Fin s))) (fun i => x i ∈ R)

theorem sampleHits_eq_sum {α : Type*} [DecidableEq α] (R : Finset α) {s : ℕ} (x : Fin s → α) :
    sampleHits R x = ∑ i : Fin s, if x i ∈ R then 1 else 0 := by
  exact Finset.card_filter _ _

theorem sampleHits_cons {α : Type*} [DecidableEq α] (R : Finset α) {s : ℕ}
    (a : α) (x : Fin s → α) :
    sampleHits R (Fin.cons a x) = (if a ∈ R then 1 else 0) + sampleHits R x := by
  simp only [sampleHits_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

def sampleSplitEquiv (α : Type*) (s : ℕ) : (Fin (s + 1) → α) ≃ α × (Fin s → α) where
  toFun x := (x 0, fun i => x i.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv z := by
    rcases z with ⟨a, x⟩
    simp

theorem sum_sampleHits_succ {α : Type*} [Fintype α] [DecidableEq α] (R : Finset α) (s : ℕ) :
    (∑ x : Fin (s + 1) → α, sampleHits R x) =
      Fintype.card α ^ s * R.card + Fintype.card α * ∑ x : Fin s → α, sampleHits R x := by
  classical
  rw [← (sampleSplitEquiv α s).symm.sum_comp (fun x => sampleHits R x), Fintype.sum_prod_type]
  change (∑ a : α, ∑ x : Fin s → α, sampleHits R (Fin.cons a x)) = _
  simp only [sampleHits_cons, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp

/-- Total hits over all tuples, stated without division or a nonempty alphabet
assumption. It is the exact finite-count version of the expectation identity. -/
theorem card_mul_sum_sampleHits {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset α) (s : ℕ) :
    Fintype.card α * (∑ x : Fin s → α, sampleHits R x) =
      s * R.card * Fintype.card α ^ s := by
  induction s with
  | zero => simp [sampleHits_eq_sum]
  | succ s ih =>
    rw [sum_sampleHits_succ, mul_add, ← mul_assoc, ih, pow_succ]
    ring

/-- For a trace of density at least `1/128`, at least `1/256` of the tuples
of length `256*t` have at least `t` hits. This uses only counting and positivity. -/
theorem many_samples_hit_heavy_trace {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (R : Finset α) {t : ℕ} (ht : 0 < t)
    (hheavy : Fintype.card α ≤ 128 * R.card) :
    Fintype.card α ^ (256 * t) ≤
      256 * ((Finset.univ : Finset (Fin (256 * t) → α)).filter
        (fun x => t ≤ sampleHits R x)).card := by
  classical
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hmean : 2 * t * (Finset.univ : Finset (Fin (256 * t) → α)).card ≤
      ∑ x : Fin (256 * t) → α, sampleHits R x := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    apply Nat.le_of_mul_le_mul_left (c := Fintype.card α) _ hn
    rw [card_mul_sum_sampleHits]
    have hmul := Nat.mul_le_mul_right (2 * t * Fintype.card α ^ (256 * t)) hheavy
    nlinarith
  have h := reverse_markov_card (Finset.univ : Finset (Fin (256 * t) → α))
    (sampleHits R) (b := 256) ht hmean (fun x _ => sampleHits_le R x)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using h

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_FiniteSampling

section OriginalModule_LinearCrossingFamilies_SampleSwaps

/-! ## Counting swap masks in the finite double-sampling argument -/

namespace LinearCrossingFamilies

open scoped BigOperators

theorem sampleHits_eq_zero_iff {α : Type*} [DecidableEq α] (R : Finset α)
    {s : ℕ} (x : Fin s → α) : sampleHits R x = 0 ↔ ∀ i, x i ∉ R := by
  simp [sampleHits, Finset.filter_eq_empty_iff]

def swapSamples {α : Type*} {s : ℕ} (b : Fin s → Bool)
    (z : (Fin s → α) × (Fin s → α)) : (Fin s → α) × (Fin s → α) :=
  (fun i => if b i then z.2 i else z.1 i, fun i => if b i then z.1 i else z.2 i)

theorem swapSamples_involutive {α : Type*} {s : ℕ} (b : Fin s → Bool) :
    Function.Involutive (swapSamples (α := α) b) := by
  intro z
  apply Prod.ext <;> funext i <;> cases hb : b i <;> simp [swapSamples, hb]

def swapSamplesEquiv {α : Type*} {s : ℕ} (b : Fin s → Bool) :
    ((Fin s → α) × (Fin s → α)) ≃ ((Fin s → α) × (Fin s → α)) :=
  Function.Involutive.toPerm (swapSamples b) (swapSamples_involutive b)

/-- Fixing Boolean coordinates leaves at most one free bit per other coordinate. -/
theorem card_agreeing_masks_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (b : ι → Bool) :
    ((Finset.univ : Finset (ι → Bool)).filter (fun c => ∀ i ∈ I, c i = b i)).card ≤
      2 ^ (Fintype.card ι - I.card) := by
  classical
  let f : (ι → Bool) → (↥(Iᶜ) → Bool) := fun c i => c i.val
  have hbound : ((Finset.univ : Finset (ι → Bool)).filter
      (fun c => ∀ i ∈ I, c i = b i)).card ≤ (Finset.univ : Finset (↥(Iᶜ) → Bool)).card := by
    apply Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
    intro c hc d hd hcd
    apply funext
    intro i
    by_cases hi : i ∈ I
    · exact ((Finset.mem_filter.mp hc).2 i hi).trans ((Finset.mem_filter.mp hd).2 i hi).symm
    · exact congrFun hcd ⟨i, Finset.mem_compl.mpr hi⟩
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, Finset.card_compl] using hbound

def goodSwapMasks {α : Type*} [DecidableEq α] (R : Finset α) {s : ℕ}
    (z : (Fin s → α) × (Fin s → α)) (t : ℕ) : Finset (Fin s → Bool) :=
  Finset.univ.filter (fun b => sampleHits R (swapSamples b z).1 = 0 ∧
    t ≤ sampleHits R (swapSamples b z).2)

/-- A trace missing the first tuple and hitting the second at least `t` times
forces at least `t` independent swap bits. -/
theorem card_goodSwapMasks_le {α : Type*} [DecidableEq α] (R : Finset α) {s : ℕ}
    (z : (Fin s → α) × (Fin s → α)) (t : ℕ) :
    (goodSwapMasks R z t).card ≤ 2 ^ (s - t) := by
  classical
  rcases (goodSwapMasks R z t).eq_empty_or_nonempty with hzero | hnon
  · simp [hzero]
  obtain ⟨b, hb⟩ := hnon
  obtain ⟨_, hbmiss, hbhit⟩ := Finset.mem_filter.mp hb
  have hbmiss' := (sampleHits_eq_zero_iff R _).mp hbmiss
  let I := Finset.univ.filter (fun i : Fin s => z.1 i ∈ R ∨ z.2 i ∈ R)
  have hI : I.card = sampleHits R (swapSamples b z).2 := by
    unfold sampleHits
    congr 1
    ext i
    have hmiss := hbmiss' i
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    change (z.1 i ∈ R ∨ z.2 i ∈ R) ↔ (if b i then z.1 i else z.2 i) ∈ R
    cases hbi : b i
    · have hm : z.1 i ∉ R := by simpa only [swapSamples, hbi, Bool.false_eq_true, ite_false] using hmiss
      simp [hm]
    · have hm : z.2 i ∉ R := by simpa only [swapSamples, hbi, ite_true] using hmiss
      simp [hm]
  have htI : t ≤ I.card := by simpa only [hI] using hbhit
  have hsub : goodSwapMasks R z t ⊆ Finset.univ.filter (fun c => ∀ i ∈ I, c i = b i) := by
    intro c hc
    have hcmiss := (sampleHits_eq_zero_iff R _).mp (Finset.mem_filter.mp hc).2.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    have hhit : z.1 i ∈ R ∨ z.2 i ∈ R := (Finset.mem_filter.mp hi).2
    have hbm := hbmiss' i
    have hcm := hcmiss i
    change (if b i then z.2 i else z.1 i) ∉ R at hbm
    change (if c i then z.2 i else z.1 i) ∉ R at hcm
    cases hbi : b i <;> cases hci : c i <;>
      simp only [hbi, hci, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hbm hcm ⊢
    all_goals first | rfl | exact False.elim (hhit.elim hbm hcm) |
      exact False.elim (hhit.elim hcm hbm)
  calc
    _ ≤ (Finset.univ.filter (fun c => ∀ i ∈ I, c i = b i)).card := Finset.card_le_card hsub
    _ ≤ 2 ^ (Fintype.card (Fin s) - I.card) := by
      apply le_trans (le_of_eq ?_) (card_agreeing_masks_le I b)
      congr 1
      ext c
      simp only [Finset.mem_filter]
    _ ≤ 2 ^ (s - t) := by simp only [Fintype.card_fin]; gcongr

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_SampleSwaps

section OriginalModule_LinearCrossingFamilies_DoubleSampling

/-! ## Finite double-sampling lower bounds and swap invariance -/

namespace LinearCrossingFamilies

open scoped BigOperators

noncomputable section

def badSamples {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Finset α)) (s : ℕ) :
    Finset (Fin s → α) := by
  classical
  exact Finset.univ.filter (fun x => ∃ R ∈ F,
    Fintype.card α ≤ 128 * R.card ∧ sampleHits R x = 0)

def doubleEvent {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (t : ℕ)
    {s : ℕ} (z : (Fin s → α) × (Fin s → α)) : Prop :=
  ∃ R ∈ F, sampleHits R z.1 = 0 ∧ t ≤ sampleHits R z.2

def doubleWitnesses {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (s t : ℕ) : Finset ((Fin s → α) × (Fin s → α)) := by
  classical
  exact Finset.univ.filter (doubleEvent F t)

def swapWitnessMasks {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (t : ℕ)
    {s : ℕ} (z : (Fin s → α) × (Fin s → α)) : Finset (Fin s → Bool) := by
  classical
  exact Finset.univ.filter (fun b => doubleEvent F t (swapSamples b z))

theorem card_filter_prod_univ {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (α × β)).filter p).card =
      ∑ a : α, ((Finset.univ : Finset β).filter (fun b => p (a, b))).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]

/-- Each bad first tuple has many second tuples witnessing its missed heavy trace. -/
theorem badSamples_mul_card_le {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (F : Finset (Finset α)) {t : ℕ} (ht : 0 < t) :
    (badSamples F (256 * t)).card * Fintype.card α ^ (256 * t) ≤
      256 * (doubleWitnesses F (256 * t) t).card := by
  classical
  let fiber := fun x : Fin (256 * t) → α =>
    (Finset.univ : Finset (Fin (256 * t) → α)).filter (fun y => doubleEvent F t (x, y))
  have hfiber : ∀ x ∈ badSamples F (256 * t),
      Fintype.card α ^ (256 * t) ≤ 256 * (fiber x).card := by
    intro x hx
    obtain ⟨_, R, hR, hheavy, hmiss⟩ := Finset.mem_filter.mp hx
    have hsub : (Finset.univ.filter (fun y : Fin (256 * t) → α => t ≤ sampleHits R y)) ⊆ fiber x := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, R, hR, hmiss, (Finset.mem_filter.mp hy).2⟩
    exact (many_samples_hit_heavy_trace R ht hheavy).trans
      (Nat.mul_le_mul_left 256 (Finset.card_le_card hsub))
  have hcard : (doubleWitnesses F (256 * t) t).card = ∑ x, (fiber x).card :=
    card_filter_prod_univ (doubleEvent F t)
  calc
    _ = ∑ _x ∈ badSamples F (256 * t), Fintype.card α ^ (256 * t) := by simp
    _ ≤ ∑ x ∈ badSamples F (256 * t), 256 * (fiber x).card := Finset.sum_le_sum hfiber
    _ ≤ ∑ x : Fin (256 * t) → α, 256 * (fiber x).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := by rw [← Finset.mul_sum, ← hcard]

/-- Swapping corresponding coordinates is a bijection on tuple pairs, so
averaging over every swap mask leaves the event count unchanged. -/
theorem sum_card_swapWitnessMasks {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (s t : ℕ) :
    (∑ z : (Fin s → α) × (Fin s → α), (swapWitnessMasks F t z).card) =
      2 ^ s * (doubleWitnesses F s t).card := by
  classical
  simp only [swapWitnessMasks, Finset.card_filter]
  rw [Finset.sum_comm]
  have hmask : ∀ b : Fin s → Bool,
      (∑ z : (Fin s → α) × (Fin s → α), if doubleEvent F t (swapSamples b z) then 1 else 0) =
        (doubleWitnesses F s t).card := by
    intro b
    change (∑ z, if doubleEvent F t ((swapSamplesEquiv b) z) then 1 else 0) = _
    calc
      _ = ∑ z, if doubleEvent F t z then (1 : ℕ) else 0 :=
        (swapSamplesEquiv b).sum_comp (fun z => if doubleEvent F t z then (1 : ℕ) else 0)
      _ = _ := (Finset.card_filter _ _).symm
  simp only [hmask, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, smul_eq_mul]

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_DoubleSampling

section OriginalModule_LinearCrossingFamilies_SampleRestriction

/-! ## Restriction and union bounds for finite double sampling -/

namespace LinearCrossingFamilies

open scoped BigOperators

def sampleLabels {α : Type*} [DecidableEq α] {s : ℕ}
    (z : (Fin s → α) × (Fin s → α)) : Finset α :=
  Finset.univ.image z.1 ∪ Finset.univ.image z.2

theorem card_sampleLabels_le {α : Type*} [DecidableEq α] {s : ℕ}
    (z : (Fin s → α) × (Fin s → α)) : (sampleLabels z).card ≤ 2 * s := by
  have h₁ : (Finset.univ.image z.1).card ≤ s := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin s))) (f := z.1))
  have h₂ : (Finset.univ.image z.2).card ≤ s := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin s))) (f := z.2))
  have := Finset.card_union_le (Finset.univ.image z.1) (Finset.univ.image z.2)
  unfold sampleLabels
  omega

theorem sampleHits_inter_eq {α : Type*} [DecidableEq α] (R S : Finset α)
    {s : ℕ} (x : Fin s → α) (hx : ∀ i, x i ∈ S) :
    sampleHits (S ∩ R) x = sampleHits R x := by
  unfold sampleHits
  congr 1
  ext i
  simp [hx i]

theorem swapSamples_mem_labels {α : Type*} [DecidableEq α] {s : ℕ}
    (z : (Fin s → α) × (Fin s → α)) (b : Fin s → Bool) (i : Fin s) :
    (swapSamples b z).1 i ∈ sampleLabels z ∧ (swapSamples b z).2 i ∈ sampleLabels z := by
  have h₁ : z.1 i ∈ sampleLabels z :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have h₂ : z.2 i ∈ sampleLabels z :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  cases hb : b i <;> simp [swapSamples, hb, h₁, h₂]

/-- Only the traces on the combined tuple matter for the mask count. -/
theorem card_swapWitnessMasks_le {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) {s : ℕ} (t : ℕ) (z : (Fin s → α) × (Fin s → α)) :
    (swapWitnessMasks F t z).card ≤
      (F.image (fun R => sampleLabels z ∩ R)).card * 2 ^ (s - t) := by
  classical
  let G := F.image (fun R => sampleLabels z ∩ R)
  have hsub : swapWitnessMasks F t z ⊆ G.biUnion (fun R => goodSwapMasks R z t) := by
    intro b hb
    obtain ⟨R, hR, hmiss, hhit⟩ := (Finset.mem_filter.mp hb).2
    refine Finset.mem_biUnion.mpr ⟨sampleLabels z ∩ R,
      Finset.mem_image.mpr ⟨R, hR, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [sampleHits_inter_eq R _ _ (fun i => (swapSamples_mem_labels z b i).1),
      sampleHits_inter_eq R _ _ (fun i => (swapSamples_mem_labels z b i).2)]
    exact ⟨hmiss, hhit⟩
  calc
    _ ≤ (G.biUnion (fun R => goodSwapMasks R z t)).card := Finset.card_le_card hsub
    _ ≤ ∑ R ∈ G, (goodSwapMasks R z t).card := Finset.card_biUnion_le
    _ ≤ ∑ _R ∈ G, 2 ^ (s - t) := Finset.sum_le_sum (fun R _ => card_goodSwapMasks_le R z t)
    _ = _ := by simp [G]

/-- The upper estimate in double sampling, expressed entirely in finite counts. -/
theorem doubleWitnesses_mul_pow_le {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) {s t K : ℕ} (hts : t ≤ s)
    (hK : ∀ S : Finset α, S.card ≤ 2 * s → (F.image (fun R => S ∩ R)).card ≤ K) :
    (doubleWitnesses F s t).card * 2 ^ t ≤ (Fintype.card α ^ s) ^ 2 * K := by
  classical
  have hbound : 2 ^ s * (doubleWitnesses F s t).card ≤
      (Fintype.card α ^ s) ^ 2 * K * 2 ^ (s - t) := by
    rw [← sum_card_swapWitnessMasks]
    calc
      _ ≤ ∑ _z : (Fin s → α) × (Fin s → α), K * 2 ^ (s - t) := by
        apply Finset.sum_le_sum
        intro z _
        exact (card_swapWitnessMasks_le F t z).trans
          (Nat.mul_le_mul_right _ (hK _ (card_sampleLabels_le z)))
      _ = _ := by simp [Fintype.card_prod, pow_two, Nat.mul_assoc]
  have hpow : 2 ^ s = 2 ^ t * 2 ^ (s - t) := by
    rw [← pow_add, Nat.add_sub_of_le hts]
  rw [hpow] at hbound
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ (s - t))
  · nlinarith only [hbound]
  · positivity

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_SampleRestriction

section OriginalModule_LinearCrossingFamilies_FiniteEpsilonNet

/-! ## A finite ε-net theorem at density 1/128

All probabilities are replaced by exact counts of tuples and Boolean masks.
The bound is uniform in the size of the underlying finite type.
-/

namespace LinearCrossingFamilies

/-- A trace bound on sets of at most twice the sample size gives a bounded net. -/
theorem exists_finite_epsilon_net {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (F : Finset (Finset α)) {t K : ℕ} (ht : 0 < t)
    (hK : ∀ S : Finset α, S.card ≤ 2 * (256 * t) →
      (F.image (fun R => S ∩ R)).card ≤ K)
    (hgap : 256 * K < 2 ^ t) :
    ∃ Q : Finset α, Q.card ≤ 256 * t ∧
      ∀ R ∈ F, Fintype.card α ≤ 128 * R.card → (Q ∩ R).Nonempty := by
  classical
  have hgood : ∃ x : Fin (256 * t) → α, x ∉ badSamples F (256 * t) := by
    by_contra hnone
    have hall : badSamples F (256 * t) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      by_contra hx
      exact hnone ⟨x, hx⟩
    have hlower := badSamples_mul_card_le F ht
    rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hlower
    have hupper := doubleWitnesses_mul_pow_le F (by omega : t ≤ 256 * t) hK
    let N := Fintype.card α ^ (256 * t)
    let D := (doubleWitnesses F (256 * t) t).card
    have hN : 0 < N := pow_pos Fintype.card_pos _
    change N * N ≤ 256 * D at hlower
    change D * 2 ^ t ≤ N ^ 2 * K at hupper
    have hprod : N ^ 2 * 2 ^ t ≤ N ^ 2 * (256 * K) := by
      calc
        _ ≤ (256 * D) * 2 ^ t := by simpa only [pow_two] using Nat.mul_le_mul_right (2 ^ t) hlower
        _ ≤ 256 * (N ^ 2 * K) := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 256 hupper
        _ = _ := by ring
    have hbad := Nat.le_of_mul_le_mul_left hprod (pow_pos hN 2)
    omega
  obtain ⟨x, hx⟩ := hgood
  refine ⟨Finset.univ.image x, ?_, ?_⟩
  · simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin (256 * t)))) (f := x))
  · intro R hR hheavy
    have hnonzero : sampleHits R x ≠ 0 := by
      intro hzero
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, R, hR, hheavy, hzero⟩)
    obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp hnonzero
    exact ⟨x i, Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, (Finset.mem_filter.mp hi).2⟩⟩

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_FiniteEpsilonNet

section OriginalModule_LinearCrossingFamilies_SectorEpsilonNet

/-! ## Bounded hitting sets for planar sectors -/

namespace LinearCrossingFamilies

noncomputable section

local instance sectorNetDecEqPoint : DecidableEq Point := Classical.decEq _

theorem subset_of_mem_sectorTraces {P R : Finset Point} (hR : R ∈ sectorTraces P) : R ⊆ P := by
  obtain ⟨⟨U, V⟩, hUV, rfl⟩ := Finset.mem_image.mp hR
  exact Finset.inter_subset_left.trans (subset_of_mem_halfplaneTraces (Finset.mem_product.mp hUV).1)

theorem sector_trace_bound_fixed {n : ℕ} (hn : n ≤ 131072) :
    (∑ k ∈ Finset.range 4, n.choose k) ^ 2 ≤ (4 * 131072 ^ 3) ^ 2 := by
  have hsum : (∑ k ∈ Finset.range 4, n.choose k) ≤ 4 * 131072 ^ 3 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range 4, 131072 ^ 3 := by
        apply Finset.sum_le_sum
        intro k hk
        exact (Nat.choose_le_choose k hn).trans ((Nat.choose_le_pow 131072 k).trans
          (pow_le_pow_right' (by omega : 1 ≤ (131072 : ℕ)) (by have := Finset.mem_range.mp hk; omega)))
      _ = _ := by simp
  simpa only [pow_two] using Nat.mul_le_mul hsum hsum

/-- Every nonempty finite planar set has a uniformly bounded subset meeting
all sector traces of density at least `1/128`. No general position is needed. -/
theorem exists_sector_epsilon_net (P : Finset Point) (hP : P.Nonempty) :
    ∃ Q : Finset Point, Q ⊆ P ∧ Q.card ≤ 65536 ∧
      ∀ R ∈ sectorTraces P, P.card ≤ 128 * R.card → (Q ∩ R).Nonempty := by
  classical
  let : Nonempty P := hP.to_subtype
  let F : Finset (Finset P) := (sectorTraces P).image (fun R => R.subtype (· ∈ P))
  have hK : ∀ S : Finset P, S.card ≤ 2 * (256 * 256) →
      (F.image (fun R => S ∩ R)).card ≤ (4 * 131072 ^ 3) ^ 2 := by
    intro S hS
    let S' := S.map (Function.Embedding.subtype (· ∈ P))
    have hSP : S' ⊆ P := fun _ hp => Finset.property_of_mem_map_subtype S hp
    have heq : F.image (fun R => S ∩ R) =
        ((sectorTraces P).image (fun R => S' ∩ R)).image (fun R => R.subtype (· ∈ P)) := by
      dsimp only [F]
      simp only [Finset.image_image]
      apply Finset.image_congr
      intro R _
      dsimp only [Function.comp_apply]
      ext p
      simp only [Finset.mem_inter, Finset.mem_subtype]
      exact and_congr (Finset.mem_map' (Function.Embedding.subtype (· ∈ P))).symm Iff.rfl
    rw [heq]
    apply Finset.card_image_le.trans
    apply (card_sector_restriction_le hSP).trans
    apply sector_trace_bound_fixed
    simpa only [S', Finset.card_map] using hS
  have hgap : 256 * (4 * 131072 ^ 3) ^ 2 < 2 ^ (256 : ℕ) := by norm_num
  obtain ⟨Q, hQcard, hQhit⟩ := exists_finite_epsilon_net F (by norm_num : 0 < (256 : ℕ)) hK hgap
  refine ⟨Q.map (Function.Embedding.subtype (· ∈ P)),
    (fun _ hp => Finset.property_of_mem_map_subtype Q hp), ?_, ?_⟩
  · simpa only [Finset.card_map] using hQcard
  · intro R hR hheavy
    have hsub := subset_of_mem_sectorTraces hR
    have hcard : (R.subtype (· ∈ P)).card = R.card := by
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr hsub]
    have hh : Fintype.card P ≤ 128 * (R.subtype (· ∈ P)).card := by
      simpa only [Fintype.card_coe, hcard] using hheavy
    obtain ⟨p, hp⟩ := hQhit (R.subtype (· ∈ P)) (Finset.mem_image.mpr ⟨R, hR, rfl⟩) hh
    obtain ⟨hpQ, hpR⟩ := Finset.mem_inter.mp hp
    exact ⟨p.val, Finset.mem_inter.mpr
      ⟨Finset.mem_map_of_mem _ hpQ, Finset.mem_subtype.mp hpR⟩⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_SectorEpsilonNet

section OriginalModule_LinearCrossingFamilies_ZoneCoverCounting

/-! ## From empty-sector covers to small arrangement zones

The counting argument uses a geometric cover, constructed in
`exists_four_sector_cover` below.
-/

namespace LinearCrossingFamilies

noncomputable section

local instance zoneCoverDecEqPoint : DecidableEq Point := Classical.decEq _

/-- Enlarge the net to contain any prescribed bounded subset. -/
theorem exists_sector_net_containing {P A : Finset Point} (hP : P.Nonempty) (hAP : A ⊆ P) :
    ∃ Q : Finset Point, Q ⊆ P ∧ A ⊆ Q ∧ Q.card ≤ 65536 + A.card ∧
      ∀ R ∈ sectorTraces P, P.card ≤ 128 * R.card → (Q ∩ R).Nonempty := by
  obtain ⟨Q, hQP, hcard, hhit⟩ := exists_sector_epsilon_net P hP
  refine ⟨Q ∪ A, Finset.union_subset hQP hAP, Finset.subset_union_right,
    (Finset.card_union_le Q A).trans (Nat.add_le_add_right hcard _), ?_⟩
  intro R hR hheavy
  obtain ⟨p, hp⟩ := hhit R hR hheavy
  exact ⟨p, Finset.mem_inter.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩⟩

theorem small_of_empty_sector {P Q R : Finset Point}
    (hnet : ∀ U ∈ sectorTraces P, P.card ≤ 128 * U.card → (Q ∩ U).Nonempty)
    (hR : R ∈ sectorTraces P) (hempty : Disjoint Q R) : 128 * R.card < P.card := by
  by_contra h
  obtain ⟨p, hp⟩ := hnet R hR (by omega)
  exact Finset.disjoint_left.mp hempty (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2

/-- Four empty sectors suffice for the exact `1/32` zone bound used in extraction. -/
theorem small_zone_of_four_sector_cover {P Q : Finset Point} {L : Finset (Point × Point)}
    {e : Sym2 Point} {C : Finset (Finset Point)}
    (hnet : ∀ U ∈ sectorTraces P, P.card ≤ 128 * U.card → (Q ∩ U).Nonempty)
    (hC : C.card ≤ 4) (hsector : ∀ R ∈ C, R ∈ sectorTraces P)
    (hempty : ∀ R ∈ C, Disjoint Q R)
    (hcover : arrangementZone P L e ⊆ C.biUnion id) :
    32 * (arrangementZone P L e).card ≤ P.card := by
  have hcard : (arrangementZone P L e).card ≤ ∑ R ∈ C, R.card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hmass : 128 * (arrangementZone P L e).card ≤ 4 * P.card := by
    calc
      _ ≤ 128 * ∑ R ∈ C, R.card := Nat.mul_le_mul_left _ hcard
      _ = ∑ R ∈ C, 128 * R.card := Finset.mul_sum ..
      _ ≤ ∑ _R ∈ C, P.card := Finset.sum_le_sum (fun R hR =>
        (small_of_empty_sector hnet (hsector R hR) (hempty R hR)).le)
      _ = C.card * P.card := by simp
      _ ≤ 4 * P.card := Nat.mul_le_mul_right _ hC
  omega

/-- A query line already present in the arrangement meets no open cell. -/
theorem arrangementZone_eq_empty_of_mem {P : Finset Point} {L : Finset (Point × Point)}
    {a b : Point} (hab : (a, b) ∈ L) : arrangementZone P L s(a, b) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨_, σ, _, x, hline, hx⟩ := Finset.mem_filter.mp hp
  have hxside := hx ⟨(a, b), hab⟩
  change orientation a b x = 0 at hline
  change (if σ ⟨(a, b), hab⟩ then 0 < orientation a b x else orientation a b x < 0) at hxside
  simp only [hline, lt_self_iff_false, ite_self] at hxside

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_ZoneCoverCounting

section OriginalModule_LinearCrossingFamilies_QueryZoneStability

/-! ## Stability of finite arrangement zones under query-line perturbation

The arrangement remains fixed. Only the query line moves; every previously
hit open cell remains hit for all sufficiently small perturbations.
-/

open Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance queryZoneDecEqPoint : DecidableEq Point := Classical.decEq _

abbrev LineQuery := Point × ℝ

def queryEval (q : LineQuery) (p : Point) : ℝ := q.1.1 * p.1 + q.1.2 * p.2 - q.2

def queryZone (P : Finset Point) (L : Finset (Point × Point)) (q : LineQuery) : Finset Point := by
  classical
  exact P.filter (fun p => ∃ σ : L → Bool, p ∈ cellRegion L σ ∧
    ∃ x ∈ cellRegion L σ, queryEval q x = 0)

theorem isOpen_cellRegion (L : Finset (Point × Point)) (σ : L → Bool) :
    IsOpen (cellRegion L σ) := by
  unfold cellRegion
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro l
  have hc : Continuous (orientation l.val.1 l.val.2) := by unfold orientation; fun_prop
  cases hσ : σ l
  · simpa only [hσ, Bool.false_eq_true, ite_false] using isOpen_lt hc continuous_const
  · simpa only [hσ, ite_true] using isOpen_lt continuous_const hc

theorem queryEval_combo (q : LineQuery) (x y : Point) (t : ℝ) :
    queryEval q ((1 - t) • x + t • y) =
      (1 - t) * queryEval q x + t * queryEval q y := by
  simp only [queryEval, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem exists_query_zero_of_opposite {U : Set Point} (hU : Convex ℝ U)
    {q : LineQuery} {x y : Point} (hx : x ∈ U) (hy : y ∈ U)
    (hxneg : queryEval q x < 0) (hypos : 0 < queryEval q y) :
    ∃ z ∈ U, queryEval q z = 0 := by
  let t := queryEval q x / (queryEval q x - queryEval q y)
  have hd : queryEval q x - queryEval q y < 0 := by linarith
  have htpos : 0 < t := div_pos_of_neg_of_neg hxneg hd
  have htone : t < 1 := (div_lt_one_of_neg hd).mpr (by linarith)
  refine ⟨(1 - t) • x + t • y,
    hU hx hy (sub_nonneg.mpr htone.le) htpos.le (sub_add_cancel 1 t), ?_⟩
  rw [queryEval_combo]
  dsimp only [t]
  field_simp [ne_of_lt hd]
  ring

/-- An open cell meeting a nondegenerate line contains points on both sides. -/
theorem exists_query_opposite_of_open {U : Set Point} (hU : IsOpen U)
    {q : LineQuery} (hq : q.1 ≠ 0) {x : Point} (hx : x ∈ U) (hxzero : queryEval q x = 0) :
    ∃ y ∈ U, ∃ z ∈ U, queryEval q y < 0 ∧ 0 < queryEval q z := by
  have hnorm : 0 < q.1.1 ^ 2 + q.1.2 ^ 2 := by
    have h₁ := sq_nonneg q.1.1
    have h₂ := sq_nonneg q.1.2
    by_contra h
    have hfirst : q.1.1 = 0 := by nlinarith
    have hsecond : q.1.2 = 0 := by nlinarith
    exact hq (Prod.ext hfirst hsecond)
  have hcPlus : Continuous (fun t : ℝ => x + t • q.1) := by fun_prop
  have hcMinus : Continuous (fun t : ℝ => x - t • q.1) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • q.1 ∈ U ∧ x - t • q.1 ∈ U := by
    exact ((hcPlus.continuousAt.eventually (hU.mem_nhds (by simpa using hx))).and
      (hcMinus.continuousAt.eventually (hU.mem_nhds (by simpa using hx))))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have htpos : 0 < ε / 2 := half_pos hε
  have htball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    linarith
  obtain ⟨hplus, hminus⟩ := hball htball
  refine ⟨x - (ε / 2) • q.1, hminus, x + (ε / 2) • q.1, hplus, ?_, ?_⟩
  · have heq : queryEval q (x - (ε / 2) • q.1) =
        queryEval q x - (ε / 2) * (q.1.1 ^ 2 + q.1.2 ^ 2) := by
      simp only [queryEval, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [heq, hxzero]
    exact sub_neg.mpr (mul_pos htpos hnorm)
  · have heq : queryEval q (x + (ε / 2) • q.1) =
        queryEval q x + (ε / 2) * (q.1.1 ^ 2 + q.1.2 ^ 2) := by
      simp only [queryEval, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [heq, hxzero, zero_add]
    exact mul_pos htpos hnorm

theorem eventually_query_hits_open_convex {U : Set Point} (hU : IsOpen U) (hc : Convex ℝ U)
    {q : LineQuery} (hq : q.1 ≠ 0) (hhit : ∃ x ∈ U, queryEval q x = 0) :
    ∀ᶠ q' : LineQuery in 𝓝 q, ∃ x ∈ U, queryEval q' x = 0 := by
  obtain ⟨x, hx, hxzero⟩ := hhit
  obtain ⟨y, hy, z, hz, hyneg, hzpos⟩ := exists_query_opposite_of_open hU hq hx hxzero
  have hcy : Continuous (fun q' : LineQuery => queryEval q' y) := by unfold queryEval; fun_prop
  have hcz : Continuous (fun q' : LineQuery => queryEval q' z) := by unfold queryEval; fun_prop
  have hnear₁ := (isOpen_lt hcy continuous_const).mem_nhds hyneg
  have hnear₂ := (isOpen_lt continuous_const hcz).mem_nhds hzpos
  filter_upwards [hnear₁, hnear₂] with q' h₁ h₂
  exact exists_query_zero_of_opposite hc hy hz h₁ h₂

/-- All original zone points persist simultaneously, since there are finitely many. -/
theorem eventually_queryZone_subset (P : Finset Point) (L : Finset (Point × Point))
    {q : LineQuery} (hq : q.1 ≠ 0) :
    ∀ᶠ q' : LineQuery in 𝓝 q, queryZone P L q ⊆ queryZone P L q' := by
  classical
  change ∀ᶠ q' : LineQuery in 𝓝 q, ∀ p ∈ queryZone P L q, p ∈ queryZone P L q'
  rw [Filter.eventually_all_finset]
  intro p hp
  obtain ⟨hpP, σ, hpσ, hhit⟩ := Finset.mem_filter.mp hp
  have hnear := eventually_query_hits_open_convex (isOpen_cellRegion L σ) (convex_cellRegion L σ) hq hhit
  filter_upwards [hnear] with q' hq'
  exact Finset.mem_filter.mpr ⟨hpP, σ, hpσ, hq'⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_QueryZoneStability

section OriginalModule_LinearCrossingFamilies_QueryGenericity

/-! ## Generic query lines preserving the entire finite zone -/

open Filter Topology

namespace LinearCrossingFamilies

noncomputable section

local instance queryGenericDecEqPoint : DecidableEq Point := Classical.decEq _

def decodeQuery (w : Fin 3 → ℝ) : LineQuery := ((w 0, w 1), w 2)

def encodeQuery (q : LineQuery) : Fin 3 → ℝ := ![q.1.1, q.1.2, q.2]

@[simp] theorem decode_encode_query (q : LineQuery) : decodeQuery (encodeQuery q) = q := by
  simp [decodeQuery, encodeQuery]

theorem continuous_decodeQuery : Continuous decodeQuery := by unfold decodeQuery; fun_prop

def queryPointPolynomial (p : Point) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C p.1 * MvPolynomial.X 0 + MvPolynomial.C p.2 * MvPolynomial.X 1 - MvPolynomial.X 2

def queryPairPolynomial (a b : Point) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (a.1 - b.1) * MvPolynomial.X 0 + MvPolynomial.C (a.2 - b.2) * MvPolynomial.X 1

theorem queryPointPolynomial_ne_zero (p : Point) : queryPointPolynomial p ≠ 0 := by
  intro h
  have heval := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → ℝ)) h
  norm_num [queryPointPolynomial] at heval

theorem queryPairPolynomial_ne_zero {a b : Point} (hab : a ≠ b) : queryPairPolynomial a b ≠ 0 := by
  intro h
  have h₁ := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → ℝ)) h
  have h₂ := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → ℝ)) h
  norm_num [queryPairPolynomial] at h₁ h₂
  exact hab (Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂))

def queryGenericPolynomial (P : Finset Point) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 1 * (∏ p ∈ P, queryPointPolynomial p) *
    ∏ e ∈ P.offDiag, queryPairPolynomial e.1 e.2

theorem queryGenericPolynomial_ne_zero (P : Finset Point) : queryGenericPolynomial P ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (MvPolynomial.X_ne_zero 1)
      (Finset.prod_ne_zero_iff.mpr (fun p _ => queryPointPolynomial_ne_zero p))
  · exact Finset.prod_ne_zero_iff.mpr (fun e he =>
      queryPairPolynomial_ne_zero (Finset.mem_offDiag.mp he).2.2)

theorem query_generic_of_eval_ne_zero {P : Finset Point} {w : Fin 3 → ℝ}
    (hw : MvPolynomial.eval w (queryGenericPolynomial P) ≠ 0) :
    (decodeQuery w).1.2 ≠ 0 ∧
    (∀ p ∈ P, queryEval (decodeQuery w) p ≠ 0) ∧
    Set.InjOn (queryEval (decodeQuery w)) (P : Set Point) := by
  simp only [queryGenericPolynomial, map_mul, map_prod, MvPolynomial.eval_X,
    mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hw
  refine ⟨hw.1.1, ?_, ?_⟩
  · intro p hp
    have heq : MvPolynomial.eval w (queryPointPolynomial p) = queryEval (decodeQuery w) p := by
      simp [queryPointPolynomial, queryEval, decodeQuery, mul_comm]
    exact heq ▸ hw.1.2 p hp
  · intro a ha b hb hab
    by_contra hne
    have h := hw.2 (a, b) (Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩)
    apply h
    have heq : MvPolynomial.eval w (queryPairPolynomial a b) =
        queryEval (decodeQuery w) a - queryEval (decodeQuery w) b := by
      simp only [queryPairPolynomial, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        queryEval, decodeQuery]
      ring
    rw [heq, hab, sub_self]

/-- Generic lines are available in every neighborhood: no point incidence,
no equal signed heights on the finite set, and a nonvertical line. -/
theorem exists_generic_query_mem_nhds (P : Finset Point) {q : LineQuery}
    {U : Set LineQuery} (hU : U ∈ 𝓝 q) :
    ∃ q' ∈ U, q'.1.2 ≠ 0 ∧ (∀ p ∈ P, queryEval q' p ≠ 0) ∧
      Set.InjOn (queryEval q') (P : Set Point) := by
  have hpre : decodeQuery ⁻¹' U ∈ 𝓝 (encodeQuery q) := by
    apply continuous_decodeQuery.continuousAt.preimage_mem_nhds
    simpa only [decode_encode_query] using hU
  obtain ⟨w, hw, hwU⟩ :=
    (dense_mvPolynomial_eval_ne_zero (queryGenericPolynomial_ne_zero P)).inter_nhds_nonempty hpre
  exact ⟨decodeQuery w, hwU, query_generic_of_eval_ne_zero hw⟩

/-- Removing degeneracies of the query line does not discard any old zone point. -/
theorem exists_generic_query_preserving_zone (P : Finset Point) (L : Finset (Point × Point))
    {q : LineQuery} (hq : q.1 ≠ 0) :
    ∃ q' : LineQuery, queryZone P L q ⊆ queryZone P L q' ∧ q'.1.2 ≠ 0 ∧
      (∀ p ∈ P, queryEval q' p ≠ 0) ∧ Set.InjOn (queryEval q') (P : Set Point) :=
  exists_generic_query_mem_nhds P (eventually_queryZone_subset P L hq)

/-- Convert an endpoint-defined supporting line to affine query coefficients. -/
def endpointQuery (a b : Point) : LineQuery :=
  ((-(b.2 - a.2), b.1 - a.1), -(b.2 - a.2) * a.1 + (b.1 - a.1) * a.2)

theorem queryEval_endpointQuery (a b p : Point) : queryEval (endpointQuery a b) p = orientation a b p := by
  unfold queryEval endpointQuery orientation
  ring

theorem endpointQuery_normal_ne_zero {a b : Point} (hab : a ≠ b) : (endpointQuery a b).1 ≠ 0 := by
  intro h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [endpointQuery, Prod.fst_zero, Prod.snd_zero] at h₁ h₂
  exact hab (Prod.ext (by linarith) (by linarith))

theorem queryZone_endpointQuery (P : Finset Point) (L : Finset (Point × Point)) (a b : Point) :
    queryZone P L (endpointQuery a b) = arrangementZone P L s(a, b) := by
  classical
  ext p
  simp only [queryZone, arrangementZone, Finset.mem_filter, queryEval_endpointQuery]
  constructor
  · rintro ⟨hp, σ, hpσ, x, hx, hzero⟩
    exact ⟨hp, σ, hpσ, x, hzero, hx⟩
  · rintro ⟨hp, σ, hpσ, x, hzero, hx⟩
    exact ⟨hp, σ, hpσ, x, hx, hzero⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_QueryGenericity

section OriginalModule_LinearCrossingFamilies_QuerySectors

/-! ## Query half-planes and extremal-ray algebra -/

namespace LinearCrossingFamilies

noncomputable section

local instance querySectorsDecEqPoint : DecidableEq Point := Classical.decEq _

def queryLinear (q : LineQuery) : Point →ₗ[ℝ] ℝ where
  toFun p := q.1.1 * p.1 + q.1.2 * p.2
  map_add' p r := by simp; ring
  map_smul' c p := by simp; ring

@[simp] theorem queryEval_neg (q : LineQuery) (p : Point) : queryEval (-q) p = -queryEval q p := by
  simp [queryEval]; ring

@[simp] theorem queryEval_smul (c : ℝ) (q : LineQuery) (p : Point) :
    queryEval (c • q) p = c * queryEval q p := by
  simp [queryEval]; ring

def positiveTrace (P : Finset Point) (q : LineQuery) : Finset Point :=
  P.filter (fun p => 0 < queryEval q p)

theorem positiveTrace_mem_halfplaneTraces (P : Finset Point) (q : LineQuery) :
    positiveTrace P q ∈ halfplaneTraces P := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
    -queryLinear q, -q.2, ?_⟩
  apply Finset.filter_congr
  intro p _
  change 0 < q.1.1 * p.1 + q.1.2 * p.2 - q.2 ↔ -(q.1.1 * p.1 + q.1.2 * p.2) < -q.2
  constructor <;> intro h <;> linarith

def querySector (P : Finset Point) (q r : LineQuery) : Finset Point :=
  positiveTrace P q ∩ positiveTrace P r

theorem querySector_mem (P : Finset Point) (q r : LineQuery) : querySector P q r ∈ sectorTraces P :=
  Finset.mem_image.mpr ⟨(positiveTrace P q, positiveTrace P r),
    Finset.mem_product.mpr ⟨positiveTrace_mem_halfplaneTraces P q, positiveTrace_mem_halfplaneTraces P r⟩, rfl⟩

theorem mem_querySector {P : Finset Point} {q r : LineQuery} {p : Point} :
    p ∈ querySector P q r ↔ p ∈ P ∧ 0 < queryEval q p ∧ 0 < queryEval r p := by
  simp only [querySector, positiveTrace, Finset.mem_inter, Finset.mem_filter]
  tauto

theorem positiveTrace_mem_sectorTraces (P : Finset Point) (q : LineQuery) :
    positiveTrace P q ∈ sectorTraces P := by
  simpa only [querySector, Finset.inter_self] using querySector_mem P q q

theorem orientation_mul_pos_of_cell {L : Finset (Point × Point)} {σ : L → Bool}
    {p x a b : Point} (hp : p ∈ cellRegion L σ) (hx : x ∈ cellRegion L σ)
    (hab : (a, b) ∈ L) : 0 < orientation a b p * orientation a b x := by
  have hp' := hp ⟨(a, b), hab⟩
  have hx' := hx ⟨(a, b), hab⟩
  change (if σ ⟨(a, b), hab⟩ then 0 < orientation a b p else orientation a b p < 0) at hp'
  change (if σ ⟨(a, b), hab⟩ then 0 < orientation a b x else orientation a b x < 0) at hx'
  split_ifs at hp' hx' with h
  · exact mul_pos hp' hx'
  · exact mul_pos_of_neg_of_neg hp' hx'

def rayQuery (q : LineQuery) (a b : Point) : LineQuery := q.1.2 • endpointQuery a b

def raySlope (q : LineQuery) (a b : Point) : ℝ :=
  (b.1 - a.1) / (queryEval q b - queryEval q a)

theorem queryEval_rayQuery (q : LineQuery) (a b p : Point) :
    queryEval (rayQuery q a b) p = q.1.2 * orientation a b p := by
  rw [rayQuery, queryEval_smul, queryEval_endpointQuery]

theorem queryEval_rayQuery_formula (q : LineQuery) (a b p : Point) :
    queryEval (rayQuery q a b) p =
      (b.1 - a.1) * (queryEval q p - queryEval q a) -
      (queryEval q b - queryEval q a) * (p.1 - a.1) := by
  rw [queryEval_rayQuery]
  unfold queryEval orientation
  ring

theorem queryEval_rayQuery_slope (q : LineQuery) (a b p : Point)
    (hba : queryEval q b ≠ queryEval q a) :
    queryEval (rayQuery q a b) p = (queryEval q b - queryEval q a) *
      (raySlope q a b * (queryEval q p - queryEval q a) - (p.1 - a.1)) := by
  rw [queryEval_rayQuery_formula]
  unfold raySlope
  field_simp [sub_ne_zero.mpr hba]

theorem rayQuery_mul_pos_of_cell {L : Finset (Point × Point)} {σ : L → Bool}
    {p x a b : Point} {q : LineQuery} (hq : q.1.2 ≠ 0)
    (hp : p ∈ cellRegion L σ) (hx : x ∈ cellRegion L σ) (hab : (a, b) ∈ L) :
    0 < queryEval (rayQuery q a b) p * queryEval (rayQuery q a b) x := by
  rw [queryEval_rayQuery, queryEval_rayQuery]
  have h := mul_pos (sq_pos_of_ne_zero hq) (orientation_mul_pos_of_cell hp hx hab)
  nlinarith only [h]

/-- A cell between the two extremal rays cannot meet the query line below the apex. -/
theorem exterior_ray_of_zone {P Q : Finset Point} {q : LineQuery} {a b c p : Point}
    (hq : q.1.2 ≠ 0) (ha : 0 < queryEval q a)
    (hb : queryEval q a < queryEval q b) (hc : queryEval q a < queryEval q c)
    (hbc : raySlope q a b ≤ raySlope q a c)
    (hab : (a, b) ∈ Q.offDiag) (hac : (a, c) ∈ Q.offDiag)
    (hp : p ∈ queryZone P Q.offDiag q) :
    0 < queryEval (rayQuery q a b) p ∨ queryEval (rayQuery q a c) p < 0 := by
  classical
  obtain ⟨_, σ, hpσ, x, hxσ, hxzero⟩ := Finset.mem_filter.mp hp
  have hpb := rayQuery_mul_pos_of_cell hq hpσ hxσ hab
  have hpc := rayQuery_mul_pos_of_cell hq hpσ hxσ hac
  by_contra h
  have hpbn : queryEval (rayQuery q a b) p ≤ 0 := le_of_not_gt (fun hb => h (Or.inl hb))
  have hpcn : 0 ≤ queryEval (rayQuery q a c) p := le_of_not_gt (fun hc => h (Or.inr hc))
  have hxb : queryEval (rayQuery q a b) x < 0 := by nlinarith
  have hxc : 0 < queryEval (rayQuery q a c) x := by nlinarith
  rw [queryEval_rayQuery_slope q a b x (ne_of_gt hb), hxzero] at hxb
  rw [queryEval_rayQuery_slope q a c x (ne_of_gt hc), hxzero] at hxc
  have hxb' : raySlope q a b * (0 - queryEval q a) - (x.1 - a.1) < 0 := by
    by_contra hnon
    have := mul_nonneg (sub_pos.mpr hb).le (le_of_not_gt hnon)
    linarith
  have hxc' := (mul_pos_iff_of_pos_left (sub_pos.mpr hc)).mp hxc
  have horder := mul_le_mul_of_nonneg_right hbc ha.le
  nlinarith only [hxb', hxc', horder]

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_QuerySectors

section OriginalModule_LinearCrossingFamilies_PositiveSectorCover

/-! ## Two sample-empty sectors cover the positive half of a generic query zone -/

namespace LinearCrossingFamilies

noncomputable section

local instance positiveCoverDecEqPoint : DecidableEq Point := Classical.decEq _

theorem rayQuery_nonpos_of_slope_le {q : LineQuery} {a b p : Point}
    (hb : queryEval q a < queryEval q b) (hp : queryEval q a < queryEval q p)
    (hbp : raySlope q a b ≤ raySlope q a p) : queryEval (rayQuery q a b) p ≤ 0 := by
  have h := (div_le_div_iff₀ (sub_pos.mpr hb) (sub_pos.mpr hp)).mp hbp
  rw [queryEval_rayQuery_formula]
  nlinarith only [h]

theorem rayQuery_nonneg_of_slope_le {q : LineQuery} {a b p : Point}
    (hb : queryEval q a < queryEval q b) (hp : queryEval q a < queryEval q p)
    (hpb : raySlope q a p ≤ raySlope q a b) : 0 ≤ queryEval (rayQuery q a b) p := by
  have h := (div_le_div_iff₀ (sub_pos.mpr hp) (sub_pos.mpr hb)).mp hpb
  rw [queryEval_rayQuery_formula]
  nlinarith only [h]

/-- The empty, singleton, and multiple-point sides are all included. -/
theorem exists_positive_sector_cover {P Q : Finset Point} {q : LineQuery}
    (hQ : 2 ≤ Q.card) (hq : q.1.2 ≠ 0)
    (hinj : Set.InjOn (queryEval q) (Q : Set Point)) :
    ∃ C : Finset (Finset Point), C.card ≤ 2 ∧
      (∀ R ∈ C, R ∈ sectorTraces P ∧ Disjoint Q R) ∧
      ∀ p ∈ queryZone P Q.offDiag q, 0 < queryEval q p → p ∈ C.biUnion id := by
  classical
  let D := positiveTrace Q q
  rcases D.eq_empty_or_nonempty with hD | hD
  · refine ⟨{positiveTrace P q}, by simp, ?_, ?_⟩
    · intro R hR
      have hR' : R = positiveTrace P q := Finset.mem_singleton.mp hR
      subst R
      refine ⟨positiveTrace_mem_sectorTraces P q, Finset.disjoint_left.mpr ?_⟩
      intro p hpQ hpR
      have hpD : p ∈ D := Finset.mem_filter.mpr ⟨hpQ, (Finset.mem_filter.mp hpR).2⟩
      simp only [hD, Finset.notMem_empty] at hpD
    · intro p hp hpq
      have hpP := (Finset.mem_filter.mp hp).1
      exact Finset.mem_biUnion.mpr ⟨positiveTrace P q, Finset.mem_singleton_self _,
        Finset.mem_filter.mpr ⟨hpP, hpq⟩⟩
  obtain ⟨a, haD, hamin⟩ := D.exists_min_image (queryEval q) hD
  have haQ : a ∈ Q := (Finset.mem_filter.mp haD).1
  have hapos : 0 < queryEval q a := (Finset.mem_filter.mp haD).2
  have habove : ∀ b ∈ D.erase a, queryEval q a < queryEval q b := by
    intro b hb
    obtain ⟨hba, hbD⟩ := Finset.mem_erase.mp hb
    apply lt_of_le_of_ne (hamin b hbD)
    intro hab
    exact hba (hinj (Finset.mem_filter.mp hbD).1 haQ hab.symm)
  rcases (D.erase a).eq_empty_or_nonempty with hsingle | hmulti
  · obtain ⟨b, hbQ, hba⟩ := Q.exists_mem_ne (by omega) a
    let r := endpointQuery a b
    let R := querySector P q r
    let S := querySector P q (-r)
    have hDsingle : ∀ p ∈ D, p = a := by
      intro p hp
      by_contra hpa
      have hm := Finset.mem_erase.mpr ⟨hpa, hp⟩
      rw [hsingle] at hm
      exact Finset.notMem_empty _ hm
    have hempty : ∀ u : LineQuery, (∀ p, queryEval u p = orientation a b p ∨
        queryEval u p = -orientation a b p) → Disjoint Q (querySector P q u) := by
      intro u hu
      apply Finset.disjoint_left.mpr
      intro p hpQ hpR
      obtain ⟨_, hpq, hpu⟩ := mem_querySector.mp hpR
      have hpa := hDsingle p (Finset.mem_filter.mpr ⟨hpQ, hpq⟩)
      subst p
      rcases hu a with he | he <;> rw [he] at hpu <;> simp [orientation] at hpu
    refine ⟨{R, S}, (Finset.card_insert_le _ _).trans (by simp), ?_, ?_⟩
    · intro U hU
      rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨querySector_mem P q r, hempty r (fun p => Or.inl (queryEval_endpointQuery a b p))⟩
      · have : U = S := Finset.mem_singleton.mp hU
        subst U
        exact ⟨querySector_mem P q (-r), hempty (-r) (fun p =>
          Or.inr (by rw [queryEval_neg, queryEval_endpointQuery]))⟩
    · intro p hp hpq
      obtain ⟨hpP, σ, hpσ, x, hxσ, _⟩ := Finset.mem_filter.mp hp
      have hprod := orientation_mul_pos_of_cell hpσ hxσ (Finset.mem_offDiag.mpr ⟨haQ, hbQ, hba.symm⟩)
      have hn : orientation a b p ≠ 0 := by intro h; rw [h, zero_mul] at hprod; exact hprod.false
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · apply Finset.mem_biUnion.mpr
        refine ⟨S, by simp, mem_querySector.mpr ⟨hpP, hpq, ?_⟩⟩
        simpa only [queryEval_neg, r, queryEval_endpointQuery, neg_pos] using hneg
      · apply Finset.mem_biUnion.mpr
        exact ⟨R, by simp, mem_querySector.mpr ⟨hpP, hpq, by
          simpa only [r, queryEval_endpointQuery] using hpos⟩⟩
  obtain ⟨b, hbD, hbmin⟩ := (D.erase a).exists_min_image (raySlope q a) hmulti
  obtain ⟨c, hcD, hcmax⟩ := (D.erase a).exists_max_image (raySlope q a) hmulti
  have hbQ := (Finset.mem_filter.mp (Finset.mem_erase.mp hbD).2).1
  have hcQ := (Finset.mem_filter.mp (Finset.mem_erase.mp hcD).2).1
  have hb := habove b hbD
  have hc := habove c hcD
  let R := querySector P q (rayQuery q a b)
  let S := querySector P q (-(rayQuery q a c))
  have hemptyR : Disjoint Q R := by
    apply Finset.disjoint_left.mpr
    intro p hpQ hpR
    obtain ⟨_, hpq, hpray⟩ := mem_querySector.mp hpR
    by_cases hpa : p = a
    · subst p
      simp [queryEval_rayQuery, orientation] at hpray
    have hpD : p ∈ D.erase a := Finset.mem_erase.mpr ⟨hpa, Finset.mem_filter.mpr ⟨hpQ, hpq⟩⟩
    exact (not_lt_of_ge (rayQuery_nonpos_of_slope_le hb (habove p hpD) (hbmin p hpD))) hpray
  have hemptyS : Disjoint Q S := by
    apply Finset.disjoint_left.mpr
    intro p hpQ hpS
    obtain ⟨_, hpq, hpray⟩ := mem_querySector.mp hpS
    rw [queryEval_neg] at hpray
    by_cases hpa : p = a
    · subst p
      simp [queryEval_rayQuery, orientation] at hpray
    have hpD : p ∈ D.erase a := Finset.mem_erase.mpr ⟨hpa, Finset.mem_filter.mpr ⟨hpQ, hpq⟩⟩
    have h := rayQuery_nonneg_of_slope_le hc (habove p hpD) (hcmax p hpD)
    linarith
  refine ⟨{R, S}, (Finset.card_insert_le _ _).trans (by simp), ?_, ?_⟩
  · intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact ⟨querySector_mem P q _, hemptyR⟩
    · have : U = S := Finset.mem_singleton.mp hU
      subst U
      exact ⟨querySector_mem P q _, hemptyS⟩
  · intro p hp hpq
    have hpP := (Finset.mem_filter.mp hp).1
    have hext := exterior_ray_of_zone hq hapos hb hc (hbmin c hcD)
      (Finset.mem_offDiag.mpr ⟨haQ, hbQ, (Finset.mem_erase.mp hbD).1.symm⟩)
      (Finset.mem_offDiag.mpr ⟨haQ, hcQ, (Finset.mem_erase.mp hcD).1.symm⟩) hp
    rcases hext with hR | hS
    · exact Finset.mem_biUnion.mpr ⟨R, by simp, mem_querySector.mpr ⟨hpP, hpq, hR⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨S, by simp, mem_querySector.mpr ⟨hpP, hpq, by simpa using hS⟩⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_PositiveSectorCover

section OriginalModule_LinearCrossingFamilies_FourSectorCover

/-! ## A four-sector cover for every nondegenerate query line -/

namespace LinearCrossingFamilies

noncomputable section

local instance fourCoverDecEqPoint : DecidableEq Point := Classical.decEq _

theorem queryZone_neg (P : Finset Point) (L : Finset (Point × Point)) (q : LineQuery) :
    queryZone P L (-q) = queryZone P L q := by
  classical
  unfold queryZone
  simp only [queryEval_neg, neg_eq_zero]

theorem exists_generic_four_sector_cover {P Q : Finset Point} {q : LineQuery}
    (hQ : 2 ≤ Q.card) (hq : q.1.2 ≠ 0)
    (hoff : ∀ p ∈ P, queryEval q p ≠ 0)
    (hinj : Set.InjOn (queryEval q) (Q : Set Point)) :
    ∃ C : Finset (Finset Point), C.card ≤ 4 ∧
      (∀ R ∈ C, R ∈ sectorTraces P ∧ Disjoint Q R) ∧
      queryZone P Q.offDiag q ⊆ C.biUnion id := by
  classical
  obtain ⟨C, hC, hCsector, hCcover⟩ := exists_positive_sector_cover (P := P) hQ hq hinj
  have hqneg : (-q).1.2 ≠ 0 := by simpa using hq
  have hinjneg : Set.InjOn (queryEval (-q)) (Q : Set Point) := by
    intro a ha b hb hab
    exact hinj ha hb (by simpa only [queryEval_neg, neg_inj] using hab)
  obtain ⟨D, hD, hDsector, hDcover⟩ := exists_positive_sector_cover (P := P) hQ hqneg hinjneg
  refine ⟨C ∪ D, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · intro R hR
    exact (Finset.mem_union.mp hR).elim (hCsector R) (hDsector R)
  · intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    rcases lt_or_gt_of_ne (hoff p hpP) with hneg | hpos
    · have hmem := hDcover p (by rwa [queryZone_neg]) (by simpa only [queryEval_neg, neg_pos] using hneg)
      obtain ⟨R, hR, hpR⟩ := Finset.mem_biUnion.mp hmem
      exact Finset.mem_biUnion.mpr ⟨R, Finset.mem_union_right _ hR, hpR⟩
    · obtain ⟨R, hR, hpR⟩ := Finset.mem_biUnion.mp (hCcover p hp hpos)
      exact Finset.mem_biUnion.mpr ⟨R, Finset.mem_union_left _ hR, hpR⟩

/-- The generic cover transfers back by zone inclusion; no boundary assumption
on the original query line is added. -/
theorem exists_four_sector_cover {P Q : Finset Point} (hQP : Q ⊆ P) (hQ : 2 ≤ Q.card)
    {a b : Point} (hab : a ≠ b) :
    ∃ C : Finset (Finset Point), C.card ≤ 4 ∧
      (∀ R ∈ C, R ∈ sectorTraces P ∧ Disjoint Q R) ∧
      arrangementZone P Q.offDiag s(a, b) ⊆ C.biUnion id := by
  obtain ⟨q, hzone, hqy, hoff, hinj⟩ :=
    exists_generic_query_preserving_zone P Q.offDiag (endpointQuery_normal_ne_zero hab)
  obtain ⟨C, hC, hsector, hcover⟩ := exists_generic_four_sector_cover hQ hqy hoff
    (fun _ ha _ hb heq => hinj (hQP ha) (hQP hb) heq)
  refine ⟨C, hC, hsector, ?_⟩
  rw [queryZone_endpointQuery] at hzone
  exact hzone.trans hcover

/-- A bounded sector net supplies small zones for all lines, not merely those
spanned by the original point set. -/
theorem small_zone_of_sector_net {P Q : Finset Point} (hQP : Q ⊆ P) (hQ : 2 ≤ Q.card)
    (hnet : ∀ R ∈ sectorTraces P, P.card ≤ 128 * R.card → (Q ∩ R).Nonempty)
    {a b : Point} (hab : a ≠ b) :
    32 * (arrangementZone P Q.offDiag s(a, b)).card ≤ P.card := by
  obtain ⟨C, hC, hsector, hcover⟩ := exists_four_sector_cover hQP hQ hab
  exact small_zone_of_four_sector_cover hnet hC (fun R hR => (hsector R hR).1)
    (fun R hR => (hsector R hR).2) hcover

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_FourSectorCover

section OriginalModule_LinearCrossingFamilies_SmallZoneArrangement

/-! ## Unconditional bounded small-zone arrangements and fixed-parameter extraction -/

namespace LinearCrossingFamilies

noncomputable section

local instance smallZoneDecEqPoint : DecidableEq Point := Classical.decEq _

/-- The sector net plus two prescribed points spans at most this many oriented lines. -/
def sectorArrangementBound : ℕ := 65538 ^ 2

/-- A fixed-size spanned-line arrangement has uniformly small zones.
General position is not needed until the subsequent boundary-loss estimate. -/
theorem exists_bounded_small_zone_arrangement (P : Finset Point) :
    ∃ L : Finset (Point × Point), L ⊆ P.offDiag ∧ L.card ≤ sectorArrangementBound ∧
      ∀ e ∈ spannedPairs P, 32 * (arrangementZone P L e).card ≤ P.card := by
  classical
  by_cases hP : 2 ≤ P.card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    have hpair : ({a, b} : Finset Point) ⊆ P :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    have hpaircard : ({a, b} : Finset Point).card = 2 := by simp [hab]
    obtain ⟨Q, hQP, hpairQ, hQcard, hnet⟩ := exists_sector_net_containing ⟨a, ha⟩ hpair
    have hQtwo : 2 ≤ Q.card := by simpa only [hpaircard] using Finset.card_le_card hpairQ
    have hQbound : Q.card ≤ 65538 := by simpa only [hpaircard] using hQcard
    refine ⟨Q.offDiag, Finset.offDiag_mono hQP, ?_, ?_⟩
    · calc
        _ ≤ Q.card * Q.card := by rw [Finset.offDiag_card]; exact Nat.sub_le _ _
        _ ≤ 65538 * 65538 := Nat.mul_le_mul hQbound hQbound
        _ = sectorArrangementBound := (pow_two _).symm
    · intro e he
      induction e using Sym2.inductionOn with | _ u v =>
      exact small_zone_of_sector_net hQP hQtwo hnet
        ((nondegenerate_mk_iff u v).mp (mem_spannedPairs.mp he).2)
  · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    intro e he
    induction e using Sym2.inductionOn with | _ a b =>
    obtain ⟨hspan, hnd⟩ := mem_spannedPairs.mp he
    obtain ⟨ha, hb⟩ := (spannedBy_mk_iff P a b).mp hspan
    have hcard := Finset.one_lt_card.mpr ⟨a, ha, b, hb, (nondegenerate_mk_iff a b).mp hnd⟩
    omega

/-- Keep the absolute arrangement bound symbolic while proving the extraction
arithmetic; its exponential cell bound need never be evaluated numerically. -/
theorem near_avoidance_extraction_of_small_zones
    (hzones : ∃ r : ℕ, ∀ P : Finset Point,
      ∃ L : Finset (Point × Point), L ⊆ P.offDiag ∧ L.card ≤ r ∧
        ∀ e ∈ spannedPairs P, 32 * (arrangementZone P L e).card ≤ P.card) :
    ∃ H : ℕ, 2 ≤ H ∧
      ∀ (P : Finset Point) (m : ℕ), GeneralPosition P → 1 ≤ m → H * m ≤ P.card →
        ∃ A B : Finset Point, A ⊆ P ∧ B ⊆ P ∧ Separated A B ∧
          A.card = m ∧ B.card = m ∧ (avoidanceDefect A B : ℝ) ≤ (m : ℝ) ^ 2 / 4 := by
  obtain ⟨r, hz⟩ := hzones
  refine ⟨zoneExtractionThreshold r, ?_, ?_⟩
  · unfold zoneExtractionThreshold
    omega
  · intro P m hP hm hlarge
    obtain ⟨L, hL, hcard, hzone⟩ := hz P
    apply exists_near_avoiding_pair_of_arrangement hP hL hm _ hzone
    exact (Nat.mul_le_mul_right m (zoneExtractionThreshold_mono hcard)).trans hlarge

/-- The fixed `ε = 1/4` near-avoidance extraction needed by the crossing proof,
with every geometric dependency discharged. -/
theorem fixed_parameter_near_avoidance_extraction :
    ∃ H : ℕ, 2 ≤ H ∧
      ∀ (P : Finset Point) (m : ℕ), GeneralPosition P → 1 ≤ m → H * m ≤ P.card →
        ∃ A B : Finset Point, A ⊆ P ∧ B ⊆ P ∧ Separated A B ∧
          A.card = m ∧ B.card = m ∧ (avoidanceDefect A B : ℝ) ≤ (m : ℝ) ^ 2 / 4 :=
  near_avoidance_extraction_of_small_zones
    ⟨sectorArrangementBound, exists_bounded_small_zone_arrangement⟩

end

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_SmallZoneArrangement

section OriginalModule_LinearCrossingFamilies_MainTheorem

/-! ## Linear crossing families

The main theorem is unconditional. The absolute constant is quantified before
the finite planar set, and no coordinate or extraction hypothesis remains.
-/

namespace LinearCrossingFamilies

theorem linearCrossingFamilies : LinearCrossingFamiliesStatement :=
  linearCrossingFamilies_of_fixed_extraction fixed_parameter_near_avoidance_extraction

/-- Every finite planar set of at least two points in general position has a
linear-size family of pairwise interior-crossing segments with pairwise distinct
endpoints, with an absolute positive constant independent of the point set. -/
theorem linear_crossing_families :
    ∃ c : ℝ, 0 < c ∧
      ∀ P : Finset Point, 2 ≤ P.card → GeneralPosition P →
        ∃ F : Set (Sym2 Point),
          IsCrossingFamily P F ∧ c * (P.card : ℝ) ≤ F.ncard :=
  linearCrossingFamilies

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_MainTheorem

section OriginalModule_LinearCrossingFamilies_SmokeTest

/-!
## Elementary environment checks

These elementary checks of arithmetic tactics are independent of the geometric proof.
-/

namespace LinearCrossingFamilies

theorem squared_distance_nonneg (p q : ℝ × ℝ) :
    0 ≤ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  positivity

theorem determinant_swap (a b c d : ℝ) :
    a * d - b * c = -(c * b - d * a) := by
  ring

theorem half_cardinality_pos (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ n / 2 := by
  omega

end LinearCrossingFamilies

end OriginalModule_LinearCrossingFamilies_SmokeTest

/-! ## Final unconditional theorem and axiom audit -/

#check LinearCrossingFamilies.linear_crossing_families
#print axioms LinearCrossingFamilies.linearCrossingFamilies
#print axioms LinearCrossingFamilies.linear_crossing_families

example : LinearCrossingFamilies.LinearCrossingFamiliesStatement :=
  LinearCrossingFamilies.linear_crossing_families
