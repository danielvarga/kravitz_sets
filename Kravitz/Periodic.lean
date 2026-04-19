import Kravitz.Witness

open scoped BigOperators

namespace KravitzLP

open Classical

variable {n : ℕ} [NeZero n]

/-- A subset of `ZMod n` avoids `6` if no triple from the set represents `6` as `a+b-2c`. -/
def SixMissing (A : Set (ZMod n)) : Prop :=
  ∀ a b c : ZMod n, a ∈ A → b ∈ A → c ∈ A → a + b - 2 * c ≠ (6 : ZMod n)

/-- The witness points embedded into `ZMod n`. -/
def witnessPointMod (i : Fin 8) : ZMod n :=
  witnessPoint i

/-- The translate pattern of `A` seen on the witness set. -/
noncomputable def pattern (A : Set (ZMod n)) (t : ZMod n) : Finset (Fin 8) :=
  Finset.univ.filter fun i => t + witnessPointMod i ∈ A

/-- The fiber of the `j`-th admissible atom under the translate-pattern map. -/
noncomputable def atomFiber (A : Set (ZMod n)) (j : Atom) : Finset (ZMod n) :=
  Finset.univ.filter fun t => pattern A t = atomSupport j

/-- The normalized mass of the `j`-th admissible atom. -/
noncomputable def atomWeight (A : Set (ZMod n)) (j : Atom) : ℚ :=
  (↑(Finset.card (atomFiber A j)) : ℚ) / Fintype.card (ZMod n)

/-- The normalized density of `A`. -/
noncomputable def density (A : Set (ZMod n)) : ℚ :=
  (↑(Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | t ∈ A}) : ℚ) / Fintype.card (ZMod n)

@[simp]
theorem mem_pattern_iff (A : Set (ZMod n)) (t : ZMod n) (i : Fin 8) :
    i ∈ pattern A t ↔ t + witnessPointMod i ∈ A := by
  classical
  simp [pattern]

theorem pattern_forbiddenFree (A : Set (ZMod n)) (hA : SixMissing A) (t : ZMod n) :
    ForbiddenFree (pattern A t) := by
  intro i j k hi hj hk hijk
  have hai : t + witnessPointMod i ∈ A := by
    simpa [mem_pattern_iff] using hi
  have haj : t + witnessPointMod j ∈ A := by
    simpa [mem_pattern_iff] using hj
  have hak : t + witnessPointMod k ∈ A := by
    simpa [mem_pattern_iff] using hk
  have hijk' :
      witnessPointMod i + witnessPointMod j - 2 * witnessPointMod k = (6 : ZMod n) := by
    have hcast :
        (((witnessPoint i + witnessPoint j - 2 * witnessPoint k : Int) : ZMod n)
          = (((6 : Int) : ZMod n))) := by
      exact congrArg (fun z : Int => (z : ZMod n)) hijk
    simpa [witnessPointMod, sub_eq_add_neg, two_mul, add_assoc, add_left_comm, add_comm, mul_add] using hcast
  have hsum :
      (t + witnessPointMod i) + (t + witnessPointMod j) - 2 * (t + witnessPointMod k)
        = (6 : ZMod n) := by
    calc
      (t + witnessPointMod i) + (t + witnessPointMod j) - 2 * (t + witnessPointMod k)
          = witnessPointMod i + witnessPointMod j - 2 * witnessPointMod k := by
              ring
      _ = (6 : ZMod n) := hijk'
  exact hA _ _ _ hai haj hak hsum

theorem existsUnique_atomIndex (A : Set (ZMod n)) (hA : SixMissing A) (t : ZMod n) :
    ∃! j : Atom, pattern A t = atomSupport j := by
  have hff : ForbiddenFree (pattern A t) := pattern_forbiddenFree A hA t
  have himage : pattern A t ∈ (Finset.univ.image atomSupport : Finset (Finset (Fin 8))) := by
    rw [← forbiddenFree_univ_eq_image]
    simpa using hff
  rcases Finset.mem_image.mp himage with ⟨j, _, hj⟩
  refine ⟨j, hj.symm, ?_⟩
  intro j' hj'
  apply atomSupport_injective
  exact (hj.trans hj').symm

/-- The unique admissible atom matching the translate pattern of `A` at `t`. -/
noncomputable def atomIndex (A : Set (ZMod n)) (hA : SixMissing A) (t : ZMod n) : Atom :=
  Classical.choose (existsUnique_atomIndex A hA t)

theorem pattern_eq_atomSupport_atomIndex (A : Set (ZMod n)) (hA : SixMissing A) (t : ZMod n) :
    pattern A t = atomSupport (atomIndex A hA t) := by
  exact (Classical.choose_spec (existsUnique_atomIndex A hA t)).1

theorem atomIndex_eq_iff (A : Set (ZMod n)) (hA : SixMissing A) (t : ZMod n) (j : Atom) :
    atomIndex A hA t = j ↔ pattern A t = atomSupport j := by
  constructor
  · intro h
    simpa [h] using pattern_eq_atomSupport_atomIndex A hA t
  · intro h
    exact ((Classical.choose_spec (existsUnique_atomIndex A hA t)).2 j h).symm

@[simp]
theorem mem_atomFiber_iff (A : Set (ZMod n)) (hA : SixMissing A) (j : Atom) (t : ZMod n) :
    t ∈ atomFiber A j ↔ atomIndex A hA t = j := by
  simp [atomFiber, atomIndex_eq_iff]

theorem atomWeight_nonneg (A : Set (ZMod n)) (j : Atom) : 0 ≤ atomWeight A j := by
  dsimp [atomWeight]
  positivity

theorem support_subset_pattern_iff (A : Set (ZMod n)) (S : Finset (Fin 8)) (t : ZMod n) :
    S ⊆ pattern A t ↔ ∀ y ∈ S.image witnessPoint, t + (y : ZMod n) ∈ A := by
  constructor
  · intro h y hy
    rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
    exact (mem_pattern_iff A t k).mp (h hk)
  · intro h k hk
    exact (mem_pattern_iff A t k).mpr <|
      h _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

theorem congrRight_subset_pattern_iff (A : Set (ZMod n)) (i : Eqn) (t : ZMod n) :
    congrRightSupport i ⊆ pattern A t ↔ congrLeftSupport i ⊆ pattern A (t + congrShift i) := by
  rw [support_subset_pattern_iff, support_subset_pattern_iff]
  constructor
  · intro h y hy
    rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
    have hy' : witnessPoint k + congrShift i ∈ (congrRightSupport i).image witnessPoint := by
      rw [congr_translate_spec i]
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    simpa [add_assoc, add_left_comm, add_comm] using h _ hy'
  · intro h y hy
    have hy' : y ∈ (congrLeftSupport i).image (fun k => witnessPoint k + congrShift i) := by
      simpa [congr_translate_spec i] using hy
    rcases Finset.mem_image.mp hy' with ⟨k, hk, hky⟩
    have hk' : t + (congrShift i : ZMod n) + witnessPoint k ∈ A := by
      simpa [add_assoc, add_left_comm, add_comm] using h _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    have hky' : ((y : Int) : ZMod n) = (((witnessPoint k + congrShift i : Int)) : ZMod n) := by
      exact congrArg (fun z : Int => (z : ZMod n)) hky.symm
    simpa [hky', add_assoc, add_left_comm, add_comm] using hk'

theorem congr_subset_count_eq (A : Set (ZMod n)) (i : Eqn) :
    Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | congrLeftSupport i ⊆ pattern A t}
      = Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | congrRightSupport i ⊆ pattern A t} := by
  classical
  refine Finset.card_bij'
    (i := fun t _ => t - congrShift i)
    (j := fun t _ => t + congrShift i)
    ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    have ht' : congrLeftSupport i ⊆ pattern A ((t - congrShift i) + congrShift i) := by
      simpa [sub_eq_add_neg, add_assoc] using ht
    have := (congrRight_subset_pattern_iff A i (t - congrShift i)).mpr ht'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    have := (congrRight_subset_pattern_iff A i t).mp ht
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  · intro t ht
    simp [sub_eq_add_neg, add_assoc]
  · intro t ht
    simp [sub_eq_add_neg, add_assoc]

theorem supportCount_eq_sum_atomFiber
    (A : Set (ZMod n)) (hA : SixMissing A) (S : Finset (Fin 8)) :
    Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | S ⊆ pattern A t}
      = (Finset.sum (Finset.univ.filter (fun j : Atom => S ⊆ atomSupport j))
          (fun j => Finset.card (atomFiber A j))) := by
  classical
  have hsum :=
    Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset (ZMod n)))
      (t := Finset.univ.filter fun j : Atom => S ⊆ atomSupport j)
      (g := atomIndex A hA)
  have hfilter :
      {t ∈ (Finset.univ : Finset (ZMod n)) | S ⊆ pattern A t}
        = {t ∈ (Finset.univ : Finset (ZMod n)) |
            atomIndex A hA t ∈ Finset.univ.filter fun j : Atom => S ⊆ atomSupport j} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pattern_eq_atomSupport_atomIndex]
  rw [hfilter]
  calc
    Finset.card
        {t ∈ (Finset.univ : Finset (ZMod n)) |
          atomIndex A hA t ∈ Finset.univ.filter fun j : Atom => S ⊆ atomSupport j}
      = Finset.sum (Finset.univ.filter (fun j : Atom => S ⊆ atomSupport j))
          (fun j => Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | atomIndex A hA t = j}) := by
            simpa using hsum.symm
    _ = Finset.sum (Finset.univ.filter (fun j : Atom => S ⊆ atomSupport j))
          (fun j => Finset.card (atomFiber A j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          congr
          ext t
          simp [atomIndex_eq_iff]

private theorem zmodCard_ne_zero_rat : (Fintype.card (ZMod n) : ℚ) ≠ 0 := by
  exact_mod_cast (show Fintype.card (ZMod n) ≠ 0 by simpa using NeZero.ne n)

theorem atomWeight_sum (A : Set (ZMod n)) (hA : SixMissing A) :
    (∑ j : Atom, atomWeight A j) = 1 := by
  have hcount_nat0 := supportCount_eq_sum_atomFiber A hA (∅ : Finset (Fin 8))
  have hcount_nat :
      Fintype.card (ZMod n) = Finset.sum Finset.univ (fun j => Finset.card (atomFiber A j)) := by
    have hleft :
        {t ∈ (Finset.univ : Finset (ZMod n)) | (∅ : Finset (Fin 8)) ⊆ pattern A t}
          = (Finset.univ : Finset (ZMod n)) := by
      ext t
      simp
    have hright :
        Finset.univ.filter (fun j : Atom => (∅ : Finset (Fin 8)) ⊆ atomSupport j) = Finset.univ := by
      ext j
      simp
    rw [hleft, hright] at hcount_nat0
    simpa using hcount_nat0
  have hcount_q :
      (↑(Fintype.card (ZMod n)) : ℚ)
        = ∑ j : Atom, (↑(Finset.card (atomFiber A j)) : ℚ) := by
    exact_mod_cast hcount_nat
  calc
    ∑ j : Atom, atomWeight A j
      = ∑ j : Atom, (↑(Finset.card (atomFiber A j)) : ℚ) / Fintype.card (ZMod n) := by
          simp [atomWeight]
    _ = (∑ j : Atom, (↑(Finset.card (atomFiber A j)) : ℚ)) / Fintype.card (ZMod n) := by
          rw [Finset.sum_div]
    _ = (↑(Fintype.card (ZMod n)) : ℚ) / Fintype.card (ZMod n) := by
          rw [← hcount_q]
    _ = 1 := by
          exact div_self zmodCard_ne_zero_rat

theorem atomWeight_objective_eq_density (A : Set (ZMod n)) (hA : SixMissing A) :
    (∑ j : Atom, (e j : ℚ) * atomWeight A j) = density A := by
  have hcount_nat0 := supportCount_eq_sum_atomFiber A hA ({0} : Finset (Fin 8))
  have hcount_nat :
      Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | t ∈ A}
        = Finset.sum (Finset.univ.filter (fun j : Atom => (0 : Fin 8) ∈ atomSupport j))
            (fun j => Finset.card (atomFiber A j)) := by
    have hleft :
        {t ∈ (Finset.univ : Finset (ZMod n)) | ({0} : Finset (Fin 8)) ⊆ pattern A t}
          = {t ∈ (Finset.univ : Finset (ZMod n)) | t ∈ A} := by
      ext t
      simp [Finset.singleton_subset_iff, mem_pattern_iff, witnessPointMod, witnessPoint]
    have hright :
        Finset.univ.filter (fun j : Atom => ({0} : Finset (Fin 8)) ⊆ atomSupport j)
          = Finset.univ.filter (fun j : Atom => (0 : Fin 8) ∈ atomSupport j) := by
      ext j
      simp [Finset.singleton_subset_iff]
    rw [hleft, hright] at hcount_nat0
    exact hcount_nat0
  have hcount_q :
      (↑(Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | t ∈ A}) : ℚ)
        = Finset.sum (Finset.univ.filter (fun j : Atom => (0 : Fin 8) ∈ atomSupport j))
            (fun j => (↑(Finset.card (atomFiber A j)) : ℚ)) := by
    exact_mod_cast hcount_nat
  calc
    ∑ j : Atom, (e j : ℚ) * atomWeight A j
      = ∑ j : Atom, (e j : ℚ) * ((↑(Finset.card (atomFiber A j)) : ℚ) / Fintype.card (ZMod n)) := by
          simp [atomWeight]
    _ = ∑ j : Atom, ((e j : ℚ) * (↑(Finset.card (atomFiber A j)) : ℚ)) / Fintype.card (ZMod n) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j : Atom, (e j : ℚ) * (↑(Finset.card (atomFiber A j)) : ℚ)) / Fintype.card (ZMod n) := by
          rw [Finset.sum_div]
    _ = (Finset.sum (Finset.univ.filter (fun j : Atom => (0 : Fin 8) ∈ atomSupport j))
            (fun j => (↑(Finset.card (atomFiber A j)) : ℚ))) / Fintype.card (ZMod n) := by
          congr 1
          calc
            ∑ j : Atom, (e j : ℚ) * (↑(Finset.card (atomFiber A j)) : ℚ)
              = ∑ j : Atom,
                  if (0 : Fin 8) ∈ atomSupport j then (↑(Finset.card (atomFiber A j)) : ℚ) else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [e_eq_indicator]
                    by_cases h0 : (0 : Fin 8) ∈ atomSupport j <;> simp [h0]
            _ = Finset.sum (Finset.univ.filter (fun j : Atom => (0 : Fin 8) ∈ atomSupport j))
                  (fun j => (↑(Finset.card (atomFiber A j)) : ℚ)) := by
                    symm
                    rw [Finset.sum_filter]
    _ = density A := by
          rw [← hcount_q]
          simp [density]

theorem atomWeight_congr (A : Set (ZMod n)) (hA : SixMissing A) (i : Eqn) :
    (∑ j : Atom, (C i j : ℚ) * atomWeight A j) = 0 := by
  let L : Finset Atom := Finset.univ.filter (fun j : Atom => congrLeftSupport i ⊆ atomSupport j)
  let R : Finset Atom := Finset.univ.filter (fun j : Atom => congrRightSupport i ⊆ atomSupport j)
  have hcount_nat : Finset.sum L (fun j => Finset.card (atomFiber A j))
      = Finset.sum R (fun j => Finset.card (atomFiber A j)) := by
    calc
      Finset.sum L (fun j => Finset.card (atomFiber A j))
        = Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | congrLeftSupport i ⊆ pattern A t} := by
            symm
            simpa [L] using supportCount_eq_sum_atomFiber A hA (congrLeftSupport i)
      _ = Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | congrRightSupport i ⊆ pattern A t} := by
            exact congr_subset_count_eq A i
      _ = Finset.sum R (fun j => Finset.card (atomFiber A j)) := by
            simpa [R] using supportCount_eq_sum_atomFiber A hA (congrRightSupport i)
  have hcount_q :
      Finset.sum L (fun j => (↑(Finset.card (atomFiber A j)) : ℚ))
        = Finset.sum R (fun j => (↑(Finset.card (atomFiber A j)) : ℚ)) := by
    exact_mod_cast hcount_nat
  calc
    ∑ j : Atom, (C i j : ℚ) * atomWeight A j
      = ∑ j : Atom, (C i j : ℚ) * ((↑(Finset.card (atomFiber A j)) : ℚ) / Fintype.card (ZMod n)) := by
          simp [atomWeight]
    _ = ∑ j : Atom, ((C i j : ℚ) * (↑(Finset.card (atomFiber A j)) : ℚ)) / Fintype.card (ZMod n) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j : Atom, (C i j : ℚ) * (↑(Finset.card (atomFiber A j)) : ℚ)) / Fintype.card (ZMod n) := by
          rw [Finset.sum_div]
    _ = ((Finset.sum L (fun j => (↑(Finset.card (atomFiber A j)) : ℚ)))
          - (Finset.sum R (fun j => (↑(Finset.card (atomFiber A j)) : ℚ)))) / Fintype.card (ZMod n) := by
          congr 1
          calc
            ∑ j : Atom, (C i j : ℚ) * (↑(Finset.card (atomFiber A j)) : ℚ)
              = ∑ j : Atom,
                  ((if congrLeftSupport i ⊆ atomSupport j then (↑(Finset.card (atomFiber A j)) : ℚ) else 0)
                    - (if congrRightSupport i ⊆ atomSupport j then (↑(Finset.card (atomFiber A j)) : ℚ) else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [C_eq_support_difference]
                    by_cases hL : congrLeftSupport i ⊆ atomSupport j <;>
                      by_cases hR : congrRightSupport i ⊆ atomSupport j <;>
                      simp [hL, hR]
            _ = (∑ j : Atom,
                    if congrLeftSupport i ⊆ atomSupport j then (↑(Finset.card (atomFiber A j)) : ℚ) else 0)
                  - (∑ j : Atom,
                    if congrRightSupport i ⊆ atomSupport j then (↑(Finset.card (atomFiber A j)) : ℚ) else 0) := by
                    rw [Finset.sum_sub_distrib]
            _ = (Finset.sum L (fun j => (↑(Finset.card (atomFiber A j)) : ℚ)))
                  - (Finset.sum R (fun j => (↑(Finset.card (atomFiber A j)) : ℚ))) := by
                    simp [L, R, Finset.sum_filter]
    _ = 0 := by
          rw [hcount_q]
          ring

theorem density_le_two_sevenths (A : Set (ZMod n)) (hA : SixMissing A) :
    density A ≤ (2 : ℚ) / 7 := by
  have hbound :=
    lp_bound_from_dual
      (x := atomWeight A)
      (hx_nonneg := atomWeight_nonneg A)
      (hx_sum := atomWeight_sum A hA)
      (hx_congr := atomWeight_congr A hA)
  simpa [atomWeight_objective_eq_density A hA] using hbound

theorem exists_six_of_density_gt_two_sevenths (A : Set (ZMod n))
    (hA : (2 : ℚ) / 7 < density A) :
    ∃ a b c : ZMod n, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + b - 2 * c = (6 : ZMod n) := by
  by_contra hNo
  have hmiss : SixMissing A := by
    intro a b c ha hb hc hEq
    exact hNo ⟨a, b, c, ha, hb, hc, hEq⟩
  have hbound := density_le_two_sevenths A hmiss
  linarith

theorem exists_mem_of_density_pos (A : Set (ZMod n)) (hA : 0 < density A) :
    ∃ a : ZMod n, a ∈ A := by
  have hcard_pos : 0 < Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | t ∈ A} := by
    by_contra hcard_pos
    have hcard_zero : Finset.card {t ∈ (Finset.univ : Finset (ZMod n)) | t ∈ A} = 0 :=
      Nat.eq_zero_of_not_pos hcard_pos
    have hdensity_zero : density A = 0 := by
      simp [density, hcard_zero]
    linarith
  rcases Finset.card_pos.mp hcard_pos with ⟨a, ha⟩
  exact ⟨a, by simpa using ha⟩

section PrimeField

variable {p : ℕ} [Fact p.Prime]

/-- Pulling back a set under multiplication by `μ`. -/
def mulPreimage (μ : ZMod p) (A : Set (ZMod p)) : Set (ZMod p) :=
  fun x => μ * x ∈ A

theorem density_mulPreimage (A : Set (ZMod p)) {μ : ZMod p} (hμ : μ ≠ 0) :
    density (mulPreimage μ A) = density A := by
  have hcard :
      Finset.card {t ∈ (Finset.univ : Finset (ZMod p)) | t ∈ mulPreimage μ A}
        = Finset.card {t ∈ (Finset.univ : Finset (ZMod p)) | t ∈ A} := by
    classical
    refine Finset.card_bij'
      (i := fun t _ => μ * t)
      (j := fun t _ => μ⁻¹ * t)
      ?_ ?_ ?_ ?_
    · intro t ht
      simpa [mulPreimage] using ht
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      change μ * (μ⁻¹ * t) ∈ A
      simpa [mul_assoc, hμ] using ht
    · intro t ht
      simp [hμ]
    · intro t ht
      simp [hμ]
  simp [density, hcard]

theorem theorem1_zmod (hp : 3 < p) (A : Set (ZMod p))
    (hA : (2 : ℚ) / 7 < density A) :
    ∀ c : ZMod p, ∃ a b d : ZMod p, a ∈ A ∧ b ∈ A ∧ d ∈ A ∧ a + b - 2 * d = c := by
  intro c
  by_cases hc : c = 0
  · have hpos : 0 < density A := by linarith
    rcases exists_mem_of_density_pos A hpos with ⟨a, ha⟩
    refine ⟨a, a, a, ha, ha, ha, ?_⟩
    simpa [hc] using (show a + a - 2 * a = (0 : ZMod p) by ring_nf)
  · have hp' : Nat.Prime p := Fact.out
    have h6 : (6 : ZMod p) ≠ 0 := by
      intro h6
      have hdiv : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp h6
      have h23 : p ∣ 2 ∨ p ∣ 3 := by
        have : p ∣ 2 * 3 := by simpa using hdiv
        exact hp'.dvd_mul.mp this
      rcases h23 with h2 | h3
      · have hp2 : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h2
        linarith
      · have hp3 : p ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) h3
        linarith
    let μ : ZMod p := c / 6
    have hμ6 : μ * 6 = c := by
      dsimp [μ]
      field_simp [h6]
    have hμ : μ ≠ 0 := by
      intro hμ
      rw [hμ, zero_mul] at hμ6
      exact hc hμ6.symm
    have hscaled : (2 : ℚ) / 7 < density (mulPreimage μ A) := by
      simpa [density_mulPreimage A hμ] using hA
    rcases exists_six_of_density_gt_two_sevenths (mulPreimage μ A) hscaled with
      ⟨x, y, z, hx, hy, hz, hxyz⟩
    refine ⟨μ * x, μ * y, μ * z, ?_, ?_, ?_, ?_⟩
    · simpa [mulPreimage] using hx
    · simpa [mulPreimage] using hy
    · simpa [mulPreimage] using hz
    · calc
        μ * x + μ * y - 2 * (μ * z)
          = μ * (x + y - 2 * z) := by ring
        _ = μ * 6 := by simpa using congrArg (fun t : ZMod p => μ * t) hxyz
        _ = c := hμ6

end PrimeField

end KravitzLP
