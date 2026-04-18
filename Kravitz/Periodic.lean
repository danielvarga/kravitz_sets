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

theorem atomWeight_nonneg (A : Set (ZMod n)) (j : Atom) : 0 ≤ atomWeight A j := by
  dsimp [atomWeight]
  positivity

end KravitzLP
