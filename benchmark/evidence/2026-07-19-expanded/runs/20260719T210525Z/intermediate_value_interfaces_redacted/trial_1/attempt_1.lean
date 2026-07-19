import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Connected.TotallyDisconnected

open Filter OrderDual TopologicalSpace Function Set
open scoped Topology Filter Interval

namespace IntermediateValue

universe u v

variable {X : Type u} {α : Type v} [TopologicalSpace X] [LinearOrder α]
  [TopologicalSpace α] [OrderClosedTopology α]

/- REQUIRED:
theorem tested_intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) {f : X → α} (hf : ContinuousOn f s) :
    Icc (f a) (f b) ⊆ f '' s
-/

theorem tested_intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) {f : X → α} (hf : ContinuousOn f s) :
    Icc (f a) (f b) ⊆ f '' s := by
  intro y hy
  by_cases hay : f a = y
  · exact ⟨a, ha, hay⟩
  by_cases hby : f b = y
  · exact ⟨b, hb, hby⟩
  have hlt_a : f a < y := lt_of_le_of_ne hy.1 hay
  have hlt_b : y < f b := by
    exact lt_of_le_of_ne hy.2 (fun h => hby h.symm)
  by_contra hyim
  have hpre : IsPreconnected (f '' s) := hs.image hf
  have hsub : f '' s ⊆ Iio y ∪ Ioi y := by
    rintro z ⟨x, hx, rfl⟩
    by_cases hxy : f x = y
    · exact False.elim (hyim ⟨x, hx, hxy⟩)
    · rcases lt_or_gt_of_ne hxy with hxy | hxy
      · exact Or.inl hxy
      · exact Or.inr hxy
  have hleft : ((f '' s) ∩ Iio y).Nonempty :=
    ⟨f a, ⟨⟨a, ha, rfl⟩, hlt_a⟩⟩
  have hright : ((f '' s) ∩ Ioi y).Nonempty :=
    ⟨f b, ⟨⟨b, hb, rfl⟩, hlt_b⟩⟩
  rcases hpre (Iio y) (Ioi y) isOpen_Iio isOpen_Ioi hsub hleft hright with
    ⟨z, hz, hzlt, hzy⟩
  exact (not_lt_of_ge (le_of_lt hzy)) hzlt


theorem benchmark_check_intermediate_value {s : Set X} (hs : IsPreconnected s)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → α}
    (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s :=
  tested_intermediate_value hs ha hb hf

#print axioms benchmark_check_intermediate_value

end IntermediateValue
