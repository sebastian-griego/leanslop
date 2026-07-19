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
  by_contra hnot
  have hpre : IsPreconnected (f '' s) := hs.image f hf
  have hfa_ne : f a ≠ y := by
    intro h
    exact hnot ⟨a, ha, h⟩
  have hyb_ne : y ≠ f b := by
    intro h
    exact hnot ⟨b, hb, h.symm⟩
  have hfa : f a < y := lt_of_le_of_ne hy.1 hfa_ne
  have hyb : y < f b := lt_of_le_of_ne hy.2 hyb_ne
  have hcover : f '' s ⊆ Iio y ∪ Ioi y := by
    intro z hz
    have hzy : z ≠ y := by
      intro h
      apply hnot
      simpa [h] using hz
    rcases lt_or_gt_of_ne hzy with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt
  rcases hpre (Iio y) (Ioi y) isOpen_Iio isOpen_Ioi hcover
      ⟨f a, ⟨a, ha, rfl⟩, hfa⟩
      ⟨f b, ⟨b, hb, rfl⟩, hyb⟩ with ⟨z, ⟨_, hzlt⟩, hzgt⟩
  exact lt_asymm hzlt hzgt


theorem benchmark_check_intermediate_value {s : Set X} (hs : IsPreconnected s)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → α}
    (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s :=
  tested_intermediate_value hs ha hb hf

#print axioms benchmark_check_intermediate_value

end IntermediateValue
