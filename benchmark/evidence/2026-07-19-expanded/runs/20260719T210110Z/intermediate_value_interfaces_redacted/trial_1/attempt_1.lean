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
  classical
  intro y hy
  by_contra hyim
  have hfa_ne : f a ≠ y := by
    intro h
    exact hyim ⟨a, ha, h⟩
  have hfb_ne : f b ≠ y := by
    intro h
    exact hyim ⟨b, hb, h⟩
  have hay : f a < y := lt_of_le_of_ne hy.1 hfa_ne
  have hyb : y < f b := lt_of_le_of_ne hy.2 hfb_ne.symm
  have hcover : f '' s ⊆ Iio y ∪ Ioi y := by
    intro x hx
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact Or.inl hxy
    · exact (hyim (hxy ▸ hx)).elim
    · exact Or.inr hxy
  rcases (hs.image f hf) (Iio y) (Ioi y) isOpen_Iio isOpen_Ioi hcover
      ⟨f a, mem_image_of_mem f ha, hay⟩
      ⟨f b, mem_image_of_mem f hb, hyb⟩ with
    ⟨x, _, hxy, hyx⟩
  exact (lt_asymm hxy hyx)


theorem benchmark_check_intermediate_value {s : Set X} (hs : IsPreconnected s)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → α}
    (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s :=
  tested_intermediate_value hs ha hb hf

#print axioms benchmark_check_intermediate_value

end IntermediateValue
