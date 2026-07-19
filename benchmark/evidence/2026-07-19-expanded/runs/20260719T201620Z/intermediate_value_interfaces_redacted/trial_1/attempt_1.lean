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
  have hpre : IsPreconnected (f '' s) := hs.image (f := f) hf
  by_contra hyimage
  have hay : f a < y := lt_of_le_of_ne hy.1 (by
    intro h
    exact hyimage ⟨a, ha, h⟩)
  have hyb : y < f b := lt_of_le_of_ne hy.2 (by
    intro h
    exact hyimage ⟨b, hb, h.symm⟩)
  have hcover : f '' s ⊆ Iio y ∪ Ioi y := by
    intro z hz
    rcases lt_trichotomy z y with hzy | hzy | hzy
    · exact Or.inl hzy
    · exact (hyimage (hzy ▸ hz)).elim
    · exact Or.inr hzy
  have hleft : ((f '' s) ∩ Iio y).Nonempty :=
    ⟨f a, ⟨a, ha, rfl⟩, hay⟩
  have hright : ((f '' s) ∩ Ioi y).Nonempty :=
    ⟨f b, ⟨b, hb, rfl⟩, hyb⟩
  have hover :=
    hpre (Iio y) (Ioi y) isOpen_Iio isOpen_Ioi hcover hleft hright
  have hcontra : ∃ z, z ∈ f '' s ∧ z < y ∧ y < z := by
    simpa only [Set.nonempty_def, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi,
      and_assoc] using hover
  rcases hcontra with ⟨z, -, hzy, hyz⟩
  exact (not_lt_of_ge (le_of_lt hyz)) hzy


theorem benchmark_check_intermediate_value {s : Set X} (hs : IsPreconnected s)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → α}
    (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s :=
  tested_intermediate_value hs ha hb hf

#print axioms benchmark_check_intermediate_value

end IntermediateValue
