
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Probability.Kernel.Composition.Comp

open CategoryTheory
open ProbabilityTheory

universe u

variable (X : Type u) [MeasurableSpace X]

abbrev MarkovHom :=
  { K : Kernel X X // IsMarkovKernel K }

instance markovKernelCategory :
    CategoryTheory.Category (One) where
  Hom _ _ := MarkovHom X
  id _ :=
    ⟨Kernel.id, inferInstance⟩
  comp f g :=
    ⟨g.1 ∘ₖ f.1, inferInstance⟩
  id_comp := by
    intro A B f
    apply Subtype.ext
    simp
  comp_id := by
    intro A B f
    apply Subtype.ext
    simp
  assoc := by
    intro A B C D f g h
    apply Subtype.ext
    exact Kernel.comp_assoc h.1 g.1 f.1

def IsCategoricalEvolution
    {T : Type*} [LinearOrder T]
    (K : T → T → MarkovHom X) : Prop :=
  ∀ s u t, s ≤ u → u ≤ t →
    (K s u).1 ∘ₖ (K u t).1 = (K s t).1

theorem categorical_chapman_kolmogorov
    {T : Type*} [LinearOrder T]
    (K : T → T → MarkovHom X)
    (hK : IsCategoricalEvolution X K)
    (s u t : T)
    (hsu : s ≤ u)
    (hut : u ≤ t) :
    (K s u).1 ∘ₖ (K u t).1 = (K s t).1 :=
  hK s u t hsu hut
