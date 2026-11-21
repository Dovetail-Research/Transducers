import Transducers.Basic

/-!
# Anticipation-free transducers

When the index type `D` carries a preorder (thought of as time, or more generally causal order),
a transducer is *anticipation-free* if what it produces up to index `d` (next states and
observations at all `e ≤ d`) depends only on what it is fed up to index `d` (actions and current
states at all `e ≤ d`). In other words, the transducer cannot react to inputs from the future.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

variable {D A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-- Restrict a `D`-indexed family to the indices `e ≤ d`. -/
def restrictIic [Preorder D] {β : Type} (d : D) (x : D → β) : Set.Iic d → β :=
  fun e ↦ x e

@[fun_prop]
lemma measurable_restrictIic [Preorder D] {β : Type} [MeasurableSpace β] (d : D) :
    Measurable (restrictIic (β := β) d) := by
  unfold restrictIic
  fun_prop

/-- A transducer is anticipation-free if, for every index `d`, the joint law of its outputs
(next states and observations) at indices `≤ d` only depends on its inputs (actions and
current states) at indices `≤ d`. -/
def Transducer.AnticipationFree [Preorder D] (t : Transducer D A O) : Prop :=
  ∀ (d : D) (x y : D → A × t.S), restrictIic d x = restrictIic d y →
    (t.K x).map (restrictIic d) = (t.K y).map (restrictIic d)

/-- A transducer is anticipation-free as soon as, for every index `d`, its restricted kernel
factors through the restriction of the inputs to the indices `≤ d`. -/
lemma Transducer.anticipationFree_of_factor [Preorder D] (t : Transducer D A O)
    (κ : ∀ d : D, ProbabilityTheory.Kernel (Set.Iic d → A × t.S) (Set.Iic d → t.S × O))
    (hκ : ∀ d, t.K.1.map (restrictIic d) = (κ d).comap (restrictIic d) (by fun_prop)) :
    t.AnticipationFree := by
  intro d x y hxy
  have hx := congrArg (fun k ↦ k x) (hκ d)
  have hy := congrArg (fun k ↦ k y) (hκ d)
  simp only [Kernel.map_apply _ (measurable_restrictIic d), Kernel.comap_apply] at hx hy
  change (t.K.1 x).map _ = (t.K.1 y).map _
  rw [hx, hy, hxy]
