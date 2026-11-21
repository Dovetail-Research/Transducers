import Mathlib.Probability.Kernel.Composition.MapComap

open MeasureTheory ProbabilityTheory

noncomputable section

-- This abbreviation is here so that instead of typing
---- `Subtype (@ProbabilityTheory.IsMarkovKernel α β mα mβ)`
-- we can just type
---- `MarkovKernel α β`
abbrev MarkovKernel (α : Type u_1) (β : Type u_2) [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] := Subtype (IsMarkovKernel (mα := mα) (mβ := mβ))

-- This instance registration tells allows us to know that mapping a MarkovKernel by a
-- MeasurableEquiv is still a MarkovKernel
instance {α : Type u_1} {β : Type u_2} {γ : Type u_3} [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSpace γ] {k : Kernel α β} [IsMarkovKernel k] (f : MeasurableEquiv β γ) :
    IsMarkovKernel (k.map f) := Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

-- This instance registration tells allows us to know that comapping a MarkovKernel by a
-- MeasurableEquiv is still a MarkovKernel
instance {α : Type u_1} {β : Type u_2} {γ : Type u_3} [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSpace γ] {k : Kernel α β} [IsMarkovKernel k] (f : MeasurableEquiv γ α) :
    IsMarkovKernel (k.comap f (f.measurable)) :=
  Kernel.IsMarkovKernel.comap _ (MeasurableEquiv.measurable _)

-- This instance registration tells Lean's typeclass search that if it is holding an object of type
-- `MarkovKernel` then it can find a proof of its markovianness by calling `k.2`.
instance {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
  [MeasurableSpace β] (k : MarkovKernel α β) : ProbabilityTheory.IsMarkovKernel k.1 := k.2

-- This instance registration tells Lean's typeclass search that if someone tries call the
-- `MarkovKernel` as if it's a function, then Lean should reroute that call by calling `f.1`.
instance {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
  [MeasurableSpace β] : CoeFun (MarkovKernel α β) (fun _ ↦ α → Measure β) := ⟨
    fun f ↦ ⇑f.1
  ⟩

-- This instance lets us use Kernels in place of MarkovKernels in places where Lean can
-- synthesise its markovianness
instance {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [MeasurableSpace β]
  {k : Kernel α β} [hk : IsMarkovKernel k] : CoeDep (Kernel α β) k (MarkovKernel α β) := ⟨
    ⟨k, hk⟩
  ⟩

@[ext] -- This auto-generates a lemma saying two transducers are equal iff their fields are.
-- This structure is *the* definition of a Transducer.
-- D: The index type over which actions, states and observations are indexed
-- A: The alphabet of actions the Transducer can take
-- O: The alphabet of observations the Transducer can make
-- The state space `S` is no longer a parameter: it is an (implicit) field of the structure, so
-- transducers with different state spaces but the same interface share a type.
structure Transducer (D A O : Type) [MeasurableSpace A] [MeasurableSpace O] where
  -- S: The state space of the Transducer
  {S : Type}
  [hS : MeasurableSpace S]
  -- K: The kernel taking an action and a (current) state at each index to a (next) state and an
  -- observation at each index.
  K : MarkovKernel (D → A × S) (D → S × O)
  p : Measure S -- This p is the initial probability distribution.
  hp : IsProbabilityMeasure p := by infer_instance

-- This variable block just means that for the rest of this file, if we say `t` it's implied that
-- `t` should be a Transducer (with relevant types (in)D(ex), A(ction) and O(bservations)).
variable {D A O : Type} [MeasurableSpace A] [MeasurableSpace O]
  (t : Transducer D A O)

-- Let typeclass search find the measurable space on the state space `t.S` of a Transducer.
attribute [instance] Transducer.hS

attribute [instance] Transducer.hp
