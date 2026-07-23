import Mathlib.Probability.Kernel.Composition.MapComap

open MeasureTheory

noncomputable section

-- This abbreviation is here so that instead of typing
---- `Subtype (@ProbabilityTheory.IsMarkovKernel α β mα mβ)`
-- we can just type
---- `MarkovKernel α β`
abbrev MarkovKernel (α : Type u_1) (β : Type u_2) [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] := Subtype (@ProbabilityTheory.IsMarkovKernel (mα := mα) (mβ := mβ))

-- This instance registration tells Lean's typeclass search that if it is holding an object of type
-- `MarkovKernel` then it can find a proof of its markovianness by calling `k.2`.
instance {α : Type u_1} {β : Type u_2} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] (k : MarkovKernel α β) : ProbabilityTheory.IsMarkovKernel k.1 := k.2

-- This instance registration tells Lean's typeclass search that if someone tries call the
-- `MarkovKernel` as if it's a function, then Lean should reroute that call by calling `f.1.toFun`.
instance {α : Type u_1} {β : Type u_2} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] : CoeFun (MarkovKernel α β) (fun _ ↦ α → Measure β) := ⟨
    fun f ↦ f.1.toFun
  ⟩

@[ext] -- This auto-generates a lemma saying two transducers are equal iff their fields are.
-- This structure is *the* definition of a Transducer.
-- A: The alphabet of actions the Transducer can take
-- S: The state space of the Transducer
-- O: The alphabet of observations the Transducer can make
structure Transducer (A S O : Type) [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O] where
  -- The kernel of a Transducer could technically be different on each time step. For almost all
  -- use cases, we will want it to be stationary, and therefore have the same kernel on each time
  -- step. We define this property below, and thus give the conventional name κ (kappa) to the
  -- stationary kernel, and give a non-conventional name K (the roman letter) to the potentially
  -- non-stationary kernel.
  K : ℕ → MarkovKernel (A × S) (S × O)
  p : Measure S -- This p is the initial probability distribution.
  hp : IsProbabilityMeasure p := by infer_instance

-- This variable block just means that for the rest of this file, if we say `t` it's implied that
-- `t` should be a Transducer (with relevant types A(ction) S(tate) and O(bservations)).
variable {A S O : Type} [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O]
  (t : Transducer A S O)

-- Because we expect to use mostly stationary Transducers, we give the more conventional name κ
-- (kappa) to the kernel at time 0.
def Transducer.κ := t.K 0

-- This is the definition of what it means for a Transducer to be stationary.
def Transducer.Stationary := ∀ i, t.K i = t.κ

@[simp]
lemma Transducer.Stationary.κ_eq {t : Transducer A S O} (ht : t.Stationary) : ∀ i, t.K i = t.κ := ht

-- The next-state kernel obtained by marginalising the output out of `Transducer.κ`.
def Transducer.κS : MarkovKernel (A × S) S :=
  ⟨t.κ.1.fst, inferInstance⟩

-- The output kernel obtained by marginalising the next state out of `Transducer.κ`.
def Transducer.κO : MarkovKernel (A × S) O :=
  ⟨t.κ.1.snd, inferInstance⟩
