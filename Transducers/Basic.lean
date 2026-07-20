import Mathlib.Probability.Kernel.Composition.MapComap

open MeasureTheory

noncomputable section

abbrev MarkovKernel (α : Type u_1) (β : Type u_2) [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] := Subtype (@ProbabilityTheory.IsMarkovKernel (mα := mα) (mβ := mβ))

instance {α : Type u_1} {β : Type u_2} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] (k : MarkovKernel α β) : ProbabilityTheory.IsMarkovKernel k.1 := k.2

instance {α : Type u_1} {β : Type u_2} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] : CoeFun (MarkovKernel α β) (fun _ ↦ α → Measure β) := ⟨
    fun f ↦ f.1.toFun
  ⟩

@[ext]
structure Transducer (A S O : Type) [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O] where
  K : ℕ → MarkovKernel (A × S) (S × O)
  p : Measure S
  hp : IsProbabilityMeasure p := by infer_instance

variable {A S O : Type} [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O]
  (t : Transducer A S O)

def Transducer.κ := t.K 0

def Transducer.Stationary := ∀ i, t.K i = t.κ

@[simp]
lemma Transducer.Stationary.κ_eq {t : Transducer A S O} (ht : t.Stationary) : ∀ i, t.K i = t.κ := ht

-- The next-state kernel obtained by marginalising the output out of `Transducer.κ`.
def Transducer.κS : MarkovKernel (A × S) S :=
  ⟨t.κ.1.fst, inferInstance⟩

-- The output kernel obtained by marginalising the next state out of `Transducer.κ`.
def Transducer.κO : MarkovKernel (A × S) O :=
  ⟨t.κ.1.snd, inferInstance⟩
