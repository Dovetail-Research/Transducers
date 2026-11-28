import Transducers.Kernel

/-!
# Transducers

The definition of a transducer: a causal-Markov kernel from an initial state and an action path
to a path of states and observations.
-/

open MeasureTheory ProbabilityTheory

@[ext] -- This auto-generates a lemma saying two transducers are equal iff their fields are.
-- This structure is *the* definition of a Transducer.
-- T: The (linearly ordered) index type, thought of as time
-- A: The alphabet of actions the Transducer can take
-- O: The alphabet of observations the Transducer can make
-- The state space `S` is not a parameter: it is an (implicit) field of the structure, so
-- transducers with different state spaces but the same interface share a type.
structure Transducer (T A O : Type) [LinearOrder T] [MeasurableSpace A] [MeasurableSpace O] where
  -- S: The state space of the Transducer
  {S : Type}
  [hS : MeasurableSpace S]
  -- K: The kernel taking an initial state and a path of actions to a path of states and
  -- observations. Each output carries the state reached at that index.
  K : MarkovKernel (S × (T → A)) (T → S × O)
  -- The outputs only depend on the current state and on present and past actions.
  causalMarkov : K.1.IsCausalMarkov

-- Let typeclass search find the measurable space on the state space `t.S` of a Transducer.
attribute [instance] Transducer.hS
