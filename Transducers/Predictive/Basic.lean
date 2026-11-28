import Transducers.HistoryTransducer

/-!
# Predictive and deterministic transducers

A transducer is *predictive* (Definition 6 of the paper) if its internal state carries no
information about the future that is not already available from the observable history: at every
index `d`, the observations after `d` are generated from the actions and the observations up to
`d` by a single kernel, which does not see the state at `d`. Equivalently, any two states that can
occur after the same observable past generate the same future (up to null sets).

A transducer is *deterministic* if its state at every index is a measurable function of the
initial state and the actions and observations so far (the ε-transducer of the paper evolves this
way). Both notions make sense for any linearly ordered index type `T`.

## Main results

* `Transducer.IsPredictive`, `Transducer.IsDeterministic`: the two definitions.
* `Transducer.IsDeterministic.isPredictive`: a deterministic transducer is predictive.
* `Interface.isDeterministic_toTransducer`, `Interface.isPredictive_toTransducer`: the history
  transducer of an interface is deterministic, hence predictive.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel

noncomputable section

variable {T A O : Type} [LinearOrder T] [MeasurableSpace A] [MeasurableSpace O]

namespace Transducer

variable {S : Type} [MeasurableSpace S]

/-- The observations of a run up to index `d`. -/
def pastObs (d : T) (y : T → S × O) : Set.Iic d → O := fun e ↦ (y e).2

/-- The observations of a run after index `d`. -/
def futureObs (d : T) (y : T → S × O) : Set.Ioi d → O := fun e ↦ (y e).2

@[fun_prop]
lemma measurable_pastObs (d : T) : Measurable (pastObs (S := S) (O := O) d) := by
  unfold pastObs
  fun_prop

@[fun_prop]
lemma measurable_futureObs (d : T) : Measurable (futureObs (S := S) (O := O) d) := by
  unfold futureObs
  fun_prop

variable (t : Transducer T A O)

/-- **Predictive transducers** (Definition 6). Started from any state `s`, at every index `d` the
observations after `d` are drawn from a kernel `G` that only sees the actions and the observations
up to `d`: given the observable past, the state at `d` carries no further information about the
future. -/
def IsPredictive : Prop :=
  ∀ (s : t.S) (d : T), ∃ G : Kernel ((T → A) × (Set.Iic d → O)) (Set.Ioi d → O),
    IsMarkovKernel G ∧ ∀ a,
      (t.K.1 (s, a)).map (fun y ↦ ((pastObs d y, (y d).1), futureObs d y)) =
        (t.K.1 (s, a)).map (fun y ↦ (pastObs d y, (y d).1)) ⊗ₘ
          G.comap (fun p : (Set.Iic d → O) × t.S ↦ (a, p.1)) (by fun_prop)

/-- **Deterministic transducers.** The state at index `d` is a measurable function `σ d` of the
initial state and the actions and observations up to `d`. -/
def IsDeterministic : Prop :=
  ∃ σ : (d : T) → t.S × (Set.Iic d → A) × (Set.Iic d → O) → t.S, (∀ d, Measurable (σ d)) ∧
    ∀ s a, t.K.1 (s, a) =
      (t.obsKernel s a).map (fun o d ↦ (σ d (s, restrictIic d a, restrictIic d o), o d))

/-- **A deterministic transducer is predictive.** The future after `d` is generated from the
state at `d`, which is itself a function of the observable past. -/
theorem IsDeterministic.isPredictive {t : Transducer T A O} (ht : t.IsDeterministic) :
    t.IsPredictive := by
  obtain ⟨σ, hσ, hK⟩ := ht
  intro s d
  obtain ⟨past, future, _, _, hsplit⟩ := t.causalMarkov d
  -- The observations after `d`, given the state at `d` and the actions after `d`.
  let η : Kernel (t.S × (Set.Ioi d → A)) (Set.Ioi d → O) :=
    future.map (fun w e ↦ (w e).2)
  have hη : IsMarkovKernel η := IsMarkovKernel.map _ (by fun_prop)
  -- The state at `d` as a function of the actions and observations up to `d`.
  let τ : (T → A) × (Set.Iic d → O) → t.S := fun p ↦ σ d (s, restrictIic d p.1, p.2)
  have hτ : Measurable τ :=
    (hσ d).comp (measurable_const.prodMk (((measurable_restrictIic d).comp measurable_fst).prodMk
      measurable_snd))
  let G : Kernel ((T → A) × (Set.Iic d → O)) (Set.Ioi d → O) :=
    η.comap (fun p ↦ (τ p, restrictIoi d p.1)) (hτ.prodMk ((measurable_restrictIoi d).comp
      measurable_fst))
  refine ⟨G, IsMarkovKernel.comap _ _, fun a ↦ ?_⟩
  -- Splitting the run at `d`, the future observations are drawn from `η` at the state at `d`.
  let f : (Set.Iic d → t.S × O) → (Set.Iic d → O) × t.S :=
    fun p ↦ (fun e ↦ (p e).2, (p ⟨d, Set.mem_Iic.2 le_rfl⟩).1)
  have hf : Measurable f := by unfold f; fun_prop
  let g : (Set.Iic d → t.S × O) → (Set.Ioi d → t.S × O) → (Set.Ioi d → O) :=
    fun _ w e ↦ (w e).2
  have hg : Measurable fun q : (Set.Iic d → t.S × O) × (Set.Ioi d → t.S × O) ↦ g q.1 q.2 := by
    unfold g; fun_prop
  let M := (t.K.1 (s, a)).map (fun y ↦ (pastObs d y, (y d).1))
  let ηa : Kernel ((Set.Iic d → O) × t.S) (Set.Ioi d → O) :=
    η.comap (fun p ↦ (p.2, restrictIoi d a)) (by fun_prop)
  have hL : (t.K.1 (s, a)).map (fun y ↦ ((pastObs d y, (y d).1), futureObs d y)) = M ⊗ₘ ηa := by
    have h1 : (t.K.1 (s, a)).map (fun y ↦ ((pastObs d y, (y d).1), futureObs d y)) =
        (past (s, restrictIic d a) ⊗ₘ future.comap
          (fun z ↦ ((z ⟨d, Set.mem_Iic.2 le_rfl⟩).1, restrictIoi d a)) (by fun_prop)).map
          (fun q ↦ (f q.1, g q.1 q.2)) := by
      have hfg : Measurable fun q : (Set.Iic d → t.S × O) × (Set.Ioi d → t.S × O) ↦
          (f q.1, g q.1 q.2) := (hf.comp measurable_fst).prodMk hg
      rw [← hsplit, Measure.map_map hfg (MeasurableEquiv.measurable _)]
      rfl
    have h2 : (t.K.1 (s, a)).map (fun y ↦ ((pastObs d y, (y d).1), futureObs d y)) =
        (past (s, restrictIic d a)).map f ⊗ₘ ηa := by
      rw [h1]
      refine Measure.map_compProd_eq _ _ hf hg ηa fun p ↦ ?_
      rw [comap_apply, comap_apply, Kernel.map_apply _ (by fun_prop)]
    have hfst := congrArg Measure.fst h2
    rw [Measure.fst_compProd, Measure.fst, Measure.map_map measurable_fst (by fun_prop)] at hfst
    rw [h2, ← hfst]
    rfl
  -- The state at `d` is a function of the observable past, so `M` lives on a graph.
  let ν := (t.obsKernel s a).map (restrictIic d)
  have hgr : Measurable fun v : Set.Iic d → O ↦ (v, τ (a, v)) :=
    measurable_id.prodMk (hτ.comp measurable_prodMk_left)
  have hM : M = ν.map (fun v ↦ (v, τ (a, v))) := by
    have hpath : Measurable fun o : T → O ↦
        (fun e ↦ (σ e (s, restrictIic e a, restrictIic e o), o e) : T → t.S × O) :=
      Measurable.of_eval fun e ↦ ((hσ e).comp (measurable_const.prodMk
        (measurable_const.prodMk (measurable_restrictIic e)))).prodMk (measurable_pi_apply e)
    simp only [M, ν]
    rw [hK s a, Measure.map_map (by fun_prop) hpath, Measure.map_map hgr
      (measurable_restrictIic d)]
    rfl
  -- On a graph, a kernel only sees the first coordinate.
  have hgraph : ∀ κ : Kernel ((Set.Iic d → O) × t.S) (Set.Ioi d → O), IsSFiniteKernel κ →
      M ⊗ₘ κ = (ν ⊗ₘ κ.comap (fun v ↦ (v, τ (a, v))) hgr).map
        (fun p ↦ ((p.1, τ (a, p.1)), p.2)) := by
    intro κ _
    rw [hM, ← Measure.map_compProd_eq ν _ hgr (g := fun _ w ↦ w) measurable_snd κ fun v ↦ by
      rw [comap_apply, Measure.map_id']]
  rw [hL, hgraph _ inferInstance, hgraph _ inferInstance]
  rfl

end Transducer

/-! ### The history transducer -/

namespace Interface

variable (I : Interface A O)

/-- **The history transducer is deterministic**: its state is the time and the history so far. -/
theorem isDeterministic_toTransducer : I.toTransducer.IsDeterministic := by
  refine ⟨fun d p ↦ (d, (splitIicIoi d).symm (p.2.1, restrictIoi d p.1.2.1),
    (splitIicIoi d).symm (p.2.2, restrictIoi d p.1.2.2)), fun d ↦ by fun_prop, fun s a ↦ ?_⟩
  refine (I.histKernel_apply s a).trans ?_
  erw [obsKernel_toTransducer]
  congr 1

/-- **The history transducer is predictive.** -/
theorem isPredictive_toTransducer : I.toTransducer.IsPredictive :=
  I.isDeterministic_toTransducer.isPredictive

end Interface
