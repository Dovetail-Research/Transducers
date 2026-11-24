import Transducers.Interface

/-!
# Interface representations

An anticipation-free kernel `ν` from action sequences to observation sequences comes from an
interface: its kernel at time `n` is a conditional kernel
(`ProbabilityTheory.Kernel.condKernel`) of the observation at time `n` given the actions at times
`0, …, n` and the observations at times `0, …, n - 1`. For it to exist, the observations must live
in a standard Borel space.

In particular, the observation kernel of every transducer over `ℕ` started in any state (the
interface `I_{T,s}` of the paper) is represented by an interface.

## Main results

* `ProbabilityTheory.Kernel.toInterface`: the interface built from a kernel.
* `ProbabilityTheory.Kernel.obsKernel_toInterface`: if `ν` is anticipation-free, the observation
  kernel of `ν.toInterface` is `ν`.
* `ProbabilityTheory.Kernel.anticipationFree_iff_exists_interface`: `ν` is anticipation-free iff
  it is the observation kernel of some interface.
* `Transducer.exists_interface`: the observation kernels of a transducer come from interfaces.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-- Extend a finite sequence to an infinite one by repeating its first entry. -/
def extendFin {β : Type} (n : ℕ) (x : Fin (n + 1) → β) : ℕ → β :=
  fun i ↦ if h : i < n + 1 then x ⟨i, h⟩ else x 0

@[fun_prop]
lemma measurable_extendFin {β : Type} [MeasurableSpace β] (n : ℕ) :
    Measurable (extendFin (β := β) n) :=
  Measurable.of_eval fun i ↦ by
    unfold extendFin
    split_ifs <;> exact measurable_pi_apply _

namespace ProbabilityTheory.Kernel

variable (ν : Kernel (ℕ → A) (ℕ → O)) [IsMarkovKernel ν]

/-- If `ν` is anticipation-free, its observations at times `0, …, n` only depend on the actions
at times `0, …, n`. -/
lemma AnticipationFree.map_restrictFin {ν : Kernel (ℕ → A) (ℕ → O)} (hν : ν.AnticipationFree)
    (n : ℕ) (x y : ℕ → A) (hxy : ∀ i ≤ n, x i = y i) :
    (ν x).map (restrictFin (n + 1)) = (ν y).map (restrictFin (n + 1)) := by
  let g : (Set.Iic n → O) → Fin (n + 1) → O :=
    fun v j ↦ v ⟨j, Set.mem_Iic.2 (Nat.lt_succ_iff.1 j.2)⟩
  have hg : Measurable g := by unfold g; fun_prop
  have hr : restrictFin (n + 1) = g ∘ restrictIic n := rfl
  rw [hr, ← Measure.map_map hg (measurable_restrictIic n),
    ← Measure.map_map hg (measurable_restrictIic n),
    hν n x y (funext fun i ↦ hxy i (Set.mem_Iic.1 i.2))]

/-- The joint law of the observations of `ν` at times `0, …, n - 1` and at time `n`, given the
actions at times `0, …, n` (extended arbitrarily to later times). -/
def stepLaw (n : ℕ) : Kernel (Fin (n + 1) → A) ((Fin n → O) × O) :=
  (ν.comap (extendFin n) (by fun_prop)).map (fun y ↦ (restrictFin n y, y n))

instance (n : ℕ) : IsMarkovKernel (ν.stepLaw n) :=
  IsMarkovKernel.map _ (by fun_prop)

variable [StandardBorelSpace O] [Nonempty O]

/-- The interface representing `ν`: the law at time `n` is a conditional kernel of the
observation of `ν` at time `n` given the actions up to time `n` and the earlier observations. -/
def toInterface : Interface A O where
  κ n := ⟨(ν.stepLaw n).condKernel, inferInstance⟩

/-- **Every anticipation-free kernel has an interface representation.** -/
theorem obsKernel_toInterface (hν : ν.AnticipationFree) : ν.toInterface.obsKernel = ν := by
  refine ν.toInterface.eq_obsKernel ν fun n a ↦ ?_
  let r := restrictFin (n + 1) a
  -- Split the first `n + 1` observations into the first `n` and the last one.
  let split : (Fin (n + 1) → O) → (Fin n → O) × O := fun w ↦ (Fin.init w, w (Fin.last n))
  have hsplit : Measurable split :=
    (Measurable.of_eval fun i ↦ measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply _)
  have hL : ν.stepLaw n r = ((ν a).map (restrictFin (n + 1))).map split := by
    have hext : ∀ i ≤ n, extendFin n r i = a i := fun i hi ↦ by
      simp [extendFin, r, restrictFin, Nat.lt_succ_iff.2 hi]
    rw [stepLaw, Kernel.map_apply _ (by fun_prop), comap_apply,
      Measure.map_map hsplit (measurable_restrictFin _), ← Measure.map_map hsplit
      (measurable_restrictFin _), ← hν.map_restrictFin n _ a hext,
      Measure.map_map hsplit (measurable_restrictFin _)]
    rfl
  have hfst : (ν.stepLaw n).fst r = (ν a).map (restrictFin n) := by
    rw [Kernel.fst_apply, hL, Measure.map_map measurable_fst hsplit,
      Measure.map_map (measurable_fst.comp hsplit) (measurable_restrictFin _)]
    rfl
  -- Disintegrate the law of the first `n + 1` observations.
  have hdis := congrArg (fun k ↦ k r) ((ν.stepLaw n).disintegrate (ν.stepLaw n).condKernel)
  rw [compProd_apply_eq_compProd_sectR, hfst, hL] at hdis
  change _ = Measure.map _ ((ν a).map (restrictFin n) ⊗ₘ sectR (ν.stepLaw n).condKernel r)
  rw [hdis, Measure.map_map measurable_fin_snoc hsplit]
  conv_lhs => rw [← Measure.map_id (μ := (ν a).map (restrictFin (n + 1)))]
  congr 1
  funext w
  exact (Fin.snoc_init_self w).symm

/-- A kernel is anticipation-free iff it is the observation kernel of an interface. -/
theorem anticipationFree_iff_exists_interface :
    ν.AnticipationFree ↔ ∃ I : Interface A O, I.obsKernel = ν :=
  ⟨fun hν ↦ ⟨ν.toInterface, ν.obsKernel_toInterface hν⟩,
    fun ⟨I, hI⟩ ↦ hI ▸ I.anticipationFree_obsKernel⟩

end ProbabilityTheory.Kernel

/-- **The interface of a transducer is represented by an interface.** The observation kernel of
a transducer over `ℕ` started in any state (the paper's `I_{T,s}`) is the observation kernel of an
interface. -/
theorem Transducer.exists_interface [StandardBorelSpace O] [Nonempty O]
    (t : Transducer ℕ A O) (s : t.S) : ∃ I : Interface A O, I.obsKernel = t.obsKernel s :=
  ⟨(t.obsKernel s).toInterface,
    (t.obsKernel s).obsKernel_toInterface (t.anticipationFree_obsKernel s)⟩
