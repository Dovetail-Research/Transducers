import Transducers.Interface

/-!
# The future of an interface given its past

Fix an interface `I` and a time `d`. Given the actions, the observations of `I.obsKernel` up to
time `d` are followed by observations after time `d`, drawn from a kernel `I.futureObs d` that
only sees the actions and the observations up to time `d`:
```
(I.obsKernel a).map (splitIicIoi d) =
  (I.obsKernel a).map (restrictIic d) ⊗ₘ (I.futureObs d).comap (Prod.mk a) _
```
`I.futureObs d` runs `Kernel.traj` from time `d + 1`, and the identity comes from Mathlib's
`Kernel.partialTraj_compProd_traj`, which splits a trajectory at time `d + 1`.

## Main results

* `Interface.futureObs`: the law of the observations after time `d`, given the actions and the
  observations up to time `d`.
* `Interface.obsKernel_map_splitIicIoi`: the observation kernel splits into its past followed by
  `futureObs`.
-/

open MeasureTheory ProbabilityTheory Finset Preorder ProbabilityTheory.Kernel

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

namespace Interface

variable (I : Interface A O)

/-! ### Reading observations off a trajectory -/

/-- The observations of a trajectory of `traj I.step`: the observation at time `n` is the last
entry of coordinate `n + 1`. -/
def obsOf (ω : Π n, (ℕ → A) × (Fin n → O)) : ℕ → O := fun n ↦ (ω (n + 1)).2 (Fin.last n)

@[fun_prop]
lemma measurable_obsOf : Measurable (obsOf (A := A) (O := O)) := by
  unfold obsOf
  fun_prop

lemma obsKernel_apply_traj (a : ℕ → A) :
    I.obsKernel a = (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step 0 (start a)).map obsOf := by
  rw [obsKernel, Kernel.map_apply _ (by fun_prop), comap_apply]
  rfl

/-- The observations up to time `d`, read off the trajectory up to time `d + 1`. -/
def pastObs (d : ℕ) (x : Π i : Iic (d + 1), (ℕ → A) × (Fin i → O)) : Set.Iic d → O :=
  fun e ↦ (x ⟨e + 1, mem_Iic.2 (by have := Set.mem_Iic.1 e.2; lia)⟩).2 (Fin.last e)

@[fun_prop]
lemma measurable_pastObs (d : ℕ) : Measurable (pastObs (A := A) (O := O) d) := by
  unfold pastObs
  fun_prop

/-! ### Laying out the trajectory up to a time -/

/-- The trajectory up to time `b`, started from the actions `a`, is laid out from `a` and the
first `b` observations. -/
lemma exists_partialTraj_start (b : ℕ) (a : ℕ → A) :
    ∃ μ : Measure (Fin b → O), IsProbabilityMeasure μ ∧
      partialTraj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step 0 b (start a) =
        μ.map (layout b a) := by
  induction b with
  | zero =>
    refine ⟨Measure.dirac Fin.elim0, inferInstance, ?_⟩
    rw [partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_layout _ _)]
    congr 1
  | succ b ih =>
    obtain ⟨μ, hμ, h⟩ := ih
    refine ⟨(μ ⊗ₘ (I.κ b).1.comap (fun w ↦ (restrictFin (b + 1) a, w)) (by fun_prop)).map
      (fun p ↦ Fin.snoc p.1 p.2), inferInstance, ?_⟩
    rw [partialTraj_succ_eq_comp (Nat.zero_le b), Kernel.comp_apply, h,
      Measure.bind_map (measurable_layout _ _).aemeasurable (Kernel.measurable _).aemeasurable,
      Measure.map_map (measurable_layout _ _) measurable_fin_snoc, Measure.compProd_eq_comp_prod,
      Measure.map_comp _ _ ((measurable_layout _ _).comp measurable_fin_snoc)]
    congr 1
    funext w
    rw [partialTraj_succ_self_layout, map_id_prod_apply _
      ((measurable_layout _ _).comp measurable_fin_snoc), comap_apply]
    rfl

/-- The trajectory up to time `d + 1`, laid out from the actions and the observations up to
time `d`. -/
def futureStart (d : ℕ) (p : (ℕ → A) × (Set.Iic d → O)) :
    Π i : Iic (d + 1), (ℕ → A) × (Fin i → O) :=
  layout (d + 1) p.1 (fun j ↦ p.2 ⟨j, Set.mem_Iic.2 (Nat.lt_succ_iff.1 j.2)⟩)

@[fun_prop]
lemma measurable_futureStart (d : ℕ) : Measurable (futureStart (A := A) (O := O) d) := by
  unfold futureStart layout
  fun_prop

/-! ### The future observations -/

/-- The law of the observations after time `d`, given the actions and the observations up to
time `d`: run `traj` from time `d + 1`. -/
def futureObs (d : ℕ) : Kernel ((ℕ → A) × (Set.Iic d → O)) (Set.Ioi d → O) :=
  ((traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (d + 1)).comap (futureStart d)
    (measurable_futureStart d)).map (fun ω ↦ restrictIoi d (obsOf ω))

instance (d : ℕ) : IsMarkovKernel (I.futureObs d) :=
  IsMarkovKernel.map _ (by fun_prop)

lemma futureObs_apply (d : ℕ) (p : (ℕ → A) × (Set.Iic d → O)) :
    I.futureObs d p = (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (d + 1)
      (futureStart d p)).map (fun ω ↦ restrictIoi d (obsOf ω)) := by
  rw [futureObs, Kernel.map_apply _ (by fun_prop), comap_apply]

/-- **The observations of an interface split into their past, followed by `futureObs`.** -/
theorem obsKernel_map_splitIicIoi (d : ℕ) (a : ℕ → A) :
    (I.obsKernel a).map (splitIicIoi d) =
      (I.obsKernel a).map (restrictIic d) ⊗ₘ
        (I.futureObs d).comap (Prod.mk a) measurable_prodMk_left := by
  obtain ⟨μ, hμ, hP⟩ := I.exists_partialTraj_start (d + 1) a
  have hpast : Measurable (pastObs (A := A) (O := O) d) := measurable_pastObs d
  have hfuture : Measurable fun ω : Π n, (ℕ → A) × (Fin n → O) ↦ restrictIoi d (obsOf ω) := by
    fun_prop
  -- Split the trajectory at time `d + 1`, and lay out its first part from `a`.
  have hsplit : (I.obsKernel a).map (splitIicIoi d) =
      μ.map (pastObs d ∘ layout (d + 1) a) ⊗ₘ
        (I.futureObs d).comap (Prod.mk a) measurable_prodMk_left := by
    calc (I.obsKernel a).map (splitIicIoi d)
        = (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step 0 (start a)).map
            (fun ω ↦ (pastObs d (frestrictLe (d + 1) ω), restrictIoi d (obsOf ω))) := by
          rw [obsKernel_apply_traj, Measure.map_map (MeasurableEquiv.measurable _) measurable_obsOf]
          rfl
      _ = (partialTraj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step 0 (d + 1) (start a) ⊗ₘ
            traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (d + 1)).map
            (fun p ↦ (pastObs d p.1, restrictIoi d (obsOf p.2))) := by
          rw [partialTraj_compProd_traj (Nat.zero_le _),
            Measure.map_map (g := fun p ↦ (pastObs d p.1, restrictIoi d (obsOf p.2)))
              (f := fun ω ↦ (frestrictLe (d + 1) ω, ω))
              ((hpast.comp measurable_fst).prodMk (hfuture.comp measurable_snd))
              ((measurable_frestrictLe _).prodMk measurable_id)]
          rfl
      _ = ((μ ⊗ₘ (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (d + 1)).comap
            (layout (d + 1) a) (measurable_layout _ _)).map
            (fun p ↦ (layout (d + 1) a p.1, p.2))).map
            (fun p ↦ (pastObs d p.1, restrictIoi d (obsOf p.2))) := by
          rw [hP, Measure.map_compProd_eq μ _ (measurable_layout _ _) (g := fun _ ω ↦ ω)
            measurable_snd _ fun w ↦ by rw [comap_apply, Measure.map_id']]
      _ = (μ ⊗ₘ (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (d + 1)).comap
            (layout (d + 1) a) (measurable_layout _ _)).map
            (fun p ↦ ((pastObs d ∘ layout (d + 1) a) p.1, restrictIoi d (obsOf p.2))) :=
          Measure.map_map ((hpast.comp measurable_fst).prodMk (hfuture.comp measurable_snd))
            (((measurable_layout _ _).comp measurable_fst).prodMk measurable_snd)
      _ = _ :=
          Measure.map_compProd_eq μ _ (hpast.comp (measurable_layout _ _))
            (g := fun _ ω ↦ restrictIoi d (obsOf ω)) (hfuture.comp measurable_snd) _ fun w ↦ by
              rw [comap_apply, comap_apply, futureObs_apply]
              rfl
  -- The first factor is the law of the observations up to time `d`.
  have hfst := congrArg Measure.fst hsplit
  rw [Measure.fst_compProd, Measure.fst, Measure.map_map measurable_fst
    (MeasurableEquiv.measurable _)] at hfst
  rw [hsplit, ← hfst]
  rfl

end Interface
