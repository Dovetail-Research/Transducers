import Transducers.InterfaceFuture
import Transducers.Representation

/-!
# The history transducer of an interface

An interface over `ℕ` is a transducer whose state at time `n` is the history so far: the actions
and observations at times `0, …, n`. To have a single state space, the history is stored as a pair
of sequences `(ℕ → A) × (ℕ → O)`, continued after time `n` by the initial state.

The run of the transducer is a deterministic function `histPath` of the observations, so its
causal-Markov property comes from that of the observations (`Interface.obsKernel_map_splitIicIoi`):
* up to time `d`, the history is read off the actions and observations up to time `d`;
* after time `d`, it is read off the state at time `d` and the later actions and observations.

## Main results

* `Interface.toTransducer`: the history transducer of an interface.
* `Interface.obsKernel_toTransducer`: from every initial state, its observation kernel is the
  observation kernel of the interface.
* `ProbabilityTheory.Kernel.anticipationFree_iff_exists_transducer`: a kernel is anticipation-free
  iff it is the observation kernel of a transducer started in some state.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-! ### Histories -/

/-- The run of the history transducer from the initial state `s`, on actions `a` and observations
`o`: at time `n` the state is the history up to time `n`, continued by `s`. -/
def histPath (s : (ℕ → A) × (ℕ → O)) (a : ℕ → A) (o : ℕ → O) :
    ℕ → ((ℕ → A) × (ℕ → O)) × O :=
  fun n ↦ ((padAfter n a s.1, padAfter n o s.2), o n)

lemma measurable_histPath :
    Measurable fun p : (((ℕ → A) × (ℕ → O)) × (ℕ → A)) × (ℕ → O) ↦ histPath p.1.1 p.1.2 p.2 := by
  unfold histPath
  fun_prop

lemma measurable_histPath' (s : (ℕ → A) × (ℕ → O)) (a : ℕ → A) : Measurable (histPath s a) :=
  measurable_histPath.comp (measurable_prodMk_left (x := (s, a)))

omit [MeasurableSpace A] [MeasurableSpace O] in
/-- The history up to time `d` only depends on the actions and observations up to time `d`. -/
lemma restrictIic_histPath (d : ℕ) (s : (ℕ → A) × (ℕ → O)) {a a' : ℕ → A} {o o' : ℕ → O}
    (ha : restrictIic d a = restrictIic d a') (ho : restrictIic d o = restrictIic d o') :
    restrictIic d (histPath s a o) = restrictIic d (histPath s a' o') := by
  funext e
  obtain ⟨e, he⟩ := e
  have hle : ∀ {β : Type} {x y : ℕ → β}, restrictIic d x = restrictIic d y → ∀ i ≤ e, x i = y i :=
    fun h i hi ↦ congrFun h ⟨i, Set.mem_Iic.2 (hi.trans (Set.mem_Iic.1 he))⟩
  simp only [restrictIic, histPath]
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)) (hle ho e le_rfl)
  all_goals
    simp only [padAfter]
    split_ifs with hi
    · first | exact hle ha i hi | exact hle ho i hi
    · rfl

omit [MeasurableSpace A] [MeasurableSpace O] in
/-- After time `d`, continuing the histories by a state at time `d` instead of by the initial
state `s` makes no difference. -/
lemma restrictIoi_histPath (d : ℕ) (s : (ℕ → A) × (ℕ → O)) (x a : ℕ → A) (y o : ℕ → O) :
    restrictIoi d (histPath (padAfter d x s.1, padAfter d y s.2) a o) =
      restrictIoi d (histPath s a o) := by
  funext e
  obtain ⟨e, he⟩ := e
  have he' : d < e := Set.mem_Ioi.1 he
  simp only [restrictIoi, histPath]
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)) rfl
  all_goals
    simp only [padAfter]
    split_ifs <;> first | rfl | lia

/-- The history up to time `d`, from the initial state `s`, the actions `a` and the observations
`v` up to time `d`. -/
def pastHist (d : ℕ) (s : (ℕ → A) × (ℕ → O)) (a : ℕ → A) (v : Set.Iic d → O) :
    Set.Iic d → ((ℕ → A) × (ℕ → O)) × O :=
  restrictIic d (histPath s a ((splitIicIoi d).symm (v, restrictIoi d s.2)))

lemma measurable_pastHist (d : ℕ) :
    Measurable fun p : (((ℕ → A) × (ℕ → O)) × (ℕ → A)) × (Set.Iic d → O) ↦
      pastHist d p.1.1 p.1.2 p.2 := by
  unfold pastHist histPath
  fun_prop

/-- The history after time `d`, from the state `z` at time `d`, the actions `c` and the
observations `w` after time `d`. -/
def futureHist (d : ℕ) (z : (ℕ → A) × (ℕ → O)) (c : Set.Ioi d → A) (w : Set.Ioi d → O) :
    Set.Ioi d → ((ℕ → A) × (ℕ → O)) × O :=
  restrictIoi d (histPath z ((splitIicIoi d).symm (restrictIic d z.1, c))
    ((splitIicIoi d).symm (restrictIic d z.2, w)))

lemma measurable_futureHist (d : ℕ) :
    Measurable fun p : (((ℕ → A) × (ℕ → O)) × (Set.Ioi d → A)) × (Set.Ioi d → O) ↦
      futureHist d p.1.1 p.1.2 p.2 := by
  unfold futureHist histPath
  fun_prop

namespace Interface

variable (I : Interface A O)

/-! ### The history kernel -/

/-- The kernel of the history transducer: draw the observations from the interface, and record
the history in the state. -/
def histKernel : Kernel (((ℕ → A) × (ℕ → O)) × (ℕ → A)) (ℕ → ((ℕ → A) × (ℕ → O)) × O) :=
  (Kernel.id ×ₖ I.obsKernel.comap Prod.snd measurable_snd).map
    (fun p ↦ histPath p.1.1 p.1.2 p.2)

instance : IsMarkovKernel I.histKernel :=
  IsMarkovKernel.map _ measurable_histPath

lemma histKernel_apply (s : (ℕ → A) × (ℕ → O)) (a : ℕ → A) :
    I.histKernel (s, a) = (I.obsKernel a).map (histPath s a) := by
  rw [histKernel, map_id_prod_apply _ measurable_histPath, comap_apply]

/-- The past of the history kernel up to time `d`, given the initial state and the actions up to
time `d`. -/
def pastKernel (d : ℕ) :
    Kernel (((ℕ → A) × (ℕ → O)) × (Set.Iic d → A)) (Set.Iic d → ((ℕ → A) × (ℕ → O)) × O) :=
  (Kernel.id ×ₖ (I.obsKernel.map (restrictIic d)).comap
      (fun p : ((ℕ → A) × (ℕ → O)) × (Set.Iic d → A) ↦
        (splitIicIoi d).symm (p.2, restrictIoi d p.1.1)) (by fun_prop)).map
    (fun q ↦ pastHist d q.1.1 ((splitIicIoi d).symm (q.1.2, restrictIoi d q.1.1.1)) q.2)

lemma measurable_pastKernel_fun (d : ℕ) :
    Measurable fun q : (((ℕ → A) × (ℕ → O)) × (Set.Iic d → A)) × (Set.Iic d → O) ↦
      pastHist d q.1.1 ((splitIicIoi d).symm (q.1.2, restrictIoi d q.1.1.1)) q.2 :=
  (measurable_pastHist d).comp
    (f := fun q : (((ℕ → A) × (ℕ → O)) × (Set.Iic d → A)) × (Set.Iic d → O) ↦
      ((q.1.1, (splitIicIoi d).symm (q.1.2, restrictIoi d q.1.1.1)), q.2))
    (by fun_prop)

instance (d : ℕ) : IsMarkovKernel (I.pastKernel d) :=
  have : IsMarkovKernel (I.obsKernel.map (restrictIic d)) :=
    IsMarkovKernel.map _ (measurable_restrictIic d)
  IsMarkovKernel.map _ (measurable_pastKernel_fun d)

lemma pastKernel_apply (d : ℕ) (s : (ℕ → A) × (ℕ → O)) (a : ℕ → A) :
    I.pastKernel d (s, restrictIic d a) =
      ((I.obsKernel a).map (restrictIic d)).map (pastHist d s a) := by
  rw [pastKernel, map_id_prod_apply _ (measurable_pastKernel_fun d), comap_apply,
    Kernel.map_apply _ (measurable_restrictIic d), I.anticipationFree_obsKernel d _ a (by simp)]
  congr 1
  funext v
  exact restrictIic_histPath d s (by simp) rfl

/-- The future of the history kernel after time `d`, given the state at time `d` and the actions
after time `d`: draw the observations from `futureObs`, given the actions and observations
recorded in the state. -/
def futureKernel (d : ℕ) :
    Kernel (((ℕ → A) × (ℕ → O)) × (Set.Ioi d → A)) (Set.Ioi d → ((ℕ → A) × (ℕ → O)) × O) :=
  (Kernel.id ×ₖ (I.futureObs d).comap
      (fun p : ((ℕ → A) × (ℕ → O)) × (Set.Ioi d → A) ↦
        ((splitIicIoi d).symm (restrictIic d p.1.1, p.2), restrictIic d p.1.2))
      (by fun_prop)).map
    (fun q ↦ futureHist d q.1.1 q.1.2 q.2)

instance (d : ℕ) : IsMarkovKernel (I.futureKernel d) :=
  IsMarkovKernel.map _ (measurable_futureHist d)

lemma futureKernel_apply (d : ℕ) (z : (ℕ → A) × (ℕ → O)) (c : Set.Ioi d → A) :
    I.futureKernel d (z, c) =
      (I.futureObs d ((splitIicIoi d).symm (restrictIic d z.1, c), restrictIic d z.2)).map
        (futureHist d z c) := by
  rw [futureKernel, map_id_prod_apply _ (measurable_futureHist d), comap_apply]

/-- **The history kernel is causal and Markov.** -/
theorem isCausalMarkov_histKernel : I.histKernel.IsCausalMarkov := by
  intro d
  refine ⟨I.pastKernel d, I.futureKernel d, inferInstance, inferInstance, fun s a ↦ ?_⟩
  let g : (Set.Iic d → O) → (Set.Ioi d → O) → Set.Ioi d → ((ℕ → A) × (ℕ → O)) × O :=
    fun v w ↦ restrictIoi d (histPath s a ((splitIicIoi d).symm (v, w)))
  have hg : Measurable fun p : (Set.Iic d → O) × (Set.Ioi d → O) ↦ g p.1 p.2 := by
    unfold g histPath
    fun_prop
  have hpast : Measurable (pastHist d s a) :=
    (measurable_pastHist d).comp (measurable_prodMk_left (x := (s, a)))
  -- The history is read off the observations up to time `d` and after time `d`.
  have hread : splitIicIoi d ∘ histPath s a =
      (fun p ↦ (pastHist d s a p.1, g p.1 p.2)) ∘ splitIicIoi d := by
    funext o
    simp only [Function.comp_apply, splitIicIoi_apply, g, splitIicIoi_symm_restrict]
    exact Prod.ext (restrictIic_histPath d s rfl (by simp)) rfl
  -- After time `d`, the history only depends on the state at time `d`.
  have hfuture : ∀ v, ((I.futureObs d).comap (Prod.mk a) measurable_prodMk_left v).map (g v) =
      (I.futureKernel d).comap (fun z ↦ ((z ⟨d, Set.mem_Iic.2 le_rfl⟩).1, restrictIoi d a))
        (by fun_prop) (pastHist d s a v) := by
    intro v
    rw [comap_apply, comap_apply]
    change _ = I.futureKernel d ((padAfter d a s.1,
      padAfter d ((splitIicIoi d).symm (v, restrictIoi d s.2)) s.2), restrictIoi d a)
    rw [futureKernel_apply]
    simp only [restrictIic_padAfter, splitIicIoi_symm_restrict, restrictIic_splitIicIoi_symm]
    congr 1
    funext w
    simp only [futureHist, g, restrictIic_padAfter, splitIicIoi_symm_restrict,
      restrictIic_splitIicIoi_symm]
    exact (restrictIoi_histPath d s _ _ _ _).symm
  rw [histKernel_apply, Measure.map_map (MeasurableEquiv.measurable _) (measurable_histPath' s a),
    hread, ← Measure.map_map (g := fun p ↦ (pastHist d s a p.1, g p.1 p.2))
      (f := splitIicIoi d) ((hpast.comp measurable_fst).prodMk hg)
      (MeasurableEquiv.measurable _),
    I.obsKernel_map_splitIicIoi d a, Measure.map_compProd_eq _ _ hpast hg _ hfuture,
    I.pastKernel_apply]

/-! ### The history transducer -/

/-- **The history transducer of an interface.** Its state at time `n` is the history of actions
and observations up to time `n`. -/
def toTransducer : Transducer ℕ A O where
  S := (ℕ → A) × (ℕ → O)
  K := ⟨I.histKernel, inferInstance⟩
  causalMarkov := I.isCausalMarkov_histKernel

/-- From every initial state, the history transducer has the observation kernel of the
interface. -/
theorem obsKernel_toTransducer (s : (ℕ → A) × (ℕ → O)) :
    I.toTransducer.obsKernel s = I.obsKernel := by
  ext1 a
  erw [Transducer.obsKernel_apply (t := I.toTransducer) (s := s)]
  change (I.histKernel (s, a)).map (fun (y : ℕ → ((ℕ → A) × (ℕ → O)) × O) n ↦ (y n).2) = _
  rw [histKernel_apply, Measure.map_map (by fun_prop) (measurable_histPath' s a)]
  exact Measure.map_id

end Interface

/-- **A kernel is anticipation-free iff it is the observation kernel of a transducer**, started in
some state. -/
theorem ProbabilityTheory.Kernel.anticipationFree_iff_exists_transducer [StandardBorelSpace O]
    [Nonempty O] [Nonempty A] (ν : Kernel (ℕ → A) (ℕ → O)) [IsMarkovKernel ν] :
    ν.AnticipationFree ↔ ∃ (t : Transducer ℕ A O) (s : t.S), t.obsKernel s = ν := by
  refine ⟨fun hν ↦ ?_, fun ⟨t, s, h⟩ ↦ h ▸ t.anticipationFree_obsKernel s⟩
  obtain ⟨s⟩ : Nonempty ((ℕ → A) × (ℕ → O)) := inferInstance
  exact ⟨ν.toInterface.toTransducer, s,
    (ν.toInterface.obsKernel_toTransducer s).trans (ν.obsKernel_toInterface hν)⟩
