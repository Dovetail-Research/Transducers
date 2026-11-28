import Transducers.Predictive.Residual
import Transducers.Predictive.Basic

/-!
# The ε-transducer of an interface

The *ε-transducer* `E(I)` of an interface `I` (Definition 7 of the paper) has as states the
classes of histories under predictive equivalence that can be reached from the empty history. From
the class of `h` it draws the observations from the residual `I_h`, and after each step it moves
to the class of the extended history (or stays put, on steps of probability zero).

The classes form a countable set as soon as the actions and observations do. We give the states the
discrete σ-algebra, which makes every map out of countable data measurable.

## Main results

* `Interface.epsTransducer`: the ε-transducer of an interface.
* `Interface.obsKernel_epsTransducer`: from the class of `h`, it has the residual `I_h` as
  observation kernel; in particular it implements `I` from the class of the empty history
  (`Interface.obsKernel_epsTransducer_init`, first half of Proposition 1).
* `Interface.isDeterministic_epsTransducer`, `Interface.isPredictive_epsTransducer`: it is
  deterministic, hence predictive (second half of the first part of Proposition 1).
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-! ### Extending and re-indexing sequences -/

/-- Extend a sequence on `Set.Iic d` to `ℕ` by repeating its last entry. -/
def extendIic {β : Type} (d : ℕ) (b : Set.Iic d → β) : ℕ → β :=
  fun i ↦ if h : i ≤ d then b ⟨i, Set.mem_Iic.2 h⟩ else b ⟨d, Set.mem_Iic.2 le_rfl⟩

@[fun_prop]
lemma measurable_extendIic {β : Type} [MeasurableSpace β] (d : ℕ) :
    Measurable (extendIic (β := β) d) :=
  Measurable.of_eval fun i ↦ by
    unfold extendIic
    split_ifs <;> exact measurable_pi_apply _

lemma extendIic_restrictIic {β : Type} (d : ℕ) (x : ℕ → β) {i : ℕ} (hi : i ≤ d) :
    extendIic d (restrictIic d x) i = x i := by
  simp [extendIic, restrictIic, hi]

/-- Re-index a sequence on `Set.Ioi d` to start at `0`. -/
def unshiftIoi {β : Type} (d : ℕ) (c : Set.Ioi d → β) : ℕ → β :=
  fun m ↦ c ⟨d + 1 + m, Set.mem_Ioi.2 (by omega)⟩

@[fun_prop]
lemma measurable_unshiftIoi {β : Type} [MeasurableSpace β] (d : ℕ) :
    Measurable (unshiftIoi (β := β) d) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- Re-index a sequence starting at `0` to start after `d`. -/
def reindexIoi {β : Type} (d : ℕ) (y : ℕ → β) : Set.Ioi d → β := fun e ↦ y (e - (d + 1))

@[fun_prop]
lemma measurable_reindexIoi {β : Type} [MeasurableSpace β] (d : ℕ) :
    Measurable (reindexIoi (β := β) d) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

lemma shiftBy_glue {β : Type} {j : ℕ} (v : Fin j → β) (r : ℕ → β) : shiftBy j (glue v r) = r :=
  funext fun n ↦ by simp [shiftBy, glue]

lemma glue_of_lt {β : Type} {j : ℕ} (v : Fin j → β) (r r' : ℕ → β) {i : ℕ} (hi : i < j) :
    glue v r i = glue v r' i := by
  simp [glue, hi]

namespace Interface

variable (I : Interface A O) [MeasurableSingletonClass O]

/-! ### The states -/

/-- The classes of histories reachable from the empty history by updates. -/
inductive Reachable : Quotient I.histSetoid → Prop
  | empty : Reachable ⟦FinHist.empty⟧
  | upd {c : Quotient I.histSetoid} (u : FinHist A O) : Reachable c → Reachable (I.upd c u)

/-- **The states of the ε-transducer**: the reachable classes of histories. -/
@[ext]
structure EpsState where
  /-- The class of histories. -/
  val : Quotient I.histSetoid
  reachable : I.Reachable val

instance : MeasurableSpace I.EpsState := ⊤

instance : MeasurableSingletonClass I.EpsState := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

instance [Countable A] [Countable O] : Countable I.EpsState :=
  Function.Injective.countable (f := EpsState.val) fun _ _ ↦ EpsState.ext

namespace EpsState

variable {I}

/-- The class of the empty history. -/
def init : I.EpsState := ⟨⟦FinHist.empty⟧, Reachable.empty⟩

/-- One step: the action `x` and the observation `y`. -/
def step (s : I.EpsState) (x : A) (y : O) : I.EpsState :=
  ⟨I.upd s.val (FinHist.single x y), Reachable.upd _ s.reachable⟩

/-- The run from `s`, along the actions `a` and the observations `o`: the state after the first
`n` steps. -/
def run (s : I.EpsState) (a : ℕ → A) (o : ℕ → O) : ℕ → I.EpsState
  | 0 => s
  | n + 1 => (run s a o n).step (a n) (o n)

lemma run_val (s : I.EpsState) (a : ℕ → A) (o : ℕ → O) (n : ℕ) :
    (s.run a o n).val = I.run s.val a o n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, step, Interface.run, ih]

/-- The state after `m` steps only depends on the first `m` steps. -/
lemma run_congr (s : I.EpsState) {a a' : ℕ → A} {o o' : ℕ → O} {m : ℕ}
    (ha : ∀ i < m, a i = a' i) (ho : ∀ i < m, o i = o' i) : s.run a o m = s.run a' o' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [run, ih (fun i hi ↦ ha i (by omega)) (fun i hi ↦ ho i (by omega)), ha m (by omega),
      ho m (by omega)]

/-- After `j` steps, the run continues from the state reached. -/
lemma run_add (s : I.EpsState) (a : ℕ → A) (o : ℕ → O) (j m : ℕ) :
    s.run a o (j + m) = (s.run a o j).run (shiftBy j a) (shiftBy j o) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, run, ih]; rfl

/-- The path of the ε-transducer: at time `n`, the state after time `n`, and the observation. -/
def path (s : I.EpsState) (a : ℕ → A) (o : ℕ → O) : ℕ → I.EpsState × O :=
  fun n ↦ (s.run a o (n + 1), o n)

variable [Countable A] [MeasurableSingletonClass A] [Countable O]

lemma measurable_run (s : I.EpsState) (n : ℕ) :
    Measurable fun p : (ℕ → A) × (ℕ → O) ↦ s.run p.1 p.2 n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have h1 : Measurable fun p : (ℕ → A) × (ℕ → O) ↦ (s.run p.1 p.2 n, p.1 n, p.2 n) :=
      ih.prodMk (((measurable_pi_apply n).comp measurable_fst).prodMk
        ((measurable_pi_apply n).comp measurable_snd))
    have h2 : Measurable fun q : I.EpsState × A × O ↦ q.1.step q.2.1 q.2.2 :=
      measurable_of_countable _
    simp only [run]
    exact (h2.comp h1 :)

lemma measurable_path (s : I.EpsState) :
    Measurable fun p : (ℕ → A) × (ℕ → O) ↦ s.path p.1 p.2 := by
  refine Measurable.of_eval fun n ↦ ?_
  have h : Measurable fun p : (ℕ → A) × (ℕ → O) ↦ (s.run p.1 p.2 (n + 1), p.2 n) :=
    (s.measurable_run (n + 1)).prodMk ((measurable_pi_apply n).comp measurable_snd)
  unfold path
  exact h

lemma measurable_path' (s : I.EpsState) (a : ℕ → A) : Measurable (s.path a) :=
  (s.measurable_path.comp measurable_prodMk_left :)

/-- The path up to time `d`, as a function of the first `d + 1` observations. -/
def pastPath (s : I.EpsState) (a : ℕ → A) (d : ℕ) (v : Fin (d + 1) → O) :
    Set.Iic d → I.EpsState × O :=
  restrictIic d (s.path a (glue v fun _ ↦ v 0))

omit [Countable A] [MeasurableSingletonClass A] [Countable O] in
lemma pastPath_state (s : I.EpsState) (a : ℕ → A) (d : ℕ) (v : Fin (d + 1) → O) :
    (s.pastPath a d v ⟨d, Set.mem_Iic.2 le_rfl⟩).1 = s.run a (glue v fun _ ↦ v 0) (d + 1) :=
  rfl

omit [Countable A] [MeasurableSingletonClass A] [Countable O] in
/-- The path up to time `d` only depends on the actions and observations up to time `d`. -/
lemma restrictIic_path (s : I.EpsState) {d : ℕ} {a a' : ℕ → A} (ha : ∀ i ≤ d, a' i = a i)
    (v : Fin (d + 1) → O) (r : ℕ → O) :
    restrictIic d (s.path a' (glue v r)) = s.pastPath a d v := by
  funext e
  obtain ⟨e, he⟩ := e
  have he' : e ≤ d := Set.mem_Iic.1 he
  simp only [pastPath, restrictIic, path]
  refine Prod.ext (s.run_congr (m := e + 1) (fun i hi ↦ ha i (by omega))
    (fun i hi ↦ glue_of_lt (i := i) v r _ (by omega)))
    (glue_of_lt (i := e) v r (fun _ ↦ v 0) (by omega))

omit [Countable A] [MeasurableSingletonClass A] [Countable O] in
/-- The path after time `d` is the path from the state at time `d`, on the later actions and
observations. -/
lemma restrictIoi_path (s : I.EpsState) (a : ℕ → A) (d : ℕ) (v : Fin (d + 1) → O) (r : ℕ → O) :
    restrictIoi d (s.path a (glue v r)) =
      reindexIoi d ((s.run a (glue v fun _ ↦ v 0) (d + 1)).path (shiftBy (d + 1) a) r) := by
  funext e
  obtain ⟨e, he⟩ := e
  have he' : d < e := Set.mem_Ioi.1 he
  simp only [restrictIoi, reindexIoi, path]
  refine Prod.ext ?_ ?_
  · rw [show e + 1 = (d + 1) + (e - (d + 1) + 1) by omega, run_add, shiftBy_glue,
      s.run_congr (m := d + 1) (a' := a) (o' := glue v fun _ ↦ v 0) (fun _ _ ↦ rfl)
        (fun i hi ↦ glue_of_lt v r _ hi)]
  · simp only [glue, show ¬ e < d + 1 by omega, ↓reduceDIte]

end EpsState

/-! ### The ε-transducer -/

variable [Countable A] [MeasurableSingletonClass A] [Countable O]

/-- The kernel of the ε-transducer: from the state `s`, draw the observations from the residual
of `s`, and follow the run. -/
def epsKernel : Kernel (I.EpsState × (ℕ → A)) (ℕ → I.EpsState × O) where
  toFun p := (I.residQ p.1.val p.2).map (p.1.path p.2)
  measurable' := measurable_from_prod_countable_right fun s ↦ by
    have : (fun a ↦ (I.residQ s.val a).map (s.path a)) =
        (Kernel.id ×ₖ I.residQ s.val).map (fun q ↦ s.path q.1 q.2) := by
      funext a
      rw [map_id_prod_apply _ s.measurable_path]
    exact this ▸ Kernel.measurable _

lemma epsKernel_apply (s : I.EpsState) (a : ℕ → A) :
    I.epsKernel (s, a) = (I.residQ s.val a).map (s.path a) :=
  rfl

instance : IsMarkovKernel I.epsKernel :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))⟩

/-- The past of the ε-kernel up to time `d`. -/
def epsPast (d : ℕ) : Kernel (I.EpsState × (Set.Iic d → A)) (Set.Iic d → I.EpsState × O) :=
  (I.epsKernel.comap (fun p ↦ (p.1, extendIic d p.2)) (by fun_prop)).map (restrictIic d)

instance (d : ℕ) : IsMarkovKernel (I.epsPast d) :=
  IsMarkovKernel.map _ (measurable_restrictIic d)

/-- The future of the ε-kernel after time `d`, from the state at time `d`. -/
def epsFuture (d : ℕ) : Kernel (I.EpsState × (Set.Ioi d → A)) (Set.Ioi d → I.EpsState × O) :=
  (I.epsKernel.comap (fun p ↦ (p.1, unshiftIoi d p.2)) (by fun_prop)).map (reindexIoi d)

instance (d : ℕ) : IsMarkovKernel (I.epsFuture d) :=
  IsMarkovKernel.map _ (measurable_reindexIoi d)

lemma epsFuture_apply (d : ℕ) (z : I.EpsState) (c : Set.Ioi d → A) :
    I.epsFuture d (z, c) =
      ((I.residQ z.val (unshiftIoi d c)).map (z.path (unshiftIoi d c))).map (reindexIoi d) := by
  rw [epsFuture, Kernel.map_apply _ (measurable_reindexIoi d), comap_apply, epsKernel_apply]

/-- **The ε-kernel is causal and Markov.** -/
theorem isCausalMarkov_epsKernel : I.epsKernel.IsCausalMarkov := by
  intro d
  refine ⟨I.epsPast d, I.epsFuture d, inferInstance, inferInstance, fun s a ↦ ?_⟩
  obtain ⟨h, hs⟩ : ∃ h, s.val = ⟦h⟧ := ⟨s.val.out, (Quotient.out_eq _).symm⟩
  have hP : Measurable (s.pastPath a d) := measurable_of_countable _
  have hQ : Measurable fun p : (Fin (d + 1) → O) × (ℕ → O) ↦
      restrictIoi d (s.path a (glue p.1 p.2)) :=
    measurable_from_prod_countable_right fun v ↦
      ((measurable_restrictIoi d).comp ((s.measurable_path' a).comp (measurable_glue v)) :)
  -- The residual at the state at time `d`, on the later actions.
  let R : Kernel (Fin (d + 1) → O) (ℕ → O) := ofFunOfCountable fun v ↦
    I.residQ (s.run a (glue v fun _ ↦ v 0) (d + 1)).val (shiftBy (d + 1) a)
  have : IsMarkovKernel R := ⟨fun v ↦ inferInstanceAs (IsProbabilityMeasure (I.residQ _ _))⟩
  have hRv : ∀ v, R v = I.residQ (s.run a (glue v fun _ ↦ v 0) (d + 1)).val (shiftBy (d + 1) a) :=
    fun _ ↦ rfl
  -- The split of the observations after `d + 1` steps.
  set μ := I.horizon h.1 (d + 1) (Fin.append h.2.1 (restrictFin (d + 1) a)) h.2.2
  let F : Kernel (Fin (d + 1) → O) (ℕ → O) := (I.futureFrom (h.1 + (d + 1))).comap
    (fun v ↦ (glue (Fin.append h.2.1 (restrictFin (d + 1) a)) (shiftBy (d + 1) a),
      Fin.append h.2.2 v)) (measurable_const.prodMk (measurable_fin_append_right _))
  have hsplit : (I.resid h a).map (fun y ↦ (restrictFin (d + 1) y, shiftBy (d + 1) y)) =
      μ ⊗ₘ F := by
    rw [← I.resid_map_split, glue_restrictFin_shiftBy]
  -- Almost surely, the residual at the state at time `d` is the one of the history so far.
  have hR : ∀ᵐ v ∂μ, F v = R v := by
    have hμ : μ = (I.resid h a).map (restrictFin (d + 1)) := (I.resid_map_restrictFin' h _ a).symm
    rw [hμ, ae_map_iff
      (measurable_restrictFin (d + 1)).aemeasurable (Set.to_countable _).measurableSet]
    filter_upwards [I.ae_run_eq h a] with o ho
    have h1 : s.run a (glue (restrictFin (d + 1) o) fun _ ↦ restrictFin (d + 1) o 0) (d + 1) =
        s.run a o (d + 1) :=
      s.run_congr (fun _ _ ↦ rfl) (fun i hi ↦ by simp [glue, restrictFin, hi])
    rw [hRv, h1, EpsState.run_val, hs, ho (d + 1), residQ_mk, resid_apply, comap_apply]
    rfl
  -- The future after time `d` is drawn from `R`, from the state at time `d`.
  have hfuture : ∀ v, (R v).map (fun r ↦ restrictIoi d (s.path a (glue v r))) =
      (I.epsFuture d).comap (fun z ↦ ((z ⟨d, Set.mem_Iic.2 le_rfl⟩).1, restrictIoi d a))
        (by fun_prop) (s.pastPath a d v) := by
    intro v
    have hu : unshiftIoi d (restrictIoi d a) = shiftBy (d + 1) a := rfl
    rw [comap_apply, epsFuture_apply, EpsState.pastPath_state, hu, ← hRv,
      Measure.map_map (measurable_reindexIoi d) (EpsState.measurable_path' _ _)]
    refine congrArg (Measure.map · (R v)) (funext fun r ↦ ?_)
    exact s.restrictIoi_path a d v r
  -- The past up to time `d` is drawn from the first `d + 1` observations.
  have hpastK : μ.map (s.pastPath a d) = I.epsPast d (s, restrictIic d a) := by
    set a' := extendIic d (restrictIic d a)
    have ha' : ∀ i ≤ d, a' i = a i := fun i hi ↦ extendIic_restrictIic d a hi
    have hra : restrictFin (d + 1) a' = restrictFin (d + 1) a :=
      funext fun i ↦ ha' i (by have := i.isLt; omega)
    rw [epsPast, Kernel.map_apply _ (measurable_restrictIic d), comap_apply, epsKernel_apply, hs,
      residQ_mk, Measure.map_map (measurable_restrictIic d) (s.measurable_path' a')]
    have hfun : restrictIic d ∘ s.path a' = s.pastPath a d ∘ restrictFin (d + 1) := by
      funext o
      simp only [Function.comp_apply]
      conv_lhs => rw [← glue_restrictFin_shiftBy (d + 1) o]
      exact s.restrictIic_path ha' _ _
    rw [hfun, ← Measure.map_map hP (measurable_restrictFin _), I.resid_map_restrictFin', hra]
  calc (I.epsKernel (s, a)).map (splitIicIoi d)
      = ((I.resid h a).map (fun y ↦ (restrictFin (d + 1) y, shiftBy (d + 1) y))).map
          (fun p ↦ (s.pastPath a d p.1, restrictIoi d (s.path a (glue p.1 p.2)))) := by
        have hPQ : Measurable fun p : (Fin (d + 1) → O) × (ℕ → O) ↦
            (s.pastPath a d p.1, restrictIoi d (s.path a (glue p.1 p.2))) :=
          (hP.comp measurable_fst).prodMk hQ
        have hsp : Measurable fun y : ℕ → O ↦ (restrictFin (d + 1) y, shiftBy (d + 1) y) :=
          (measurable_restrictFin _).prodMk (measurable_shiftBy _)
        rw [epsKernel_apply, hs, residQ_mk, Measure.map_map (MeasurableEquiv.measurable _)
          (s.measurable_path' a), Measure.map_map hPQ hsp]
        refine congrArg (Measure.map · (I.resid h a)) (funext fun o ↦ ?_)
        simp only [Function.comp_apply, splitIicIoi_apply]
        conv_lhs => rw [← glue_restrictFin_shiftBy (d + 1) o]
        exact Prod.ext (s.restrictIic_path (fun _ _ ↦ rfl) _ _) rfl
    _ = (μ ⊗ₘ R).map
          (fun p ↦ (s.pastPath a d p.1, restrictIoi d (s.path a (glue p.1 p.2)))) := by
        rw [hsplit, Measure.compProd_congr hR]
    _ = μ.map (s.pastPath a d) ⊗ₘ (I.epsFuture d).comap
          (fun z ↦ ((z ⟨d, Set.mem_Iic.2 le_rfl⟩).1, restrictIoi d a)) (by fun_prop) :=
        Measure.map_compProd_eq μ R hP hQ _ hfuture
    _ = _ := by rw [hpastK]

/-- **The ε-transducer of an interface** (Definition 7). -/
def epsTransducer : Transducer ℕ A O where
  S := I.EpsState
  K := ⟨I.epsKernel, inferInstance⟩
  causalMarkov := I.isCausalMarkov_epsKernel

/-- From the class of a history, the ε-transducer has the residual as observation kernel. -/
theorem obsKernel_epsTransducer (s : I.EpsState) :
    I.epsTransducer.obsKernel s = I.residQ s.val := by
  ext1 a
  erw [Transducer.obsKernel_apply (t := I.epsTransducer) (s := s)]
  change (I.epsKernel (s, a)).map (fun (y : ℕ → I.EpsState × O) n ↦ (y n).2) = _
  rw [epsKernel_apply, Measure.map_map (by fun_prop) (s.measurable_path' a)]
  exact Measure.map_id'

/-- **The ε-transducer implements the interface** (first part of Proposition 1): from the class
of the empty history, its observation kernel is the one of `I`. -/
theorem obsKernel_epsTransducer_init :
    I.epsTransducer.obsKernel EpsState.init = I.obsKernel := by
  rw [obsKernel_epsTransducer]
  exact I.resid_empty

/-- **The ε-transducer is deterministic**: its state is a function of the initial state and the
history so far. -/
theorem isDeterministic_epsTransducer : I.epsTransducer.IsDeterministic := by
  have hσ : ∀ d, Measurable fun p : I.EpsState × (Set.Iic d → A) × (Set.Iic d → O) ↦
      p.1.run (extendIic d p.2.1) (extendIic d p.2.2) (d + 1) := fun d ↦
    measurable_of_countable _
  refine ⟨fun d p ↦ EpsState.run (I := I) p.1 (extendIic d p.2.1) (extendIic d p.2.2) (d + 1), hσ,
    fun (s : I.EpsState) a ↦ ?_⟩
  erw [obsKernel_epsTransducer]
  refine (I.epsKernel_apply s a).trans
    (congrArg (Measure.map · (I.residQ s.val a)) (funext fun o ↦ funext fun n ↦ ?_))
  exact Prod.ext (EpsState.run_congr _ (fun i hi ↦ (extendIic_restrictIic n a (by omega)).symm)
    (fun i hi ↦ (extendIic_restrictIic n o (by omega)).symm)) rfl

/-- **The ε-transducer is predictive** (first part of Proposition 1). -/
theorem isPredictive_epsTransducer : I.epsTransducer.IsPredictive :=
  I.isDeterministic_epsTransducer.isPredictive

end Interface
