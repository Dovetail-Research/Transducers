import Transducers.InterfaceFuture

/-!
# The future of an interface after a history

Fix an interface `I`. After `k` observations `w : Fin k → O`, given the whole action sequence
`a : ℕ → A` (of which the first `k` entries are the past actions), the observations at times
`k, k + 1, …` have a law `I.futureFrom k (a, w)`, read off `Kernel.traj` started at time `k`.
Started at `k = 0` this is the observation kernel of `I`.

The law of the next `j` observations is `I.horizon k j`, defined step by step from the interface.
It only depends on the actions up to time `k + j`.

## Main results

* `Interface.futureFrom`: the observations from time `k` on, after a history of `k` observations.
* `Interface.horizon`: the law of the next `j` observations.
* `Interface.futureFrom_map_split`: after `j` more observations, the future is `futureFrom (k + j)`
  of the extended history.
* `Interface.futureFrom_map_restrictFin`: the next `j` observations have law `horizon k j`.
-/

open MeasureTheory ProbabilityTheory Finset Preorder ProbabilityTheory.Kernel

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-! ### Finite and infinite sequences -/

lemma fin_append_apply_of_lt {β : Type} {k j : ℕ} (w : Fin k → β) (v : Fin j → β)
    (i : Fin (k + j)) (h : (i : ℕ) < k) : Fin.append w v i = w ⟨i, h⟩ := by
  conv_lhs => rw [show i = Fin.castAdd j ⟨i, h⟩ from Fin.ext rfl]
  exact Fin.append_left w v _

lemma fin_append_apply_of_le {β : Type} {k j : ℕ} (w : Fin k → β) (v : Fin j → β)
    (i : Fin (k + j)) (h : k ≤ (i : ℕ)) :
    Fin.append w v i = v ⟨i - k, by have := i.isLt; omega⟩ := by
  conv_lhs => rw [show i = Fin.natAdd k ⟨i - k, by have := i.isLt; omega⟩ from
    Fin.ext (by simp only [Fin.natAdd_mk]; omega)]
  exact Fin.append_right w v _

lemma measurable_fin_append_right {β : Type} [MeasurableSpace β] {k j : ℕ} (w : Fin k → β) :
    Measurable (fun v : Fin j → β ↦ Fin.append w v) :=
  Measurable.of_eval fun i ↦ by
    induction i using Fin.addCases with
    | left i => simp only [Fin.append_left]; exact measurable_const
    | right i => simp only [Fin.append_right]; exact measurable_pi_apply i

/-- Drop the first `j` entries of a sequence. -/
def shiftBy {β : Type} (j : ℕ) (y : ℕ → β) : ℕ → β := fun n ↦ y (j + n)

@[fun_prop]
lemma measurable_shiftBy {β : Type} [MeasurableSpace β] (j : ℕ) :
    Measurable (shiftBy (β := β) j) :=
  Measurable.of_eval fun n ↦ measurable_pi_apply (j + n)

namespace Interface

variable (I : Interface A O)

/-! ### The future after a history -/

/-- The observations of a trajectory of `traj I.step` from time `k` on. -/
def obsFrom (k : ℕ) (ω : Π n, (ℕ → A) × (Fin n → O)) : ℕ → O := fun n ↦ obsOf ω (k + n)

@[fun_prop]
lemma measurable_obsFrom (k : ℕ) : Measurable (obsFrom (A := A) (O := O) k) :=
  Measurable.of_eval fun n ↦ (measurable_pi_apply (k + n)).comp measurable_obsOf

lemma measurable_layout_prod (k : ℕ) :
    Measurable fun p : (ℕ → A) × (Fin k → O) ↦ layout k p.1 p.2 := by
  unfold layout
  fun_prop

/-- **The future after a history.** Given the actions and `k` observations, the law of the
observations at times `k, k + 1, …`: run `traj` from time `k`. -/
def futureFrom (k : ℕ) : Kernel ((ℕ → A) × (Fin k → O)) (ℕ → O) :=
  ((traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step k).comap (fun p ↦ layout k p.1 p.2)
    (measurable_layout_prod k)).map (obsFrom k)

instance (k : ℕ) : IsMarkovKernel (I.futureFrom k) :=
  IsMarkovKernel.map _ (measurable_obsFrom k)

lemma futureFrom_apply (k : ℕ) (p : (ℕ → A) × (Fin k → O)) :
    I.futureFrom k p =
      (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step k (layout k p.1 p.2)).map
        (obsFrom k) := by
  rw [futureFrom, Kernel.map_apply _ (measurable_obsFrom k), comap_apply]

/-- With no history, the future is the observation kernel. -/
lemma futureFrom_zero (a : ℕ → A) (w : Fin 0 → O) : I.futureFrom 0 (a, w) = I.obsKernel a := by
  have hstart : layout 0 a w = start a := by
    funext i
    refine Prod.ext rfl (funext fun j ↦ ?_)
    exact absurd (j.2.trans_le (mem_Iic.1 i.2)) j.val.not_lt_zero
  have hobs : obsFrom (A := A) (O := O) 0 = obsOf := by
    funext ω n
    simp only [obsFrom, Nat.zero_add]
  rw [futureFrom_apply, obsKernel_apply_traj, hstart, hobs]

/-! ### The next observations -/

/-- **The law of the next `j` observations**, after the history `w` of `k` observations, given the
actions `b` up to time `k + j`: draw them one by one from the interface. -/
def horizon (k : ℕ) : (j : ℕ) → (Fin (k + j) → A) → (Fin k → O) → Measure (Fin j → O)
  | 0, _, _ => Measure.dirac Fin.elim0
  | j + 1, b, w =>
    (horizon k j (Fin.init b) w ⊗ₘ (I.κ (k + j)).1.comap (fun v ↦ (b, Fin.append w v))
      (measurable_const.prodMk (measurable_fin_append_right w))).map (fun p ↦ Fin.snoc p.1 p.2)

lemma horizon_zero (k : ℕ) (b : Fin (k + 0) → A) (w : Fin k → O) :
    I.horizon k 0 b w = Measure.dirac Fin.elim0 :=
  rfl

lemma horizon_succ (k j : ℕ) (b : Fin (k + (j + 1)) → A) (w : Fin k → O) :
    I.horizon k (j + 1) b w =
      (I.horizon k j (Fin.init b) w ⊗ₘ (I.κ (k + j)).1.comap (fun v ↦ (b, Fin.append w v))
        (measurable_const.prodMk (measurable_fin_append_right w))).map
        (fun p ↦ Fin.snoc p.1 p.2) :=
  rfl

instance (k j : ℕ) (b : Fin (k + j) → A) (w : Fin k → O) :
    IsProbabilityMeasure (I.horizon k j b w) := by
  induction j with
  | zero => rw [horizon_zero]; infer_instance
  | succ j ih =>
    rw [horizon_succ]
    have := ih (Fin.init b)
    infer_instance

/-- The trajectory from time `k` up to time `k + j` is laid out from the next `j` observations,
drawn from `horizon`. -/
lemma partialTraj_layout (k j : ℕ) (a : ℕ → A) (w : Fin k → O) :
    partialTraj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step k (k + j) (layout k a w) =
      (I.horizon k j (restrictFin (k + j) a) w).map
        (fun v ↦ layout (k + j) a (Fin.append w v)) := by
  induction j with
  | zero =>
    have hL : Measurable fun v : Fin 0 → O ↦ layout (k + 0) a (Fin.append w v) :=
      (measurable_layout _ _).comp (measurable_fin_append_right w)
    change partialTraj _ k k _ = _
    rw [partialTraj_self, Kernel.id_apply, horizon_zero, Measure.map_dirac' hL]
    congr 1
    funext i
    refine Prod.ext rfl (funext fun l ↦ ?_)
    simp only [layout]
    rw [fin_append_apply_of_lt _ _ _ (by have := l.isLt; have := mem_Iic.1 i.2; simp; omega)]
  | succ j ih =>
    have hL : Measurable fun v : Fin j → O ↦ layout (k + j) a (Fin.append w v) :=
      (measurable_layout _ _).comp (measurable_fin_append_right w)
    have hL' : Measurable fun v : Fin (j + 1) → O ↦
        layout (k + j + 1) a (Fin.append w v : Fin (k + (j + 1)) → O) :=
      (measurable_layout _ _).comp (measurable_fin_append_right w)
    change partialTraj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step k (k + j + 1)
      (layout k a w) =
      (I.horizon k (j + 1) (restrictFin (k + j + 1) a) w).map
        (fun v : Fin (j + 1) → O ↦ layout (k + j + 1) a (Fin.append w v : Fin (k + (j + 1)) → O))
    rw [partialTraj_succ_eq_comp (Nat.le_add_right k j),
      Kernel.comp_apply, ih, Measure.bind_map hL.aemeasurable (Kernel.measurable _).aemeasurable,
      horizon_succ, Measure.map_map hL' measurable_fin_snoc, Measure.compProd_eq_comp_prod,
      Measure.map_comp _ _ (hL'.comp measurable_fin_snoc)]
    congr 1
    funext v
    rw [partialTraj_succ_self_layout, map_id_prod_apply _ (hL'.comp measurable_fin_snoc),
      comap_apply]
    congr 1
    funext o
    simp only [Function.comp_apply, Fin.append_snoc]

/-- The next `j` observations, read off the trajectory up to time `k + j`. -/
def firstObs (k j : ℕ) (x : Π i : Iic (k + j), (ℕ → A) × (Fin i → O)) : Fin j → O :=
  fun i ↦ (x ⟨k + i + 1, mem_Iic.2 (by have := i.isLt; omega)⟩).2 (Fin.last (k + i))

@[fun_prop]
lemma measurable_firstObs (k j : ℕ) : Measurable (firstObs (A := A) (O := O) k j) := by
  unfold firstObs
  fun_prop

omit [MeasurableSpace A] [MeasurableSpace O] in
lemma firstObs_layout (k j : ℕ) (a : ℕ → A) (w : Fin k → O) (v : Fin j → O) :
    firstObs k j (layout (k + j) a (Fin.append w v)) = v := by
  funext i
  simp only [firstObs, layout]
  rw [fin_append_apply_of_le _ _ _ (by simp)]
  congr 1
  ext
  simp

/-- **Splitting the future after `j` more observations.** The next `j` observations are drawn from
`horizon`, and the observations after them from `futureFrom (k + j)` of the extended history. -/
theorem futureFrom_map_split (k j : ℕ) (a : ℕ → A) (w : Fin k → O) :
    (I.futureFrom k (a, w)).map (fun y ↦ (restrictFin j y, shiftBy j y)) =
      I.horizon k j (restrictFin (k + j) a) w ⊗ₘ
        (I.futureFrom (k + j)).comap (fun v ↦ (a, Fin.append w v))
          (measurable_const.prodMk (measurable_fin_append_right w)) := by
  set μ := I.horizon k j (restrictFin (k + j) a) w
  have hL : Measurable fun v : Fin j → O ↦ layout (k + j) a (Fin.append w v) :=
    (measurable_layout _ _).comp (measurable_fin_append_right w)
  calc (I.futureFrom k (a, w)).map (fun y ↦ (restrictFin j y, shiftBy j y))
      = (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step k (layout k a w)).map
          (fun ω ↦ (firstObs k j (frestrictLe (k + j) ω), obsFrom (k + j) ω)) := by
        rw [futureFrom_apply, Measure.map_map (by fun_prop) (measurable_obsFrom k)]
        congr 1
        funext ω
        refine Prod.ext rfl (funext fun n ↦ ?_)
        simp only [Function.comp_apply, shiftBy, obsFrom, Nat.add_assoc]
    _ = (partialTraj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step k (k + j) (layout k a w) ⊗ₘ
          traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (k + j)).map
          (fun p ↦ (firstObs k j p.1, obsFrom (k + j) p.2)) := by
        rw [partialTraj_compProd_traj (Nat.le_add_right k j),
          Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = ((μ ⊗ₘ (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (k + j)).comap _ hL).map
          (fun p ↦ (layout (k + j) a (Fin.append w p.1), p.2))).map
          (fun p ↦ (firstObs k j p.1, obsFrom (k + j) p.2)) := by
        rw [partialTraj_layout, Measure.map_compProd_eq μ _ hL (g := fun _ ω ↦ ω) measurable_snd _
          fun v ↦ by rw [comap_apply, Measure.map_id']]
    _ = (μ ⊗ₘ (traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step (k + j)).comap _ hL).map
          (fun p ↦ ((fun v ↦ v) p.1, obsFrom (k + j) p.2)) := by
        have hLp : Measurable fun p : (Fin j → O) × (Π n, (ℕ → A) × (Fin n → O)) ↦
            (layout (k + j) a (Fin.append w p.1), p.2) := (hL.comp measurable_fst).prodMk
          measurable_snd
        rw [Measure.map_map (by fun_prop) hLp]
        congr 1
        funext p
        simp only [Function.comp_apply, firstObs_layout]
    _ = _ := by
        rw [Measure.map_compProd_eq μ _ (f := fun v : Fin j → O ↦ v) measurable_id'
          (g := fun _ ω ↦ obsFrom (k + j) ω)
          ((measurable_obsFrom _).comp measurable_snd)
          ((I.futureFrom (k + j)).comap (fun v ↦ (a, Fin.append w v))
            (measurable_const.prodMk (measurable_fin_append_right w))) fun v ↦ by
            rw [comap_apply, comap_apply, futureFrom_apply], Measure.map_id']

/-- **The next `j` observations have law `horizon k j`.** In particular they only depend on the
actions up to time `k + j`. -/
theorem futureFrom_map_restrictFin (k j : ℕ) (a : ℕ → A) (w : Fin k → O) :
    (I.futureFrom k (a, w)).map (restrictFin j) = I.horizon k j (restrictFin (k + j) a) w := by
  have h := congrArg Measure.fst (I.futureFrom_map_split k j a w)
  rwa [Measure.fst_compProd, Measure.fst, Measure.map_map measurable_fst (by fun_prop)] at h

end Interface
